import ARA.Basic

/-!
  ### Grind implementation

  We build a localized, specialized environment for the `grind` tactic.
  By explicitly defining how to handle `ENNReal` arithmetic, finite sums,
  and uniform distribution binds, we prevent `grind` from getting lost in
  the infinite measure space definitions.
-/

/-!
  #### Environment Audit (`grind` tags already present in current environment)

  Audit scope used:
  - Mathlib source in `.lake/packages/mathlib/Mathlib`
  - Lean core source in `~/.elan/toolchains/.../src/lean/Init`

  Target query:
  - declarations tagged with one of
    `@[grind]`, `@[grind =]`, `@[grind →]`, `@[grind ←]`
  - and related to `PMF`, `ENNReal`, or `uniformOfFintype`.

  Result summary:
  - **No existing `@[grind*]` lemmas in Mathlib's `Probability` folder**.
  - **No existing `@[grind*]` lemmas in Mathlib's `Data/ENNReal` folder**.
  - **No existing `@[grind*]` lemma mentioning `uniformOfFintype`**.

  Closest already-available automation relevant to your proofs:
  - Lean core `Init/Data/List/Lemmas.lean`:
    `@[grind =] List.filter_cons` and
    `grind_pattern List.length_filter_le => (l.filter p).length`.
  - Lean core `Init/Data/Nat/Basic.lean`:
    `@[grind =] Nat.min_def` and `@[grind =] Nat.max_def`.
  - Mathlib `Order/Defs/LinearOrder.lean`:
    `@[grind =] min_def` and `@[grind =] max_def` for generic linear orders.
-/

/-!
  #### Tactic Subsumption (what you do **not** need to manually tag)

  In your current setup, `grind` already leverages enough built-in support that:

  - For **basic List reductions** around filters and lengths, you usually do *not*
    need custom tags:
    - `filter` unfolding is already exposed (`@[grind =] List.filter_cons`),
    - and `length` bounds are discovered by pattern-triggered use of
      `List.length_filter_le`.

  - For **Nat min/max normalization**, you usually do *not* need to add custom
    `min/max` grind lemmas:
    - `Nat.min_def` / `Nat.max_def` are already tagged for `grind`,
    - and `simp` can close branches using standard lemmas such as
      `Nat.min_eq_left`, `Nat.max_eq_right`, etc., once inequalities are known.

  - For **linear Nat arithmetic side conditions**, you usually do *not* need to
    restate routine arithmetic facts:
    - `grind` has built-in ordered/ring arithmetic infrastructure,
    - and for purely Presburger-style leftovers, `omega` remains a good fallback.

  Practical takeaway: manually tag only the *bridging lemmas* specific to PMF/ENNReal
  semantics (e.g. bind unfolding into finite sums), not generic list/Nat plumbing.
-/

/-!
  #### Extension Strategy (local, robust, timeout-resistant)

  Best practices for your PMF workflow:
  1. Put experimental grind rules in a small local `section`.
  2. Prefer one-direction rules (`@[grind →]`) to avoid rewrite loops.
  3. Keep hypotheses explicit (`x ≠ 0`, `x ≠ ⊤`) so e-matching is selective.
  4. Register only domain-bridge lemmas (PMF bind/uniform/pure), not every algebraic identity.
  5. Use `grind only [...]` when debugging to bound search space.
  6. Promote to global `@[grind =]` only after profiling several representative goals.
-/

/-!
  #### Detailed Design Rationale

  The toolkit below addresses all the pain points identified in the Phase 1
  and Phase 2 proofs.  It is organized into three layers:

  **Layer A — `grind` Rules (e-matching).**
  These are equational (`@[grind =]`) and forward (`@[grind →]`) rules that
  `grind` can fire automatically via its e-matching engine. Only lemmas
  whose universally-quantified parameters can all be inferred from a
  pattern in the LHS are eligible; the rest are handled by Layer B.

  **Layer B — `pmf_simp` Tactic Macro.**
  A curated `simp only [...]` call covering ~40 lemmas that collectively
  reduce PMF goals: monad laws, `tsum` over `Fin n` / `Bool`, uniform
  distribution weights, `if/ite` arithmetic, and ENNReal normalization.
  Followed by fallback passes of `simp`, `norm_num`, and `ring` to close
  residual arithmetic. Handles all the lemmas that `grind` cannot accept
  due to pattern restrictions.

  **Layer C — Standalone Derived Lemmas.**
  Higher-level lemmas proved once (e.g., "uniform bind where all branches
  agree collapses to the common value") that can be invoked by name in
  more complex proofs.

  ##### Mapping to Phase 1 / Phase 2 Pain Points

  | Pain point                                     | Layer | Key lemmas / tactics              |
  |------------------------------------------------|-------|-----------------------------------|
  | `calc` blocks for `2⁻¹*t + 2⁻¹*t = t`         | A+B   | `ennreal_inv_nsmul_cancel`, `pmf_simp` |
  | `tsum_eq_single` + `rcases` over `Fin`         | B     | `pmf_simp` (uses `tsum_fintype` + `Fin.sum_univ_*`) |
  | `change` to rewrite `do` notation as `bind`    | A+B   | `PMF.pure_bind`, `PMF.bind_apply` |
  | Manual `Functor.map` unfolding                  | B     | `PMF.pure_map`, `PMF.map_apply`   |
  | `Fintype.card` detours for uniform weights     | A+B   | `pmf_uniformOfFintype_fin_one`, `Fintype.card_fin` |
  | `bindOnSupport` ↔ `bind` conversion            | A     | `PMF.pure_bindOnSupport`, `PMF.bindOnSupport_apply` |
  | ENNReal non-zero / non-top side conditions     | A     | `ennreal_natCast_inv_ne_zero`, `ennreal_natCast_inv_ne_top` |
-/

namespace ARA

open ENNReal PMF


/-! ================================================================
    LAYER A: `@[simp]` Monad Normalization + `@[grind]` Domain Bridge
    ================================================================

  **Design principle:**
  - `@[simp]` for the *monad laws* — these are universally safe rewrite rules
    that normalize any PMF expression (pure_bind, bind_pure, bind_const,
    bind_bind). Follows Mathlib convention for monad normalization.
  - `@[grind =]` only for *domain-bridge* lemmas — things that connect the PMF
    world to concrete arithmetic (bind_apply → tsum, uniformOfFintype_apply →
    inverse cardinality, ENNReal inverse cancellation). These are the lemmas
    where `simp` alone can't close the goal but `grind`'s e-matching shines.
  - `@[grind →]` for forward-reasoning side conditions (ne_zero, ne_top).
-/

/-! ##### A.1  ENNReal Arithmetic -/

lemma ennreal_inv_mul_add_inv_mul (c a b : ENNReal) :
    c⁻¹ * a + c⁻¹ * b = c⁻¹ * (a + b) := by ring

@[grind =]
lemma ennreal_natCast_inv_mul_self {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ * (n : ENNReal) = 1 :=
  ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)

@[grind =]
lemma ennreal_natCast_mul_inv_self {n : ℕ} [NeZero n] :
    (n : ENNReal) * (n : ENNReal)⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)

@[grind →]
lemma ennreal_natCast_inv_ne_zero {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ ≠ 0 :=
  ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)

@[grind →]
lemma ennreal_natCast_inv_ne_top {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ ≠ ⊤ :=
  ENNReal.inv_ne_top.mpr (by exact_mod_cast NeZero.ne n)

lemma ennreal_add_halves' (a : ENNReal) : a / 2 + a / 2 = a :=
  ENNReal.add_halves a

attribute [grind =] ENNReal.div_add_div_same

/-- Summing `n` copies of `n⁻¹ * t` over `Fin n` gives `t`. -/
lemma ennreal_inv_nsmul_cancel {n : ℕ} [NeZero n] (t : ENNReal) :
    ∑ _i : Fin n, (n : ENNReal)⁻¹ * t = t := by
  rw [Finset.sum_const]; simp [Fintype.card_fin]
  rw [← mul_assoc, ENNReal.mul_inv_cancel]
  · simp
  · exact_mod_cast NeZero.ne n
  · exact ENNReal.natCast_ne_top n


/-! ##### A.2  PMF Monad Laws (`@[simp]` — safe normalization) -/

-- These follow Mathlib convention: monad identity/associativity laws are @[simp].
attribute [simp] PMF.pure_bind    -- `pure a >>= f = f a`
attribute [simp] PMF.bind_pure    -- `p >>= pure = p`
attribute [simp] PMF.bind_const   -- `p >>= (fun _ => q) = q`
attribute [simp] PMF.bind_bind    -- `(p >>= f) >>= g = p >>= (fun a => f a >>= g)`
attribute [simp] PMF.pure_map     -- `f <$> pure a = pure (f a)`
attribute [simp] PMF.map_id       -- `id <$> p = p`

-- Also register for grind (grind and simp are independent engines).
attribute [grind =] PMF.pure_bind
attribute [grind =] PMF.bind_pure
attribute [grind =] PMF.bind_bind


/-! ##### A.3  PMF Pointwise Application & Distribution Weights (`@[grind =]` — domain bridge) -/

-- These expand PMF expressions into concrete arithmetic. Not safe as @[simp]
-- because they introduce tsum/ite which can blow up, but perfect for grind's
-- e-matching when the goal already mentions these terms.
attribute [grind =] PMF.pure_apply            -- `pure a b = if b = a then 1 else 0`
attribute [grind =] PMF.bind_apply            -- `(p >>= f) b = ∑' a, p a * (f a) b`
attribute [grind =] PMF.map_apply             -- `(f <$> p) b = ∑' a, if f a = b then p a else 0`
attribute [grind =] PMF.uniformOfFintype_apply -- `uniformOfFintype α a = (card α)⁻¹`
attribute [grind =] PMF.uniformOfFinset_apply  -- `uniformOfFinset s a = if a ∈ s then (card s)⁻¹ else 0`
attribute [grind =] PMF.bernoulli_apply        -- `bernoulli p b = if b then p else 1-p`
attribute [grind =] Fintype.card_fin           -- `card (Fin n) = n`
attribute [grind =] Fintype.card_bool          -- `card Bool = 2`

-- map/bind interaction laws (grind only — not @[simp] to avoid rewrite loops)
attribute [grind =] PMF.map_comp       -- `f <$> (g <$> p) = (f ∘ g) <$> p`
attribute [grind =] PMF.bind_map       -- `(f <$> p) >>= q = p >>= (q ∘ f)`
attribute [grind =] PMF.map_bind       -- `f <$> (p >>= q) = p >>= (fun a => f <$> q a)`
attribute [grind =] PMF.bind_pure_comp -- `p >>= (pure ∘ f) = f <$> p`


/-! ##### A.4  Support & bindOnSupport -/

attribute [grind =] PMF.support_uniformOfFintype    -- support is everything
attribute [grind =] PMF.support_uniformOfFinset     -- support is the finset
attribute [grind =] PMF.support_pure                -- support of pure is singleton
attribute [grind =] PMF.mem_support_iff             -- membership ↔ nonzero prob
attribute [grind =] PMF.support_bind                -- support of bind
attribute [grind =] PMF.mem_support_uniformOfFinset_iff
attribute [grind =] PMF.pure_bindOnSupport          -- `pure a >>= f = f a _`
attribute [grind =] PMF.bindOnSupport_apply         -- pointwise expansion


/-! ================================================================
    LAYER B: `pmf_simp` — Probability Computation Tactic
    ================================================================

  Use `pmf_simp` when computing concrete probability values, e.g.:
  - `P(X = 3) = 1/12`
  - `(p.bind f) b = p 0 * (f 0) b + p 1 * (f 1) b`

  It collapses tsum to finite sums, applies distribution weights,
  and cleans up arithmetic. NOT meant for correctness proofs
  (use `pmf_correct` below for those).
-/
macro "pmf_simp" : tactic =>
  `(tactic| (
    simp only [
      -- Tsum → Finset.sum collapse
      tsum_fintype,
      Fin.sum_univ_one, Fin.sum_univ_two, Fin.sum_univ_three,
      Fin.sum_univ_four, Fin.sum_univ_five, Fin.sum_univ_six,
      Fin.sum_univ_seven, Fin.sum_univ_eight,
      Fintype.sum_bool,
      tsum_ite_eq,
      -- PMF monad + application
      PMF.tsum_coe,
      PMF.pure_bind, PMF.bind_pure, PMF.pure_apply,
      PMF.bind_apply, PMF.bind_const,
      PMF.pure_map, PMF.map_apply, PMF.map_id,
      PMF.bind_pure_comp,
      -- PMF distributions
      PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply,
      PMF.bernoulli_apply,
      -- bindOnSupport
      PMF.bindOnSupport_eq_bind, PMF.pure_bindOnSupport,
      PMF.bindOnSupport_apply,
      -- Cardinality
      Fintype.card_fin, Fintype.card_bool,
      -- Conditional arithmetic
      ite_mul, mul_ite,
      Finset.sum_ite_eq, Finset.sum_ite_eq',
      -- Basic arithmetic cleanup
      mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add,
      ENNReal.inv_two_add_inv_two,
      -- Boolean / if-then-else cleanup
      if_true, if_false, ite_self, dite_true, dite_false,
      eq_self_iff_true, ne_eq,
      -- Finset membership
      Finset.mem_univ, Finset.mem_singleton, Finset.mem_insert
    ]
    <;> try simp
    <;> try norm_num
    <;> try ring_nf))

/-- `pmf_norm` extends `pmf_simp` with `omega` for index bounds. -/
macro "pmf_norm" : tactic =>
  `(tactic| (
    try pmf_simp
    <;> try omega
    <;> try (simp; ring_nf)
    <;> try norm_num))


/-! ================================================================
    LAYER C: Reusable Derived Lemmas
    ================================================================

  Lemmas proved once, used by name in algorithm-specific proofs.
  These are the building blocks for correctness and probability proofs.
-/

/-- When all branches produce the same PMF, `bindOnSupport` collapses. -/
lemma PMF.bindOnSupport_const {α β : Type*} (p : PMF α)
    (q : PMF β) :
    (p.bindOnSupport fun _ _ => q) = q := by
  ext b; simp [show ∀ a, (if p a = 0 then (0 : ENNReal) else p a * q b) = p a * q b from
      fun a => by split_ifs with h <;> simp_all]

/-- `uniformOfFintype (Fin 1)` is `pure 0` — singleton base case. -/
lemma pmf_uniformOfFintype_fin_one :
    PMF.uniformOfFintype (Fin 1) = PMF.pure (0 : Fin 1) := by
  ext a
  have ha : a = 0 := Fin.ext (by omega)
  subst ha; simp [PMF.uniformOfFintype_apply]

/-- `bind` over a finite-type PMF unfolds to a `Finset.sum`. -/
lemma pmf_bind_apply_fintype {α β : Type*} [Fintype α] (p : PMF α)
    (f : α → PMF β) (b : β) :
    (p.bind f) b = ∑ a : α, p a * (f a) b := by
  rw [PMF.bind_apply, tsum_fintype]

/-- Uniform-bind over `Fin n` expressed as `n⁻¹ * ∑ i, …`. -/
lemma pmf_uniform_fin_bind_apply {β : Type*} {n : ℕ} [NeZero n]
    (f : Fin n → PMF β) (b : β) :
    ((PMF.uniformOfFintype (Fin n)).bind f) b =
    (n : ENNReal)⁻¹ * ∑ i : Fin n, (f i) b := by
  rw [pmf_bind_apply_fintype]
  simp [PMF.uniformOfFintype_apply, Fintype.card_fin, Finset.mul_sum]

/-- When all branches of a uniform bind over `Fin n` yield the same probability
    for a given outcome, that probability equals the common value.
    Core normalization for uniform-distribution computations. -/
lemma pmf_uniform_fin_bind_const_prob {β : Type*} {n : ℕ} [NeZero n]
    (f : Fin n → PMF β) (b : β) (v : ENNReal)
    (hv : ∀ i, (f i) b = v) :
    ((PMF.uniformOfFintype (Fin n)).bind f) b = v := by
  rw [pmf_uniform_fin_bind_apply]
  simp only [hv, Finset.mul_sum]
  exact ennreal_inv_nsmul_cancel v


/-! ================================================================
    LAYER D: Correctness Proof Infrastructure
    ================================================================

  These lemmas and tactics target the *correctness* proof pattern for
  randomized algorithms that produce deterministic outputs:

    "Every branch of a uniform bind produces the same `PMF.pure Output`,
     so the whole computation is `PMF.pure Output`."

  This pattern applies to QuickSort, randomized selection, treaps, and
  any algorithm where randomization affects only performance, not the result.
-/

/-- **Uniform bind collapse (deterministic output).**
    If every branch of a uniform bind over `Fin n` produces the same
    `PMF.pure v`, then the entire bind equals `PMF.pure v`.

    This is the master lemma for proving that randomized algorithms with
    deterministic outputs are indeed deterministic. -/
lemma PMF.uniformOfFintype_bind_const_pure {α : Type*} [Fintype α] [Nonempty α]
    (f : α → PMF β) (v : β)
    (hv : ∀ a, f a = PMF.pure v) :
    (PMF.uniformOfFintype α).bind f = PMF.pure v := by
  conv_lhs => rw [show f = fun _ => PMF.pure v from funext hv]
  exact PMF.bind_const _ _

#check PMF.bind_const
#check PMF.bindOnSupport_const

end ARA
