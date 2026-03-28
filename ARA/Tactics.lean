import ARA.Basic

/-!
  ### Phase 3: Grind implementation

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
    LAYER A: `grind` Rules (e-matching compatible)
    ================================================================ -/

/-! ##### A.1  ENNReal Arithmetic -/

/- Two halves make a whole — the symmetric-branch pattern. -/
-- NOTE: `ENNReal.inv_two_add_inv_two` is a specific numerical identity (2⁻¹ + 2⁻¹ = 1)
-- that is unlikely to trigger in general randomized algorithm analysis beyond coin-flip
-- scenarios. Kept as a standalone lemma but not tagged for grind.
-- attribute [grind =] ENNReal.inv_two_add_inv_two

/- Factoring a common inverse weight out of a sum of two branches. -/
lemma ennreal_inv_mul_add_inv_mul (c a b : ENNReal) :
    c⁻¹ * a + c⁻¹ * b = c⁻¹ * (a + b) := by ring

/-- `n⁻¹ · n = 1` in ENNReal for nonzero natural `n`. -/
@[grind =]
lemma ennreal_natCast_inv_mul_self {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ * (n : ENNReal) = 1 :=
  ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)

/-- `n · n⁻¹ = 1` in ENNReal for nonzero natural `n`. -/
@[grind =]
lemma ennreal_natCast_mul_inv_self {n : ℕ} [NeZero n] :
    (n : ENNReal) * (n : ENNReal)⁻¹ = 1 :=
  ENNReal.mul_inv_cancel (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)

/-- `(↑n)⁻¹ ≠ 0` when `n` is a natural number (since `↑n ≠ ⊤`). -/
@[grind →]
lemma ennreal_natCast_inv_ne_zero {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ ≠ 0 :=
  ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n)

/-- `(↑n)⁻¹ ≠ ⊤` when `n ≠ 0`. -/
@[grind →]
lemma ennreal_natCast_inv_ne_top {n : ℕ} [NeZero n] :
    (n : ENNReal)⁻¹ ≠ ⊤ :=
  ENNReal.inv_ne_top.mpr (by exact_mod_cast NeZero.ne n)

/-- Splitting `a / 2 + a / 2 = a`. -/
-- NOTE: Like `inv_two_add_inv_two`, this is specific to the constant 2.
-- Useful but not general enough for grind in arbitrary randomized algorithm analysis.
-- attribute [grind =] ENNReal.add_halves'
lemma ennreal_add_halves' (a : ENNReal) : a / 2 + a / 2 = a :=
  ENNReal.add_halves a

/- Splitting common denominator: `a / c + b / c = (a + b) / c`. -/
-- NOTE: `ENNReal.div_add_div_same` is a general algebraic identity that is useful
-- for any randomized algorithm analysis involving weighted sums.
attribute [grind =] ENNReal.div_add_div_same

/-- Summing `n` copies of `n⁻¹ * t` over `Fin n` gives `t`.
    This is the core normalization for uniform-distribution bind goals. -/
lemma ennreal_inv_nsmul_cancel {n : ℕ} [NeZero n] (t : ENNReal) :
    ∑ _i : Fin n, (n : ENNReal)⁻¹ * t = t := by
  rw [Finset.sum_const]; simp [Fintype.card_fin]
  rw [← mul_assoc, ENNReal.mul_inv_cancel]
  · simp
  · exact_mod_cast NeZero.ne n
  · exact ENNReal.natCast_ne_top n


/-! ##### A.2  PMF Monad Laws & Pointwise Application (grind-compatible) -/

-- Left identity: `pure a >>= f = f a`.
attribute [grind =] PMF.pure_bind

-- Right identity: `p >>= pure = p`.
attribute [grind =] PMF.bind_pure

-- Associativity: `(p >>= f) >>= g = p >>= (fun a => f a >>= g)`.
attribute [grind =] PMF.bind_bind

-- `PMF.pure a` applied to `a'` is `if a' = a then 1 else 0`.
attribute [grind =] PMF.pure_apply

-- `PMF.bind` applied pointwise is `∑' a, p a * (f a) b`.
attribute [grind =] PMF.bind_apply

-- `PMF.map f p` applied pointwise.
attribute [grind =] PMF.map_apply

-- `map` over `pure`: `f <$> pure a = pure (f a)`.
attribute [grind =] PMF.pure_map

-- `map id = id`.
attribute [grind =] PMF.map_id

-- `map` composition.
attribute [grind =] PMF.map_comp

-- `bind` of `map`: `(f <$> p) >>= q = p >>= (q ∘ f)`.
attribute [grind =] PMF.bind_map

-- `map` of `bind`: `f <$> (p >>= q) = p >>= (fun a => f <$> q a)`.
attribute [grind =] PMF.map_bind

-- `bind (pure ∘ f) = map f`.
attribute [grind =] PMF.bind_pure_comp


/-! ##### A.3  Uniform Distribution & Support (grind-compatible) -/

-- Weight of each element in `uniformOfFintype`.
attribute [grind =] PMF.uniformOfFintype_apply

-- Weight of each element in `uniformOfFinset`.
attribute [grind =] PMF.uniformOfFinset_apply

-- `Fintype.card (Fin n) = n`.
attribute [grind =] Fintype.card_fin

-- `Fintype.card Bool = 2`.
attribute [grind =] Fintype.card_bool

-- Support of `uniformOfFintype` is everything.
attribute [grind =] PMF.support_uniformOfFintype

-- Support of `uniformOfFinset` is the finset.
attribute [grind =] PMF.support_uniformOfFinset

-- Support of `pure a` is `{a}`.
attribute [grind =] PMF.support_pure

-- Bernoulli distribution applied pointwise.
attribute [grind =] PMF.bernoulli_apply

-- Support membership ↔ nonzero probability.
attribute [grind =] PMF.mem_support_iff

-- Support of `bind`.
attribute [grind =] PMF.support_bind

-- Support membership for `uniformOfFinset`.
attribute [grind =] PMF.mem_support_uniformOfFinset_iff


/-! ##### A.4  bindOnSupport (grind-compatible) -/

-- `pure a` followed by `bindOnSupport f` just applies `f` to `a`.
attribute [grind =] PMF.pure_bindOnSupport

-- Pointwise expansion of `bindOnSupport`.
attribute [grind =] PMF.bindOnSupport_apply


/-! ================================================================
    LAYER B: `pmf_simp` and `pmf_norm` Tactic Macros
    ================================================================

  These tactics package the entire simp lemma set (including the lemmas
  that `grind` cannot accept due to pattern restrictions) into a single
  invocation.  They are the primary workhorse for closing PMF goals.

  * `pmf_simp`  — a focused `simp only [...]` followed by fallback `simp`,
    `norm_num`, and `ring` passes.  Designed to close most PMF probability
    equalities in a single call.

  * `pmf_norm` — `pmf_simp` plus `omega` for leftover natural-number goals.
    Use when list/array index bounds appear alongside probability goals.
-/

/-- `pmf_simp` applies a curated `simp only` lemma set for PMF goals,
    followed by fallback passes of `simp`, `norm_num`, and `ring`.
    It handles:
    - Tsum → finite sum collapse (`tsum_fintype`, `Fin.sum_univ_*`, `Fintype.sum_bool`)
    - PMF monad laws and application (`pure_bind`, `bind_apply`, `bind_const`, …)
    - Uniform / Bernoulli distribution weights
    - bindOnSupport simplification
    - Conditional arithmetic (`ite_mul`, `mul_ite`, `Finset.sum_ite_eq`, …)
    - Basic ENNReal cleanup (`mul_one`, `zero_mul`, `if_true`, …)
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

/-- `pmf_norm` extends `pmf_simp` with `omega` for natural-number side goals. -/
macro "pmf_norm" : tactic =>
  `(tactic| (
    try pmf_simp
    <;> try omega
    <;> try (simp; ring_nf)
    <;> try norm_num))


/-! ================================================================
    LAYER C: Standalone Derived Lemmas
    ================================================================ -/

/-- `uniformOfFintype (Fin 1)` is `pure 0` — a degenerate uniform distribution.
    Useful for singleton-list base cases in recursive algorithms. -/
lemma pmf_uniformOfFintype_fin_one :
    PMF.uniformOfFintype (Fin 1) = PMF.pure (0 : Fin 1) := by
  ext a
  have ha : a = 0 := Fin.ext (by omega)
  subst ha; simp [PMF.uniformOfFintype_apply]

/-- `uniformOfFintype` is never zero on any element. -/
lemma pmf_uniformOfFintype_ne_zero {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    (PMF.uniformOfFintype α) a ≠ 0 := by
  rw [PMF.uniformOfFintype_apply]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

/-- Probability of any element under a `uniformOfFinset` that contains it. -/
lemma pmf_uniformOfFinset_mem {α : Type*} {s : Finset α} (hs : s.Nonempty)
    {a : α} (ha : a ∈ s) :
    (PMF.uniformOfFinset s hs) a = (s.card : ENNReal)⁻¹ := by
  simp [PMF.uniformOfFinset_apply, ha]

/-- Probability of an element NOT in a `uniformOfFinset` is zero. -/
lemma pmf_uniformOfFinset_not_mem {α : Type*} {s : Finset α} (hs : s.Nonempty)
    {a : α} (ha : a ∉ s) :
    (PMF.uniformOfFinset s hs) a = 0 := by
  simp [PMF.uniformOfFinset_apply, ha]

/-- If every branch produces the same PMF, `bind` collapses to that PMF.
    Generalizes `PMF.bind_const` with a pointwise hypothesis. -/
lemma pmf_bind_eq_of_forall_eq {α β : Type*} (p : PMF α) (f : α → PMF β)
    (q : PMF β) (hfq : ∀ a, f a = q) :
    p.bind f = q := by
  rw [show f = fun _ => q from funext hfq, PMF.bind_const]

/-- `bind` over a finite-type PMF unfolds to a `Finset.sum`. -/
lemma pmf_bind_apply_fintype {α β : Type*} [Fintype α] (p : PMF α)
    (f : α → PMF β) (b : β) :
    (p.bind f) b = ∑ a : α, p a * (f a) b := by
  rw [PMF.bind_apply, tsum_fintype]

/-- Uniform-bind over `Fin n` expressed as `n⁻¹ * ∑ i, …`.
    This is the workhorse for analyzing algorithms with a uniform random choice
    over `n` options (e.g., pivot selection in randomized quicksort). -/
lemma pmf_uniform_fin_bind_apply {β : Type*} {n : ℕ} [NeZero n]
    (f : Fin n → PMF β) (b : β) :
    ((PMF.uniformOfFintype (Fin n)).bind f) b =
    (n : ENNReal)⁻¹ * ∑ i : Fin n, (f i) b := by
  rw [pmf_bind_apply_fintype]
  simp [PMF.uniformOfFintype_apply, Fintype.card_fin, Finset.mul_sum]

/-- When all `n` branches of a uniform bind over `Fin n` produce the same
    probability for a given outcome, that probability equals the common value.
    (The `n` copies of `n⁻¹ * v` sum to `v`.) -/
lemma pmf_uniform_fin_bind_const_prob {β : Type*} {n : ℕ} [NeZero n]
    (f : Fin n → PMF β) (b : β) (v : ENNReal)
    (hv : ∀ i, (f i) b = v) :
    ((PMF.uniformOfFintype (Fin n)).bind f) b = v := by
  rw [pmf_uniform_fin_bind_apply]
  simp only [hv, Finset.mul_sum]
  exact ennreal_inv_nsmul_cancel v

end ARA
