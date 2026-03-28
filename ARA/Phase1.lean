import ARA.Basic

/-!
  ### Phase 1: Basic Probability Manipulation and familiarisation with PMF

  Here we implement the specific "Pragmatic Use" cases:
  1.  **Chaining (bind):** A coin flip deciding between different subsequent random processes.
  2.  **Deterministic Steps (pure):** Embedding deterministic values into the probability space.
  3.  **Strict Safety (bindOnSupport):** Mathematically guaranteeing that invalid operations are never reachable.
-/

namespace ARA

open PMF

/-
  **Pragmatic Use 1: The Monadic Bind (Branching)**

  "Imagine an algorithm that flips a fair coin, and if heads, it rolls a 6-sided die;
  if tails, it rolls a 20-sided die."

  `bind` (>>=) automatically handles the probability mass multiplication:
  - Path 1: P(Heads) * P(d6=k) = 1/2 * 1/6
  - Path 2: P(Tails) * P(d20=k) = 1/2 * 1/20
-/
/--
  First we model a simple coin flip modeled as a Bernoulli trial with parameter p=1/2.
  This corresponds to the simplest randomized algorithm primitive.
-/
noncomputable def coin_flip : PMF Bool := PMF.bernoulli (1/2 : NNReal) (by norm_num)

/--
  lemma: The probability of obtaining Heads (true) in a fair coin flip is exactly 1/2.
  This demonstrates the "rapid, multi-line verification of probability bounds" goal.
-/
lemma coin_flip_prob_heads : coin_flip true = 1/2 := by
  -- Unfold the definition of coin_flip and apply Bernoulli properties
  simp [coin_flip, PMF.bernoulli_apply]

noncomputable def d6 : PMF (Fin 6) := PMF.uniformOfFintype (Fin 6)
noncomputable def d20 : PMF (Fin 20) := PMF.uniformOfFintype (Fin 20)

/-
The probability mass function is obtained by two layers of bind operation:
  -- One for the coin flip: coin_flip >>= (λ outcome => if outcome then d6 else d20)
  -- One for the subsequent die roll based on the coin outcome:
    * d6 >>= (λ result => PMF ℕ.pure (result.val + 1)) for heads
      (we add 1 to the die result because result lives in Fin 6 which is {0,1,2,3,4,5})
    * d20 >>= (λ result => PMF ℕ.pure (result.val + 1)) for tails.
-/

noncomputable def algorithm1: Bool → PMF ℕ
| true => d6.bind (λ result => PMF.pure (result.val + 1))
| false => d20.bind (λ result => PMF.pure (result.val + 1))

noncomputable def mixed_dice_game : PMF ℕ := coin_flip.bind algorithm1

-- e.g. to "compute" the probability of rolling a 3:
theorem prob_rolling_3 : mixed_dice_game 3 = (1/2) * (1/6) + (1/2) * (1/20) := by
  rw [mixed_dice_game, PMF.bind_apply, coin_flip]
  simp [PMF.bernoulli_apply]
  -- We prove the values for the two branches

  have : algorithm1 true 3 = 1/6 := by
    unfold algorithm1 d6
    simp [PMF.bind_apply, PMF.uniformOfFintype_apply]
    rw [Finset.sum_eq_single (2 : Fin 6)]
    · simp
    · intro b _ hb
      simp
      intro h
      apply hb
      apply Fin.eq_of_val_eq
      simp_all
    · simp

  rw [this]

  have : algorithm1 false 3 = 1/20 := by
    unfold algorithm1 d20
    simp [PMF.bind_apply, PMF.uniformOfFintype_apply]
    rw [Finset.sum_eq_single (2 : Fin 20)]
    · simp
    · intro b _ hb
      simp
      intro h
      apply hb
      apply Fin.eq_of_val_eq
      simp_all
    · simp

  rw [this]

  simp_all

/--
  **Pragmatic Use 2: Deterministic Embedding (Pure)**

  "If an algorithm reaches a deterministic step... pure embeds that guaranteed result."

  For example building on the previous example, we can define a deterministic bonus
  that adds 100 to the die result.
-/
noncomputable def deterministic_bonus (score : ℕ) : PMF ℕ := PMF.pure (score + 100)

-- So that:
noncomputable def mixed_dice_game_with_bonus : PMF ℕ := mixed_dice_game.bind deterministic_bonus

-- The probability of rolling a 3 and then adding the bonus is the same as rolling a 3:
theorem prob_rolling_3_with_bonus : mixed_dice_game_with_bonus 103 = mixed_dice_game 3 := by
  rw [mixed_dice_game_with_bonus, PMF.bind_apply, mixed_dice_game]
  simp [deterministic_bonus]

/--
  **Pragmatic Use 3: STRICTLY SAFE CHAINING (bindOnSupport)**

  "bindOnSupport is the standard bind operation but with an additional safety check: it
  requires a logical proof that a specific outcome is actually possible before allowing
  the function to calculate the next step."

  Specifically, this means that if we have a distribution P : PMF α that is only supported
  on certain values S ⊆ α that satisfy a property P(x) (e.g. "x < 2"), we can use `bindOnSupport`
  to ensure that any subsequent operations are only defined on those values i.e.
  P.bindsupport (λ x h => ...) (for a λ : α → β) (where h is the proof that x is in the support
  of P and thus satisfies P(x)) will be the probability distribution on β obtained by
  applying the function λ to all x in the support of P, weighted by their probability
  (it is a PMF since the total sum remains 1 as the domain of the function λ is exactly
  those that satisfy):

  for b : β, P.bindsupport (λ x h => ...) b = ∑ x in support of P, P x * (λ x h) b.

  Example:
  Accessing an array at an out-of-bounds index is impossible if we use `Fin n`.
  We cannot even construct the function call without a proof that the index is in bounds.

  Here, we have a distribution over `ℕ` that we know is supported on `{0, 1}`.
  We want to safely access a list of size 2. `bindOnSupport` allows us to bridge the gap.
-/

-- A distribution that only supports {0, 1}
noncomputable def safe_index_dist : PMF ℕ := PMF.uniformOfFinset {0, 1} (by simp)

-- A strict operation that cannot be called without a proof that n < 2 (our λ).
-- It safely extracts elements from a 2-element list.
noncomputable def strict_list_access (n : ℕ) (h : n < 2) : PMF String :=
  let my_data := ["Result A", "Result B"]
  -- We construct a valid Fin index using the proof `h`
  let safe_idx : Fin 2 := ⟨n, h⟩
  -- We need to prove the index is valid for the list length
  have h_valid : safe_idx.val < my_data.length := by simp [my_data]
  -- Finally, we return the result as a pure distribution (deterministic)
  PMF.pure (my_data.get ⟨safe_idx, h_valid⟩)

-- So our λ takes n : ℕ and a proof that n < 2, and returns a PMF String.

-- Using `bindOnSupport` to connect them.
-- The compiler forces us to prove that every element in the support of `safe_index_dist`
-- satisfies `n < 2`.
noncomputable def safe_chaining_example : PMF String :=
  safe_index_dist.bindOnSupport (λ n h_support =>
    have h_safe : n < 2 := by
      unfold safe_index_dist at h_support
      simp_all
      omega

    strict_list_access n h_safe
  )

lemma safe_chaining_example_resultA : safe_chaining_example "Result A" = 1/2 := by
  unfold safe_chaining_example safe_index_dist strict_list_access
  simp_all
  apply tsum_eq_single 0
  · intro a ha
    rcases a with _ | _ | a
    · contradiction
    · simp
    · simp

lemma safe_chaining_example_resultB : safe_chaining_example "Result B" = 1/2 := by
  unfold safe_chaining_example safe_index_dist strict_list_access
  simp_all
  apply tsum_eq_single 1
  · intro a ha
    rcases a with _ | _ | a
    · simp
    · contradiction
    · simp

end ARA
