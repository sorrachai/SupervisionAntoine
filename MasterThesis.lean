import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Rat.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
  Framework for analysis of randomized algorithm.
  ARA = "Analysis of Randomized Algorithms"
  Author: Antoine du Fresne von Hohenesche
  Date: March 2026
-/

/-
Essentially, if we fix multipple random variables and an algorithm that uses them,
we want to model the entire execution of the algorithm and at the end be able to
prove bounds on the probability of certain events (e.g. "the algorithm returns the wrong answer")
prove bounds on the expected running time of the algorithm (so a cost function)
prove bounds on the probability of certain events happening within a certain time bound
(e.g. "the algorithm returns the wrong answer within 100 steps"). Things like this.
-/

/-
We are in a shallow embedding setting "Giry Monad":

We utilize the `PMF` type (Probability Mass Function) which
for a type α is the type of function α → ℝ≥0∞ such that the
values have (infinite) sum 1.

Clearly any such function gives a probability measure on α on the set
of its parts (so singleton are measurable), by assigning
each set the sum of the probabilities of each of its elements.
This is done by the `toOuterMeasure` function:  PMF.toOuterMeasure.
PMF.toMeasure.isProbabilityMeasure shows this associated measure
is a probability measure.

Conversely any probability measure on α where singletons are measurable gives a PMF
by assigning to each element the measure of its singleton. This is done by the `toPMF`
function: .toPMF . These two functions are inverses of each other.

On top of this structure, Mathlib defines a monad structure on PMF, with the following operations:

- `pure : α → PMF α` which takes a value and returns the distribution that is
  concentrated on that value (the Dirac distribution).

- `bind : PMF α → (α → PMF β) → PMF β` which for two types α and β:
  Takes (P,f) where :
  * P is a distribution over α, P : PMF α,
  * f is a function that assigns to each elements of α a distribution over β, f : α → PMF β
  Returns:
  the distribution over β obtained by "sampling" from the first distribution and
  then "sampling" from the second distribution i.e. assigns b : β to the probability:
  ∑ a : α, P a * (f a) b

  It used concretely like this : pure x for pure x and P >>= f for bind (P,f).
-/

namespace ARA

open PMF

/--
  A simple coin flip modeled as a Bernoulli trial with parameter p=1/2.
  This corresponds to the simplest randomized algorithm primitive.
-/
noncomputable def coin_flip : PMF Bool := PMF.bernoulli (1/2 : NNReal) (by norm_num)

/--
  Theorem: The probability of obtaining Heads (true) in a fair coin flip is exactly 1/2.
  This demonstrates the "rapid, multi-line verification of probability bounds" goal.
-/
theorem coin_flip_prob_heads : coin_flip true = 1/2 := by
  -- Unfold the definition of coin_flip and apply Bernoulli properties
  simp [coin_flip, PMF.bernoulli_apply]

/-!
  ### Phase 1: Advanced Primitives & Invariant Mapping

  Here we implement the specific "Pragmatic Use" cases requested:
  1.  **Chaining (bind):** A coin flip deciding between different subsequent random processes.
  2.  **Deterministic Steps (pure):** Embedding deterministic values into the probability space.
  3.  **Strict Safety (bindOnSupport):** Mathematically guaranteeing that invalid operations are never reachable.
-/

/-
  **Pragmatic Use 1: The Monadic Bind (Branching)**

  "Imagine an algorithm that flips a fair coin, and if heads, it rolls a 6-sided die;
  if tails, it rolls a 20-sided die."

  `bind` (>>=) automatically handles the probability mass multiplication:
  - Path 1: P(Heads) * P(d6=k) = 1/2 * 1/6
  - Path 2: P(Tails) * P(d20=k) = 1/2 * 1/20
-/

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
theorem prob_rolling_3 : mixed_dice_game 3 = (1/2 : ENNReal) * (1/6 : ENNReal) + (1/2 : ENNReal) * (1/20 : ENNReal) := by
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

/-
A nice thing to have would be that we can specify a randomized algorithm in pseudo code
and then analyze each of its branch very easily.
-/

/--
  **Pragmatic Use 3: STRICTLY SAFE CHAINING (bindOnSupport)**

  "bindOnSupport is the standard bind operation but with an additional safety check: it
  requires a logical proof that a specific outcome is actually possible before allowing
  the function to calculate the next step."
  Specifically, this means that if we have a distribution P : PMF α that is only supported
  on certain values S ⊆ α that satisfy a property P(x) (e.g. "x < 2"), we can use `bindOnSupport`
  to ensure that any subsequent operations are only defined on those values i.e.
  P.bindsupport (λ x h => ...) (λ: \alpha)βre h is the proof that x is in the support of P and thus
  satisfies P(x)) will be the probability distribution obtained by applying the function
  λ to all x in the support of P, weighted by their probability
  (it is a PMF since the total sum remains 1 as the domain of the function λ is exactly those
  that satisfy): P.bindsupport (λ x h => ...) a =

  Example:
  Accessing an array at an out-of-bounds index is impossible if we use `Fin n`.
  We cannot even construct the function call without a proof that the index is in bounds.

  Here, we have a distribution over `ℕ` that we know is supported on `{0, 1}`.
  We want to safely access a list of size 2. `bindOnSupport` allows us to bridge the gap.
-/

-- A distribution that only supports {0, 1}
noncomputable def safe_index_dist : PMF ℕ := PMF.uniformOfFinset {0, 1} (by simp)

-- A strict operation that cannot be called without a proof that n < 2.
-- It safely extracts elements from a 2-element list.
noncomputable def strict_list_access (n : ℕ) (h : n < 2) : PMF String :=
  let my_data := ["Result A", "Result B"]
  -- We construct a valid Fin index using the proof `h`
  let safe_idx : Fin 2 := ⟨n, h⟩
  -- We need to prove the index is valid for the list length
  have h_valid : safe_idx.val < my_data.length := by
    simp [my_data]

  PMF.pure (my_data.get ⟨safe_idx, h_valid⟩)

-- Using `bindOnSupport` to connect them.
-- The compiler forces us to prove that every element in the support of `safe_index_dist`
-- satisfies `n < 2`.
noncomputable def safe_chaining_example : PMF String :=
  safe_index_dist.bindOnSupport (λ n h_support =>
    have h_safe : n < 2 := by
      -- The support is {0, 1}.
      simp [safe_index_dist, PMF.support_uniformOfFinset] at h_support
      -- Prove that if n ∈ {0, 1}, then n < 2
      cases h_support with
      | inl h0 => rw [h0]; norm_num
      | inr h1 => rw [h1]; norm_num

    strict_list_access n h_safe
  )

/-
Lets write some typical other exceptions than division by 0:

- Accessing the head of an empty list
- Taking the logarithm of a non-positive number
- Inverting a non-invertible matrix
and so on...
-/

/-
We should also be able handle and distinguishe non-termination
observation failures and error states.
-/

/-
A nice thing would be to potentially mixing continuous and discrete dis-
tributions.
-/


/-
  NOTE ON RUNNING TIME:
  The standard `PMF` monad tracks probability mass but not computational cost (running time).
  In "Phase 2: Framework Construction", we will extend this to a custom `Rnd` monad
  that pairs the probability space with a cost accumulator (WriterT Cost PMF), allowing
  formal bounds on time complexity alongside probability.
-/

/-
There are various approaches for reasoning about randomized algorithms in a
formal way. Analogously to the non-randomized setting described in Sect. 2,
there again exists an entire spectrum of diﬀerent approaches:
– fully explicit/deeply-embedded approaches
– “no embedding” approaches that model randomized algorithms directly in the
logic as functions returning a probability distribution
– shallow embeddings, e.g. with shallow deterministic operations but explicit
random choice and explicit “while” loops. Examples are the approaches by
Petcher and Morrisett [165] in Coq and by Kaminski et al. [110] on paper
(which was formalized by Hölzl [105]).
– combined approaches that start with a program in a deeply-embedded prob-
abilistic programming language and then relate it to a distribution specified
directly in the logic, cf. e.g. Tassarotti and Harper [188].

The ideal would be no embedings.
-/

/-
Directly in the Logic (No Embedding). As was mentioned before, many
ITPs oﬀer functionality to define algorithms directly in the logic of the system
– usually functionally. This approach is more flexible since algorithms can use
the full expressiveness of the system’s logic and not only some fixed restricted
set of language constructs. One possible drawback of this approach is that it
can be diﬃcult or even impossible to reason about notions such as running time
explicitly. A possible workaround is to define an explicit cost function for the
algorithm, but since there is no formal connection between that function and
the algorithm, one must check by inspection that the cost function really does
correspond to the incurred cost. Another disadvantage is that, as was said earlier,
most logics do not have builtin support for imperative algorithms.
-/

end ARA
