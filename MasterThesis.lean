import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic

/-!
  Framework for analysis of randomized algorithm.
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
"Phase 1: Invariant Mapping & Toy Implementations"
-/

/-
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
by assigning to each element the measure of its singleton. This is done by the `toPmf`
function: -.toPmf. These two functions are inverses of each other.

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
-/


namespace RandomizedFramework

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

  NOTE ON RUNNING TIME:
  The standard `PMF` monad tracks probability mass but not computational cost (running time).
  In "Phase 2: Framework Construction", we will extend this to a custom `Rnd` monad
  that pairs the probability space with a cost accumulator (WriterT Cost PMF), allowing
  formal bounds on time complexity alongside probability.
-/

/--
  **Pragmatic Use 1: The Monadic Bind (Branching)**

  "Imagine an algorithm that flips a fair coin, and if heads, it rolls a 6-sided die;
  if tails, it rolls a 20-sided die."

  `bind` (>>=) automatically handles the probability mass multiplication:
  - Path 1: P(Heads) * P(d6=k) = 1/2 * 1/6
  - Path 2: P(Tails) * P(d20=k) = 1/2 * 1/20
-/
noncomputable def d6 : PMF (Fin 6) := PMF.uniformOfFintype (Fin 6)
noncomputable def d20 : PMF (Fin 20) := PMF.uniformOfFintype (Fin 20)

noncomputable def mixed_dice_game : PMF ℕ :=
  coin_flip >>= λ is_heads =>
    if is_heads then
      -- If Heads, roll d6 and convert to Nat (1-based)
      d6 >>= (λ result => pure (result.val + 1))
    else
      -- If Tails, roll d20 and convert to Nat (1-based)
      d20 >>= (λ result => pure (result.val + 1))

/--
  **Pragmatic Use 2: Deterministic Embedding (Pure)**

  "If an algorithm reaches a deterministic step... pure embeds that guaranteed result."

  Here, `deterministic_bonus` takes a value and deterministically adds to it.
  In the monad, this is a transition with probability 1.
-/
noncomputable def deterministic_bonus (score : ℕ) : PMF ℕ :=
  pure (score + 100)

/--
  **Pragmatic Use 3: STRICTLY SAFE CHAINING (bindOnSupport)**

  "bindOnSupport requires a logical proof that a specific outcome is actually possible...
   before allowing the function to calculate the next step."

  We model a distribution that yields 1 or 2, and a function that computes 10 / x.
  While Lean division is total (x/0 = 0), `bindOnSupport` allows us to model
  partial functions or constraints rigorously, proving the "bad" case (0) never happens.

  The compiler mathematically rejects execution paths where the invalid number
  had a 0 probability of occurring.
-/

-- A distribution that only supports {1, 2}
noncomputable def safe_input_dist : PMF ℕ :=
  PMF.uniformOfFinset {1, 2} (by simp)

-- A safer operation that requires a proof that the input is non-zero
def rigorous_conditional_op (x : ℕ) (h : x ≠ 0) : PMF ℚ :=
  pure (10 / (x : ℚ))

-- Using `bindOnSupport` to connect them.
-- The compiler forces us to prove that every element in the support of `safe_input_dist`
-- satisfies the precondition `x ≠ 0`.
noncomputable def safe_chaining_example : PMF ℚ :=
  safe_input_dist.bindOnSupport (λ x h_support =>
    have h_safe : x ≠ 0 := by
      -- The proof: The support is {1, 2}. If x ∈ {1, 2}, then x ≠ 0.
      simp [safe_input_dist, PMF.support_uniformOfFinset] at h_support
      intro h_zero
      rw [h_zero] at h_support
      -- 0 ∈ {1, 2} simplifies to false
      simp at h_support

    rigorous_conditional_op x h_safe
  )

  field_simp

end RandomizedFramework
