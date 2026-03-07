import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Rat.Defs

/-!
  Core definitions for the Master Thesis:
  Framework for analysis of randomized algorithm.
  Author: Antoine du Fresne von Hohenesche

  This file demonstrates the "Phase 1: Invariant Mapping & Toy Implementations"
  specifically focused on Discrete Probability using the Coin Flip example.

  We utilize the `PMF` (Probability Mass Function) monad from Mathlib to rigorously
  formalize the probabilistic aspects, fulfilling the "Measure-Theoretic Backing" requirement.
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

/--
  Theorem: The total probability mass of the coin flip is 1.
-/
theorem coin_flip_normalization : (PMF.toOuterMeasure coin_flip) ⊤ = 1 := by
  -- Pmf by definition sums to 1
  rw [PMF.toOuterMeasure_apply]
  simp [coin_flip, PMF.bernoulli_apply]

  field_simp

end RandomizedFramework
