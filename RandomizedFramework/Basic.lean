import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.Rat.Basic

/--
  Core definitions for the Master Thesis: 
  Framework for analysis of randomized algorithm.
  Author: Antoine du Fresne von Hohenesche

  This file demonstrates the "Phase 1: Invariant Mapping & Toy Implementations"
  specifically focused on Discrete Probability using the Coin Flip example.

  We utilize the `Pmf` (Probability Mass Function) monad from Mathlib to rigorously
  formalize the probabilistic aspects, fulfilling the "Measure-Theoretic Backing" requirement.
-/

/--
  A simple coin flip modeled as a Bernoulli trial with parameter p=1/2.
  This corresponds to the simplest randomized algorithm primitive.
-/
def coin_flip : Pmf Bool := Pmf.bernoulli (1/2)

/--
  Theorem: The probability of obtaining Heads (true) in a fair coin flip is exactly 1/2.
  This demonstrates the "rapid, multi-line verification of probability bounds" goal.
-/
theorem coin_flip_prob_heads : coin_flip true = 1/2 := by
  -- Unfold the definition of coin_flip and apply Bernoulli properties
  simp [coin_flip, Pmf.bernoulli_apply]
  -- Arithmetic simplification
  norm_num

/--
  Theorem: The total probability mass of the coin flip is 1.
  This validates the "Measure-Theoretic Backing" ensures valid probability spaces.
-/
theorem coin_flip_normalization : (coin_flip.toOuterMeasure) ⊤ = 1 := by
  -- Pmf by definition sums to 1
  exact coin_flip.toOuterMeasure_apply_top

