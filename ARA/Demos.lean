import ARA.Phase1
import ARA.Phase2
import ARA.Tactics

/-!
  ### Phase 3 Demonstrations

  Below we re-prove selected lemmas from Phase 1 and Phase 2 using the
  sandbox toolkit.  Compare the proof lengths with the originals above.
-/

namespace ARA

open ENNReal PMF

/-! ##### Demo 4: QuickSort singleton (Phase 2)
    Original: 15 lines with manual `hunif`, `change`, and monadic rewriting.
    New:      5 lines using `pmf_uniformOfFintype_fin_one`.
-/
lemma prob_quicksort_singleton_auto (n : ℕ) : QuickSort_A [n] [n] = 1 := by
  unfold QuickSort_A
  simp only [List.length_singleton]
  rw [pmf_uniformOfFintype_fin_one, PMF.pure_bindOnSupport]
  simp [QuickSort_A, Functor.map]
  change ((PMF.pure []).bind (fun S1 => PMF.pure (S1 ++ [n]))) [n] = 1; simp

/-! ##### Demo 5: Bind over Fin 2 (unit test for pmf_simp)
    Shows how `pmf_simp` reduces a bind over Fin 2 to explicit arithmetic.
-/
example (p : PMF (Fin 2)) (f : Fin 2 → PMF ℕ) (b : ℕ) :
    (p.bind f) b = p 0 * (f 0) b + p 1 * (f 1) b := by
  pmf_simp

/-! ##### Demo 6: Uniform-bind constant-branch collapse
    When every pivot produces the same sorted list, the probability is 1.
-/
example (f : Fin 4 → PMF ℕ) (b : ℕ) (v : ENNReal)
    (hv : ∀ i, (f i) b = v) :
    ((PMF.uniformOfFintype (Fin 4)).bind f) b = v := by
  exact pmf_uniform_fin_bind_const_prob f b v hv

/-! ##### Demo 7: QuickSort two distinct elements (Phase 2)
The annoying lemma about Quicksort_A seems to resist in our attemps of automation
(maybe it is easy, to try more the available tools...)
-/
lemma prob_quicksort_two_distinct_auto (a b : ℕ) (h : a ≠ b) :
  QuickSort_A [a, b] [min a b, max a b] = 1 := by sorry

end ARA
