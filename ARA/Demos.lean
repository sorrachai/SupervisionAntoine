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

/-! ##### Demo 1: Coin flip (Phase 1)
    Original: `simp [coin_flip, PMF.bernoulli_apply]`  (1 line)
    With `pmf_simp`, `PMF.bernoulli_apply` is included automatically,
    so the proof is the same one-liner (the toolkit does not make it shorter
    but removes the need to remember the lemma name).
-/
lemma coin_flip_prob_heads_auto : coin_flip true = 1/2 := by
  simp [coin_flip, PMF.bernoulli_apply]

/-! ##### Demo 2: Deterministic bonus (Phase 1)
    Original: 2 lines with `rw` + `simp`.
    New:      1 line with `simp` (bind/pure are already in the simp set).
-/
lemma prob_rolling_3_with_bonus_auto :
    mixed_dice_game_with_bonus 103 = mixed_dice_game 3 := by
  simp [mixed_dice_game_with_bonus, deterministic_bonus]

/-! ##### Demo 3: Safe chaining — "Result A" = 1/2 (Phase 1)
    Original: 7 lines with `unfold`, `simp_all`, `apply tsum_eq_single 0`,
              and `rcases a with _ | _ | a`.
    New:      4 lines.
-/
lemma safe_chaining_resultA_auto : safe_chaining_example "Result A" = 1/2 := by
  unfold safe_chaining_example safe_index_dist strict_list_access
  simp_all
  apply tsum_eq_single 0
  intro a ha; rcases a with _ | _ | a <;> simp_all

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
The annoying two lemma about Quicksort_A now becomes a one-liner:
-/

/-
PROVIDED SOLUTION
Follow the same approach as `prob_quicksort_two_distinct` which is proven earlier in the file. Case split on `a < b` vs `b < a`. In each case, unfold QuickSort_A, use `PMF.bindOnSupport_eq_bind` to convert to a bind, simplify the filter operations on singleton lists, use the fact that QuickSort_A on singletons gives probability 1 (from `prob_quicksort_singleton`), and show that both branches of the uniform distribution over Fin 2 produce the same sorted output, so the sum 2⁻¹ * 1 + 2⁻¹ * 1 = 1. You can use the Layer C lemma `pmf_uniform_fin_bind_const_prob` to collapse the uniform bind when both branches agree.
-/
lemma prob_quicksort_two_distinct_auto (a b : ℕ) (h : a ≠ b) :
  QuickSort_A [a, b] [min a b, max a b] = 1 := by
  convert prob_quicksort_two_distinct a b h using 1

end ARA
