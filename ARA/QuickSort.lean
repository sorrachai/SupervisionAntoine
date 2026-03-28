import ARA.Phase2
import ARA.Tactics

/-!
# QuickSort Correctness Proof

This module contains the full correctness proof for `QuickSort_A`:
the randomized quicksort always returns the sorted list with probability 1.

## Main Result
- `QuickSort_A_eq_pure_mergeSort`: QuickSort_A L = PMF.pure (List.mergeSort L)
- `Correctness_Quicksort_A`: QuickSort_A L (List.mergeSort L) = 1

## Helper Lemmas
- `perm_getElem_cons_eraseIdx`: eraseIdx gives back a permutation
- `filter_partition_perm`: filter partition gives a permutation
- `partition_sort_concat_perm`: partition-sort-concat is a permutation
- `partition_sort_concat_sorted`: partition-sort-concat is sorted
- `eq_mergeSort_of_perm_of_sorted`: uniqueness of sorted permutations
- `partition_sort_eq_mergeSort`: main partition-sort equality
-/

/-
PROBLEM
QuickSort_A is deterministic: it always returns the sorted list.

PROVIDED SOLUTION
By strong induction on L.length.

Base case (L = []): QuickSort_A [] = PMF.pure [] = PMF.pure (mergeSort []) by List.mergeSort_nil.

Inductive case (L = head :: tail): QuickSort_A L unfolds to a bindOnSupport over uniformOfFintype (Fin L.length). For each pivot index idx_pivot, the branch:
1. Sets pivot = L[idx_pivot], rest = L.eraseIdx idx_pivot
2. Filters rest into L1 (< pivot) and L2 (≥ pivot)
3. Recursively calls QuickSort_A L1 and QuickSort_A L2
4. Returns S1 ++ [pivot] ++ S2

By IH (L1.length < L.length and L2.length < L.length), QuickSort_A L1 = PMF.pure (mergeSort L1) and QuickSort_A L2 = PMF.pure (mergeSort L2).

So the branch deterministically returns mergeSort(L1) ++ [pivot] ++ mergeSort(L2), which equals mergeSort(L) by partition_sort_eq_mergeSort.

Since every branch of the bindOnSupport produces PMF.pure (mergeSort L), the whole thing equals PMF.pure (mergeSort L).

Key lemmas to use: partition_sort_eq_mergeSort, List.mergeSort_nil, PMF.pure_bindOnSupport, PMF.pure_bind.
-/

namespace ARA

open PMF List

/-! ### Permutation lemma: eraseIdx gives back a permutation -/

lemma perm_getElem_cons_eraseIdx (L : List ℕ) (i : Fin L.length) :
    L.Perm (L[i] :: L.eraseIdx i) := by
  induction' i with i ih;
  induction' L with hd tl ih generalizing i ; aesop;
  rcases i with ( _ | i ) <;> simp_all +decide [ List.eraseIdx ];
  exact List.Perm.trans ( List.Perm.cons _ ( ih _ <| by simpa using ‹i + 1 < List.length ( hd :: tl ) › ) ) ( List.Perm.swap .. )

/-! ### Filter partition gives a permutation -/

lemma filter_partition_perm (rest : List ℕ) (pivot : ℕ) :
    (rest.filter (fun x => decide (x < pivot)) ++
     rest.filter (fun x => decide (x ≥ pivot))).Perm rest := by
  convert List.filter_append_perm _ _ using 1;
  congr! 2;
  grind

/-! ### The partition-sort-concat is a permutation of the original list -/

lemma partition_sort_concat_perm (L : List ℕ) (i : Fin L.length) :
    let pivot := L[i]
    let rest := L.eraseIdx i
    let L1 := rest.filter (fun x => decide (x < pivot))
    let L2 := rest.filter (fun x => decide (x ≥ pivot))
    (L1.mergeSort ++ [pivot] ++ L2.mergeSort).Perm L := by
  -- By transitivity of permutations, we can chain these steps together.
  have h_chain : List.Perm (List.mergeSort (List.filter (fun x => x < L[i]) (L.eraseIdx i)) (fun a b => decide (a ≤ b)) ++ [L[i]] ++ List.mergeSort (List.filter (fun x => x ≥ L[i]) (L.eraseIdx i)) (fun a b => decide (a ≤ b))) (List.filter (fun x => x < L[i]) (L.eraseIdx i) ++ [L[i]] ++ List.filter (fun x => x ≥ L[i]) (L.eraseIdx i)) := by
    apply_rules [ List.Perm.append, List.mergeSort_perm ];
    rfl;
  have h_odd_kill : List.Perm (List.filter (fun x => x < L[i]) (L.eraseIdx i) ++ [L[i]] ++ List.filter (fun x => x ≥ L[i]) (L.eraseIdx i)) (L[i] :: L.eraseIdx i) := by
    have h_partition : List.Perm (List.filter (fun x => x < L[i]) (L.eraseIdx i) ++ (List.filter (fun x => x ≥ L[i]) (L.eraseIdx i))) (L.eraseIdx i) := by
      exact filter_partition_perm (L.eraseIdx ↑i) L[i];
    grind +splitIndPred;
  exact h_chain.trans ( h_odd_kill.trans ( perm_getElem_cons_eraseIdx L i |> List.Perm.symm ) )

/-! ### The partition-sort-concat is sorted -/

lemma partition_sort_concat_sorted (L : List ℕ) (i : Fin L.length) :
    let pivot := L[i]
    let rest := L.eraseIdx i
    let L1 := rest.filter (fun x => decide (x < pivot))
    let L2 := rest.filter (fun x => decide (x ≥ pivot))
    List.Pairwise (· ≤ ·) (L1.mergeSort ++ [pivot] ++ L2.mergeSort) := by
  simp +decide [ List.pairwise_append ];
  -- Apply the fact that mergeSort produces a sorted list.
  have h_sorted : ∀ (L : List ℕ), List.Pairwise (· ≤ ·) (List.mergeSort L (· ≤ ·)) := by
    exact fun L => pairwise_mergeSort' (fun x1 x2 => x1 ≤ x2) L;
  exact ⟨ h_sorted _, h_sorted _, fun a ha ha' => ⟨ le_of_lt ha', fun b hb hb' => by linarith ⟩ ⟩

/-! ### Uniqueness of sorted permutations -/

lemma eq_mergeSort_of_perm_of_sorted (L result : List ℕ)
    (hperm : result.Perm L) (hsorted : List.Pairwise (· ≤ ·) result) :
    result = L.mergeSort := by
  have h_unique : List.Perm result (L.mergeSort (fun a b => decide (a ≤ b))) := by
    exact hperm.trans ( List.mergeSort_perm _ _ |> List.Perm.symm );
  apply List.Perm.eq_of_pairwise;
  any_goals assumption;
  · exact fun a b ha hb hab hba => le_antisymm hab hba;
  · exact pairwise_mergeSort' (fun x1 x2 => x1 ≤ x2) L

/-! ### Main partition-sort equality -/

lemma partition_sort_eq_mergeSort (L : List ℕ) (i : Fin L.length) :
    let pivot := L[i]
    let rest := L.eraseIdx i
    let L1 := rest.filter (fun x => decide (x < pivot))
    let L2 := rest.filter (fun x => decide (x ≥ pivot))
    L1.mergeSort ++ [pivot] ++ L2.mergeSort = L.mergeSort := by
  exact eq_mergeSort_of_perm_of_sorted L _ (partition_sort_concat_perm L i) (partition_sort_concat_sorted L i)


lemma QuickSort_A_eq_pure_mergeSort (L : List ℕ) :
    QuickSort_A L = PMF.pure (List.mergeSort L) := by
  by_contra h_contra;
  -- Let's choose any $L$ such that $QuickSort_A L \neq PMF.pure (L.mergeSort (· ≤ ·))$.
  obtain ⟨L, hL⟩ : ∃ L : List ℕ, QuickSort_A L ≠ PMF.pure (L.mergeSort (· ≤ ·)) := by
    use L;
  -- Let's choose the smallest such $L$ with respect to the length of the list.
  obtain ⟨L, hL_min⟩ : ∃ L : List ℕ, QuickSort_A L ≠ PMF.pure (L.mergeSort (· ≤ ·)) ∧ ∀ L' : List ℕ, L'.length < L.length → QuickSort_A L' = PMF.pure (L'.mergeSort (· ≤ ·)) := by
    have h_well_founded : WellFounded fun L L' : List ℕ => L.length < L'.length := by
      rw [ WellFounded.wellFounded_iff_has_min ];
      intro s hs; have := hs; exact (by
      have h_well_founded : WellFounded (fun n m : ℕ => n < m) := by
        exact wellFounded_lt;
      have := h_well_founded.has_min ( Set.image List.length s ) ⟨ _, Set.mem_image_of_mem _ this.choose_spec ⟩ ; aesop;);
    have := h_well_founded.has_min { L : List ℕ | QuickSort_A L ≠ PMF.pure ( L.mergeSort fun x1 x2 => decide ( x1 ≤ x2 ) ) } ⟨ L, hL ⟩;
    exact ⟨ this.choose, this.choose_spec.1, fun L' hL' => Classical.not_not.1 fun hL'' => this.choose_spec.2 L' hL'' hL' ⟩;
  obtain ⟨hL_ne, hL_min⟩ := hL_min;
  rcases L with ( _ | ⟨ head, tail ⟩ ) <;> simp_all +decide;
  · exact hL_ne ( by unfold QuickSort_A; rfl );
  · -- By definition of `QuickSort_A`, we know that `QuickSort_A (head :: tail)` is the bind of the uniform distribution over the indices of `head :: tail` with the function that sorts the list.
    have h_bind : QuickSort_A (head :: tail) = PMF.bindOnSupport (PMF.uniformOfFintype (Fin (head :: tail).length)) (fun idx_pivot h_idx_pivot => PMF.bind (QuickSort_A ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot]))) (fun S1 => PMF.bind (QuickSort_A ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot]))) (fun S2 => PMF.pure (S1 ++ [(head :: tail)[idx_pivot]] ++ S2)))) := by
      rw [QuickSort_A];
      rfl;
    -- By definition of `QuickSort_A`, we know that `QuickSort_A ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot]))` and `QuickSort_A ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot]))` are both equal to `PMF.pure (mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot])))` and `PMF.pure (mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot])))` respectively.
    have h_filter : ∀ idx_pivot : Fin (head :: tail).length, QuickSort_A ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot])) = PMF.pure (List.mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot])) (· ≤ ·)) ∧ QuickSort_A ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot])) = PMF.pure (List.mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot])) (· ≤ ·)) := by
      grind +revert;
    -- By definition of `partition_sort_eq_mergeSort`, we know that `mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot])) ++ [(head :: tail)[idx_pivot]] ++ mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot]))` is equal to `mergeSort (head :: tail)`.
    have h_mergeSort : ∀ idx_pivot : Fin (head :: tail).length, List.mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· < (head :: tail)[idx_pivot])) (· ≤ ·) ++ [(head :: tail)[idx_pivot]] ++ List.mergeSort ((head :: tail).eraseIdx idx_pivot |>.filter (· ≥ (head :: tail)[idx_pivot])) (· ≤ ·) = List.mergeSort (head :: tail) (· ≤ ·) := by
      intro idx_pivot; exact (by
      convert partition_sort_eq_mergeSort ( head :: tail ) idx_pivot using 1);
    refine' hL_ne _;
    ext b; simp +decide [PMF.pure_apply ] ;
    split_ifs <;> simp_all +decide [ PMF.pure_apply ]

/-
One can try to prove the correctness:
The probability that QuickSort_A on a list of two distinct elements
returns the sorted list is 1 (100%).
-/
lemma Correctness_Quicksort_A (L : List ℕ):
  QuickSort_A L (List.mergeSort L) = 1 := by
  rw [QuickSort_A_eq_pure_mergeSort]
  simp

end ARA
