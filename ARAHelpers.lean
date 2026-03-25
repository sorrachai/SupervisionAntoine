import Mathlib

/-!
# Helper lemmas for QuickSort correctness proof
-/

open List

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
