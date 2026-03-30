import ARA.Phase2
import ARA.Tactics

/-!
# QuickSort Correctness Proof

This module contains the full correctness proof for `QuickSort_A`:
the randomized quicksort always returns the sorted list with probability 1.

## Main Result
- QuickSort_A is deterministic (that is a pure distribution)
  `QuickSort_A_eq_pure_mergeSort`: QuickSort_A L = PMF.pure (List.mergeSort L)

- Since List.mergeSort L is the sorted version of L, the correctness of the
  algorithm follows `Correctness_Quicksort_A`:
  QuickSort_A L (Output) = 1 → (Output.SortedLE ∧ List.Perm Output L)

## Helper Lemmas
- `perm_getElem_cons_eraseIdx`: eraseIdx gives back a permutation
- `filter_partition_perm`: filter partition gives a permutation
- `partition_sort_concat_perm`: partition-sort-concat is a permutation
- `partition_sort_concat_sorted`: partition-sort-concat is sorted
- `eq_mergeSort_of_perm_of_sorted`: uniqueness of sorted permutations
- `partition_sort_eq_mergeSort`: main partition-sort equality
-/

/-
QuickSort_A is deterministic: it always returns the sorted list. This follows by strong induction on L.length.

Base case (L = []): QuickSort_A [] = PMF.pure [] = PMF.pure (mergeSort []) by List.mergeSort_nil.

Inductive case (L = head :: tail): QuickSort_A L unfolds to a bindOnSupport over uniformOfFintype (Fin L.length).
For each pivot index idx_pivot, the branch:
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
  -- By transitivity of permutations, we can chain these steps together:
  -- 1. The mergeSort of the partitioned lists is a permutation of the concatenation of the partitioned lists.
  -- 2. The concatenation of the partitioned lists is a permutation of the original list with the pivot element moved to the front.
  have h_chain :
  List.Perm (List.mergeSort
  (List.filter (fun x => x < L[i]) (L.eraseIdx i)) (fun a b => decide (a ≤ b)) ++ [L[i]] ++ List.mergeSort (List.filter (fun x => x ≥ L[i]) (L.eraseIdx i)) (fun a b => decide (a ≤ b))) (List.filter (fun x => x < L[i]) (L.eraseIdx i) ++ [L[i]] ++ List.filter (fun x => x ≥ L[i]) (L.eraseIdx i)) := by
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
    haveI : Nonempty (Fin (head :: tail).length) := ⟨0, by simp⟩
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
Quicksort_A is correct: For any list L, the list that has probability 1 through
Quicksort_A L is always sorted and is a permutation of L.
This follows from the previous lemma, the fact that List.mergeSort L is sorted
and a permutation of L.
-/
lemma Correctness_Quicksort_A (L : List ℕ):
  ∃ Output : List ℕ, QuickSort_A L (Output) = 1 ∧ (Output.SortedLE ∧ Output.Perm L) := by
  rw [QuickSort_A_eq_pure_mergeSort L]
  use List.mergeSort L
  simp [PMF.pure_apply]
  constructor
  · exact List.sortedLE_mergeSort
  · exact List.mergeSort_perm L (fun a b => decide (a ≤ b))

/-
Direct proof by strong induction on L.length.
This avoids the detour through QuickSort_A_eq_pure_mergeSort.

Proof structure:
- Base case (L = []): QuickSort_A [] has probability 1 on [], which is sorted and a permutation of [].
- Inductive case (L = head :: tail):
  1. By IH, for all L' with L'.length < L.length, QuickSort_A produces a sorted permutation with prob 1.
  2. For each pivot index, QuickSort_A partitions L into L1 (< pivot) and L2 (≥ pivot).
  3. By IH, QuickSort_A L1 and QuickSort_A L2 return sorted permutations with prob 1.
  4. Concatenating sorted partitions with the pivot yields a sorted permutation of L.
  5. Since all branches deterministically produce the same result, prob = 1.
-/
lemma Correctness_Quicksort_A_bis:
  ∀ L : List ℕ, ∃ Output : List ℕ, QuickSort_A L (Output) = 1 ∧ Output.SortedLE ∧ Output.Perm L := by
  -- Proof by strong induction on L.length
  intro L
  -- Bind the length of L to n and generalize L so the induction hypothesis
  -- applies to any list of strictly smaller length.
  induction' hn : L.length using Nat.strong_induction_on with n ih generalizing L
  by_cases h : n = 0
  · simp [h] at hn
    simp [hn]
    unfold QuickSort_A
    grind
  · have h_nonempty : L ≠ [] := by grind
    unfold QuickSort_A
    match L with
    | [] => contradiction
    | head::tail =>
      let L := head :: tail
      -- For each pivot index, we will show that the partitioned lists are
      -- sorted permutations of their respective partitions with probability 1.
      haveI : Nonempty (Fin L.length) := ⟨0, by grind⟩
      have idx_pivot_dist := PMF.uniformOfFintype (Fin L.length)
      have h_partition : ∀ idx_pivot : Fin L.length,
        let pivot := L[idx_pivot]
        let rest := L.eraseIdx idx_pivot
        let L1 := rest.filter (fun x => decide (x < pivot))
        let L2 := rest.filter (fun x => decide (x ≥ pivot))
        ∃ Output : List ℕ,
        PMF.bind (QuickSort_A L1)
        (fun S1 =>
        PMF.bind (QuickSort_A L2) (fun S2 => PMF.pure (S1 ++ [pivot] ++ S2))) (Output) = 1
        ∧ Output.SortedLE ∧ Output.Perm L := by
        intro idx_pivot
        let pivot := L[idx_pivot]
        let rest := L.eraseIdx idx_pivot
        let L1 := rest.filter (fun x => decide (x < pivot))
        let L2 := rest.filter (fun x => decide (x ≥ pivot))
        /- By ih, since L1.length < L.length and L2.length < L.length,
        we know that QuickSort_A L1 and QuickSort_A L2 return sorted
        permutations with probability 1 on a certain respective outputs
        Output1 and Output2 that are sorted and are permutations
        of L1 and L2 respectively.-/
        obtain ⟨Output1, ⟨Mass1, ⟨Sorted1, Perm1⟩⟩⟩ := by
          apply ih L1.length
          grind
          rfl
        obtain ⟨Output2, ⟨Mass2, ⟨Sorted2, Perm2⟩⟩⟩ := by
          apply ih L2.length
          grind
          rfl
        use Output1 ++ [pivot] ++ Output2
        constructor
        · -- The probability that the branch corresponding to idx_pivot
          -- returns Output1 ++ [pivot] ++ Output2 is Mass1 * Mass2, which is 1 * 1 = 1.
          sorry
        · constructor
          · -- One has to show that Output1 ++ [pivot] ++ Output2 is sorted,
            -- which follows from the fact that Output1 is sorted, Output2
            -- is sorted and all elements of Output1 are less than pivot and
            -- all elements of Output2 are greater than or equal to pivot.
            sorry
          · -- One has to show that Output1 ++ [pivot] ++ Output2 is a
            -- permutation of L, which follows from the fact that Output1
            -- is a permutation of L1, Output2 is a permutation of L2 and
            -- the fact that L1 ++ [pivot] ++ L2 is a permutation of L.
            sorry




end ARA
