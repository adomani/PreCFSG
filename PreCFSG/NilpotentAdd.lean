module

public import Mathlib.GroupTheory.Nilpotent

/-!
This file contains a minimally polished proof of Fitting's Theorem.
Below there are more details on the actual proof.

This file serves several purposes.

1. This is probably the human analogue of the kinds of non-idiomatic files that AIs generate,
   although I hope that the lemma selection is "better" than what an LLM would generate.
   Maybe, aiming for such files with AI agents is more accessible and a good stepping stone.
2. Polishing this proof and making it more "`mathlib` style" is probably a simpler goal than
   doing it from scratch.
   In turn, this could be a useful training model for AIs.
3. The argument itself is a thin wrapper around a result on non-associative, non-unitals semirings.
   This means that proving results about group theory can go via the API for rings.
   Exploring such connections is something that would be awesome to automate!
-/

/-!
# Fitting's Theorem (nilpotent normal subgroups)

If `H` and `K` are nilpotent normal subgroups of a group `G`, then `H ⊔ K` is nilpotent.
Moreover, if `H` has class `h` and `K` has class `k`, then the class of `H ⊔ K` is at most `h + k`.

This file implements the proof via a semiring structure on normal subgroups with
addition given by `⊔` and multiplication by the commutator `⁅·, ·⁆`, and translates
bounds on lower central series into estimates on powers in that semiring.
-/

@[expose] public section

namespace Ring

/-- A fold-equivalence over `List.range (n - 1)` when the step function depends only on
values `< n` and the membership predicate agrees on two finite sets. -/
lemma foldl_range {α : Type*} {n : ℕ}
    (s t : Finset ℕ) (init : α) (f : α → ℕ → Finset ℕ → α)
    (h : ∀ i < n, ∀ a, f a i s = f a i t) :
    (List.range (n - 1)).foldl (fun tot i => f tot (i + 1) s) init =
    (List.range (n - 1)).foldl (fun tot i => f tot (i + 1) t) init := by
  apply List.foldl_ext
  grind

section Mul

variable {M : Type*} [Mul M]

/--
Power by positive naturals on a (non-unital) semiring-like structure, defined by left multiplication
recursion.

We use `ℕ+` for the exponent since the ground ring does not necessarily contain a unit.
-/
instance : HPow M ℕ+ M where
  hPow m n := Nat.leRec m (fun ⦃_⦄ _ m' ↦ m * m') (Nat.one_le_of_lt n.2)

/-- The `1` in `ℕ+`. -/
instance : One ℕ+ where
  one := ⟨1, Nat.one_pos⟩

@[simp] lemma pow_one (a : M) : (a ^ (1 : ℕ+) : M) = a := rfl

/-- Successor step for positive power. -/
lemma pow_succ (n : ℕ+) (a : M) : a ^ (n + 1) = a * a ^ n :=
  Nat.leRec_succ a (fun ⦃_⦄ _ m ↦ a * m) _

variable (H K : M)

/--
Form the product of `n` factors, where the `i`-th one is `H`, if `i ∈ s` and it is `K` otherwise.
-/
def factor (n : ℕ) (s : Finset ℕ) : M :=
  (List.range (n - 1)).foldl
    (fun tot i => tot * if i + 1 ∈ s then H else K)
    (if 0 ∈ s then H else K)

variable {H K}

/-- One-step recursion for `factor`. -/
lemma factor_succ {n : ℕ} (hn : n ≠ 0) (s : Finset ℕ) :
    factor H K (n + 1) s = factor H K n s * if n ∈ s then H else K := by
  simp only [factor, mul_ite, add_tsub_cancel_right]
  conv_lhs =>
    rw [show n = n - 1 + 1 by grind, List.range_succ, List.foldl_append]
  grind only [= List.foldl_cons, = List.foldl_nil]

@[simp] lemma factor_zero (s : Finset ℕ) :
    factor H K 0 s = if 0 ∈ s then H else K := by
  simp [factor]

/-- If membership in `s` and `t` agrees below `n`, then the corresponding `factor`s agree. -/
lemma factor_eq_factor_of {n : ℕ} (hn : n ≠ 0) (s t : Finset ℕ)
    (h : ∀ i < n, (i ∈ s ↔ i ∈ t)) :
    factor H K n s = factor H K n t := by
  unfold factor
  convert foldl_range s t (if 0 ∈ s then H else K) (· * if · ∈ · then H else K) _ using 2
  · simp_rw [h _ (Nat.ne_zero_iff_zero_lt.mp hn)]
  · simp_all

end Mul

variable {R : Type*} [NonUnitalNonAssocCommSemiring R]

section JustAlgebraicManipulations

variable {H K : R}

/-- The canonical embedding `range n ↪ range (n+1)`. -/
abbrev castRangeSucc (n : ℕ) : Finset.range n → Finset.range (n + 1) :=
  fun ⟨a, ha⟩ ↦ ⟨a, Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp ha) (lt_add_one n))⟩

/-- Reindexing a sum over subsets of `range (n+1)` depending on whether `n` is selected. -/
lemma sum_factor_filter_eq (n : ℕ+)
    (p : Finset (Finset.range (n + 1)) → Prop) [DecidablePred p]
    (hp :
      letI n' : Finset.range (n + 1) := ⟨n, Finset.self_mem_range_succ n⟩
      (∀ i, p i ↔ n' ∈ i) ∨ (∀ i, p i ↔ n' ∉ i)) :
    (∑ x with p x, factor H K n (x.image Subtype.val)) =
      (∑ s : Finset (Finset.range n), factor H K n (s.image Subtype.val)) := by
  let n' : Finset.range (n + 1) := ⟨n, Finset.self_mem_range_succ n⟩
  symm
  apply Finset.sum_nbij (i := fun a ↦
    if p {n'} then
      (a.image (castRangeSucc n)).cons n' (by simp [n'])
    else
      a.image (castRangeSucc n))
  · aesop
  · unfold castRangeSucc
    simp_all only [Finset.cons_eq_insert, Finset.coe_univ, Set.injOn_univ, n']
    obtain ⟨val, property⟩ := n'
    intros a b ab
    ext ⟨val, property⟩
    rw [Finset.ext_iff] at ab
    have vn := Finset.mem_range.mp property
    simp_all only [Finset.mem_range, Order.lt_add_one_iff, Subtype.forall]
    cases hp with
    | inl h =>
      simp_all [↓reduceIte]
      grind
    | inr h_1 =>
      simp_all [↓reduceIte]
      grind
  · intro x hx
    simp_all only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Finset.coe_univ,
      Set.image_univ, Set.mem_range]
    let y : Finset (Finset.range n.1) := (x.erase n').image fun s : Finset.range (n + 1) =>
      if h : s < n.1 then
        ⟨s, Finset.mem_range.mpr h⟩
      else
        ⟨0, Finset.mem_range.mpr n.2⟩
    use y
    ext ⟨val, property⟩
    obtain rfl | ha := eq_or_ne val n'
    · unfold castRangeSucc
      aesop
    simp_all only [ne_eq, Finset.cons_eq_insert, n', y]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨val_1, property_1⟩ := n'
      cases hp with
      | inl h_1 =>
        simp_all only [Finset.mem_singleton, ↓reduceIte, Finset.mem_insert, Subtype.mk.injEq,
          Finset.mem_image, Subtype.exists, Finset.mem_range, exists_and_right, exists_eq_right,
          false_or]
        obtain ⟨hvn, hr⟩ := h
        erw [Finset.mem_image] at hr
        obtain ⟨⟨hvn, hr⟩, ⟨n1, h2⟩⟩ := hr
        rw [dif_pos] at h2
        · grind
        · apply Nat.lt_of_le_of_ne (Finset.mem_range_succ_iff.mp hr)
          rw [Finset.mem_erase] at n1
          simp_all
      | inr h_2 =>
        simp_all only [Finset.mem_singleton, not_true_eq_false, ↓reduceIte, not_false_eq_true,
          Finset.erase_eq_of_notMem, Finset.mem_image, Subtype.mk.injEq, Subtype.exists,
          Finset.mem_range, exists_and_right, exists_eq_right]
        obtain ⟨w, h⟩ := h
        erw [Finset.mem_image] at h
        simp_all only [Subtype.exists, Finset.mem_range, Order.lt_add_one_iff]
        obtain ⟨w_1, ⟨w_2, h⟩⟩ := h
        obtain ⟨left, right⟩ := h
        split at right
        · grind
        have : w_1 = n := le_antisymm w_2 (not_lt.mp ‹_›)
        simp_all
    · have h_val_n : val < n := by
        rw [Finset.mem_range] at property
        grind
      split
      · simp only [Finset.mem_insert, Subtype.mk.injEq, h_val_n.ne, Finset.mem_image,
        Subtype.exists, Finset.mem_range, exists_and_right, exists_eq_right, false_or]
        use h_val_n
        erw [Finset.mem_image]
        use ⟨val, property⟩, ?_
        · rw [dif_pos]
          · congr
          · simpa
        · rw [Finset.mem_erase]
          simpa [h] using Nat.ne_of_lt h_val_n
      · simp only [Finset.mem_image, Subtype.mk.injEq, Subtype.exists, Finset.mem_range,
        exists_and_right, exists_eq_right, h_val_n, exists_true_left]
        erw [Finset.mem_image]
        use ⟨val, property⟩
        simp_all only [Finset.mem_erase, ne_eq, Subtype.mk.injEq, not_false_eq_true, and_self,
          true_and]
        · rw [dif_pos]
          · congr
          · simpa
  intro a _
  simp only [Finset.cons_eq_insert]
  refine factor_eq_factor_of n.ne_zero _ _ ?_
  simp
  grind

/-- A nonassociative binomial-style expansion:
`(H + K) ^ n` is the sum over subsets `s ⊆ {0,…,n-1}` of the corresponding `factor`. -/
lemma pow_add_eq_sum_factor (n : ℕ+) :
    (H + K) ^ n = ∑ s : Finset (Finset.range n), factor H K n (s.image (↑)) := by
  induction n with
  | one =>
    simp only [pow_one, PNat.val_ofNat, Finset.range_one, factor, Finset.mem_image, Subtype.exists,
      Finset.mem_singleton, exists_and_right, exists_eq_right, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, IsEmpty.exists_iff, ↓reduceIte, exists_and_self, exists_prop_eq, tsub_self,
      List.range_zero, List.foldl_nil]
    rw [Finset.sum_eq_add Finset.univ ∅]
    · grind
    · simp
    · grind only [= Finset.mem_singleton, ← Finset.mem_univ, ← Finset.notMem_empty]
    · simp
    · simp
  | succ n ih =>
    rw [pow_succ, add_mul, ih]
    simp only [PNat.add_coe, PNat.val_ofNat]
    have : n.1 ≠ 0 := n.2.ne'
    conv_rhs =>
      congr
      rfl
      ext
      rw [factor_succ]
      rfl
      exact n.2.ne'
    simp_rw [mul_ite]
    rw [@Finset.sum_ite]
    congr 1
    · trans
        H * ∑ x : Finset (Finset.range (n + 1)) with ⟨n, Finset.self_mem_range_succ n⟩ ∈ x,
          factor H K n (Finset.image Subtype.val x)
      · rw [sum_factor_filter_eq]
        simp
      · rw [mul_comm, ← Finset.sum_mul]
        simp
        rfl
    · rw [mul_comm, ← Finset.sum_mul]
      erw [sum_factor_filter_eq]
      simp

/-- `factor` is invariant under complement in `range n` after swapping `H` and `K`. -/
lemma factor_eq_factor_compl {n : ℕ} (hn : n ≠ 0) (s : Finset ℕ) :
    factor H K n s = factor K H n (Finset.range n \ s) := by
  induction n with
  | zero => contradiction
  | succ n ih =>
    obtain rfl | n0 := eq_or_ne n 0
    · simp_all [factor]
    rw [factor_succ n0, factor_succ n0]
    by_cases nh : n ∈ s
    · rw [if_pos nh, ih n0, if_neg]
      · congr 1
        refine factor_eq_factor_of n0 _ _ ?_
        grind
      · grind
    · rw [if_neg nh]
      simp_all only [Finset.mem_sdiff, Finset.mem_range, lt_add_iff_pos_right, zero_lt_one,
        not_false_eq_true, and_self, ↓reduceIte]
      rw [ih n0]
      congr 1
      refine factor_eq_factor_of n0 _ _ ?_
      grind

end JustAlgebraicManipulations

section Order

variable [PartialOrder R]

/-- If `J * K ≤ K` holds for all `J, K`, then the power map `n ↦ H ^ n` is antitone in `ℕ+`. -/
lemma pow_antitone (H : R) (hmul : ∀ J K : R, J * K ≤ K) :
    Antitone (fun n : ℕ+ ↦ H ^ n) := by
  intros a b ab
  dsimp only
  induction b with
  | one => simp_all
  | succ n ih =>
    obtain rfl | an := eq_or_ne a (n + 1)
    · simp
    · rw [pow_succ]
      exact (hmul _ _).trans <| ih (Nat.le_of_lt_succ (ab.lt_of_ne an))

variable [MulPosMono R] {H K : R}

variable (K) in
/-- Upper bound in terms of powers of `H` when at least one index `< n` chooses `H`. -/
lemma factor_le_left (H0 : 0 ≤ H)
    (n : ℕ) (s : Finset ℕ)
    (hs : (s.filter (· < n)).Nonempty)
    (hmul : ∀ J K : R, J * K ≤ K) :
    letI s' : ℕ+ := ⟨(s.filter (· < n)).card, hs.card_pos⟩
    factor H K n s ≤ H ^ s' := by
  classical
  revert s
  induction n with
  | zero => simp
  | succ n ih =>
    obtain rfl | n0 := eq_or_ne n 0
    · unfold factor
      intro s hs
      simp_all only [not_lt_zero, Finset.filter_false, Finset.not_nonempty_empty, factor_zero,
        Finset.filter_true, IsEmpty.forall_iff, implies_true, mul_ite, zero_add, tsub_self,
        List.range_zero, List.foldl_nil, Nat.lt_one_iff]
      split
      next h =>
        apply le_of_eq
        symm
        convert pow_one _
        grind only [Finset.card_filter_eq_zero_iff, Finset.filter_eq, Finset.filter_eq',
          Finset.card_filter_eq_iff, Finset.filter_card_eq, = Finset.card_singleton, PNat.mk_one]
      next h => grind
    intros s s0
    rw [factor_succ n0]
    by_cases hns : n ∈ s
    · rw [if_pos hns]
      by_cases hs0 : {x ∈ s | x < n}.Nonempty
      · let h' : ℕ+ := ⟨{x ∈ s | x < n}.card, hs0.card_pos⟩
        trans H ^ h' * H
        · exact mul_le_mul_of_nonneg_right (ih _ hs0) H0
        · apply le_of_eq
          rw [mul_comm, Eq.comm]
          convert pow_succ h' H
          suffices {x ∈ s | x < n + 1}.card = {x ∈ s | x < n}.card + 1 by aesop
          rw [Finset.card_eq_succ]
          use n, {x ∈ s | x < n}
          grind
      have : ({x ∈ s | x < n + 1} : Finset ℕ) = {n} := by
        simp_all only [ne_eq, Order.lt_add_one_iff, Finset.not_nonempty_iff_eq_empty,
          Finset.filter_eq_empty_iff, not_lt]
        grind
      simp_rw [this]
      simp only [Finset.card_singleton, PNat.mk_ofNat, pow_one, ge_iff_le]
      exact hmul _ _
    · rw [if_neg hns]
      trans factor H K n s
      · rw [mul_comm]
        exact hmul _ _
      · suffices {x ∈ s | x < n + 1} = {x ∈ s | x < n} by aesop
        grind

/-- Nonnegativity of `factor` when `H, K ≥ 0`. -/
lemma factor_nonneg_of_nonneg (H0 : 0 ≤ H) (K0 : 0 ≤ K) (n : ℕ+) (s : Finset ℕ) :
    0 ≤ factor H K n s := by
  unfold factor
  induction n with
  | one => aesop
  | succ n ih =>
    simp_all only [mul_ite, PNat.add_coe, PNat.val_ofNat, add_tsub_cancel_right]
    split
    next h =>
      simp_all only [↓reduceIte]
      rw [show n = (n.1 - 1) + 1 by cases n; dsimp; grind]
      rw [List.range_succ]
      simp_all only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      split
      next h_1 => exact Right.mul_nonneg ih H0
      next h_1 => exact Right.mul_nonneg ih K0
    next h =>
      simp_all only [↓reduceIte]
      rw [show n = (n.1 - 1) + 1 by cases n; dsimp; grind]
      rw [List.range_succ]
      simp_all only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      split
      next h_1 => exact Right.mul_nonneg ih H0
      next h_1 => exact Right.mul_nonneg ih K0

variable (H) in
/-- Upper bound in terms of powers of `K` when at least one index `< n` chooses `K`. -/
lemma factor_le_right (K0 : 0 ≤ K) (n : ℕ) (s : Finset ℕ)
    (hs : ((Finset.range n \ s).filter (· < n)).Nonempty)
    (hmul : ∀ J K : R, J * K ≤ K) :
    letI s' : ℕ+ := ⟨((Finset.range n \ s).filter (· < n)).card, hs.card_pos⟩
    factor H K n s ≤ K ^ s' := by
  obtain rfl | n0 := eq_or_ne n 0
  · grind
  rw [factor_eq_factor_compl n0]
  exact factor_le_left H K0 n (Finset.range n \ s) hs hmul

/-- Vanishing of a factor when enough `H`-steps or `K`-steps vanish. -/
lemma factor_eq_zero_of_le (H0 : 0 ≤ H) (K0 : 0 ≤ K)
    (hmul : ∀ J K : R, J * K ≤ K)
    (nh nk : ℕ+) (s : Finset ℕ)
    (hH : H ^ nh = 0) (hK : K ^ nk = 0) :
    factor H K (nh + nk - 1) s = 0 := by
  by_cases hs : nh ≤ (s.filter (· < nh.1 + nk - 1)).card
  · suffices factor H K (↑nh + ↑nk - 1) s ≤ 0 from
      this.antisymm (factor_nonneg_of_nonneg H0 K0 (nh + nk - 1) _)
    apply (factor_le_left _ H0 _ _ _ hmul ..).trans
    · refine le_trans ?_ hH.le
      apply pow_antitone _ hmul hs
      rw [← Finset.one_le_card]
      exact le_trans NeZero.one_le hs
  · suffices factor H K (↑nh + ↑nk - 1) s ≤ 0 from
      this.antisymm (factor_nonneg_of_nonneg H0 K0 (nh + nk - 1) _)
    have : nk ≤ ((Finset.range (↑nh + ↑nk - 1) \ s).filter (· < nh.1 + nk - 1)).card := by
      rw [not_le] at hs
      have : (s.filter (· < nh.1 + nk - 1)) ∪
          ((Finset.range (↑nh + ↑nk - 1) \ s).filter (· < nh.1 + nk - 1)) =
            Finset.range (nh + nk - 1) := by
        ext a
        simp_all only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range]
        refine ⟨by aesop, fun h ↦ ?_⟩
        by_cases as : a ∈ s
        · solve_by_elim
        · tauto
      grind
    refine le_trans ?_ hK.le
    refine (factor_le_right _ K0 _ _ ?_  hmul).trans (pow_antitone _ hmul this)
    rw [← Finset.one_le_card]
    exact le_trans NeZero.one_le this

/-- The vanishing of the power of a binomial, assuming enough vanishing and inequalities. -/
lemma pow_add_eq_zero_of_le (H0 : 0 ≤ H) (K0 : 0 ≤ K)
    (hmul : ∀ J K : R, J * K ≤ K)
    (nh nk : ℕ+) (hH : H ^ nh = 0) (hK : K ^ nk = 0) :
    (H + K) ^ (nh + nk - 1) = 0 := by
  rw [pow_add_eq_sum_factor]
  exact Finset.sum_eq_zero <| fun _ _ ↦ factor_eq_zero_of_le H0 K0 hmul _ _ _ hH hK

end Order

end Ring

variable {G} [Group G] {H K : Subgroup G}

open Group

namespace Subgroup

@[simp] lemma map_top : map H.subtype ⊤ = H := by
  ext
  simp

open Pointwise in
/-- Membership in `H ⊔ K` equals membership in the product set when `H` is normal. -/
@[simp] lemma mem_sup_iff_mem_mul_of_normal_left (g : G) [H.Normal] :
    g ∈ H ⊔ K ↔ g ∈ (H : Set G) * K := by
  rw [← SetLike.mem_coe, normal_mul]

/-- `⁅L, ·⁆` is subadditive over `⊔` on the right when the left factor is normal. -/
lemma commutator_sup_le_sup_commutator_of_normal_left (H K L : Subgroup G)
    (HNorm : H.Normal) (LK : ⁅L, K⁆.Normal) :
    ⁅L, H ⊔ K⁆ ≤ ⁅L, H⁆ ⊔ ⁅L, K⁆ := by
  intro s hs
  refine closure_induction ?_ (by simp) (fun l k hl hk ↦ mul_mem) (by simp) hs
  intro g hg
  simp_all only [mem_sup_iff_mem_mul_of_normal_left, Set.mem_setOf_eq]
  obtain ⟨l, hl, b, hb, rfl⟩ := hg
  obtain ⟨h, hh, k, hk, rfl⟩ := Set.mem_mul.mp hb
  rw [commutatorElement_def]
  have : l * (h * k) * l⁻¹ * (h * k)⁻¹ = ⁅l, h⁆ * (h * ⁅l, k⁆ * h⁻¹) := by
    simp [commutatorElement_def, ← mul_assoc]
  rw [this]
  refine mul_mem_sup (commutator_mem_commutator hl hh) ?_
  exact LK.conj_mem _ (commutator_mem_commutator hl hk) h

/-- `⁅L, ·⁆` is superadditive over `⊔` on the right when the left factor is normal. -/
lemma commutator_sup_le_sup_commutator_of_normal_left_other (H K L : Subgroup G) :
    ⁅L, H⁆ ⊔ ⁅L, K⁆ ≤ ⁅L, H ⊔ K⁆ :=
  sup_le (commutator_mono le_rfl le_sup_left) (commutator_mono le_rfl le_sup_right)

/-- Commutator distributes over `⊔` on the right when all three subgroups are normal.

See `commutator_sup_le_sup_commutator_of_normal_left` and
`commutator_sup_le_sup_commutator_of_normal_left_other` for the separate inclusions, with weaker
assumptions.
-/
lemma commutator_sup_distrib_left_of_normal (H K L : Subgroup G)
    (HNorm : H.Normal) (LNorm : L.Normal) (KNorm : K.Normal) :
    ⁅L, H ⊔ K⁆ = ⁅L, H⁆ ⊔ ⁅L, K⁆ := by
  refine le_antisymm ?_ ?_
  · exact commutator_sup_le_sup_commutator_of_normal_left _ _ _ HNorm (commutator_normal _ _)
  · exact commutator_sup_le_sup_commutator_of_normal_left_other _ _ _

variable (G) in
/--
The type of normal subgroups of `G`.

We endow this type with the semiring structure:
* `H + K := H ⊔ K`,
* `H * K := ⁅H, K⁆`.
-/
def NoS := {H : Subgroup G // H.Normal}

namespace NoS

instance : NonUnitalNonAssocCommSemiring (NoS G) where
  add := fun ⟨H, hH⟩ ⟨K, hK⟩ ↦ ⟨H ⊔ K, sup_normal H K⟩
  add_assoc := fun ⟨H, hH⟩ ⟨K, hK⟩ ⟨L, hL⟩ ↦ by
    change ⟨H ⊔ K ⊔ L, _⟩ = (⟨H ⊔ (K ⊔ L), _⟩ : NoS G)
    simp [sup_assoc]
  zero := ⟨⊥, normal_bot⟩
  zero_add := fun ⟨H, hH⟩ ↦ by
    change ⟨⊥ ⊔ H, _⟩ = (⟨H, _⟩ : NoS G)
    simp
  add_zero := fun ⟨H, hH⟩ ↦ by
    change ⟨H ⊔ ⊥ , _⟩ = (⟨H, _⟩ : NoS G)
    simp
  nsmul := fun
    | 0, _ => (⟨⊥, normal_bot⟩ : NoS G)
    | _, H => H
  nsmul_succ := by
    intro n ⟨H, hH⟩
    simp_all only
    split
    next _ _ =>
      change ⟨H, _⟩ = (⟨⊥ ⊔ H, _⟩ : NoS G)
      simp
    next _ _ _ _ =>
      change _ = (⟨H ⊔ H, _⟩ : NoS G)
      simp
  add_comm := fun ⟨H, hH⟩ ⟨K, hK⟩ ↦ by
    change ⟨H ⊔ K, _⟩ = (⟨K ⊔ H, _⟩ : NoS G)
    simp [sup_comm]
  mul := fun ⟨H, hH⟩ ⟨K, hK⟩ ↦ ⟨⁅H, K⁆, commutator_normal H K⟩
  left_distrib := fun ⟨H, hH⟩ ⟨K, hK⟩ ⟨L, hL⟩ ↦ by
    change ⟨⁅H, K ⊔ L⁆ , _⟩ = (⟨⁅H, K⁆ ⊔ ⁅H, L⁆, _⟩ : NoS G)
    simp_rw [commutator_sup_distrib_left_of_normal]
  right_distrib := fun ⟨H, hH⟩ ⟨K, hK⟩ ⟨L, hL⟩ ↦ by
    change ⟨⁅H ⊔ K, L⁆ , _⟩ = (⟨⁅H, L⁆ ⊔ ⁅K, L⁆, _⟩ : NoS G)
    simp_rw [commutator_comm _ L, commutator_sup_distrib_left_of_normal]
  zero_mul := fun ⟨H, hH⟩ ↦ by
    change (⟨⁅⊥, H⁆, _⟩) = (⟨⊥, _⟩ : NoS G)
    simp
  mul_zero := fun ⟨H, hH⟩ ↦ by
    change ⟨⁅H, ⊥⁆, _⟩ = (⟨⊥, _⟩ : NoS G)
    simp
  mul_comm := fun ⟨H, hH⟩ ⟨K, hK⟩ ↦ by
    change ⟨⁅H, K⁆, _⟩ = (⟨⁅K, H⁆, _⟩ : NoS G)
    simp_rw [commutator_comm]

@[simp] lemma ext_iff (H K : NoS G) : H = K ↔ H.1 = K.1 := Subtype.ext_iff
@[ext] lemma ext (H K : NoS G) (h : H.1 = K.1) : H = K := Subtype.ext_iff.mpr h
@[simp] lemma zero_eq_bot : (0 : NoS G).1 = (⊥ : Subgroup G) := rfl
lemma add_eq_sup (H K : NoS G) : (H + K).1 = H.1 ⊔ K.1 := rfl
lemma mul_eq_comm (H K : NoS G) : (H * K).1 = ⁅H.1, K.1⁆ := rfl

/-- Order structure induced from inclusion of the underlying subgroups. -/
instance : PartialOrder (NoS G) :=
  PartialOrder.lift Subtype.val <| (Set.injective_codRestrict Subtype.property).mp fun ⦃_ _⦄ a ↦ a

instance : OrderBot (NoS G) where
  bot := 0
  bot_le _ := show (⟨⊥ , _⟩ : NoS G).1 ≤ _ from bot_le

lemma le_iff (H K : NoS G) : H ≤ K ↔ H.1 ≤ K.1 := Iff.rfl

/-- `H ≤ K` implies the inequality `(C ⊔ H) ≤ (C ⊔ K)`. -/
instance : AddLeftMono (NoS G) where
  elim := fun ⟨C, _⟩ ⟨H, _⟩ ⟨K, _⟩ HK ↦
    show (C ⊔ H : Subgroup G) ≤ C ⊔ K from sup_le_sup_left HK C

/-- Monotonicity in the right commutator slot. -/
instance : MulRightMono (NoS G) where
  elim _ _ _ bc := commutator_mono bc le_rfl

/-- Monotonicity in the left commutator position. -/
instance : MulLeftMono (NoS G) where
  elim _ _ _ := commutator_mono le_rfl

lemma zero_le (H : NoS G) : 0 ≤ H := bot_le (α := NoS G)

/--
The `k`‑th power of a normal subgroup `H : NoS G` corresponds to the
`(k - 1)`‑st term of the lower central series of `H`, viewed as a subgroup of `G`.
-/
lemma pow_eq_lowerCentralSeries_pred (k : ℕ+) (H : NoS G) :
    (H ^ k).1 = (lowerCentralSeries H.1 (k - 1)).map H.1.subtype := by
  induction k with
  | one => simp
  | succ n ih =>
    simp only [Ring.pow_succ, mul_eq_comm, PNat.add_coe, PNat.val_ofNat, add_tsub_cancel_right]
    cases n with
    | mk n hn =>
      have : n = n - 1 + 1 := by grind
      simp only [PNat.mk_coe]
      conv_rhs => rw [this]
      change _ = map H.1.subtype ⁅_, _⁆
      simp [ih, commutator_comm, map_commutator]

end NoS

open NoS

/--
If the lower central series of `H` is trivial after `nH` steps and
the lower central series of `K` is trivial after `nK` steps,
then the lower central series of `H ⊔ K` is trivial after `nH + nK` steps.

Assumes that `H` and `K` are normal (and would not necessarily be true otherwise).
-/
lemma lowerCentralSeries_eq_zero_of_add {nH nK : ℕ} {H K : Subgroup G}
    [HN : H.Normal] (hH : lowerCentralSeries H nH = ⊥)
    [KN : K.Normal] (hK : lowerCentralSeries K nK = ⊥) :
    lowerCentralSeries (H ⊔ K : Subgroup G) (nH + nK) = ⊥ := by
  let H' : NoS G := ⟨_, HN⟩
  let K' : NoS G := ⟨_, KN⟩
  let hk : ℕ+ := ⟨nH + nK + 1, Nat.zero_lt_succ _⟩
  suffices (H' + K') ^ hk = 0 by
    apply_fun map (⟨H ⊔ K, sup_normal H K⟩ : NoS G).1.subtype
    · convert (pow_eq_lowerCentralSeries_pred hk _).symm using 2
      simpa [Eq.comm]
    · exact map_injective <| subtype_injective _
  convert Ring.pow_add_eq_zero_of_le (zero_le H') (zero_le K') _
    ⟨nH + 1, Nat.zero_lt_succ _⟩ ⟨nK + 1, Nat.zero_lt_succ _⟩ _ _
  · apply PNat.coe_injective
    rw [PNat.sub_coe, if_pos ((PNat.coe_lt_coe _ _).mp (by simp; grind))]
    simp [hk]
    grind
  · exact fun J K ↦ commutator_le_right (h := K.2) _ _
  all_goals
    ext : 1
    rw [pow_eq_lowerCentralSeries_pred, PNat.mk_coe, add_tsub_cancel_right]
  · rw [hH, map_bot, zero_eq_bot]
  · rw [hK, map_bot, zero_eq_bot]

/-- **Fitting's Theorem**:
If `H` and `K` are nilpotent normal subgroups of `G`, then `H ⊔ K` is nilpotent. -/
lemma isNilpotent_sup_of_normal (H K : Subgroup G)
    [HN : H.Normal] [hH : IsNilpotent H] [KN : K.Normal] [hK : IsNilpotent K] :
    IsNilpotent (H ⊔ K : Subgroup G) := by
  rw [nilpotent_iff_lowerCentralSeries] at hH hK ⊢
  obtain ⟨nH, hH⟩ := hH
  obtain ⟨nK, hK⟩ := hK
  use nH + nK
  exact lowerCentralSeries_eq_zero_of_add hH hK

end Subgroup
