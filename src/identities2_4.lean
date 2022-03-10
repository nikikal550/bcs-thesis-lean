import identities2_3


open finset
open_locale big_operators




lemma aux1 (f : ℕ → ℕ → ℝ) (s : finset ℕ) (sj : finset ℕ) (snat : finset ℕ) (s ⊆ snat) (j : ℕ) :
 ite (j ∈ sj) (Sum (f j) s) 0 = Sum (λ k, f j k * (ite (j ∈ sj ∧ k ∈ s) 1 0)) snat :=
begin

  have h : Sum (λ k, ((ite (j ∈ sj ∧ k ∈ s) (f j k) 0))) snat = Sum (λ k, (f j k * (ite (j ∈ sj ∧ k ∈ s) 1 0))) snat,
  { apply congr, apply congr, refl, apply funext, intro x, exact (mul_boole (j ∈ sj ∧ x ∈ s) (f j x)).symm, refl, },
  rw ← h,
  unfold Sum,
  
  have h3 : ∑ (k : ℕ) in snat, ite (j ∈ sj ∧ k ∈ s) (f j k) 0 = 
  ite (j ∈ sj) (∑ (k : ℕ) in snat, ite (k ∈ s) (f j k) 0) 0, 
  { rw ← boole_mul, rw mul_sum, apply congr, refl, apply funext, intro k, rw mul_comm, rw mul_boole,
  rw ite_and, },
  rw h3,

  rw sum_ite,
  rw sum_const_zero,
  rw add_zero,
  have h1 : filter (λ (x : ℕ), x ∈ s) snat = s,
  { exact inf_eq_right.mpr H, },
  have h2 : ∑ (k : ℕ) in s, f j k = ∑ (k : ℕ) in filter (λ (x : ℕ), x ∈ s) snat, f j k,
  { rw h1, },
  rw h2,

end






lemma aux2 (f : ℕ → ℕ → ℝ) (sk : finset ℕ) (sj : finset ℕ) (s : finset ℕ) (H1 : sj ⊆ s) ( H2 : sk ⊆ s) :
Sum (λ j, Sum (λ k, f j k) sk) sj = Sum (λ j, Sum (λ k, f j k * (ite (j ∈ sj ∧ k ∈ sk) 1 0)) s) s :=
begin

  have h1 : Sum (λ j, Sum (λ k, f j k * (ite (j ∈ sj ∧ k ∈ sk) 1 0)) s) s = 
  Sum (λ j, ite (j ∈ sj) (Sum (f j) sk) 0) s, 
  { apply congr, apply congr, refl, apply funext, intro j, rw aux1, exact s, exact H2, refl,},
  rw h1,
  
  unfold Sum,
  rw sum_ite,
  rw sum_const_zero,
  rw add_zero,

  have h2 : filter (λ (x : ℕ), x ∈ sj) s = sj,
  { exact inf_eq_right.mpr H1,},
  rw h2,

end






lemma id227a (f : ℕ → ℕ → ℝ) (sk : finset ℕ) (sj : finset ℕ) (s : finset ℕ) (h1 : sk ⊆ s) (h2 : sj ⊆ s) :
Sum (λ j, Sum (λ k, f j k * (ite (j ∈ sj ∧ k ∈ sk) 1 0)) s) s =
∑ x in (sj.product sk), f x.fst x.snd :=
begin
  rw ← aux2,
  unfold Sum,
  rw ← sum_product.symm,
  exact h2,
  exact h1,
end




lemma id227b (f : ℕ → ℕ → ℝ) (sk : finset ℕ) (sj : finset ℕ) (s : finset ℕ) :
Sum (λ j, Sum (λ k, f j k * (ite (j ∈ sj ∧ k ∈ sk) 1 0)) s) s = 
Sum (λ k, Sum (λ j, f j k * (ite (j ∈ sj ∧ k ∈ sk) 1 0)) s) s :=
begin
  unfold Sum,
  exact sum_comm,
end






lemma id228 (fa : ℕ → ℝ) (fb : ℕ → ℝ) (sk : finset ℕ) (sj : finset ℕ) :
∑ p in (sj.product sk), fa p.fst * fb p.snd = Sum fa sj * Sum fb sk :=
begin
  unfold Sum,
  rw sum_mul_sum,
end



lemma id229a (f : ℕ → ℕ → ℝ) (sk : finset ℕ) (sj : finset ℕ) :
Sum (λ j, Sum (λ k, f j k) sk) sj = ∑ p in (sj.product sk), f p.fst p.snd :=
begin
  unfold Sum,
  rw ← sum_product.symm,
end




lemma id229b (f : ℕ → ℕ → ℝ) (sk : finset ℕ) (sj : finset ℕ) :
Sum (λ j, Sum (λ k, f j k) sk) sj = Sum (λ k, Sum (λ j, f j k) sj) sk :=
begin
  exact sum_comm,
end




lemma id230 (f : ℕ → ℕ → ℝ) (sk sj a b  : finset ℕ) (sk' sj': ℕ → finset ℕ)
(ht : ∀ j, a = sk' j) (hp : ∀ k, b = sj' k) 
(h : ∀ j k, (ite (j ∈ sj) 1 0) * (ite (k ∈ (a)) 1 0) = (ite (k ∈ sk) 1 0) * (ite (j ∈ (b)) 1 0)) :
Sum (λ j, Sum (λ k, f j k) (a)) sj = Sum (λ k, Sum (λ j, f j k) (b)) sk :=
begin

  have h6 : sj ⊆ (sk ∪ sj ∪ a ∪ b) ∧ sk ⊆ (sk ∪ sj ∪ a ∪ b) ∧ a ⊆ (sk ∪ sj ∪ a ∪ b) ∧ b ⊆ (sk ∪ sj ∪ a ∪ b),
  { split, rw union_assoc, rw union_assoc, rw union_comm, rw union_assoc, 
  apply (subset_union_left sj), split, rw union_assoc, rw union_assoc, 
  apply (subset_union_left sk), split, rw union_assoc, rw union_assoc, rw union_comm,
  rw union_assoc, rw union_comm, rw union_assoc, rw union_assoc, apply (subset_union_left a),
  rw union_comm, apply (subset_union_left b), },


  rw aux2 f a sj,
  apply eq.symm,
  rw id229b,
  rw aux2 f sk b,
  

  have h3 : ∀ x y, ite (y ∈ b ∧ x ∈ sk) 1 0 = ite (y ∈ b) 1 0 * ite (x ∈ sk) 1 0,
  { intros x y, rw ← ite_mul_zero_left, rw one_mul, rw ← ite_and, },
  have h4 : ∀ x y, ite (y ∈ sj ∧ x ∈ a) 1 0 = ite (y ∈ sj) 1 0 * ite (x ∈ a) 1 0,
  { intros x y, rw ← ite_mul_zero_left, rw one_mul, rw ← ite_and, },

  repeat {rw Sum},
  apply sum_congr, refl, intros q i,  
  repeat {rw Sum},
  apply sum_congr, refl, intros w i2, 
  
  apply mul_eq_mul_left_iff.mpr,
  left,

  have h5 : ((ite (q ∈ sj ∧ w ∈ (a)) 1 0)) = 
  ((ite (q ∈ (b) ∧ w ∈ sk) 1 0) ),
  { rw (h3 w q), rw (h4 w q), rw (h q w), rw mul_comm, },

  
  apply eq.symm, 
  exact_mod_cast h5,


  exact h6.right.right.right,
  exact h6.right.left,
  exact h6.left,
  exact h6.right.right.left,
  

end





lemma id231a (j : ℕ) (k : ℕ) (n : ℕ) : 
ite (1 ≤ j ∧ j ≤ n) 1 0 * ite (j ≤ k ∧ k ≤ n) 1 0 = ite (1 ≤ j ∧ j ≤ k ∧ k ≤ n) 1 0 :=
begin

  have h1 : (j ≤ k ∧ k ≤ n) → j ≤ n, { intro g, apply le_trans g.left g.right, },
  have h2 : (1 ≤ j ∧ j ≤ k ∧ k ≤ n) ↔ (1 ≤ j ∧ j ≤ n) ∧ (j ≤ k ∧ k ≤ n),
  { rw iff_def, split, intro i, split, split, exact i.left, apply h1, exact i.right,
  exact i.right, intro i, split, exact i.left.left, exact i.right, },

  rw ← ite_mul_zero_left,
  rw one_mul,
  rw ← ite_and,
  apply eq.symm,
  
  by_cases (1 ≤ j ∧ j ≤ k ∧ k ≤ n),
  { rw if_pos, rw if_pos, rw ← h2, exact h, exact h, },
  rw if_neg,
  rw if_neg,
  rw not_iff_not_of_iff h2.symm,
  exact h,
  exact h,

end





lemma id231b (j : ℕ) (k : ℕ) (n : ℕ) : 
ite (1 ≤ k ∧ k ≤ n) 1 0 * ite (1 ≤ j ∧ j ≤ k) 1 0 = ite (1 ≤ j ∧ j ≤ k ∧ k ≤ n) 1 0 :=
begin

  rw ← ite_mul_zero_left,
  rw one_mul,
  rw ← ite_and,

  have h1 : ((1 ≤ k ∧ k ≤ n) ∧ 1 ≤ j ∧ j ≤ k) ↔ (1 ≤ j ∧ j ≤ k ∧ k ≤ n),
  { rw iff_def, split, intro i, split, exact i.right.left, split, exact i.right.right, 
  exact i.left.right, intro i, split, split, apply le_trans, exact i.left, exact i.right.left, 
  exact i.right.right, split, exact i.left, exact i.right.left, },

  by_cases (1 ≤ j ∧ j ≤ k ∧ k ≤ n),
  { rw if_pos, rw if_pos, rw ← h1, exact h1.mpr h, exact h1.mpr h, },
  rw if_neg,
  rw if_neg,
  exact h,
  rw not_iff_not_of_iff h1,
  exact h,

end





lemma id232a (f : ℕ → ℕ → ℝ) (n : ℕ) (s s2 : finset ℕ) (hs : s = range (n+1) \ (range 1))
(h : ∀ j , s2 = (range (n+1) \ range j)) ( sp = (filter (λ (p:ℕ × ℕ), (p.fst ≤ p.snd)) (s.product s))) :
Sum (λ j, Sum (λ k, (f j k)) s2) s =
∑ p in sp, f p.fst p.snd :=
begin

  rw H,
  rw sum_filter,
  rw aux2,
  rw sum_product,
  rw Sum,
  apply sum_congr,
  refl, intros x i,
  apply sum_congr,
  refl, intros y i2, simp,
  rw hs, rw (h x), simp,

  have h1a : ∀ (x:ℕ), ¬ x<0, { exact nat.not_lt_zero, },

  have h1 : ∀ (x : ℕ), ¬ x = 0 → 1 ≤ x, {intros x i2, apply le_of_not_lt, rw hs at i,
  simp at i, rw not_lt, apply nat.succ_le_of_lt, rw ← gt_iff_lt, exact pos_iff_ne_zero.mpr i2, },

  by_cases (x ≤ y),
  { rw if_pos, rw if_pos, exact h,  rw hs at i, simp at i, split, split, exact i.left, 
  exact (h1 x i.right), rw hs at i2, simp at i2, split, exact i2.left, exact h, },
  rw if_neg, rw if_neg, exact h, rw not_and, intro i3, rw not_and, intro i4, exact h,

  simp,
  rw hs, rw h, 
  exact subset.refl (range (n + 1) \ range 1),

end




lemma id232b (f : ℕ → ℕ → ℝ) (n : ℕ) (s s1 s2 : finset ℕ) (hs1 : ∀ j, s1 = (range (n+1)\range j))
(hs2 : ∀ k, s2 = (range (k+1)\(range 1))) (hs : s = (range (n+1) \ (range 1))) :
Sum (λ j, Sum (λ k, f j k) s1) s =
Sum (λ k, Sum (λ j, f j k) s2) s :=
begin

  rw id230,
  intros j, exact (hs1 j), intro k, exact (hs2 k),

  intros j k,

  have ha : ((j < n + 1 ∧ 1 ≤ j) ∧ k < n + 1 ∧ j ≤ k) ↔ ((1 ≤ j ∧ j ≤ n) ∧ j ≤ k ∧ k ≤ n),
  { split, intro i, split, split, exact i.left.right, apply nat.le_of_lt_succ,
  exact i.left.left, split, exact i.right.right, apply nat.le_of_lt_succ, exact i.right.left,
  intro i, split, split, apply nat.lt_succ_of_le, exact i.left.right, exact i.left.left, split,
  apply nat.lt_succ_of_le, exact i.right.right, exact i.right.left, },

  have hb : ((k < n + 1 ∧ 1 ≤ k) ∧ j < k + 1 ∧ 1 ≤ j) ↔ ((1 ≤ k ∧ k ≤ n) ∧ 1 ≤ j ∧ j ≤ k),
  { split, intro i, split, split, exact i.left.right, apply nat.le_of_lt_succ, exact i.left.left,
  split, exact i.right.right, apply nat.le_of_lt_succ, exact i.right.left, intro i, split, split,
  apply nat.lt_succ_of_le, exact i.left.right, exact i.left.left, split, apply nat.lt_succ_of_le,
  exact i.right.right, exact i.right.left, },


  have h1 : ite (j ∈ range (n + 1) \ range 1) 1 0 * ite (k ∈ range (n + 1) \ range j) 1 0 =
  ite (1 ≤ j ∧ j ≤ k ∧ k ≤ n) 1 0,
  { rw ← id231a, norm_num, rw ← ite_and, rw ← ite_and, by_cases ((1 ≤ j ∧ j ≤ n) ∧ j ≤ k ∧ k ≤ n),
  { rw if_pos, rw if_pos, exact h, rw ha, exact h, }, rw if_neg, rw if_neg, exact h, 
  rw (not_iff_not.mpr ha), exact h, },
  rw hs, rw hs1, rw hs2,
  rw h1,

  have h2 : ite (k ∈ range (n + 1) \ range 1) 1 0 * ite (j ∈ range (k + 1) \ range 1) 1 0 =
  ite (1 ≤ j ∧ j ≤ k ∧ k ≤ n) 1 0,
  { rw ← id231b, norm_num,  rw ← ite_and, rw ← ite_and, by_cases ((1 ≤ k ∧ k ≤ n) ∧ 1 ≤ j ∧ j ≤ k),
  { rw if_pos, rw if_pos,exact h, rw hb, exact h, }, rw if_neg, rw if_neg, exact h, 
  rw (not_iff_not.mpr hb), exact h, },
  rw h2,

end






lemma id233 (f : ℕ → ℝ) (n : ℕ) (s : finset ℕ) (hs : s = range (n+1) \ (range 1))
 ( sp = (filter (λ (p:ℕ × ℕ), (p.fst ≤ p.snd)) (s.product s))):
∑ p in sp, f p.fst * f p.snd = (1/2) * ((Sum f s)^2 + Sum (f^2) s) := 
begin

  have h1 : ∑ (p : ℕ × ℕ) in filter (λ (p : ℕ × ℕ), p.fst ≤ p.snd) (s.product s), 
  f p.fst * f p.snd = ∑ (p : ℕ × ℕ) in filter (λ (p : ℕ × ℕ), p.fst ≥ p.snd)
  (s.product s), f p.fst * f p.snd,
  { simp, rw sum_filter, rw sum_filter, rw sum_product, rw sum_product, simp, rw sum_comm,
  apply congr, refl, apply funext, intro x, apply congr, refl, apply funext, intro y, rw mul_comm, },

  have h2 : ∑ (p : ℕ × ℕ) in filter (λ (p : ℕ × ℕ), p.fst ≤ p.snd) (s.product s),
  f p.fst * f p.snd + ∑ (p : ℕ × ℕ) in filter (λ (p : ℕ × ℕ), p.fst ≤ p.snd) (s.product s),
  f p.fst * f p.snd = ∑ (p : ℕ × ℕ) in filter (λ (p : ℕ × ℕ), p.fst ≤ p.snd) (s.product s), 
  f p.fst * f p.snd + ∑ (p : ℕ × ℕ) in filter (λ (p : ℕ × ℕ), p.fst ≥ p.snd)
  (s.product s), f p.fst * f p.snd,
  { rw h1, },

  have h3 : filter (λ (p : ℕ × ℕ), p.fst ≤ p.snd) (s.product s) =
  filter (λ (p : ℕ × ℕ), p.fst <  p.snd) (s.product s) ∪ 
  filter (λ (p : ℕ × ℕ), p.fst = p.snd) (s.product s),
  { rw filter_union_right, apply filter_congr, intros x i, exact le_iff_lt_or_eq, }, 

  have h4 : filter (λ (p : ℕ × ℕ), p.fst ≥ p.snd) (s.product s) =
  filter (λ (p : ℕ × ℕ), p.fst > p.snd) (s.product s) ∪ 
  filter (λ (p : ℕ × ℕ), p.fst = p.snd) (s.product s),
  { rw filter_union_right, apply filter_congr, intros x i, rw ge_iff_le, rw gt_iff_lt,
  rw le_iff_lt_or_eq, split, intro i2, apply (or.elim i2), intro i3, left, exact i3, 
  intro i3, right, exact i3.symm, intro i2, apply (or.elim i2), intro i3, left, exact i3,
  intro i3, right, exact i3.symm, }, 

  have h5 : ∀ (a:ℕ × ℕ) , (a.fst < a.snd ∨ a.fst = a.snd) ∨ a.fst > a.snd ↔ true, 
  { intros a, rw ← le_iff_lt_or_eq, simp, exact le_or_lt a.fst a.snd, },

  have h6 : filter (λ (a : ℕ × ℕ), (a.fst < a.snd ∨ a.fst = a.snd) 
  ∨ a.fst > a.snd) (s.product s) = filter (λ (a : ℕ × ℕ), true) (s.product s),
  { apply filter_congr, intros x i, exact (h5 x), },
  
  have h7 : 2 * ∑ p in sp, f p.fst * f p.snd = ∑ p in s.product s, f p.fst * f p.snd
  + ∑ p in (filter (λ (p:ℕ × ℕ), (p.fst = p.snd)) (s.product s)), f p.fst * f p.snd,
  
  {  rw H, rw two_mul, rw h2, rw h3, rw h4, rw sum_union, rw sum_union, rw ← add_assoc, 
  rw add_right_cancel_iff, rw ← sum_union, rw ← sum_union, rw ← filter_or, rw ← filter_or, 
  rw h6, rw filter_true, simp, split, rw disjoint_filter, intros x i i2, exact asymm i2,
  rw disjoint_filter, intros x i i2, norm_num, exact (eq.symm i2).ge, repeat {rw disjoint_filter,
  intros x i i2, apply ne_of_lt, exact i2,}, rw disjoint_filter, intros x i i2, apply ne_of_gt,
  exact i2, },

  rw mul_comm,
  rw ← div_eq_iff,
  rw div_div_eq_mul_div,
  rw div_one,
  rw mul_comm,
  rw h7,
  rw id228,
  rw ← pow_two,
  rw add_left_cancel_iff,

  have h8 : ∑ (p : ℕ × ℕ) in filter (λ (p : ℕ × ℕ), p.fst = p.snd)
  (s.product s), f p.fst * f p.snd = ∑ (p : ℕ × ℕ) in filter (λ (p : ℕ × ℕ), p.fst = p.snd)
  (s.product s), (f p.fst)^2,
  { rw sum_filter, rw sum_filter, apply congr, refl, apply funext, intro x, rw pow_two,
   by_cases (x.fst = x.snd), { rw if_pos, rw if_pos, rw ← h, exact h, exact h, },
   rw if_neg, rw if_neg, exact h, exact h, },

  rw h8,
  unfold Sum,
  rw sum_filter,
  rw ← sum_product.symm,
  simp,
  exact sum_extend_by_zero s (λ (i : ℕ), f i ^ 2),
  norm_num,
end--check this





lemma id234 (fa fb : ℕ → ℝ) (n : ℕ) (s : finset ℕ) (sp : finset ℕ × ℕ) 
(hs : s = range (n+1) \ {0}) (sp = (filter (λ (p:ℕ × ℕ), (p.fst < p.snd)) (s.product s))) :
Sum fa s * Sum fb s = n * Sum (fa * fb) s - 
∑ p in sp, (fa p.snd - fa p.fst) * ((fb p.snd) - (fb p.fst)) :=
begin
  have h1 : ∑ p in sp, (fa p.snd - fa p.fst) * ((fb p.snd) - (fb p.fst)) =
  ∑ p in sp, (fa p.fst - fa p.snd) * ((fb p.fst) - (fb p.snd)),
  { apply congr, refl, apply funext, intro x, ring, },

  have h2 : ∑ p in sp, (fa p.snd - fa p.fst) * ((fb p.snd) - (fb p.fst)) =
  ∑ p in (filter (λ (p:ℕ × ℕ), (p.fst > p.snd)) (s.product s)),
  (fa p.snd - fa p.fst) * ((fb p.snd) - (fb p.fst)),
  { rw h1, rw H, simp, rw sum_filter, rw sum_product, simp, rw sum_comm, rw sum_filter, 
  rw sum_product, },

  have ha : 2 * ∑ p in sp, (fa p.snd - fa p.fst) * ((fb p.snd) - (fb p.fst)) =
  ∑ p in sp, (fa p.snd - fa p.fst) * ((fb p.snd) - (fb p.fst)) +
  ∑ p in (filter (λ (p:ℕ × ℕ), (p.fst > p.snd)) (s.product s)),
  (fa p.snd - fa p.fst) * ((fb p.snd) - (fb p.fst)),
  {rw two_mul, rw ← h2,},

  have h3 :  ∑ p in (filter (λ (p:ℕ × ℕ), (p.fst = p.snd)) (s.product s)),
  (fa p.snd - fa p.fst) * ((fb p.snd) - (fb p.fst)) = 0,
  { rw sum_eq_zero, intros x i, rw mul_eq_zero, left, rw sub_eq_zero, apply congr, refl, 
  rw mem_filter at i, apply eq.symm, exact i.right,},

  have hv : s.product s = filter (λ (a : ℕ × ℕ), true) (s.product s),
  { simp, },

  have ho : ∀ (a b : ℕ), a < b ∨ a = b ∨ a > b, {exact trichotomous, },
  

  have h4: 2 * ∑ p in sp, (fa p.snd - fa p.fst) * ((fb p.snd) - (fb p.fst)) =
  ∑ p in s.product s, (fa p.snd - fa p.fst) * ((fb p.snd) - (fb p.fst)) -
  ∑ p in (filter (λ (p:ℕ × ℕ), (p.fst = p.snd)) (s.product s)),
  (fa p.snd - fa p.fst) * ((fb p.snd) - (fb p.fst)),
  { rw ha, apply eq.symm, rw sub_eq_iff_eq_add', rw ← sum_union, rw H, rw ← sum_union,
  rw ← filter_or, rw ← filter_or, apply congr, apply congr, refl, rw hv, rw filter_filter,
  apply filter_congr, intros x i, simp, rw ← gt_iff_lt, exact or.left_comm.mp (ho x.fst x.snd),
  refl, rw ← filter_or, rw disjoint_filter, intros x i i2 i3, apply or.elim i3,
  intro i4, linarith, intro i4, linarith, rw H, rw disjoint_filter, intros x i i2 i3,
  linarith, },

  rw h3 at h4,
  rw sub_zero at h4,

  have h6 : ∑ p in s.product s, fa p.fst * fb p.snd =
  ∑ p in s.product s, fa p.snd * fb p.fst,
  { rw sum_product, rw sum_comm, rw sum_product, },

  have h7 : ∑ p in s.product s, fa p.fst * fb p.fst =
   ∑ p in s.product s, fa p.snd * fb p.snd,
   { rw sum_product, rw sum_comm, rw sum_product, },

  
  have h5 : ∑ p in s.product s, (fa p.snd - fa p.fst) * ((fb p.snd) - (fb p.fst)) =
  2*n * Sum (fa * fb) s - 2 * Sum fa s * Sum fb s, 
  {calc
  ∑ p in s.product s, (fa p.snd - fa p.fst) * ((fb p.snd) - (fb p.fst)) =
  ∑ p in s.product s, fa p.fst * fb p.fst - ∑ p in s.product s, fa p.fst * fb p.snd -
  ∑ p in s.product s, fa p.snd * fb p.fst + ∑ p in s.product s, fa p.snd * fb p.snd :
  by { rw ← sum_sub_distrib, rw ← sum_sub_distrib, rw ← sum_add_distrib, apply congr, refl,
  apply funext, intro x, ring, }
  ...                 = 2 * ∑ p in s.product s, fa p.snd * fb p.snd - 
  2 * ∑ p in s.product s, fa p.fst * fb p.snd :
  by {rw h6, rw sub_sub, rw ← two_mul, rw h7, ring, }
  ...                 = 2 * ∑ p in s.product s, fa p.snd * fb p.snd - 2 * Sum fa s * Sum fb s :
  by {simp, rw mul_assoc, rw id228, }
  ...                 = 2*n * Sum (fa * fb) s - 2 * Sum fa s * Sum fb s :
  by { rw mul_assoc, rw mul_assoc, rw ← mul_sub, rw ← mul_sub, simp, rw sum_product,
  rw Sum, simp, left, rw hs, rw card_sdiff, norm_num, norm_num, },
  },

  rw ← h4 at h5,
  repeat {rw mul_assoc at h5},
  rw ← mul_sub at h5,
  rw mul_eq_mul_left_iff at h5,
  apply or.elim h5,
  { intro i, apply eq.symm, rw sub_eq_iff_eq_add', rw ← sub_eq_iff_eq_add, exact i.symm, },
  norm_num,
  
end







lemma id235 (fa : ℕ → ℝ) (fp : ℕ → ℕ) (sj sk : finset ℕ) (hp : ∀ j ∈ sj, fp j ∈ sk) :
Sum (λ j, fa (fp j)) sj = Sum (λ k, fa k * card (filter (λ j, fp j = k) sj)) sk :=
begin
  have h1 : ∀ k, Sum (λ j, ite (fp j = k) 1 0 ) sj = card (filter (λ j, fp j = k) sj),
  { intro k, rw Sum, rw sum_ite, rw add_comm, rw sum_eq_zero, rw zero_add, 
  rw sum_const, simp, intros x i, refl, },

  have h2 : Sum (λ k, fa k * card (filter (λ j, fp j = k) sj)) sk =
  Sum (λ k, fa k * Sum (λ j, ite (fp j = k) 1 0 ) sj ) sk,
  { apply congr, apply congr, refl, apply funext, intro x, simp, left, exact (h1 x).symm,
  refl, },

  rw h2,

  have h3 : Sum (λ k, fa k * Sum (λ j, ite (fp j = k) 1 0 ) sj ) sk =
  Sum (λ k, Sum (λ j, fa k * ite (fp j = k) 1 0 ) sj ) sk,
  { apply congr, apply congr, refl, apply funext, intro x, rw SumDistr, refl, },

  rw h3,
  rw id229b,

  have tst : ∀ x, (λ (j : ℕ), fa (fp j)) x = fa (fp x), {exact congr_fun rfl,},
  have tst2 : ∀ x, (λ (k : ℕ), Sum (λ (j : ℕ), fa j * ite (fp k = j) 1 0) sk) x =
   Sum (λ (j : ℕ), fa j * ite (fp x = j) 1 0) sk, { exact congr_fun rfl,},

  apply sum_congr, refl, intros x hj, rw tst, rw tst2,  rw Sum,
  rw sum_mul_boole, 

  rw if_pos, apply hp, exact hj, 

end




 

lemma id236 (n : ℕ) :
Sum (λ k, Sum (λ j, 1/j) (range (k+1)\{0})) (range n) = 
n * Sum (λ j, 1/j) (range (n+1)\{0}) - n :=
begin

  induction n with n ih,
  { simp, rw Sum, rw sum_empty,  },
  change n.succ with (n+1),
  have h1 : range (n + 1) = range n ∪ {n}, { rw range_add_one, rw union_comm, refl,},
  rw h1,
  rw Sum,
  rw sum_union,
  rw ← Sum,
  rw ih,
  rw sum_singleton,
  have h2 : range (n + 1 + 1) = range (n+1) ∪ {n+1}, 
  { rw range_add_one, rw union_comm,  refl,},
  have h3 : {n+1} \ {0} = {n+1}, { rw sdiff_singleton_eq_erase, refl, },
  rw h2,
  rw Sum, rw Sum,
  rw union_sdiff_distrib,
  rw sum_union,
  rw h3,
  rw sum_singleton,
  rw add_comm,
  rw add_sub,
  have h4 : ∑ (k : ℕ) in range (n + 1) \ {0}, 1 / ↑k +
   ↑n * ∑ (k : ℕ) in range (n + 1) \ {0}, 1 / ↑k = (n + 1) * 
   ∑ (k : ℕ) in range (n + 1) \ {0}, 1 / ↑k,
  { rw add_mul, rw one_mul, rw add_comm, simp, },
  rw mul_comm ↑(n + 1),
  rw add_mul,
  rw div_mul_cancel,
  simp,
  rw mul_comm (∑ (x : ℕ) in range (n + 1) \ {0}, (↑x)⁻¹),
  ring,
  exact (nat.add n 0).cast_add_one_ne_zero,
  rw disjoint_iff_inter_eq_empty,
  rw inter_sdiff,
  rw sdiff_singleton_eq_erase,
  simp,
  simp,

end