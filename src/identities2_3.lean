import algebra.big_operators
import data.real.basic

open finset
open_locale big_operators


def Sum (f : ℕ -> ℝ) (s : finset ℕ) :=
∑ k in s, f k



lemma SumDistr (f : ℕ -> ℝ) (s : finset ℕ) (c : ℝ) : Sum (λ k, c * (f k)) s  = c * Sum f s :=
begin
  unfold Sum,
  rw mul_sum,
end 



lemma SumAssoc (a : ℕ -> ℝ) (b : ℕ -> ℝ) (s : finset ℕ) : Sum (λ k, a k + b k) s = Sum a s + Sum b s :=
begin
  exact sum_add_distrib,
end




lemma SumComm (f : ℕ -> ℝ) (l1 : list ℕ) (p : ℕ → ℕ) (h : l1 ~ (l1.map p) ) :
Sum f l1.to_finset = Sum f (l1.map p).to_finset := 
begin
  have h1 : l1.to_finset = (l1.map p).to_finset,
  { exact list.to_finset_eq_of_perm l1 (l1.map p) h,  },
  rw h1,
end





lemma GaussSum (n : ℕ) : 2 * Sum (λ k, k) (finset.range (n+1)) = n * (n + 1) :=
begin 
unfold Sum,
induction n with n IH,
{  simp, },
rw sum_range_succ,
rw mul_add,
rw IH,
norm_num,
ring,
end



lemma AuxRev (a : ℝ) (b : ℝ) (n : ℕ) (s = finset.range (n+1)) : 
Sum (λ k, a + b*(n-k)) s = Sum (λ k, a + b*k) s :=
begin
  unfold Sum,
  apply eq_of_sub_eq_zero,
  rw ← sum_sub_distrib,
  simp,
  rw ← mul_sum,
  rw ← mul_sum,
  rw ← mul_sub,
  rw sum_sub_distrib,
  rw sub_sub,
  rw ← two_mul,
  rw mul_sum,
  rw ← sum_sub_distrib,
  simp,
  right,
  rw sub_eq_zero,
  rw H,
  rw card_range,
  rw ← mul_sum,
  rw eq_comm,
  rw mul_comm ↑(n + 1) ↑n,
  rw ← Sum,
  rw GaussSum n,
  refl,
end





lemma SumArithProg (a : ℝ) (b : ℝ) (n : ℕ) (s = range (n+1)) : 
Sum (λ k, a + b*k) s = (a + (1/2)*b*n) * (n + 1) :=
begin
  have h1 : Sum (λ k, a + b*k) s = Sum (λ k, a + b*(n-k)) s,
  { rw (AuxRev a b n s H), },

  have h2 : Sum (λ k, a + b*(n-k)) s = Sum (λ k, a + b*n - b*k) s,
  { ring_nf, },

  have h3 : Sum (λ k, a + b*k) s + Sum (λ k, a + b*n - b*k) s = Sum (λ k, 2*a + b*n) s,
  { rw ← SumAssoc, simp, rw ← add_assoc, rw two_mul, },

  have h4 : Sum (λ k, 1) s = n + 1,
  { unfold Sum, rw H, rw sum_const, rw card_range, simp, },

  have h5 : Sum (λ k, 2*a + b*n) s = (2*a + b*n) * (n + 1),
  { rw ← mul_one (2*a + b*n), rw SumDistr, rw mul_one, rw h4, },

  rw ← h2 at h3,
  rw ← h1 at h3,
  rw ← two_mul at h3,
  rw h5 at h3,
  rw mul_comm at h3,

  have h6 : Sum (λ k, a + b*k) s = ((2*a + b*n) * (n + 1)) / 2,
  { apply eq_div_of_mul_eq, norm_num, exact h3,},
  
  rw h6,
  ring,
end




lemma id220 (f : ℕ -> ℝ) (s1 : finset ℕ ) (s2 : finset ℕ ) :
Sum f s1 + Sum f s2 = Sum f (s1 ∩ s2) + Sum f (s1 ∪ s2) :=
begin
  rw add_comm (Sum f (s1 ∩ s2)),
  unfold Sum,
  rw sum_union_inter,
end


lemma id223 (f : ℕ -> ℝ) (n : ℕ) : Sum f (range (n+1)) = f 0 + Sum f ( (range (n+1)) \ (range 1)) :=
begin
  unfold Sum,
  rw add_comm (f 0),
  rw ← (sum_range_one f),
  rw sum_sdiff,
  norm_num,
end




lemma id224 (f : ℕ -> ℝ) (n : ℕ) : 
Sum f (range (n+1)) + f (n+1) = f 0 + Sum (λ k, f (k+1)) (range (n+1)) :=
begin
  unfold Sum,
  rw add_comm (f 0),
  rw ← sum_range_succ',
  rw ← sum_range_succ,
end




lemma id225 (a : ℕ) (x : ℝ) (n : ℕ) (s = range (n+1)) (h : x ≠ 1) :
 Sum (λ k, a * x^k) s = (a - a * x^(n+1)) / (1 - x) :=
begin
  have h1 : Sum (λ k, a * x^k) s + (a * x^(n+1)) = 
  (a * x^0) + Sum (λ k, a * x^(k+1)) s,
  {rw H, rw id224, },
  
  have h2 :  Sum (λ k, a * x^(k+1)) s = x * Sum (λ k, a * x^k) s,
  { rw ← SumDistr, unfold Sum, apply congr, refl, apply funext, intro k, rw pow_add, ring, },

  rw h2 at h1,
  rw [pow_zero, mul_one, ← sub_eq_zero, add_comm, ← sub_sub] at h1,
  
  have h3 : Sum (λ (k : ℕ), ↑a * x ^ k) s - x * Sum (λ (k : ℕ), ↑a * x ^ k) s =
   0 - ↑a * x ^ (n + 1) + ↑a,
  { rw ← sub_eq_zero, rw zero_sub, rw ← h1, ring, },

  apply eq_div_of_mul_eq,
  { rw sub_ne_zero, rw ne_comm, exact h, },
  rw [mul_comm, sub_mul, one_mul],
  rw h3,
  ring,
end



lemma id226 (x : ℝ) (n : ℕ) (h : x ≠ 1) (s = range (n + 1)) (f : ℕ → ℝ) (H2 : f = (λ b, b * x^b)) : 
Sum (λ k, k * x^k) s = (x - (n + 1) * x^(n+1) + n * x^(n+2)) / (1 - x)^2 :=
begin
  have h1 : Sum f (range (n + 1)) + f (n + 1) =
  f 0 + Sum (λ k, f (k+1)) (range (n + 1)),
  { rw id224, },

  have h2 : Sum (λ k, f (k+1)) s = Sum (λ k, k * x^(k+1)) s + Sum (λ k, ↑1 * x^(k+1)) s,
  { rw H2, rw ← SumAssoc, apply congr, apply congr, refl, apply funext, intro k, simp, ring, refl, },

  have h3 : Sum (λ k, k * x^(k+1)) s = x * Sum (λ k, k * x^k) s,
  { rw ← SumDistr, unfold Sum, apply congr, refl, apply funext, intro k, rw pow_add, ring, },

  have haux : Sum (λ k, ↑1 * x^(k+1)) s = x * Sum (λ k, ↑1 * x^k) s,
  { rw ← SumDistr, unfold Sum, apply congr, refl, apply funext, intro k, rw pow_add, ring, },
  have h4 : Sum (λ k, ↑1 * x^(k+1)) s = (x - 1 * x^(n+1+1)) / (1 - x),
  { rw haux, rw pow_add, rw pow_one, rw id225, rw ← mul_div_assoc, rw mul_sub, norm_num, rw mul_comm, exact H, exact h, },

  have h5 : Sum (λ k, k * x^k) s + f (n+1) =
  x * Sum (λ k, k * x^k) s + (x - 1 * x^(n+2)) / (1 - x),
  { rw H, rw ← H2, rw h1, norm_num, rw ← H, rw h2, rw h3, rw h4, rw H2, norm_num, },

  have h6 : Sum (λ k, k * x^k) s - x * Sum (λ k, k * x^k) s = 
  (x - 1 * x^(n+2)) / (1 - x) - ((n + 1) * x^(n+1)),
  { apply eq_sub_of_add_eq, rw add_comm, rw add_sub, apply eq.symm, 
  apply eq_sub_of_add_eq, rw add_comm, rw ← h5, rw add_comm, rw H2, simp, },

  have h7 : Sum f s - x * Sum f s = (1 - x) * Sum f s,
  { ring,},
  rw ← H2 at h6,
  rw h7 at h6,
  have h8 : (1 - x) ≠ 0, { rw sub_ne_zero, rw ne_comm, exact h, },
  rw mul_comm at h6,
  rw ← (div_eq_iff_mul_eq h8) at h6,
  rw ← H2,

  calc
  Sum f s =
  ((x - 1 * x ^ (n + 2)) / (1 - x) - (↑n + 1) * x ^ (n + 1)) / (1 - x) :
  by { rw h6, }
  ...                       = (x - x ^ (n + 2)) / (1 - x)^2 - (↑n + 1) * x ^ (n + 1) / (1 - x) :
  by { rw sub_div, rw pow_two, rw div_div_eq_div_mul, rw one_mul, } 
  ...                       = (x - x ^ (n + 2)) / (1 - x)^2 - (((↑n + 1) * x ^ (n + 1)) * (1-x)) / ((1 - x) * (1 - x)) :
  by { simp, rw (mul_div_mul_right ((↑n + 1) * x ^ (n + 1))), exact h8, }
  ...                       = ((x - x ^ (n + 2)) -  ((↑n + 1) * x ^ (n + 1)) * (1-x)) / (1 - x)^2 :
  by { rw ← pow_two, rw div_sub_div_same, }
  ...                       = ((x - x ^ (n + 2)) - ((↑n + 1) * x ^ (n + 1)) + ((↑n + 1) * x ^ (n+1+1)) ) / (1 - x)^2 :
  by { rw mul_sub, rw mul_one, rw mul_assoc, rw ← sub_add, rw pow_add x (n+1), rw pow_one, }
  ...                       = (x - (↑n + 1) * x ^ (n + 1) + (↑n + 1) * x ^ (n+2) - x ^ (n + 2) ) / (1 - x)^2 :
  by ring
  ...                       = (x - (n + 1) * x^(n+1) + n * x^(n+2)) / (1 - x)^2 :
  by ring,
end



lemma id221 (f : ℕ → ℝ) (s : finset ℕ) (snat : finset ℕ) (s ⊆ snat) :
 Sum f s = Sum (λ k, f k * (ite (k ∈ s) 1 0)) snat :=
begin
  have h : Sum (λ k, ((ite (k ∈ s) (f k) 0))) snat = Sum (λ k, (f k * (ite (k ∈ s) 1 0))) snat,
  { apply congr, apply congr, refl, apply funext, intro x, exact (mul_boole (x ∈ s) (f x)).symm, refl, },
  rw ← h,
  unfold Sum,
  rw sum_ite,
  rw sum_const_zero,
  rw add_zero,
  have h : filter (λ (x : ℕ), x ∈ s) snat = s,
  { exact inf_eq_right.mpr H, },
  rw h,
end




lemma id222 (s1 : finset ℕ) (s2 : finset ℕ) (k : ℕ) :
 (ite (k ∈ s1) 1 0) + (ite (k ∈ s2) 1 0) = (ite (k ∈ s1 ∩ s2) 1 0) + (ite (k ∈ s1 ∪ s2) 1 0) :=
begin
  simp,
  by_cases h1 : (k ∈ s1),
  { by_cases h2 : (k ∈ s2),
    { rw (if_pos h1), rw (if_pos h2), rw (if_pos (and.intro h1 h2)), rw (if_pos (or.inl h1)), },
    rw (if_pos h1), rw (if_neg h2), have hb : (k ∈ s1 ∧ k ∈ s2) = false,
   { apply and_eq_of_eq_false_right, simp, exact h2, },
    rw (if_neg (not_of_eq_false hb)), rw (if_pos (or.inl h1)), },
  by_cases h2 : (k ∈ s2),
    { rw (if_neg h1), rw (if_pos h2), have hb : (k ∈ s1 ∧ k ∈ s2) = false,
   { apply and_eq_of_eq_false_left, simp, exact h1, },
    rw (if_neg (not_of_eq_false hb)), rw (if_pos (or.inr h2)), },
  rw (if_neg h1), rw (if_neg h2),  have hb : (k ∈ s1 ∧ k ∈ s2) = false,
   { apply and_eq_of_eq_false_right, simp, exact h2, },
    rw (if_neg (not_of_eq_false hb)), have ho : (k ∈ s1 ∨ k ∈ s2) = false,
  { simp, intro notor, apply or.elim notor h1 h2, }, rw (if_neg (not_of_eq_false ho)),
end







