import algebra.ring
import data.nat.basic
import data.real.basic
import tactic

--variables {ℕ : Type*} [ring ℕ]

lemma test_mul_sub (a : ℝ) (b : ℝ) (c : ℝ) : a * (b - c) = a * b - a * c :=
begin
  rw mul_sub,
end

#check mul_sub


/-lemma test_dvd (a : ℕ)(n : ℕ)(b : ℕ) (h : a = n): b * a = b * n :=
begin
  simp,
 -/

#check mul_left_cancel

--(range (n + 1)).sum (λ k, f k)

 /-def SumRec  (s : ℕ → ℕ) (n : ℕ) : ℕ → (ℕ → ℕ) → ℕ
| 0 s     := 3
| (n+1) s  := n + s n 

#reduce (  SumRec (λ k, k*2) 0)-/ 





/-
def TermsInList : ℕ → (ℕ -> ℕ) → list ℕ
| 0   f    := []
| (n+1) f  := ((f (n+1)) :: (TermsInList n f) )


def SumListofLists : list (list ℕ) → list ℕ
| []       := []
| (h :: t) := (list.sum h) :: SumListofLists t


def AreListMemEq : list ℕ → bool 
| []      := true
| (h::t)  := ((t = []) ∨ (h = t.head)) && (AreListMemEq t)
-/

/-def ListToSum (l : list ℕ) (n : ℕ)  (h : n < (list.lenght l))  :=
∑ k in range (n+1), l.nth_le k (k< list.length l)-/

/-lemma Test1 (n : ℕ) (f : ℕ -> ℕ) : S1 f n = (TermsInList n f).sum :=
begin 
  unfold S1,
  induction n with n ih,
  {norm_num, sorry},
  sorry
end-/


/-lemma SumComm2 (n : ℕ) (f : ℕ -> ℕ) (fperm : ℕ -> ℕ) (h : (TermsInList n f) ~ (TermsInList n fperm)) :
(TermsInList n f).sum = (TermsInList n fperm).sum := 
begin
  exact list.perm.sum_eq h,
end-/




/-lemma SumComm3 (f : ℕ -> ℝ) (r1 : finset ℕ) (r2 : finset ℕ) (h : has_mem r2 (perms_of_finset r1)) :
S1p f r1 = S1p f r2 := 
begin
  unfold S1p,
  have h1 : (r1 = r2), 
  ext1,
  split,
  assume h2,
  suggest,
   --{refine val_inj.mp _, suggest,},
  

end-/


--lemma h  : (3 < (list.permutations (TermsInList 3 f)).length ) := sorry

/-lemma SumComm (n : ℕ) (f : ℕ → ℕ) (h : n < (list.permutations (TermsInList n f)).length) 
(h2 : (n-1) < (list.permutations (TermsInList n f)).length) : 
list.sum (( (TermsInList n f).permutations ).nth_le n h) = 
list.sum ((list.permutations (TermsInList n f)).nth_le (n-1) (h2)) :=
begin
  induction n with n ih,
  sorry
end-/



/-lemma id224 (f : ℕ -> ℝ) (n : ℕ) :
Sum f (range (n+1)) + f (n+1) = f 0 + Sum f (range (n+2) \ (range 1)) :=
begin
  rw ← id223,
  unfold Sum,
  rw ← sum_range_succ,
end-/




open finset




#reduce perms_of_finset (range 2)


def l := [3,7,9]
def m := [7,9,3]

def u := range 3
def y := u + {52}

#reduce range 7
#reduce m.to_finset
#check list.to_finset_eq_of_perm
#reduce list.sum [4,2]
#check sum_hom
#reduce perms_of_list [7,9]
#reduce perms_of_finset (range 1)


/-
#check sum_hom
#reduce S1 f 3
#reduce TermsInList 3 f
#reduce  AreListMemEq [3,3,3,3,3,3]
#reduce list.head [3,3,5] = (list.tail [3,3,5]).head 
#reduce (3 = 3 : bool) && (4 = 4 :bool)
#reduce (list  (range 2))
#reduce  list.permutations (list.range' 1 3)
#reduce list.range' 1 3
#reduce list.sum [1,2,3,4]
--#reduce SumListofLists (list.permutations (TermsInList 3 f))
#reduce  (l.nth_le (1 )) (((1 ≤  l.length) :bool)) 
#check succ_order.le_of_succ_le_succ
#reduce list.nth_le l 1 (h → 6)
#check (3 :: l).nth_le 0 (h l) = 3
-/



/-rw ← Sum,
  rw ← Sum,
  rw H,
  rw GaussSum n,
  unfold Sum,
  rw sum_const,
  rw card_range,
  library_search,
  simp,-/



  /-lemma id219a (f : ℕ -> ℝ) (s : finset ℕ) : 
Sum f (filter (λ (k:ℕ) , k % 2 = 0)  s) = Sum (λ k, f (2*k)) (filter (λ (k:ℕ) , (2*k ∈ s) && ((2*k) % 2 = 0))  s) :=
begin
  unfold Sum,
  suggest,
  sorry,
end


lemma id219b (f : ℕ -> ℝ) (s : finset ℕ) : 
Sum (λ k, f (2*k)) (filter (λ (k:ℕ) , (2*k ∈ s) && ((2*k) % 2 = 0))  s) = 
Sum (λ k, f (2*k)) (filter (λ (k:ℕ) , 2*k ∈ s)  s) :=
begin
  unfold Sum,
  --apply eq_of_veq,
  have h: filter (λ (k:ℕ) , (2*k ∈ s) && ((2*k) % 2 = 0)) s = filter (λ (k:ℕ) , (2*k) ∈ s)  s,
  { rw ext_iff, sorry},
  sorry,
end-/



lemma id230 (f : ℕ → ℕ → ℝ) (sk sj s: finset ℕ) (sk' sj': ℕ → finset ℕ) (H1 : sj ⊆ s) ( H2 : sk ⊆ s)
--(j k : ℕ) --(sk' = d1 j) (sj' = d2 k) 
--(sk' = (λ x, d1 x)) (sj' = (λ x, d2 x)) --(ht : ∀ j, (sk' j) : finset ℕ)
(h : ∀ j k, (ite (j ∈ sj) 1 0) * (ite (k ∈ (sk' j)) 1 0) = (ite (k ∈ sk) 1 0) * (ite (j ∈ (sj' k)) 1 0)) :
Sum (λ j, Sum (λ k, f j k) (sk' j)) sj = Sum (λ k, Sum (λ j, f j k) (sj' k)) sk :=
begin
  
  --rw id229b,
  have h1 : Sum (λ j, Sum (λ k, f j k) ((sk' j):(finset ℕ))) sj = 
  Sum (λ j, Sum (λ k, f j k * ite (j ∈ sj ∧ k ∈ ((sk' j):(finset ℕ))) 1 0) s) s,
  { sorry,  }, 
  have h2 : Sum (λ k, Sum (λ j, f j k) (sj' k)) sk = 
  Sum (λ k, Sum (λ j, f j k * ite (k ∈ sk ∧ j ∈ (sj' k)) 1 0) s) s,
  {sorry, }, 
  -- aux2 f ,
  rw h1,
  rw h2,

  

have h3 : ∀ x y, ite (x ∈ sk ∧ y ∈ sj' x) 1 0 = ite (x ∈ sk) 1 0 * ite (y ∈ sj' x) 1 0,
  { intros x y, rw ← ite_mul_zero_left, rw one_mul, rw ← ite_and, },
  have h4 : ∀ x y, ite (y ∈ sj ∧ x ∈ sk' y) 1 0 = ite (y ∈ sj) 1 0 * ite (x ∈ sk' y) 1 0,
  { intros x y, rw ← ite_mul_zero_left, rw one_mul, rw ← ite_and, },
 
  --apply eq.symm,
  --rw aux2,
  rw id229b,

  unfold Sum,
  apply congr,
  refl,
  apply funext,
  intro a,
  apply congr,
  refl,
  apply funext,
  intro b,

  
  
  /-rw ← ite_mul_zero_left at h,
  rw ← ite_mul_zero_left at h,
  rw one_mul at h,
  rw one_mul at h,
  rw ← ite_and at h,
  rw ← ite_and at h,-/
  
  apply mul_eq_mul_left_iff.mpr,
  left,

  


  
  --have h5 : 
  --have h5 : (b ∈ sj ∧ a ∈ sk' b) ↔ (a ∈ sk ∧ b ∈ sj' a),
  --{ rw iff_def, split, intro i,  },
  
  by_cases (b ∈ sj ∧ a ∈ sk' b),
  { rw if_pos, rw if_pos,  },
  --rw h3 a b,

  rw ite_eq_iff,
  left,
  
  apply eq.symm,
  rw ite_eq_iff,


  

  rw ite_and,
  rw ite_and,
  
  --rw ← ite_mul_zero_left,
  --rw ← ite_mul_zero_left at h,
  rw ← one_mul (ite (y ∈ d2 x) 1 0),
  rw one_mul at h,
  

  unfold Sum,
  apply congr,
end






lemma id232a (f : ℕ → ℕ → ℝ) (n : ℕ) (s s2 : finset ℕ) (hs : s = range (n+1) \ (range 1)) --(sp : finset ℕ × ℕ)
(h : ∀ j , s2 = (range (n+1) \ range j)) ( sp = (filter (λ (p:ℕ × ℕ), (p.fst ≤ p.snd)) (s.product s))) :
Sum (λ j, Sum (λ k, (f j k)) s2) s =
∑ p in sp, f p.fst p.snd :=
begin
  --rw H,
  --rw ← id229a,
  --rw sum_product,


  rw aux2,
  /-rw id227a,
  rw H,
  rw h,
  rw hs,-/


  have ht : ∀ k, k ∈ s ↔ (1 ≤ k ∧ k ≤ n),
  { rw hs, norm_num, intro k, split, intro a, rw and.comm, split, apply nat.le_of_lt_succ, exact a.left, 
   sorry,sorry,},

  unfold Sum,
  --rw ← sum_product.symm,
  --rw id229a,
  
  
  --unfold Sum,
  
  rw H,
  apply eq.symm,
  rw sum_filter,
  
  have h1 : ∑ (a : ℕ × ℕ) in s.product s, ite (a.fst ≤ a.snd) (f a.fst a.snd) 0 = 
  ∑ (a : ℕ × ℕ) in s.product s, (f a.fst a.snd) * ite (a.fst ≤ a.snd) 1 0 ,
  { apply congr, refl, apply funext, intro x, rw mul_boole, },
  rw h1,
  --rw h,
  --rw hs,

  rw ← sum_product.symm,
  
  simp,
  rw h,
  --rw hs,
  simp,


  apply congr, refl, apply funext, intro b,
  
  have ha : s = filter (λ x, x ∈ s) s, { simp, },


--have h3 : 
  have h2: ∑ (x : ℕ) in filter (λ x, x ∈ s) s, ∑ (x_1 : ℕ) in s, 
  ite (x ≤ x_1) (f x x_1) 0
  = ∑ (x : ℕ) in filter (λ x, x ∈ s) s, ∑ (x_1 : ℕ) in s, ite (x ∈ s) (ite (x ≤ x_1) (f x x_1) 0) 0,
  { rw sum_filter, rw sum_filter, apply congr, refl, apply funext, intro b, rw ha, rw sum_filter,
   rw sum_filter, rw ← ha, apply congr,  apply congr,  refl,  sorry, refl,  },
sorry,
sorry,
simp,
sorry,
/-
  rw ← id229a,
  rw ← id229a,
  rw ← mul_sum,

  --have h1 : (empty.product ∅)  = ∅, from {},
  induction n with n ih,
  { rw zero_add, rw sum_filter, rw finset.sdiff_self, rw sum_empty, ring_nf, },
  change n.succ with (n+1),-/
  
  --have h1: ∑ (k : ℕ) in range (n + 1 + 1) \ range 1, 
  --∑ (k_1 : ℕ) in range (n + 1 + 1) \ range k, f k k_1
end




