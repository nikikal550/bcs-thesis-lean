import data.real.basic
import data.nat.parity

open nat


def F : ℕ → ℝ      
| 0     := 0
| 1     := 1
| (n+2) := F n + F (n+1)

lemma fib (n : ℕ) : F (n+2) = F (n) + F (n+1) := by refl



lemma Cassini (n : ℕ ) : F (n+2) * F n - (F (n+1))^2 = (- 1)^(n+1) :=
begin
  induction n with n ih,
  { repeat {unfold F}, norm_num, },
  change n.succ with (n+1),
  repeat {rw add_assoc},
  norm_num,

  have h1 : F (n+3) * F (n+1) - F (n+2)^2 = F (n+1)^2 - F n * F (n+2), 
  calc
  F (n+3) * F (n+1) - F (n+2)^2 = ( F (n+1) + F (n+2) ) * F (n+1) - ( F n + F (n+1) )^2 : 
    by { simp only [fib n, fib (n+1), add_assoc], }
  ...                                   =  F (n+1)^2 + F (n+2) * F (n+1) - ( F n^2 + 2*F n*F (n+1) + F (n+1)^2 ) :
    by rw [add_mul, add_sq, ← pow_two]
  ...                                   = F (n+1)^2 + F (n+2) * F (n+1) - F n^2 - 2*F n*F (n+1) - F (n+1)^2  :
    by ring 
  ...                                   = F (n+2) * F (n+1) - F n^2 - 2*F n*F (n+1)  :
    by ring
  ...                                   = ( F n + F (n+1) ) * F (n+1) - F n^2 - 2*F n*F (n+1)  :
    by rw fib n 
  ...                                   = F n * F (n+1) + F (n+1)^2 - F n^2 - 2*F n*F (n+1) :
    by ring
  ...                                   = F (n+1)^2 - F n^2 - F n*F (n+1)  :
    by ring
  ...                                   = F (n+1)^2 - F n * ( F n + F (n+1) )  :
    by ring
  ...                                   = (F (n+1))^2 - F n * F (n+2) :
    by rw ← fib n,
 
  rw h1,
  rw [← neg_sub, mul_comm],
  rw ih,

  apply or.elim (classical.em (even n)),
  { intro evn, 
    have h : ((-1) :ℝ) ^ n = 1, from neg_one_pow_of_even evn,
    repeat {rw pow_add}, rw h,
    norm_num, },
  intro odn, rw ← odd_iff_not_even at odn,
  have h : (((-1) ^ n) :ℝ ) = -1, from neg_one_pow_of_odd odn,
  repeat {rw pow_add}, rw h, norm_num,

end

