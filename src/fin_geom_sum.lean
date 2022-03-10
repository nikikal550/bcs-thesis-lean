import data.real.basic
import algebra.big_operators

open finset

open_locale big_operators


def geom_sum (r : ℝ) (n : ℕ) :=
∑ i in range n, r^i

lemma FinGeomSum (r : ℝ) (n : ℕ) : (geom_sum r n) * (1 - r) = (1 - (r^n))  :=
begin
  unfold geom_sum,
  induction n with n ih,
  { simp only [sum_empty, zero_mul, range_zero, pow_zero, sub_self] },
  rw sum_range_succ,
  rw add_mul,
  rw ih,
  change n.succ with (n+1),
  calc
  1 - r^n + r^n * (1 - r) = 1 - r^n + (r^n - r^(n+1)) : by simp only [mul_sub, mul_one, pow_one, pow_add]
  ...                     = 1 - r^(n+1) : by ring,
  
end

