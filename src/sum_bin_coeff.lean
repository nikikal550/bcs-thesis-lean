import algebra.big_operators
import data.real.basic

open finset

open_locale big_operators

lemma SumBinCoeff (k : ℕ) (n : ℕ) : (∑ k in range n, n.choose k) = 2^n := 
begin
  rw mul_left_cancel_iff
  --have h :  (∑ k in range n, n.choose k) ∣ (2^n) = 1, from ring,

end

#check mul_left_cancel_iff