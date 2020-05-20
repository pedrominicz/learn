import data.int.parity
import data.real.irrational

open real

#print irrational
#check set.range (coe : ℚ → ℝ)

lemma eq_mul_div_of_nonneg {a b : ℝ} (h : b ≠ 0) : a = a / b * b :=
begin
  calc
  a   = 1 * a     : by ring
  ... = b / b * a : by rw ←div_self h
  ... = a / b * b : by exact div_mul_comm' b b a
end

#check div_self
#check mul_div_right_comm

lemma eq_of_mul_eq_mul_left' {a b t : ℕ} (ht : t ≠ 0) :
  t * a = t * b → a = b :=
begin
end

example : irrational (sqrt 2) :=
begin
  rintro ⟨⟨a, b, pos, cop⟩, h⟩,
  have : (b : ℝ) ≠ 0,
  { norm_cast,
    apply ne_of_gt,
    assumption },
  have h₁ : (a : ℝ) = sqrt 2 * b,
  { apply_fun (λ x, x * b) at h,
    calc
    (a : ℝ) = 1 * a      : by ring
    ...     = b / b * a  : by rwa ←div_self
    ...     = a / b * b  : by ring
    ...     = sqrt 2 * b : by exact h },
  have h₂ : (a : ℝ)^2 = 2 * b^2,
  { apply_fun (λ x, x * x) at h₁,
    ring at *,
    rw sqr_sqrt at *; linarith },
  have a_even : a.even,
  { suffices : (a^2).even,
    { rw int.even_pow at this, cc },
    use b^2, norm_cast at *, assumption },
  have a_even : b.even,
  { suffices : (b^2).even,
    { rw nat.even_pow at this, cc },
    cases a_even with c hc,
    use (c^2).to_nat,
    apply eq_of_mul_eq_mul_left' (show 2 ≠ 0, by linarith),
    rw hc at h₂,
    norm_cast at *,
    ring,
    calc
    2 * b ^ 2 = 2 * b * b          : by ring
    ...       = ((2 * c)^2).to_nat : by { rw h₂, ring }
    ...       = (4 * c^2).to_nat   : by ring
    -- Is at this point that I stop. This is not worthwhile. My strategy is
    -- probably really bad. I should just be working with `ℚ`.
    ...       = 4 * (c ^ 2).to_nat : by { sorry } },
  sorry
end