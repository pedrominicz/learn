import algebra.pi_instances
import data.real.basic

local attribute [instance] classical.prop_decidable

class metric_space (α : Type*) :=
(dist : α → α → ℝ)
(dist_self : ∀ x, dist x x = 0)
(eq_of_dist_eq_zero : ∀ {x y : α}, dist x y = 0 → x = y)
(dist_comm : ∀ x y : α, dist x y = dist y x)
(dist_triangle : ∀ x y z : α, dist x z ≤ dist x y + dist y z)

open metric_space

section

variables {α : Type*} [metric_space α]
variables {u v : ℕ → α} {l l₁ l₂ : α}

def limit (u : ℕ → α) (l : α) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) l ≤ ε

theorem dist_nonneg {x y : α}: 0 ≤ dist x y :=
begin
  have : dist x x ≤ dist x y + dist y x, from dist_triangle _ _ _,
  rw dist_comm y x at this,
  rw dist_self at this,
  linarith
end

theorem dist_pos {x y : α} : 0 < dist x y ↔ x ≠ y :=
begin
  split; contrapose!,
  { rintro rfl,
    have : dist x x = 0, from dist_self _,
    linarith },
  { intro h,
    apply eq_of_dist_eq_zero,
    have : 0 ≤ dist x y, from dist_nonneg,
    linarith }
end

lemma limit_unique (h₁ : limit u l₁) (h₂ : limit u l₂) : l₁ = l₂ :=
begin
  by_contra h,
  let ε := dist l₁ l₂,
  have : ε > 0, from dist_pos.mpr h,
  cases h₁ (ε/3) (by linarith) with N₁ hN₁,
  cases h₂ (ε/3) (by linarith) with N₂ hN₂,
  let n := max N₁ N₂,
  specialize hN₁ n (le_max_left _ _),
  specialize hN₂ n (le_max_right _ _),
  have : dist (u n) l₁ + dist (u n) l₂ < ε, by linarith,
  have : ε ≤ dist l₁ (u n) + dist (u n) l₂, from dist_triangle _ _ _,
  linarith [dist_comm l₁ (u n)]
end

end

notation `|`x`|` := abs x

noncomputable instance : metric_space ℝ :=
{ dist := λ x y, |x - y|,
  -- This proof term is hideous and beautiful simultaneously.
  dist_self := λ x, eq.symm (sub_self x) ▸ abs_zero,
  eq_of_dist_eq_zero := λ x y, eq_of_abs_sub_eq_zero,
  dist_comm := abs_sub,
  dist_triangle := abs_sub_le }

variables {u v : ℕ → ℝ} {c l l₁ l₂ : ℝ}

@[simp] def const (l : ℝ) : ℕ → ℝ := function.const _ l

lemma neg_const : -const l = const (-l) := by funext; simp

theorem const_limit : limit (const c) c :=
begin
  intros ε ε_pos,
  use 0,
  intros n hn,
  unfold dist,
  simp,
  linarith
end

theorem limit_add_limit (h₁ : limit u l₁) (h₂ : limit v l₂) :
  limit (u + v) (l₁ + l₂) :=
begin
  intros ε ε_pos,
  cases h₁ (ε/2) (by linarith) with N₁ hN₁,
  cases h₂ (ε/2) (by linarith) with N₂ hN₂,
  use max N₁ N₂,
  intros n hn,
  specialize hN₁ n (le_of_max_le_left hn),
  specialize hN₂ n (le_of_max_le_right hn),
  unfold dist at *,
  calc
  |(u + v) n - (l₁ + l₂)| = |(u n + v n) - (l₁ + l₂)| : rfl
  ...                     = |(u n - l₁) + (v n - l₂)| : by congr; ring
  ...                     ≤ |u n - l₁| + |v n - l₂|   : by apply abs_add
  ...                     ≤ ε                         : by linarith
end

lemma limit_add_const (h : limit u l) : limit (u + const c) (l + c) := 
limit_add_limit h const_limit

lemma limit_sub_self (h : limit u l) : limit (u - const l) 0 :=
begin
  rw [←sub_self l, sub_eq_add_neg, sub_eq_add_neg, neg_const],
  exact limit_add_const h
end

example (α : Type*) [linear_ordered_field α] (a b c : α) (h : a ≤ b / c) (H : c > 0) : a*c ≤ b := by refine (le_div_iff H).mp h

lemma limit_mul_const (h : limit u l) : limit (u * const c) (l * c) :=
begin
  intros ε ε_pos,
  by_cases hc : c = 0,
  { use 0,
    intros n hn,
    rw hc,
    simp,
    rw dist_self,
    exact le_of_lt ε_pos },
  { change c ≠ 0 at hc,
    have : ε / |c| > 0, from div_pos_of_pos_of_pos ε_pos (by rwa abs_pos_iff),
    cases h _ this with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    unfold dist at *,
    suffices : |(u n - l) * c| ≤ ε,
    { calc
      |(u * const c) n - l * c| = |(u n * c) - l * c| : rfl
      ...                       = |(u n - l) * c|     : by congr; ring
      ...                       ≤ ε                   : this },
    rwa [abs_mul, ←le_div_iff],
    rwa abs_pos_iff }
end

theorem limit_zero_mul_limit_zero (h₁ : limit u 0) (h₂ : limit v 0) :
  limit (u * v) 0 :=
begin
  intros ε ε_pos,
  have : ε.sqrt > 0, from real.sqrt_pos.mpr ε_pos,
  cases h₁ (ε.sqrt) this with N₁ hN₁,
  cases h₂ (ε.sqrt) this with N₂ hN₂,
  use max N₁ N₂,
  intros n hn,
  specialize hN₁ n (le_of_max_le_left hn),
  specialize hN₂ n (le_of_max_le_right hn),
  unfold dist at *,
  calc
  |(u * v) n - 0| = |(u n * v n) - 0|       : rfl
  ...             = |(u n - 0) * (v n - 0)| : by ring
  ...             = |u n - 0| * |v n - 0|   : by apply abs_mul
  ...             ≤ ε.sqrt * ε.sqrt         : mul_le_mul hN₁ hN₂ (abs_nonneg _) (le_of_lt this)
  ...             = ε.sqrt ^ 2              : by ring
  ...             = ε                       : real.sqr_sqrt (le_of_lt ε_pos)
end

lemma limit_neg_iff : limit (-u) (-l) ↔ limit u l :=
begin
  split;
  { intros h ε ε_pos,
    cases h ε ε_pos with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    unfold dist at *,
    simp at *,
    rwa abs_sub at hN }
end

notation u `+` v := limit_add_limit u v

theorem limit_mul_limit (h₁ : limit u l₁) (h₂ : limit v l₂) :
  limit (u * v) (l₁ * l₂) :=
begin
  let c₁ := const l₁,
  let c₂ := const l₂,
  have w₁ : limit ((u - c₁) * (v - c₂)) 0,
  from limit_zero_mul_limit_zero (limit_sub_self h₁) (limit_sub_self h₂),
  rw (show (u - c₁) * (v - c₂) = u * v - u * c₂ - v * c₁ + c₁ * c₂, by ring) at w₁,
  have w₂ : limit (-c₁ * c₂) (-l₁ * l₂),
  { simp,
    rw limit_neg_iff,
    exact limit_mul_const const_limit },
  have w₃ : limit (u * c₂) (l₁ * l₂), from limit_mul_const h₁,
  have w₄ : limit (v * c₁) (l₁ * l₂), by { rw mul_comm l₁, exact limit_mul_const h₂ },
  have w := w₁ + w₂ + w₃ + w₄,
  -- The most satisfying two lines.
  simp at w,
  ring at w,
  rwa [mul_comm u, mul_comm l₁]
end