import set_theory.game.pgame
import tactic.abel

open pgame

open_locale pgame

universes u v

namespace game

instance pgame.setoid : setoid pgame.{u} :=
⟨(≈), equiv_refl, @pgame.equiv.symm, @pgame.equiv.trans⟩

abbreviation game : Type (u+1) := quotient pgame.setoid.{u}

instance : add_comm_group game :=
{ zero := ⟦0⟧,
  neg := quotient.lift (λ x, ⟦-x⟧) (λ x₁ x₂ h, quotient.sound ((@neg_equiv_neg_iff x₁ x₂).mpr h)),
  add := quotient.lift₂ (λ x y : pgame, ⟦x + y⟧)
    (λ x₁ y₁ x₂ y₂ hx hy, quotient.sound (add_congr hx hy)),
  add_zero := by { rintro ⟨x⟩, exact quotient.sound (add_zero_equiv x) },
  zero_add := by { rintro ⟨x⟩, exact quotient.sound (zero_add_equiv x) },
  add_assoc := by { rintros ⟨x⟩ ⟨y⟩ ⟨z⟩, exact quotient.sound add_assoc_equiv },
  add_left_neg := by { rintro ⟨x⟩, exact quotient.sound (add_left_neg_equiv x), },
  add_comm := by { rintros ⟨x⟩ ⟨y⟩, exact quotient.sound add_comm_equiv } }

instance : has_one game := ⟨⟦1⟧⟩
instance : inhabited game := ⟨0⟩

instance : partial_order game :=
{ le := quotient.lift₂ (λ x y, x ≤ y) (λ x₁ y₁ x₂ y₂ hx hy, propext (le_congr hx hy)),
  le_refl := by { rintro ⟨x⟩, exact le_refl x },
  le_trans := by { rintros ⟨x⟩ ⟨y⟩ ⟨z⟩, exact @le_trans _ _ x y z },
  le_antisymm := by { rintros ⟨x⟩ ⟨y⟩ h₁ h₂, exact quotient.sound ⟨h₁, h₂⟩ } }

def lf : game → game → Prop :=
quotient.lift₂ lf (λ x₁ y₁ x₂ y₂ hx hy, propext (lf_congr hx hy))

local infix ` ⧏ `:50 := lf

@[simp] theorem not_le : ∀ {x y : game}, ¬ x ≤ y ↔ y ⧏ x :=
by { rintro ⟨x⟩ ⟨y⟩, exact pgame.not_le }

@[simp] theorem not_lf : ∀ {x y : game}, ¬ x ⧏ y ↔ y ≤ x :=
by { rintro ⟨x⟩ ⟨y⟩, exact not_lf }

instance : is_trichotomous game (⧏) :=
⟨by { rintro ⟨x⟩ ⟨y⟩, change _ ∨ ⟦x⟧ = ⟦y⟧ ∨ _, rw quotient.eq, exact lf_or_equiv_or_gf x y }⟩

theorem _root_.pgame.le_iff_game_le {x y : pgame} : x ≤ y ↔ ⟦x⟧ ≤ ⟦y⟧ := iff.rfl
theorem _root_.pgame.lf_iff_game_lf {x y : pgame} : pgame.lf x y ↔ ⟦x⟧ ⧏ ⟦y⟧ := iff.rfl
theorem _root_.pgame.lt_iff_game_lt {x y : pgame} : x < y ↔ ⟦x⟧ < ⟦y⟧ := iff.rfl
theorem _root_.pgame.equiv_iff_game_eq {x y : pgame} : x ≈ y ↔ ⟦x⟧ = ⟦y⟧ :=
(@quotient.eq _ _ x y).symm

def fuzzy : game → game → Prop :=
quotient.lift₂ fuzzy (λ x₁ y₁ x₂ y₂ hx hy, propext (fuzzy_congr hx hy))

local infix ` ∥ `:50 := fuzzy

theorem _root_.pgame.fuzzy_iff_game_fuzzy {x y : pgame} : pgame.fuzzy x y ↔ ⟦x⟧ ∥ ⟦y⟧ := iff.rfl

instance covariant_class_add_le : covariant_class game game (+) (≤) :=
⟨by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩ h, exact @add_le_add_left _ _ _ _ y z h x }⟩

instance covariant_class_swap_add_le : covariant_class game game (function.swap (+)) (≤) :=
⟨by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩ h, exact @add_le_add_right _ _ _ _ y z h x }⟩

instance covariant_class_add_lt : covariant_class game game (+) (<) :=
⟨by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩ h, exact @add_lt_add_left _ _ _ _ y z h x }⟩

instance covariant_class_swap_add_lt : covariant_class game game (function.swap (+)) (<) :=
⟨by { rintro ⟨x⟩ ⟨y⟩ ⟨z⟩ h, exact @add_lt_add_right _ _ _ _ y z h x }⟩

theorem add_lf_add_right : ∀ {y z : game} (h : y ⧏ z) (x), y + x ⧏ z + x :=
by { rintro ⟨y⟩ ⟨z⟩ h ⟨x⟩, apply add_lf_add_right h }

theorem add_lf_add_left : ∀ {y z : game} (h : y ⧏ z) (x), x + y ⧏ x + z :=
by { rintro ⟨y⟩ ⟨z⟩ h ⟨x⟩, apply add_lf_add_left h }

instance ordered_add_comm_group : ordered_add_comm_group game :=
{ add_le_add_left := @add_le_add_left _ _ _ game.covariant_class_add_le,
  ..game.add_comm_group,
  ..game.partial_order }

end game

namespace pgame

@[simp] lemma quot_neg (x : pgame) : ⟦-x⟧ = -⟦x⟧ := rfl

@[simp] lemma quot_add (x y : pgame) : ⟦x + y⟧ = ⟦x⟧ + ⟦y⟧ := rfl

@[simp] lemma quot_sub (x y : pgame) : ⟦x - y⟧ = ⟦x⟧ - ⟦y⟧ := rfl

theorem quot_eq_of_mk_quot_eq {x y : pgame}
  (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves)
  (hl : ∀ (i : x.left_moves), ⟦x.move_left i⟧ = ⟦y.move_left (L i)⟧)
  (hr : ∀ (j : y.right_moves), ⟦x.move_right (R.symm j)⟧ = ⟦y.move_right j⟧) :
  ⟦x⟧ = ⟦y⟧ :=
begin
  simp only [quotient.eq] at hl hr,
  exact quotient.sound (equiv_of_mk_equiv L R hl hr)
end

def mul : pgame → pgame → pgame
| x@⟨xl, xr, xL, xR⟩ y@⟨yl, yr, yL, yR⟩ :=
⟨xl × yl ⊕ xr × yr, xl × yr ⊕ xr × yl,
 @sum.rec _ _ (λ _, pgame)
    (@prod.rec _ _ (λ _, pgame) (λ i₁ i₂, mul (xL i₁) y + mul x (yL i₂) - mul (xL i₁) (yL i₂)))
    (@prod.rec _ _ (λ _, pgame) (λ j₁ j₂, mul (xR j₁) y + mul x (yR j₂) - mul (xR j₁) (yR j₂))),
 @sum.rec _ _ (λ _, pgame)
    (@prod.rec _ _ (λ _, pgame) (λ i j, mul (xL i) y + mul x (yR j) - mul (xL i) (yR j)))
    (@prod.rec _ _ (λ _, pgame) (λ j i, mul (xR j) y + mul x (yL i) - mul (xR j) (yL i)))⟩
using_well_founded { dec_tac := pgame_wf_tac }

instance : has_mul pgame.{u} :=
⟨λ x y, begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  have y := mk yl yr yL yR,
  refine ⟨xl × yl ⊕ xr × yr, xl × yr ⊕ xr × yl, _, _⟩; rintro (⟨i, j⟩ | ⟨i, j⟩),
  { exact IHxl i y + IHyl j - IHxl i (yL j) },
  { exact IHxr i y + IHyr j - IHxr i (yR j) },
  { exact IHxl i y + IHyr j - IHxl i (yR j) },
  { exact IHxr i y + IHyl j - IHxr i (yL j) }
end⟩

example {x y : pgame} : x * y = mul x y :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  dsimp only [(*)],
  unfold mul,
  congr,
  all_goals
  { ext,
    change _ * _ + mk _ _ _ _ * _ - _ * _ = _,
    congr; simp [IHxl, IHxr, IHyl, IHyr] }
end

theorem left_moves_mul : ∀ (x y : pgame.{u}), (x * y).left_moves
  = (x.left_moves × y.left_moves ⊕ x.right_moves × y.right_moves)
| ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ := rfl

theorem right_moves_mul : ∀ (x y : pgame.{u}), (x * y).right_moves
  = (x.left_moves × y.right_moves ⊕ x.right_moves × y.left_moves)
| ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ := rfl

def to_left_moves_mul {x y : pgame} :
  x.left_moves × y.left_moves ⊕ x.right_moves × y.right_moves ≃ (x * y).left_moves :=
equiv.cast (left_moves_mul x y).symm

def to_right_moves_mul {x y : pgame} :
  x.left_moves × y.right_moves ⊕ x.right_moves × y.left_moves ≃ (x * y).right_moves :=
equiv.cast (right_moves_mul x y).symm

@[simp] lemma mk_mul_move_left_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inl (i, j))
  = xL i * (mk yl yr yL yR) + (mk xl xr xL xR) * yL j - xL i * yL j :=
rfl

@[simp] lemma mul_move_left_inl {x y : pgame} {i j} :
   (x * y).move_left (to_left_moves_mul (sum.inl (i, j)))
   = x.move_left i * y + x * y.move_left j - x.move_left i * y.move_left j :=
by { cases x, cases y, refl }

@[simp] lemma mk_mul_move_left_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_left (sum.inr (i, j))
  = xR i * (mk yl yr yL yR) + (mk xl xr xL xR) * yR j - xR i * yR j :=
rfl

@[simp] lemma mul_move_left_inr {x y : pgame} {i j} :
   (x * y).move_left (to_left_moves_mul (sum.inr (i, j)))
   = x.move_right i * y + x * y.move_right j - x.move_right i * y.move_right j :=
by { cases x, cases y, refl }

@[simp] lemma mk_mul_move_right_inl {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inl (i, j))
  = xL i * (mk yl yr yL yR) + (mk xl xr xL xR) * yR j - xL i * yR j :=
rfl

@[simp] lemma mul_move_right_inl {x y : pgame} {i j} :
   (x * y).move_right (to_right_moves_mul (sum.inl (i, j)))
   = x.move_left i * y + x * y.move_right j - x.move_left i * y.move_right j :=
by { cases x, cases y, refl }

@[simp] lemma mk_mul_move_right_inr {xl xr yl yr} {xL xR yL yR} {i j} :
  (mk xl xr xL xR * mk yl yr yL yR).move_right (sum.inr (i, j))
  = xR i * (mk yl yr yL yR) + (mk xl xr xL xR) * yL j - xR i * yL j :=
rfl

@[simp] lemma mul_move_right_inr {x y : pgame} {i j} :
   (x * y).move_right (to_right_moves_mul (sum.inr (i, j)))
   = x.move_right i * y + x * y.move_left j - x.move_right i * y.move_left j :=
by { cases x, cases y, refl }

lemma left_moves_mul_cases {x y : pgame} (k) {P : (x * y).left_moves → Prop}
  (hl : ∀ ix iy, P $ to_left_moves_mul (sum.inl ⟨ix, iy⟩))
  (hr : ∀ jx jy, P $ to_left_moves_mul (sum.inr ⟨jx, jy⟩)) : P k :=
begin
  rw ←to_left_moves_mul.apply_symm_apply k,
  rcases to_left_moves_mul.symm k with ⟨ix, iy⟩ | ⟨jx, jy⟩,
  { apply hl },
  { apply hr }
end

lemma right_moves_mul_cases {x y : pgame} (k) {P : (x * y).right_moves → Prop}
  (hl : ∀ i j, P $ to_right_moves_mul (sum.inl ⟨i, j⟩))
  (hr : ∀ j i, P $ to_right_moves_mul (sum.inr ⟨j, i⟩)) : P k :=
begin
  rw ←to_right_moves_mul.apply_symm_apply k,
  rcases to_right_moves_mul.symm k with ⟨i, j⟩ | ⟨j, i⟩,
  { apply hl },
  { apply hr }
end

theorem quot_mul_comm : Π (x y : pgame.{u}), ⟦x * y⟧ = ⟦y * x⟧
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  refine quot_eq_of_mk_quot_eq
    (equiv.sum_congr (equiv.prod_comm _ _) (equiv.prod_comm _ _))
    ((equiv.sum_comm _ _).trans (equiv.sum_congr (equiv.prod_comm _ _) (equiv.prod_comm _ _))) _ _;
  all_goals { rintro (⟨i, j⟩ | ⟨i, j⟩); dsimp; rw [quot_mul_comm, quot_mul_comm (mk xl xr xL xR)] },
  { rw [quot_mul_comm (xL i), add_comm] },
  { rw [quot_mul_comm (xR i), add_comm] },
  { rw [quot_mul_comm (xR j), add_comm] },
  { rw [quot_mul_comm (xL j), add_comm] }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem mul_comm_equiv (x y : pgame) : x * y ≈ y * x :=
quotient.exact $ quot_mul_comm _ _

instance is_empty_mul_zero_left_moves (x : pgame.{u}) : is_empty (x * 0).left_moves :=
by { cases x, apply sum.is_empty }
instance is_empty_mul_zero_right_moves (x : pgame.{u}) : is_empty (x * 0).right_moves :=
by { cases x, apply sum.is_empty }
instance is_empty_zero_mul_left_moves (x : pgame.{u}) : is_empty (0 * x).left_moves :=
by { cases x, apply sum.is_empty }
instance is_empty_zero_mul_right_moves (x : pgame.{u}) : is_empty (0 * x).right_moves :=
by { cases x, apply sum.is_empty }

def mul_zero_relabelling (x : pgame) : x * 0 ≡r 0 := relabelling.is_empty _

theorem mul_zero_equiv (x : pgame) : x * 0 ≈ 0 := (mul_zero_relabelling x).equiv

@[simp] theorem quot_mul_zero (x : pgame) : ⟦x * 0⟧ = ⟦0⟧ :=
@quotient.sound _ _ (x * 0) _ x.mul_zero_equiv

def zero_mul_relabelling (x : pgame) : 0 * x ≡r 0 := relabelling.is_empty _

theorem zero_mul_equiv (x : pgame) : 0 * x ≈ 0 := (zero_mul_relabelling x).equiv

@[simp] theorem quot_zero_mul (x : pgame) : ⟦0 * x⟧ = ⟦0⟧ :=
@quotient.sound _ _ (0 * x) _ x.zero_mul_equiv

@[simp] theorem quot_neg_mul : ∀ (x y : pgame), ⟦-x * y⟧ = -⟦x * y⟧
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  refine quot_eq_of_mk_quot_eq _ _ _ _,
  any_goals
  { fsplit; rintro (⟨_, _⟩ | ⟨_, _⟩);
    solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 4 } },
  all_goals
  { rintro (⟨_, _⟩ | ⟨_, _⟩),
    all_goals
    { change ⟦-_ * y + (-x) * _ - (-_) * _⟧ = ⟦-(_ * y + x * _ - _ * _)⟧,
      simp only [quot_add, quot_sub, quot_neg_mul],
      simp, abel } }
end
using_well_founded { dec_tac := pgame_wf_tac }

@[simp] theorem quot_mul_neg (x y : pgame) : ⟦x * -y⟧ = -⟦x * y⟧ :=
by rw [quot_mul_comm, quot_neg_mul, quot_mul_comm]

@[simp] theorem quot_left_distrib : ∀ (x y z : pgame), ⟦x * (y + z)⟧ = ⟦x * y⟧ + ⟦x * z⟧
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  let z := mk zl zr zL zR,
  refine quot_eq_of_mk_quot_eq _ _ _ _,
  { fsplit,
    { rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩); refl },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩); refl } },
  { fsplit,
    { rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 5 } },
    { rintro (⟨_, _ | _⟩ | ⟨_, _ | _⟩); refl },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, _⟩ | ⟨_, _⟩); refl } },
  { rintro (⟨i, j | k⟩ | ⟨i, j | k⟩),
    { change ⟦xL i * (y + z) + x * (yL j + z) - xL i * (yL j + z)⟧
             = ⟦xL i * y + x * yL j - xL i * yL j + x * z⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xL i * (y + z) + x * (y + zL k) - xL i * (y + zL k)⟧
             = ⟦x * y + (xL i * z + x * zL k - xL i * zL k)⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xR i * (y + z) + x * (yR j + z) - xR i * (yR j + z)⟧
             = ⟦xR i * y + x * yR j - xR i * yR j + x * z⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xR i * (y + z) + x * (y + zR k) - xR i * (y + zR k)⟧
             = ⟦x * y + (xR i * z + x * zR k - xR i * zR k)⟧,
      simp [quot_left_distrib], abel } },
  { rintro (⟨⟨i, j⟩ | ⟨i, j⟩⟩ | ⟨i, k⟩ | ⟨i, k⟩),
    { change ⟦xL i * (y + z) + x * (yR j + z) - xL i * (yR j + z)⟧
             = ⟦xL i * y + x * yR j - xL i * yR j + x * z⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xR i * (y + z) + x * (yL j + z) - xR i * (yL j + z)⟧
             = ⟦xR i * y + x * yL j - xR i * yL j + x * z⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xL i * (y + z) + x * (y + zR k) - xL i * (y + zR k)⟧
             = ⟦x * y + (xL i * z + x * zR k - xL i * zR k)⟧,
      simp [quot_left_distrib], abel },
    { change ⟦xR i * (y + z) + x * (y + zL k) - xR i * (y + zL k)⟧
             = ⟦x * y + (xR i * z + x * zL k - xR i * zL k)⟧,
      simp [quot_left_distrib], abel } }
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem left_distrib_equiv (x y z : pgame) : x * (y + z) ≈ x * y + x * z :=
quotient.exact $ quot_left_distrib _ _ _

@[simp] theorem quot_left_distrib_sub (x y z : pgame) : ⟦x * (y - z)⟧ = ⟦x * y⟧ - ⟦x * z⟧ :=
by { change  ⟦x * (y + -z)⟧ = ⟦x * y⟧ + -⟦x * z⟧, rw [quot_left_distrib, quot_mul_neg] }

@[simp] theorem quot_right_distrib (x y z : pgame) : ⟦(x + y) * z⟧ = ⟦x * z⟧ + ⟦y * z⟧ :=
by simp only [quot_mul_comm, quot_left_distrib]

theorem right_distrib_equiv (x y z : pgame) : (x + y) * z ≈ x * z + y * z :=
quotient.exact $ quot_right_distrib _ _ _

@[simp] theorem quot_right_distrib_sub (x y z : pgame) : ⟦(y - z) * x⟧ = ⟦y * x⟧ - ⟦z * x⟧ :=
by { change ⟦(y + -z) * x⟧ = ⟦y * x⟧ + -⟦z * x⟧, rw [quot_right_distrib, quot_neg_mul] }

@[simp] theorem quot_mul_one : ∀ (x : pgame), ⟦x * 1⟧ = ⟦x⟧
| (mk xl xr xL xR) :=
begin
  let x := mk xl xr xL xR,
  refine quot_eq_of_mk_quot_eq _ _ _ _,
  { fsplit,
    { rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩), assumption },
    { rintro i, exact sum.inl (i, punit.star) },
    { rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩), refl },
    { rintro i, refl } },
  { fsplit,
    { rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩), assumption },
    { rintro i, exact sum.inr (i, punit.star) },
    { rintro (⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩), refl },
    { rintro i, refl } },
  { rintro (⟨i, ⟨⟩⟩ | ⟨_, ⟨⟩⟩),
    change ⟦xL i * 1 + x * 0 - xL i * 0⟧ = ⟦xL i⟧,
    simp [quot_mul_one] },
  { rintro i,
    change ⟦xR i * 1 + x * 0 - xR i * 0⟧ = ⟦xR i⟧,
    simp [quot_mul_one] }
end

theorem mul_one_equiv (x : pgame) : x * 1 ≈ x := quotient.exact $ quot_mul_one _

@[simp] theorem quot_one_mul (x : pgame) : ⟦1 * x⟧ = ⟦x⟧ :=
by rw [quot_mul_comm, quot_mul_one x]

theorem one_mul_equiv (x : pgame) : 1 * x ≈ x := quotient.exact $ quot_one_mul _

theorem quot_mul_assoc : ∀ (x y z : pgame), ⟦x * y * z⟧ = ⟦x * (y * z)⟧
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  let z := mk zl zr zL zR,
  refine quot_eq_of_mk_quot_eq _ _ _ _,
  { fsplit,
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 7 } },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_,⟨_, _⟩ | ⟨_, _⟩⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 7 } },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_,_⟩ | ⟨_, _⟩,_⟩); refl },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_,⟨_, _⟩ | ⟨_, _⟩⟩); refl } },
  { fsplit,
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩,_⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 7 } },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩);
      solve_by_elim [sum.inl, sum.inr, prod.mk] { max_depth := 7 } },
    { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩,_⟩); refl },
    { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩); refl } },
  all_goals
  { try { rintro (⟨⟨_, _⟩ | ⟨_, _⟩, _⟩ | ⟨⟨_, _⟩ | ⟨_, _⟩, _⟩) },
    try { rintro (⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩ | ⟨_, ⟨_, _⟩ | ⟨_, _⟩⟩) },
    all_goals
    { change ⟦(_ * y + x * _ - _ * _) * z + (x * y) * _
               - (_ * y + x * _ - _ * _) * _⟧
             = ⟦_ * (y * z) + x * (_ * z + y * _ - _ * _)
               - _ * (_ * z + y * _ - _ * _)⟧,
      simp [quot_mul_assoc], abel } },
end
using_well_founded { dec_tac := pgame_wf_tac }

theorem mul_assoc_equiv (x y z : pgame) : x * y * z ≈ x * (y * z) :=
quotient.exact $ quot_mul_assoc _ _ _

section

parameters {l r : Type u}

inductive inv_ty (l r : Type u) : bool → Type u
| zero : inv_ty ff
| left₁ : r → inv_ty ff → inv_ty ff
| left₂ : l → inv_ty tt → inv_ty ff
| right₁ : l → inv_ty ff → inv_ty tt
| right₂ : r → inv_ty tt → inv_ty tt

mutual inductive inv_ty_ff, inv_ty_tt (l r : Type u)
with inv_ty_ff : Type u
| zero : inv_ty_ff
| left₁ : r → inv_ty_ff → inv_ty_ff
| left₂ : l → inv_ty_tt → inv_ty_ff
with inv_ty_tt : Type u
| right₁ : l → inv_ty_ff → inv_ty_tt
| right₂ : r → inv_ty_tt → inv_ty_tt

def inv_ty' : bool → Type u
| ff := inv_ty_ff
| tt := inv_ty_tt

def inv_ty'.sizeof : (Σ' b, inv_ty' b) → ℕ
| ⟨ff, x⟩ := @sizeof inv_ty_ff _ x
| ⟨tt, x⟩ := @sizeof inv_ty_tt _ x

meta def inv_ty'.rel_tac : expr → list expr → tactic unit :=
λ _ _, `[exact ⟨_, measure_wf inv_ty'.sizeof⟩]

@[simp] def inv_ty'.rec {C : Π b, inv_ty' b → Sort v}
  (hz : C ff inv_ty_ff.zero)
  (hl₁ : Π {j x}, C ff x → C ff (inv_ty_ff.left₁ j x))
  (hl₂ : Π {i x}, C tt x → C ff (inv_ty_ff.left₂ i x))
  (hr₁ : Π {i x}, C ff x → C tt (inv_ty_tt.right₁ i x))
  (hr₂ : Π {j x}, C tt x → C tt (inv_ty_tt.right₂ j x))
  : Π {b} x, C b x
| ff inv_ty_ff.zero := hz
| ff (inv_ty_ff.left₁ _ x) := hl₁ (@inv_ty'.rec ff x)
| ff (inv_ty_ff.left₂ _ x) := hl₂ (@inv_ty'.rec tt x)
| tt (inv_ty_tt.right₁ _ x) := hr₁ (@inv_ty'.rec ff x)
| tt (inv_ty_tt.right₂ _ x) := hr₂ (@inv_ty'.rec tt x)
using_well_founded { rel_tac := inv_ty'.rel_tac }

@[simp] def f_aux : Π {b}, inv_ty b → inv_ty' b
| _ inv_ty.zero := inv_ty_ff.zero
| _ (inv_ty.left₁ j x) := inv_ty_ff.left₁ j (f_aux x)
| _ (inv_ty.left₂ i x) := inv_ty_ff.left₂ i (f_aux x)
| _ (inv_ty.right₁ i x) := inv_ty_tt.right₁ i (f_aux x)
| _ (inv_ty.right₂ j x) := inv_ty_tt.right₂ j (f_aux x)

@[simp] def f : (Σ b, inv_ty b) → Σ b, inv_ty' b
| ⟨_, x⟩ := ⟨_, f_aux x⟩

@[simp] def f_inv_aux : Π b, inv_ty' b → inv_ty b
| ff inv_ty_ff.zero := inv_ty.zero
| ff (inv_ty_ff.left₁ j x) := inv_ty.left₁ j (f_inv_aux ff x)
| ff (inv_ty_ff.left₂ i x) := inv_ty.left₂ i (f_inv_aux tt x)
| tt (inv_ty_tt.right₁ i x) := inv_ty.right₁ i (f_inv_aux ff x)
| tt (inv_ty_tt.right₂ j x) := inv_ty.right₂ j (f_inv_aux tt x)
using_well_founded { rel_tac := inv_ty'.rel_tac }

@[simp] def f_inv : (Σ b, inv_ty' b) → Σ b, inv_ty b
| ⟨_, x⟩ := ⟨_, f_inv_aux _ x⟩

example : (Σ b, inv_ty b) ≃ Σ b, inv_ty' b :=
by refine ⟨f, f_inv, _, _⟩; rintro ⟨_, x⟩; induction x; simp * at *

end

instance (l r : Type u) [is_empty l] [is_empty r] : is_empty (inv_ty l r tt) :=
⟨by rintro (_|_|_|a|a); exact is_empty_elim a⟩

instance (l r : Type u) : inhabited (inv_ty l r ff) := ⟨inv_ty.zero⟩

instance unique_inv_ty (l r : Type u) [is_empty l] [is_empty r] : unique (inv_ty l r ff) :=
⟨_, by { rintro (_|a|a), refl, all_goals { exact is_empty_elim a } }⟩

def inv_val {l r} (L : l → pgame) (R : r → pgame)
  (IHl : l → pgame) (IHr : r → pgame) : ∀ {b}, inv_ty l r b → pgame
| _ inv_ty.zero := 0
| _ (inv_ty.left₁ j x) := (1 + (R j - mk l r L R) * inv_val x) * IHr j
| _ (inv_ty.left₂ i x) := (1 + (L i - mk l r L R) * inv_val x) * IHl i
| _ (inv_ty.right₁ i x) := (1 + (L i - mk l r L R) * inv_val x) * IHl i
| _ (inv_ty.right₂ j x) := (1 + (R j - mk l r L R) * inv_val x) * IHr j

@[simp] theorem inv_val_is_empty {l r b} (L R IHl IHr) (x : inv_ty l r b)
  [is_empty l] [is_empty r] : inv_val L R IHl IHr x = 0 :=
by { cases x with a _ a _ a _ a, refl, all_goals { exact is_empty_elim a } }

def inv' : pgame → pgame
| ⟨l, r, L, R⟩ :=
  let l' := {i // 0 < L i},
      L' : l' → pgame := λ i, L i.1,
      IHl' : l' → pgame := λ i, inv' (L i.1),
      IHr := λ i, inv' (R i) in
  ⟨inv_ty l' r ff, inv_ty l' r tt,
    inv_val L' R IHl' IHr, inv_val L' R IHl' IHr⟩

def inv'' : pgame → pgame
| ⟨l, r, L, R⟩ := begin
  let l' := {i // 0 < L i},
  let L' := λ i : l', L i.1,
  let IHl' := λ i : l', inv'' (L i.1),
  let IHr := λ j, inv'' (R j),
  exact ⟨inv_ty l' r ff, inv_ty l' r tt, inv_val L' R IHl' IHr, inv_val L' R IHl' IHr⟩
end

example : inv' = inv'' :=
begin
  ext x,
  induction x with _ _ _ _ IHl _,
  dsimp only [inv'],
  congr; ext; solve_by_elim [λ i, IHl (subtype.val i)]
end

def inv''' (x : pgame) : pgame :=
begin
  induction x with l r L R IHl IHr,
  let l' := {i // 0 < L i},
  let L' := λ i : l', L i.1,
  let IHl' := λ i : l', IHl i.1,
  exact ⟨inv_ty l' r ff, inv_ty l' r tt, inv_val L' R IHl' IHr, inv_val L' R IHl' IHr⟩
end

example : inv' = inv''' :=
begin
  ext x,
  induction x with _ _ _ _ IHl _,
  dsimp only [inv'],
  congr; ext; solve_by_elim [λ i, IHl (subtype.val i)]
end

theorem zero_lf_inv' : ∀ (x : pgame), 0 ⧏ inv' x
| ⟨xl, xr, xL, xR⟩ := by { convert lf_mk _ _ inv_ty.zero, refl }

def inv'_zero : inv' 0 ≡r 1 :=
begin
  change mk _ _ _ _ ≡r 1,
  refine ⟨_, _, λ i, _, is_empty_elim⟩,
  { dsimp, apply equiv.equiv_punit },
  { dsimp, apply equiv.equiv_pempty },
  { simp }
end

theorem inv'_zero_equiv : inv' 0 ≈ 1 := inv'_zero.equiv

def inv'_one : inv' 1 ≡r (1 : pgame.{u}) :=
begin
  change mk _ _ _ _ ≡r 1,
  haveI : is_empty {i : punit.{u+1} // (0 : pgame.{u}) < 0},
  { rw lt_self_iff_false, apply_instance },
  refine ⟨_, _, λ i, _, is_empty_elim⟩,
  { dsimp, apply equiv.equiv_punit },
  { dsimp, apply equiv.equiv_pempty },
  { simp }
end

theorem inv'_one_equiv : inv' 1 ≈ 1 := inv'_one.equiv

noncomputable instance : has_inv pgame :=
⟨by { classical, exact λ x, if x ≈ 0 then 0 else if 0 < x then inv' x else -inv' (-x) }⟩

noncomputable instance : has_div pgame := ⟨λ x y, x * y⁻¹⟩

theorem inv_eq_of_equiv_zero {x : pgame} (h : x ≈ 0) : x⁻¹ = 0 := if_pos h

@[simp] theorem inv_zero : (0 : pgame)⁻¹ = 0 :=
inv_eq_of_equiv_zero (equiv_refl _)

theorem inv_eq_of_pos {x : pgame} (h : 0 < x) : x⁻¹ = inv' x :=
(if_neg h.lf.not_equiv').trans (if_pos h)

theorem inv_eq_of_lf_zero {x : pgame} (h : x ⧏ 0) : x⁻¹ = -inv' (-x) :=
(if_neg h.not_equiv).trans (if_neg h.not_gt)

def inv_one : 1⁻¹ ≡r 1 :=
by { rw inv_eq_of_pos zero_lt_one, exact inv'_one }

theorem inv_one_equiv : 1⁻¹ ≈ 1 := inv_one.equiv

end pgame