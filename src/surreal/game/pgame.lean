import logic.relation
import set_theory.game.pgame
import tactic

example : (0 : pgame) = pgame.mk pempty pempty pempty.elim pempty.elim := rfl
example : (1 : pgame) = pgame.mk punit pempty (λ star, 0) pempty.elim := rfl

example : -(0 : pgame) = 0 :=
pgame.neg_zero

lemma neg_one_mk : -(1 : pgame) = pgame.mk pempty punit pempty.elim (λ star, 0) :=
by simp [has_one.one, pgame.neg, pgame.neg_zero]

example (x : pgame) : pgame.relabelling (0 + x) x :=
pgame.zero_add_relabelling x

example {x y z : pgame} : pgame.relabelling ((x + y) + z) (x + (y + z)) :=
pgame.add_assoc_relabelling x y z

example : pgame.relabelling ((1 : pgame) - (1 : pgame)) (pgame.mk punit punit (λ star, -1) (λ star, 1) : pgame) :=
begin
  refine ⟨equiv.sum_empty _ _, equiv.empty_sum _ _, _, _⟩,
  { intro i,
    rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩,
    refine ⟨equiv.sum_empty _ _, equiv.empty_sum _ _, _, _⟩,
    { intro i, rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ },
    { intro j,
      cases j,
      refine ⟨equiv.sum_empty _ _, equiv.sum_empty _ _, _, _⟩,
      { intro i, rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ },
      { intro j, cases j } } },
  { intro j,
    cases j,
    refine ⟨equiv.sum_empty _ _, equiv.sum_empty _ _, _, _⟩,
    { intro i,
      rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩,
      refine ⟨equiv.sum_empty _ _, equiv.sum_empty _ _, _, _⟩,
      { intro i, rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ },
      { intro j, cases j } },
    { intro j, cases j } }
end

example (x : pgame) : pgame.equiv (x - x) 0 :=
pgame.sub_self_equiv x

namespace G

def equiv : pgame → pgame → Prop
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ :=
  ((∀ i, ∃ i', equiv (xL i) (yL i')) ∧ (∀ i, ∃ i', equiv (xL i') (yL i)))
∧ ((∀ j, ∃ j', equiv (xR j) (yR j')) ∧ (∀ j, ∃ j', equiv (xR j') (yR j)))

theorem equiv.refl (x : pgame) : equiv x x :=
begin
  induction x with l r L R IHl IHr,
  change ∀ i, equiv (L i) (L i) at IHl,
  change ∀ j, equiv (R j) (R j) at IHr,
  refine ⟨
    ⟨λ i, ⟨i, IHl i⟩, λ i, ⟨i, IHl i⟩⟩,
    ⟨λ j, ⟨j, IHr j⟩, λ j, ⟨j, IHr j⟩⟩⟩
end

theorem equiv.rfl : ∀ {x : pgame}, equiv x x := equiv.refl

theorem equiv.symm {x y : pgame} : equiv x y → equiv y x :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  change ∀ i y, equiv (xL i) y → equiv y (xL i) at IHxl,
  change ∀ j y, equiv (xR j) y → equiv y (xR j) at IHxr,
  cases y with yl yr yL yR,
  rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩,
  refine ⟨⟨_, _⟩, ⟨_, _⟩⟩,
  { intro i,
    cases h₂ i with i h,
    exact ⟨i, IHxl _ _ h⟩ },
  { intro i,
    cases h₁ i with i h,
    exact ⟨i, IHxl _ _ h⟩ },
  { intro j,
    cases h₄ j with j h,
    exact ⟨j, IHxr _ _ h⟩ },
  { intro j,
    cases h₃ j with j h,
    exact ⟨j, IHxr _ _ h⟩ }
end

theorem equiv.trans {x y z : pgame} (h₁ : equiv x y) (h₂ : equiv y z) :
  equiv x z :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y z,
  change ∀ i y z, equiv (xL i) y → equiv y z → equiv (xL i) z at IHxl,
  change ∀ j y z, equiv (xR j) y → equiv y z → equiv (xR j) z at IHxr,
  cases y with yl yr yL yR,
  cases z with zl zr zL zR,
  rcases h₁ with ⟨⟨h₁₁, h₁₂⟩, ⟨h₁₃, h₁₄⟩⟩,
  rcases h₂ with ⟨⟨h₂₁, h₂₂⟩, ⟨h₂₃, h₂₄⟩⟩,
  refine ⟨⟨_, _⟩, ⟨_, _⟩⟩,
  { intro i,
    cases h₁₁ i with i h₁,
    cases h₂₁ i with i h₂,
    exact ⟨i, IHxl _ _ _ h₁ h₂⟩ },
  { intro i,
    cases h₂₂ i with i h₂,
    cases h₁₂ i with i h₁,
    exact ⟨i, IHxl _ _ _ h₁ h₂⟩ },
  { intro j,
    cases h₁₃ j with j h₁,
    cases h₂₃ j with j h₂,
    exact ⟨j, IHxr _ _ _ h₁ h₂⟩ },
  { intro j,
    cases h₂₄ j with j h₂,
    cases h₁₄ j with j h₁,
    exact ⟨j, IHxr _ _ _ h₁ h₂⟩ }
end

instance setoid : setoid pgame :=
⟨equiv, equiv.refl, @equiv.symm, @equiv.trans⟩

def G : Type 1 := quotient G.setoid

example {x y : pgame} (h : pgame.relabelling x y) : equiv x y :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  change ∀ i y, pgame.relabelling (xL i) y → equiv (xL i) y at IHxl,
  change ∀ j y, pgame.relabelling (xR j) y → equiv (xR j) y at IHxr,
  let x := pgame.mk xl xr xL xR,
  cases y with yl yr yL yR,
  cases h with _ _ hl hr hL hR,
  change xl ≃ yl at hl,
  change xr ≃ yr at hr,
  cases hl with fl₁ fl₂ hl₁ hl₂,
  change ∀ i, _ at hl₁,
  change ∀ i, _ at hl₂,
  cases hr with fr₁ fr₂ hr₁ hr₂,
  change ∀ j, _ at hr₁,
  change ∀ j, _ at hr₂,
  change ∀ i, pgame.relabelling (xL i) (yL (fl₁ i)) at hL,
  change ∀ j, pgame.relabelling (xR (fr₂ j)) (yR j) at hR,
  refine ⟨⟨_, _⟩, ⟨_, _⟩⟩,
  { exact λ i, ⟨fl₁ i, IHxl _ _ (hL _)⟩ },
  { refine λ i, ⟨fl₂ i, _⟩,
    apply IHxl,
    convert hL (fl₂ i),
    rw hl₂ },
  { refine λ j, ⟨fr₁ j, _⟩,
    apply IHxr,
    convert hR (fr₁ j),
    rw hr₁ },
  { exact λ j, ⟨fr₂ j, IHxr _ _ (hR _)⟩ }
end

example : ∃ x y : pgame, equiv x y ∧ (pgame.relabelling x y → false) :=
begin
  let x := pgame.mk unit empty (λ _, 0) empty.elim,
  let y := pgame.mk bool empty (λ _, 0) empty.elim,
  refine ⟨x, y, _, _⟩,
  { refine ⟨by simp [equiv.refl], ⟨by rintro ⟨⟩, by rintro ⟨⟩⟩⟩ },
  { intro h,
    suffices : tt = ff,
    { cases this },
    cases h with _ _ h h₁ h₂ h₃, clear h₂ h₃ h₁,
    cases h with to_fun inv_fun left_inv right_inv,
    change unit → bool at to_fun,
    change bool → unit at inv_fun,
    change ∀ x : unit, _ at left_inv,
    change ∀ x : bool, _ at right_inv,
    transitivity,
    { exact (right_inv tt).symm },
    { suffices : inv_fun tt = inv_fun ff,
      { rw this, exact right_inv ff },
      simp } }
end

example : pgame.equiv (pgame.mk unit empty (λ _, 0) empty.elim) (pgame.mk bool empty (λ _, 0) empty.elim) :=
begin
  split,
  all_goals
  { simp only [pgame.mk_le_mk, forall_const, bool.forall_bool, and_self],
    refine ⟨_, by rintro ⟨⟩⟩,
    simp [has_zero.zero] }
end

theorem lf_of_equiv_left_move {x y : pgame} {i : pgame.left_moves y} :
  pgame.equiv x (pgame.move_left y i) → pgame.lf x y :=
begin
  intro h,
  cases x with xl xr xL xR,
  cases y with yl yr yL yR,
  simp only [pgame.mk_lf_mk],
  left,
  use i,
  exact pgame.equiv.le h
end

theorem lf_of_right_move_equiv {x y : pgame} {j : pgame.right_moves x} :
  pgame.equiv (pgame.move_right x j) y → pgame.lf x y :=
begin
  intro h,
  cases x with xl xr xL xR,
  cases y with yl yr yL yR,
  simp only [pgame.mk_lf_mk],
  right,
  use j,
  exact pgame.equiv.le h
end

example {x y : pgame} (h : equiv x y) : pgame.equiv x y :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  change ∀ i y, equiv (xL i) y → pgame.equiv (xL i) y at IHxl,
  change ∀ j y, equiv (xR j) y → pgame.equiv (xR j) y at IHxr,
  let x := pgame.mk xl xr xL xR,
  cases y with yl yr yL yR,
  let y := pgame.mk yl yr yL yR,
  rcases h with ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩,
  simp only [pgame.equiv, pgame.mk_le_mk],
  refine ⟨⟨_, _⟩, ⟨_, _⟩⟩,
  { intro i,
    cases h₁ i with i h,
    exact lf_of_equiv_left_move (IHxl _ _ h) },
  { intro j,
    cases h₄ j with j h,
    exact lf_of_right_move_equiv (IHxr _ _ h) },
  { intro i,
    cases h₂ i with i' h,
    exact lf_of_equiv_left_move (IHxl _ _ h).symm },
  { intro j,
    cases h₃ j with j h,
    exact lf_of_right_move_equiv (IHxr _ _ h).symm }
end

end G

#exit

inductive pgame : Type 1
| mk (l r : Type) (L : l → pgame) (R : r → pgame) : pgame

namespace pgame

def left_moves : pgame → Type
| (mk l _ _ _) := l

def right_moves : pgame → Type
| (mk _ r _ _) := r

def move_left : Π x, left_moves x → pgame
| (mk _ _ L _) := L

def move_right : Π x, right_moves x → pgame
| (mk _ _ _ R) := R

@[simp] lemma left_moves_mk {l r L R} : left_moves ⟨l, r, L, R⟩ = l := rfl
@[simp] lemma right_moves_mk {l r L R} : right_moves ⟨l, r, L, R⟩ = r := rfl
@[simp] lemma move_left_mk {l r L R} : move_left ⟨l, r, L, R⟩ = L := rfl
@[simp] lemma move_right_mk {l r L R} : move_right ⟨l, r, L, R⟩ = R := rfl

@[elab_as_eliminator] def {u} move_rec_on {P : pgame → Sort u} (x : pgame)
  (ih : ∀ y, (∀ i, P (move_left y i)) → (∀ j, P (move_right y j)) → P y) : P x :=
x.rec_on $ λ yl yr yL yR, ih (mk yl yr yL yR)

@[mk_iff] inductive is_option : pgame → pgame → Prop
| move_left {x : pgame} (i : left_moves x) : is_option (move_left x i) x
| move_right {x : pgame} (j : right_moves x) : is_option (move_right x j) x

theorem is_option.mk_left {l r : Type} (L : l → pgame) (R : r → pgame) (i : l) :
  is_option (L i) (mk l r L R) :=
@is_option.move_left (mk _ _ _ _) i

theorem is_option.mk_right {l r : Type} (L : l → pgame) (R : r → pgame) (j : r) :
  is_option (R j) (mk l r L R) :=
@is_option.move_right (mk _ _ _ _) j

theorem wf_is_option : well_founded is_option :=
begin
  refine ⟨λ x, _⟩,
  induction x with l r L R ih₁ ih₂,
  change ∀ i, acc is_option (L i) at ih₁,
  change ∀ j, acc is_option (R j) at ih₂,
  refine acc.intro _ (λ y h, _),
  rw [is_option_iff] at h,
  cases h,
  { change ∃ i : l, y = L i at h,
    rcases h with ⟨i, rfl⟩,
    exact ih₁ i },
  { change ∃ j : r, y = R j at h,
    rcases h with ⟨j, rfl⟩,
    exact ih₂ j }
end

def subsequent : pgame → pgame → Prop :=
relation.trans_gen is_option

instance : is_trans _ subsequent :=
relation.trans_gen.is_trans

@[trans] theorem subsequent.trans {x y z} :
  subsequent x y → subsequent y z → subsequent x z :=
relation.trans_gen.trans

theorem wf_subsequent : well_founded subsequent :=
wf_is_option.trans_gen

instance : has_well_founded pgame :=
⟨_, wf_subsequent⟩

lemma subsequent.move_left {x : pgame} (i : left_moves x) :
  subsequent (move_left x i) x :=
relation.trans_gen.single (is_option.move_left i)

lemma subsequent.move_right {x : pgame} (j : right_moves x) :
  subsequent (move_right x j) x :=
relation.trans_gen.single (is_option.move_right j)

lemma subsequent.mk_left {l r} (L : l → pgame) (R : r → pgame) (i : l) :
  subsequent (L i) (mk l r L R) :=
@subsequent.move_left (mk _ _ _ _) i

lemma subsequent.mk_right {l r} (L : l → pgame) (R : r → pgame) (j : r) :
  subsequent (R j) (mk l r L R) :=
@subsequent.move_right (mk _ _ _ _) j

meta def dec_tac : tactic unit :=
`[solve_by_elim
  [psigma.lex.left, psigma.lex.right, subsequent.move_left, subsequent.move_right,
   subsequent.mk_left, subsequent.mk_right, subsequent.trans]
  { max_depth := 6 }]

instance : has_zero pgame :=
⟨mk pempty pempty pempty.elim pempty.elim⟩

@[simp] lemma zero_left_moves : left_moves 0 = pempty := rfl
@[simp] lemma zero_right_moves : right_moves 0 = pempty := rfl

instance is_empty_zero_left_moves : is_empty (left_moves 0) := pempty.is_empty
instance is_empty_zero_right_moves : is_empty (right_moves 0) := pempty.is_empty

instance : inhabited pgame := ⟨0⟩

instance : has_one pgame :=
⟨mk punit pempty (λ _, 0) pempty.elim⟩

@[simp] lemma one_left_moves : left_moves 1 = punit := rfl
@[simp] lemma one_move_left (star : punit) : move_left 1 star = 0 := rfl
@[simp] lemma one_right_moves : right_moves 1 = pempty := rfl

instance unique_one_left_moves : unique (left_moves 1) := punit.unique
instance is_empty_one_right_moves : is_empty (right_moves 1) := pempty.is_empty

def le_lf : pgame → pgame → Prop × Prop
| x@(mk xl xr xL xR) y@(mk yl yr yL yR) :=
⟨(∀ i, (le_lf (xL i) y).2) ∧ ∀ j, (le_lf x (yR j)).2,
 (∃ i, (le_lf x (yL i)).1) ∨ ∃ j, (le_lf (xR j) y).1⟩
using_well_founded { dec_tac := dec_tac }

instance : has_le pgame := ⟨λ x y, (le_lf x y).1⟩

def lf (x y : pgame) : Prop := (le_lf x y).2

local infix ` ⧏ `:50 := lf

@[simp] theorem mk_le_mk {xl xr xL xR yl yr yL yR} :
  mk xl xr xL xR ≤ mk yl yr yL yR ↔
  (∀ i, xL i ⧏ mk yl yr yL yR) ∧ ∀ j, mk xl xr xL xR ⧏ yR j :=
begin
  change (le_lf _ _).1 ↔ _,
  rw le_lf,
  refl
end

theorem le_iff_forall_lf {x y : pgame} :
  x ≤ y ↔ (∀ i, x.move_left i ⧏ y) ∧ ∀ j, x ⧏ y.move_right j :=
begin
  cases x with xl xr xL xR,
  cases y with yl yr yL yR,
  exact mk_le_mk
end

theorem le_of_forall_lf {x y : pgame} :
  ((∀ i, x.move_left i ⧏ y) ∧ ∀ j, x ⧏ y.move_right j) → x ≤ y :=
le_iff_forall_lf.2

@[simp] theorem mk_lf_mk {xl xr xL xR yl yr yL yR} :
  mk xl xr xL xR ⧏ mk yl yr yL yR ↔
  (∃ i, mk xl xr xL xR ≤ yL i) ∨ ∃ j, xR j ≤ mk yl yr yL yR :=
begin
  change (le_lf _ _).2 ↔ _,
  rw le_lf,
  refl
end

theorem lf_iff_exists_le {x y : pgame} :
  x ⧏ y ↔ (∃ i, x ≤ y.move_left i) ∨ ∃ j, x.move_right j ≤ y :=
begin
  cases x with xl xr xL xR,
  cases y with yl yr yL yR,
  exact mk_lf_mk
end

theorem lf_of_exists_le {x y : pgame} :
  ((∃ i, x ≤ y.move_left i) ∨ ∃ j, x.move_right j ≤ y) → x ⧏ y :=
lf_iff_exists_le.2

private theorem not_le_lf {x y : pgame} :
  (¬ x ≤ y ↔ y ⧏ x) ∧ (¬ x ⧏ y ↔ y ≤ x) :=
begin
  induction x with xl xr xL xR ih₁ ih₂ generalizing y,
  induction y with yl yr yL yR ih₃ ih₄,
  simp only [mk_le_mk, mk_lf_mk, ih₁, ih₂, ih₃, ih₄,
    not_and_distrib, not_or_distrib, not_forall, not_exists,
    iff_self, and_self]
end

@[simp] protected theorem not_le {x y : pgame} : ¬ x ≤ y ↔ y ⧏ x := not_le_lf.1
@[simp] theorem not_lf {x y : pgame} : ¬ x ⧏ y ↔ y ≤ x := not_le_lf.2
theorem lf.not_ge {x y : pgame} : x ⧏ y → ¬ y ≤ x := pgame.not_le.2
theorem _root_.has_le.le.not_gf {x y : pgame} : x ≤ y → ¬ y ⧏ x := not_lf.2

theorem le_or_gf (x y : pgame) : x ≤ y ∨ y ⧏ x :=
by { rw ←pgame.not_le, exact em _ }

theorem move_left_lf_of_le {x y : pgame} (i) : x ≤ y → x.move_left i ⧏ y :=
by { cases x, cases y, rw mk_le_mk, tauto }

theorem lf_move_right_of_le {x y : pgame} (j) : x ≤ y → x ⧏ y.move_right j :=
by { cases x, cases y, rw mk_le_mk, tauto }

theorem lf_of_move_right_le {x y : pgame} {j} : x.move_right j ≤ y → x ⧏ y :=
by { cases x, cases y, rw mk_lf_mk, tauto }

theorem lf_of_le_move_left {x y : pgame} {i} : x ≤ y.move_left i → x ⧏ y :=
by { cases x, cases y, rw mk_lf_mk, exact λ h, or.inl ⟨_, h⟩ }

theorem lf_of_le_mk {xl xr xL xR y} : ∀ i, mk xl xr xL xR ≤ y → xL i ⧏ y :=
@move_left_lf_of_le (mk _ _ _ _) y

theorem lf_of_mk_le {x yl yr yL yR} : ∀ j, x ≤ mk yl yr yL yR → x ⧏ yR j :=
@lf_move_right_of_le x (mk _ _ _ _)

theorem mk_lf_of_le {xl xr y j} (xL) {xR : xr → pgame} : xR j ≤ y → mk xl xr xL xR ⧏ y :=
@lf_of_move_right_le (mk _ _ _ _) y j

theorem lf_mk_of_le {x yl yr} {yL : yl → pgame} (yR) {i} : x ≤ yL i → x ⧏ mk yl yr yL yR :=
@lf_of_le_move_left x (mk _ _ _ _) i

private theorem le_trans_aux
  {xl xr} {xL : xl → pgame} {xR : xr → pgame}
  {yl yr} {yL : yl → pgame} {yR : yr → pgame}
  {zl zr} {zL : zl → pgame} {zR : zr → pgame}
  (h₁ : ∀ i, mk yl yr yL yR ≤ mk zl zr zL zR → mk zl zr zL zR ≤ xL i → mk yl yr yL yR ≤ xL i)
  (h₂ : ∀ j, zR j ≤ mk xl xr xL xR → mk xl xr xL xR ≤ mk yl yr yL yR → zR j ≤ mk yl yr yL yR) :
  mk xl xr xL xR ≤ mk yl yr yL yR →
  mk yl yr yL yR ≤ mk zl zr zL zR →
  mk xl xr xL xR ≤ mk zl zr zL zR :=
begin
  simp only [mk_le_mk] at *,
  exact
    λ ⟨xLy, xyR⟩ ⟨yLz, yzR⟩, ⟨
      λ i, pgame.not_le.1 (λ h, (h₁ i ⟨yLz, yzR⟩ h).not_gf (xLy i)),
      λ j, pgame.not_le.1 (λ h, (h₂ j h ⟨xLy, xyR⟩).not_gf (yzR j))⟩
end

private theorem le_refl (x : pgame) : x ≤ x :=
begin
  induction x with l r L R ih₁ ih₂,
  exact le_of_forall_lf ⟨λ i, lf_of_le_move_left (ih₁ i), λ j, lf_of_move_right_le (ih₂ j)⟩
end

private theorem le_trans : ∀ x y z : pgame, x ≤ y → y ≤ z → x ≤ z :=
begin
  suffices : ∀ {x y z : pgame},
    (x ≤ y → y ≤ z → x ≤ z) ∧ (y ≤ z → z ≤ x → y ≤ x) ∧ (z ≤ x → x ≤ y → z ≤ y),
  { exact λ x y z, this.1 },
  intros x y z,
  induction x with xl xr xL xR IHxl IHxr generalizing y z,
  induction y with yl yr yL yR IHyl IHyr generalizing z,
  induction z with zl zr zL zR IHzl IHzr,
  exact ⟨
    le_trans_aux (λ i, (IHxl i).2.1) (λ j, (IHzr j).2.2),
    le_trans_aux (λ i, (IHyl i).2.2) (λ j, (IHxr j).1),
    le_trans_aux (λ i, (IHzl i).1) (λ j, (IHyr j).2.1)⟩,
end

instance : preorder pgame :=
{ le_refl := le_refl,
  le_trans := le_trans,
  ..pgame.has_le }

theorem lf_irrefl (x : pgame) : ¬ x ⧏ x := le_rfl.not_gf
instance : is_irrefl _ (⧏) := ⟨lf_irrefl⟩


@[trans] theorem lf_of_le_of_lf {x y z : pgame} (h₁ : x ≤ y) (h₂ : y ⧏ z) : x ⧏ z :=
by { rw ←pgame.not_le at h₂ ⊢, exact λ h₃, h₂ (h₃.trans h₁) }
@[trans] theorem lf_of_lf_of_le {x y z : pgame} (h₁ : x ⧏ y) (h₂ : y ≤ z) : x ⧏ z :=
by { rw ←pgame.not_le at h₁ ⊢, exact λ h₃, h₁ (h₂.trans h₃) }

alias lf_of_le_of_lf ← has_le.le.trans_lf
alias lf_of_lf_of_le ← pgame.lf.trans_le

@[trans] theorem lf_of_lt_of_lf {x y z : pgame} (h₁ : x < y) (h₂ : y ⧏ z) : x ⧏ z :=
h₁.le.trans_lf h₂

@[trans] theorem lf_of_lf_of_lt {x y z : pgame} (h₁ : x ⧏ y) (h₂ : y < z) : x ⧏ z :=
h₁.trans_le h₂.le

alias lf_of_lt_of_lf ← has_lt.lt.trans_lf
alias lf_of_lf_of_lt ← pgame.lf.trans_lt

theorem move_left_lf {x : pgame} (i) : x.move_left i ⧏ x :=
move_left_lf_of_le i le_rfl

theorem lf_move_right {x : pgame} (j) : x ⧏ x.move_right j :=
lf_move_right_of_le j le_rfl

theorem lf_mk {xl xr} (xL : xl → pgame) (xR : xr → pgame) (i) : xL i ⧏ mk xl xr xL xR :=
@move_left_lf (mk _ _ _ _) i

theorem mk_lf {xl xr} (xL : xl → pgame) (xR : xr → pgame) (j) : mk xl xr xL xR ⧏ xR j :=
@lf_move_right (mk _ _ _ _) j

theorem lt_iff_le_and_lf {x y : pgame} : x < y ↔ x ≤ y ∧ x ⧏ y :=
by rw [lt_iff_le_not_le, pgame.not_le]

theorem lt_of_le_of_lf {x y : pgame} (h₁ : x ≤ y) (h₂ : x ⧏ y) : x < y :=
lt_iff_le_and_lf.2 ⟨h₁, h₂⟩

theorem lf_of_lt {x y : pgame} (h : x < y) : x ⧏ y := (lt_iff_le_and_lf.1 h).2
alias lf_of_lt ← has_lt.lt.lf

theorem le_of_forall_lt {x y : pgame} (h : (∀ i, x.move_left i < y) ∧ ∀ j, x < y.move_right j) :
  x ≤ y :=
le_of_forall_lf ⟨λ i, (h.1 i).lf, λ i, (h.2 i).lf⟩

theorem le_def {x y : pgame} : x ≤ y ↔
  (∀ i, (∃ i', x.move_left i ≤ y.move_left i')  ∨ ∃ j, (x.move_left i).move_right j ≤ y) ∧
   ∀ j, (∃ i, x ≤ (y.move_right j).move_left i) ∨ ∃ j', x.move_right j' ≤ y.move_right j :=
by { rw le_iff_forall_lf, conv { to_lhs, simp only [lf_iff_exists_le] } }

theorem lf_def {x y : pgame} : x ⧏ y ↔
  (∃ i, (∀ i', x.move_left i' ⧏ y.move_left i)  ∧ ∀ j, x ⧏ (y.move_left i).move_right j) ∨
   ∃ j, (∀ i, (x.move_right j).move_left i ⧏ y) ∧ ∀ j', x.move_right j ⧏ y.move_right j' :=
by { rw lf_iff_exists_le, conv { to_lhs, simp only [le_iff_forall_lf] } }

theorem zero_le_lf {x : pgame} : 0 ≤ x ↔ ∀ j, 0 ⧏ x.move_right j :=
by { rw le_iff_forall_lf, dsimp, simp }

theorem le_zero_lf {x : pgame} : x ≤ 0 ↔ ∀ i, x.move_left i ⧏ 0 :=
by { rw le_iff_forall_lf, dsimp, simp }

theorem zero_lf_le {x : pgame} : 0 ⧏ x ↔ ∃ i, 0 ≤ x.move_left i :=
by { rw lf_iff_exists_le, dsimp, simp }

theorem lf_zero_le {x : pgame} : x ⧏ 0 ↔ ∃ j, x.move_right j ≤ 0 :=
by { rw lf_iff_exists_le, dsimp, simp }

theorem zero_le {x : pgame} : 0 ≤ x ↔ ∀ j, ∃ i, 0 ≤ (x.move_right j).move_left i :=
by { rw le_def, dsimp, simp }

theorem le_zero {x : pgame} : x ≤ 0 ↔ ∀ i, ∃ j, (x.move_left i).move_right j ≤ 0 :=
by { rw le_def, dsimp, simp }

theorem zero_lf {x : pgame} : 0 ⧏ x ↔ ∃ i, ∀ j, 0 ⧏ (x.move_left i).move_right j :=
by { rw lf_def, dsimp, simp }

theorem lf_zero {x : pgame} : x ⧏ 0 ↔ ∃ j, ∀ i, (x.move_right j).move_left i ⧏ 0 :=
by { rw lf_def, dsimp, simp }

@[simp] theorem zero_le_of_is_empty_right_moves (x : pgame) [is_empty x.right_moves] : 0 ≤ x :=
zero_le.2 is_empty_elim

@[simp] theorem le_zero_of_is_empty_left_moves (x : pgame) [is_empty x.left_moves] : x ≤ 0 :=
le_zero.2 is_empty_elim

noncomputable def right_response {x : pgame} (h : x ≤ 0) (i : x.left_moves) :
  (x.move_left i).right_moves :=
classical.some $ (le_zero.1 h) i

lemma right_response_spec {x : pgame} (h : x ≤ 0) (i : x.left_moves) :
  (x.move_left i).move_right (right_response h i) ≤ 0 :=
classical.some_spec $ (le_zero.1 h) i

noncomputable def left_response {x : pgame} (h : 0 ≤ x) (j : x.right_moves) :
  (x.move_right j).left_moves :=
classical.some $ (zero_le.1 h) j

lemma left_response_spec {x : pgame} (h : 0 ≤ x) (j : x.right_moves) :
  0 ≤ (x.move_right j).move_left (left_response h j) :=
classical.some_spec $ (zero_le.1 h) j

def equiv (x y : pgame) : Prop := x ≤ y ∧ y ≤ x

local infix ` ≈ ` := pgame.equiv

instance : is_equiv _ (≈) :=
{ refl := λ x, ⟨le_rfl, le_rfl⟩,
  trans := λ x y z ⟨xy, yx⟩ ⟨yz, zy⟩, ⟨xy.trans yz, zy.trans yx⟩,
  symm := λ x y, and.symm }

theorem equiv.le {x y : pgame} (h : x ≈ y) : x ≤ y := h.1
theorem equiv.ge {x y : pgame} (h : x ≈ y) : y ≤ x := h.2

@[refl, simp] theorem equiv_rfl {x} : x ≈ x := refl x
theorem equiv_refl (x) : x ≈ x := refl x
@[symm] protected theorem equiv.symm {x y} : x ≈ y → y ≈ x := symm
@[trans] protected theorem equiv.trans {x y z} : x ≈ y → y ≈ z → x ≈ z := trans

theorem equiv_of_eq {x y} (h : x = y) : x ≈ y := by rw h

@[trans] theorem le_of_le_of_equiv {x y z} (h₁ : x ≤ y) (h₂ : y ≈ z) : x ≤ z := h₁.trans h₂.1
@[trans] theorem le_of_equiv_of_le {x y z} (h₁ : x ≈ y) : y ≤ z → x ≤ z := h₁.1.trans

theorem lf.not_equiv {x y} (h : x ⧏ y) : ¬ x ≈ y := λ h', h.not_ge h'.2
theorem lf.not_equiv' {x y} (h : x ⧏ y) : ¬ y ≈ x := λ h', h.not_ge h'.1

theorem lf.not_gt {x y} (h : x ⧏ y) : ¬ y < x := λ h', h.not_ge h'.le

theorem le_congr_imp {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ ≤ y₁) : x₂ ≤ y₂ :=
hx.2.trans (h.trans hy.1)
theorem le_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ≤ y₁ ↔ x₂ ≤ y₂ :=
⟨le_congr_imp hx hy, le_congr_imp hx.symm hy.symm⟩
theorem le_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ ≤ y ↔ x₂ ≤ y :=
le_congr hx equiv_rfl
theorem le_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x ≤ y₁ ↔ x ≤ y₂ :=
le_congr equiv_rfl hy

theorem lf_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ ↔ x₂ ⧏ y₂ :=
pgame.not_le.symm.trans $ (not_congr (le_congr hy hx)).trans pgame.not_le
theorem lf_congr_imp {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ⧏ y₁ → x₂ ⧏ y₂ :=
(lf_congr hx hy).1
theorem lf_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ ⧏ y ↔ x₂ ⧏ y :=
lf_congr hx equiv_rfl
theorem lf_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x ⧏ y₁ ↔ x ⧏ y₂ :=
lf_congr equiv_rfl hy

@[trans] theorem lf_of_lf_of_equiv {x y z} (h₁ : x ⧏ y) (h₂ : y ≈ z) : x ⧏ z :=
lf_congr_imp equiv_rfl h₂ h₁
@[trans] theorem lf_of_equiv_of_lf {x y z} (h₁ : x ≈ y) : y ⧏ z → x ⧏ z :=
lf_congr_imp h₁.symm equiv_rfl

@[trans] theorem lt_of_lt_of_equiv {x y z} (h₁ : x < y) (h₂ : y ≈ z) : x < z := h₁.trans_le h₂.1
@[trans] theorem lt_of_equiv_of_lt {x y z} (h₁ : x ≈ y) : y < z → x < z := h₁.1.trans_lt

theorem lt_congr_imp {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) (h : x₁ < y₁) : x₂ < y₂ :=
hx.2.trans_lt (h.trans_le hy.1)
theorem lt_congr {x₁ y₁ x₂ y₂} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ < y₁ ↔ x₂ < y₂ :=
⟨lt_congr_imp hx hy, lt_congr_imp hx.symm hy.symm⟩
theorem lt_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ < y ↔ x₂ < y :=
lt_congr hx equiv_rfl
theorem lt_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x < y₁ ↔ x < y₂ :=
lt_congr equiv_rfl hy

theorem lf_or_equiv_of_le {x y : pgame} (h : x ≤ y) : x ⧏ y ∨ x ≈ y :=
or_iff_not_imp_left.2 $ λ h', ⟨h, pgame.not_lf.1 h'⟩

theorem lf_or_equiv_or_gf (x y : pgame) : x ⧏ y ∨ x ≈ y ∨ y ⧏ x :=
begin
  by_cases h : x ⧏ y,
  { exact or.inl h },
  { right,
    cases (lf_or_equiv_of_le (pgame.not_lf.1 h)) with h' h',
    { exact or.inr h' },
    { exact or.inl h'.symm } }
end

theorem equiv_congr_left {y₁ y₂} : y₁ ≈ y₂ ↔ ∀ x₁, x₁ ≈ y₁ ↔ x₁ ≈ y₂ :=
⟨λ h x₁, ⟨λ h', h'.trans h, λ h', h'.trans h.symm⟩,
 λ h, (h y₁).1 $ equiv_rfl⟩

theorem equiv_congr_right {x₁ x₂} : x₁ ≈ x₂ ↔ ∀ y₁, x₁ ≈ y₁ ↔ x₂ ≈ y₁ :=
⟨λ h y₁, ⟨λ h', h.symm.trans h', λ h', h.trans h'⟩,
 λ h, (h x₂).2 $ equiv_rfl⟩

theorem equiv_of_mk_equiv {x y : pgame}
  (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves)
  (hl : ∀ (i : x.left_moves), x.move_left i ≈ y.move_left (L i))
  (hr : ∀ (j : y.right_moves), x.move_right (R.symm j) ≈ y.move_right j) :
  x ≈ y :=
begin
  split; rw le_def,
  { exact ⟨λ i, or.inl ⟨L i, (hl i).1⟩, λ j, or.inr ⟨R.symm j, (hr j).1⟩⟩ },
  { split,
    { intro i,
      left,
      specialize hl (L.symm i),
      simp only [move_left_mk, equiv.apply_symm_apply] at hl,
      use ⟨L.symm i, hl.2⟩ },
    { intro j,
      right,
      specialize hr (R j),
      simp only [move_right_mk, equiv.symm_apply_apply] at hr,
      use ⟨R j, hr.2⟩ } }
end

def fuzzy (x y : pgame) : Prop := x ⧏ y ∧ y ⧏ x

local infix ` ∥ `:50 := fuzzy

@[symm] theorem fuzzy.swap {x y : pgame} : x ∥ y → y ∥ x := and.swap
instance : is_symm _ (∥) := ⟨λ x y, fuzzy.swap⟩
theorem fuzzy.swap_iff {x y : pgame} : x ∥ y ↔ y ∥ x := ⟨fuzzy.swap, fuzzy.swap⟩

theorem fuzzy_irrefl (x : pgame) : ¬ x ∥ x := λ h, lf_irrefl x h.1
instance : is_irrefl _ (∥) := ⟨fuzzy_irrefl⟩

theorem lf_iff_lt_or_fuzzy {x y : pgame} : x ⧏ y ↔ x < y ∨ x ∥ y :=
by { simp only [lt_iff_le_and_lf, fuzzy, ←pgame.not_le], tauto! }

theorem lf_of_fuzzy {x y : pgame} (h : x ∥ y) : x ⧏ y := lf_iff_lt_or_fuzzy.2 (or.inr h)
alias lf_of_fuzzy ← pgame.fuzzy.lf

theorem lt_or_fuzzy_of_lf {x y : pgame} : x ⧏ y → x < y ∨ x ∥ y :=
lf_iff_lt_or_fuzzy.1

theorem fuzzy.not_equiv {x y : pgame} (h : x ∥ y) : ¬ x ≈ y :=
λ h', h'.1.not_gf h.2
theorem fuzzy.not_equiv' {x y : pgame} (h : x ∥ y) : ¬ y ≈ x :=
λ h', h'.2.not_gf h.2

theorem not_fuzzy_of_le {x y : pgame} (h : x ≤ y) : ¬ x ∥ y :=
λ h', h'.2.not_ge h
theorem not_fuzzy_of_ge {x y : pgame} (h : y ≤ x) : ¬ x ∥ y :=
λ h', h'.1.not_ge h

theorem equiv.not_fuzzy {x y : pgame} (h : x ≈ y) : ¬ x ∥ y :=
not_fuzzy_of_le h.1
theorem equiv.not_fuzzy' {x y : pgame} (h : x ≈ y) : ¬ y ∥ x :=
not_fuzzy_of_le h.2

theorem fuzzy_congr {x₁ y₁ x₂ y₂ : pgame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ∥ y₁ ↔ x₂ ∥ y₂ :=
show _ ∧ _ ↔ _ ∧ _, by rw [lf_congr hx hy, lf_congr hy hx]
theorem fuzzy_congr_imp {x₁ y₁ x₂ y₂ : pgame} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ ∥ y₁ → x₂ ∥ y₂ :=
(fuzzy_congr hx hy).1
theorem fuzzy_congr_left {x₁ x₂ y} (hx : x₁ ≈ x₂) : x₁ ∥ y ↔ x₂ ∥ y :=
fuzzy_congr hx equiv_rfl
theorem fuzzy_congr_right {x y₁ y₂} (hy : y₁ ≈ y₂) : x ∥ y₁ ↔ x ∥ y₂ :=
fuzzy_congr equiv_rfl hy

@[trans] theorem fuzzy_of_fuzzy_of_equiv {x y z} (h₁ : x ∥ y) (h₂ : y ≈ z) : x ∥ z :=
(fuzzy_congr_right h₂).1 h₁
@[trans] theorem fuzzy_of_equiv_of_fuzzy {x y z} (h₁ : x ≈ y) (h₂ : y ∥ z) : x ∥ z :=
(fuzzy_congr_left h₁).2 h₂

theorem lt_or_equiv_or_gt_or_fuzzy (x y : pgame) : x < y ∨ x ≈ y ∨ y < x ∨ x ∥ y :=
begin
  cases le_or_gf x y with h₁ h₁;
  cases le_or_gf y x with h₂ h₂,
  { right, left, exact ⟨h₁, h₂⟩ },
  { left, exact lt_of_le_of_lf h₁ h₂ },
  { right, right, left, exact lt_of_le_of_lf h₂ h₁ },
  { right, right, right, exact ⟨h₂, h₁⟩ }
end

theorem lt_or_equiv_or_gf (x y : pgame) : x < y ∨ x ≈ y ∨ y ⧏ x :=
begin
  rw [lf_iff_lt_or_fuzzy, fuzzy.swap_iff],
  exact lt_or_equiv_or_gt_or_fuzzy x y
end

inductive restricted : pgame → pgame → Type 1
| mk : Π {x y : pgame} (L : x.left_moves → y.left_moves) (R : y.right_moves → x.right_moves),
         (∀ i, restricted (x.move_left i) (y.move_left (L i))) →
         (∀ j, restricted (x.move_right (R j)) (y.move_right j)) → restricted x y

@[refl] def restricted.refl : Π (x : pgame), restricted x x
| ⟨xl, xr, xL, xR⟩ := ⟨_, _, λ i, restricted.refl _, λ j, restricted.refl _⟩
using_well_founded { dec_tac := dec_tac }

instance (x : pgame) : inhabited (restricted x x) := ⟨restricted.refl _⟩

def restricted.trans : Π {x y z : pgame} (r : restricted x y) (s : restricted y z),
  restricted x z
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ⟨zl, zr, zL, zR⟩ ⟨L₁, R₁, hL₁, hR₁⟩ ⟨L₂, R₂, hL₂, hR₂⟩ :=
⟨_, _, λ i, (hL₁ i).trans (hL₂ _), λ j, (hR₁ _).trans (hR₂ j)⟩

theorem restricted.le : Π {x y : pgame} (r : restricted x y), x ≤ y
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ⟨L, R, hL, hR⟩ :=
le_def.2 ⟨λ i, or.inl ⟨L i, (hL i).le⟩, λ i, or.inr ⟨R i, (hR i).le⟩⟩

inductive relabelling : pgame → pgame → Type 1
| mk : Π {x y : pgame} (L : x.left_moves ≃ y.left_moves) (R : x.right_moves ≃ y.right_moves),
         (∀ i, relabelling (x.move_left i) (y.move_left (L i))) →
         (∀ j, relabelling (x.move_right (R.symm j)) (y.move_right j)) →
       relabelling x y

local infix ` ≡r `:50 := relabelling

def relabelling.restricted : Π {x y : pgame} (r : x ≡r y), restricted x y
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ⟨L, R, hL, hR⟩ :=
⟨L, R.symm, λ i, (hL i).restricted, λ j, (hR j).restricted⟩

@[refl] def relabelling.refl : Π (x : pgame), x ≡r x
| ⟨xl, xr, xL, xR⟩ := ⟨equiv.refl _, equiv.refl _, λ i, relabelling.refl _, λ j, relabelling.refl _⟩
using_well_founded { dec_tac := dec_tac }

instance (x : pgame) : inhabited (x ≡r x) := ⟨relabelling.refl _⟩

@[symm] def relabelling.symm : Π {x y : pgame}, x ≡r y → y ≡r x
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ⟨L, R, hL, hR⟩ :=
⟨L.symm, R.symm, λ i, by simpa using (hL (L.symm i)).symm, λ j, by simpa using (hR (R j)).symm⟩

theorem relabelling.le {x y : pgame} (r : x ≡r y) : x ≤ y := r.restricted.le
theorem relabelling.ge {x y : pgame} (r : x ≡r y) : y ≤ x := r.symm.restricted.le

theorem relabelling.equiv {x y : pgame} (r : x ≡r y) : x ≈ y := ⟨r.le, r.ge⟩

@[trans] def relabelling.trans : Π {x y z : pgame}, x ≡r y → y ≡r z → x ≡r z
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ⟨zl, zr, zL, zR⟩ ⟨L₁, R₁, hL₁, hR₁⟩ ⟨L₂, R₂, hL₂, hR₂⟩ :=
⟨L₁.trans L₂, R₁.trans R₂,
  λ i, by simpa using (hL₁ i).trans (hL₂ _), λ j, by simpa using (hR₁ _).trans (hR₂ j)⟩

def relabelling.is_empty (x : pgame) [is_empty x.left_moves] [is_empty x.right_moves] : x ≡r 0 :=
⟨equiv.equiv_pempty _, equiv.equiv_pempty _, is_empty_elim, is_empty_elim⟩

theorem equiv.is_empty (x : pgame) [is_empty x.left_moves] [is_empty x.right_moves] : x ≈ 0 :=
(relabelling.is_empty x).equiv

instance {x y : pgame} : has_coe (x ≡r y) (x ≈ y) := ⟨relabelling.equiv⟩

def relabel {x : pgame} {xl' xr'} (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') : pgame :=
⟨xl', xr', λ i, x.move_left (el.symm i), λ j, x.move_right (er.symm j)⟩

@[simp] lemma relabel_move_left' {x : pgame} {xl' xr'}
  (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') (i : xl') :
  move_left (relabel el er) i = x.move_left (el.symm i) :=
rfl
@[simp] lemma relabel_move_left {x : pgame} {xl' xr'}
  (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') (i : x.left_moves) :
  move_left (relabel el er) (el i) = x.move_left i :=
by simp

@[simp] lemma relabel_move_right' {x : pgame} {xl' xr'}
  (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') (j : xr') :
  move_right (relabel el er) j = x.move_right (er.symm j) :=
rfl
@[simp] lemma relabel_move_right {x : pgame} {xl' xr'}
  (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') (j : x.right_moves) :
  move_right (relabel el er) (er j) = x.move_right j :=
by simp

def relabel_relabelling {x : pgame} {xl' xr'} (el : x.left_moves ≃ xl') (er : x.right_moves ≃ xr') :
  x ≡r relabel el er :=
relabelling.mk el er (λ i, by simp) (λ j, by simp)

def neg : pgame → pgame
| ⟨l, r, L, R⟩ := ⟨r, l, λ i, neg (R i), λ i, neg (L i)⟩

instance : has_neg pgame := ⟨neg⟩

@[simp] lemma neg_def {xl xr xL xR} : -(mk xl xr xL xR) = mk xr xl (λ j, -(xR j)) (λ i, -(xL i)) :=
rfl

private theorem neg_neg_impl (x : pgame) : - -x = x :=
begin
  induction x with l r L R IHl IHr,
  change ∀ i, - -L i = L i at IHl,
  change ∀ j, - -R j = R j at IHr,
  simp [IHl, IHr]
end

instance : has_involutive_neg pgame :=
{ neg_neg := neg_neg_impl, ..pgame.has_neg }

@[simp] protected lemma neg_zero : -(0 : pgame) = 0 :=
begin
  dsimp [has_zero.zero, has_neg.neg, neg],
  congr; funext i; cases i
end

theorem left_moves_neg : ∀ x : pgame, (-x).left_moves = x.right_moves
| ⟨_, _, _, _⟩ := rfl

theorem right_moves_neg : ∀ x : pgame, (-x).right_moves = x.left_moves
| ⟨_, _, _, _⟩ := rfl

def to_left_moves_neg {x : pgame} : x.right_moves ≃ (-x).left_moves :=
equiv.cast (left_moves_neg x).symm

def to_right_moves_neg {x : pgame} : x.left_moves ≃ (-x).right_moves :=
equiv.cast (right_moves_neg x).symm

lemma move_left_neg {x : pgame} (i) :
  (-x).move_left (to_left_moves_neg i) = -x.move_right i :=
by { cases x, refl }

@[simp] lemma move_left_neg' {x : pgame} (i) :
  (-x).move_left i = -x.move_right (to_left_moves_neg.symm i) :=
by { cases x, refl }

lemma move_right_neg {x : pgame} (i) :
  (-x).move_right (to_right_moves_neg i) = -(x.move_left i) :=
by { cases x, refl }

@[simp] lemma move_right_neg' {x : pgame} (i) :
  (-x).move_right i = -x.move_left (to_right_moves_neg.symm i) :=
by { cases x, refl }

lemma move_left_neg_symm {x : pgame} (i) :
  x.move_left (to_right_moves_neg.symm i) = -(-x).move_right i :=
by simp

lemma move_left_neg_symm' {x : pgame} (i) :
  x.move_left i = -(-x).move_right (to_right_moves_neg i) :=
by simp

lemma move_right_neg_symm {x : pgame} (i) :
  x.move_right (to_left_moves_neg.symm i) = -(-x).move_left i :=
by simp

lemma move_right_neg_symm' {x : pgame} (i) :
  x.move_right i = -(-x).move_left (to_left_moves_neg i) :=
by simp

def relabelling.neg_congr : ∀ {x y : pgame}, x ≡r y → -x ≡r -y
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ⟨L, R, hL, hR⟩ :=
  ⟨R, L,
    λ i, relabelling.neg_congr (by simpa using hR (R i)),
    λ j, relabelling.neg_congr (by simpa using hL (L.symm j))⟩

example (x y : pgame) : (-y ≤ -x ↔ x ≤ y) ∧ (-y ⧏ -x ↔ x ⧏ y) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  change ∀ i y, _ at IHxl,
  change ∀ j y, _ at IHxr,
  induction y with yl yr yL yR IHyl IHyr,
  change ∀ i, (-yL i ≤ -_ ↔ _ ≤ yL i) ∧ (-yL i ⧏ -_ ↔ _ ⧏ yL i) at IHyl,
  change ∀ j, (-yR j ≤ -_ ↔ _ ≤ yR j) ∧ (-yR j ⧏ -_ ↔ _ ⧏ yR j) at IHyr,
  simp only [neg_def],
  simp only [mk_le_mk, mk_lf_mk],
  simp only [←neg_def],
  set x := mk xl xr xL xR,
  set y := mk yl yr yL yR,
  refine ⟨⟨_, _⟩, ⟨_, _⟩⟩,
  { exact λ h, ⟨λ i, (IHxl i y).2.1 (h.2 i), λ j, (IHyr j).2.1 (h.1 j)⟩ },
  { exact λ h, ⟨λ j, (IHyr j).2.2 (h.2 j), λ i, (IHxl i y).2.2 (h.1 i)⟩ },
  { intro h, cases h with h h,
    { cases h with j h, exact or.inr ⟨j, (IHxr j y).1.1 h⟩ },
    { cases h with i h, exact or.inl ⟨i, (IHyl i).1.1 h⟩ } },
  { intro h, cases h with h h,
    { cases h with i h, exact or.inr ⟨i, (IHyl i).1.2 h⟩ },
    { cases h with j h, exact or.inl ⟨j, (IHxr j y).1.2 h⟩ } }
end

private theorem neg_le_lf_neg_iff :
  Π {x y : pgame}, (-y ≤ -x ↔ x ≤ y) ∧ (-y ⧏ -x ↔ x ⧏ y)
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  simp_rw [neg_def, mk_le_mk, mk_lf_mk, ← neg_def],
  split,
  { rw and_comm, apply and_congr; exact forall_congr (λ _, neg_le_lf_neg_iff.2) },
  { rw or_comm, apply or_congr; exact exists_congr (λ _, neg_le_lf_neg_iff.1) },
end
using_well_founded { dec_tac := dec_tac }

@[simp] theorem neg_le_neg_iff {x y : pgame} : -y ≤ -x ↔ x ≤ y := neg_le_lf_neg_iff.1

@[simp] theorem neg_lf_neg_iff {x y : pgame} : -y ⧏ -x ↔ x ⧏ y := neg_le_lf_neg_iff.2

@[simp] theorem neg_lt_neg_iff {x y : pgame} : -y < -x ↔ x < y :=
by rw [lt_iff_le_and_lf, lt_iff_le_and_lf, neg_le_neg_iff, neg_lf_neg_iff]

@[simp] theorem neg_equiv_neg_iff {x y : pgame} : -x ≈ -y ↔ x ≈ y :=
by rw [equiv, equiv, neg_le_neg_iff, neg_le_neg_iff, and.comm]

@[simp] theorem neg_fuzzy_neg_iff {x y : pgame} : -x ∥ -y ↔ x ∥ y :=
by rw [fuzzy, fuzzy, neg_lf_neg_iff, neg_lf_neg_iff, and.comm]

theorem neg_le_iff {x y : pgame} : -y ≤ x ↔ -x ≤ y :=
by rw [←neg_neg x, neg_le_neg_iff, neg_neg]

theorem neg_lf_iff {x y : pgame} : -y ⧏ x ↔ -x ⧏ y :=
by rw [←neg_neg x, neg_lf_neg_iff, neg_neg]

theorem neg_lt_iff {x y : pgame} : -y < x ↔ -x < y :=
by rw [←neg_neg x, neg_lt_neg_iff, neg_neg]

theorem neg_equiv_iff {x y : pgame} : -x ≈ y ↔ x ≈ -y :=
by rw [←neg_neg y, neg_equiv_neg_iff, neg_neg]

theorem neg_fuzzy_iff {x y : pgame} : -x ∥ y ↔ x ∥ -y :=
by rw [←neg_neg y, neg_fuzzy_neg_iff, neg_neg]

theorem le_neg_iff {x y : pgame} : y ≤ -x ↔ x ≤ -y :=
by rw [←neg_neg x, neg_le_neg_iff, neg_neg]

theorem lf_neg_iff {x y : pgame} : y ⧏ -x ↔ x ⧏ -y :=
by rw [←neg_neg x, neg_lf_neg_iff, neg_neg]

theorem lt_neg_iff {x y : pgame} : y < -x ↔ x < -y :=
by rw [←neg_neg x, neg_lt_neg_iff, neg_neg]

@[simp] theorem neg_le_zero_iff {x : pgame} : -x ≤ 0 ↔ 0 ≤ x :=
by rw [neg_le_iff, pgame.neg_zero]

@[simp] theorem zero_le_neg_iff {x : pgame} : 0 ≤ -x ↔ x ≤ 0 :=
by rw [le_neg_iff, pgame.neg_zero]

@[simp] theorem neg_lf_zero_iff {x : pgame} : -x ⧏ 0 ↔ 0 ⧏ x :=
by rw [neg_lf_iff, pgame.neg_zero]

@[simp] theorem zero_lf_neg_iff {x : pgame} : 0 ⧏ -x ↔ x ⧏ 0 :=
by rw [lf_neg_iff, pgame.neg_zero]

@[simp] theorem neg_lt_zero_iff {x : pgame} : -x < 0 ↔ 0 < x :=
by rw [neg_lt_iff, pgame.neg_zero]

@[simp] theorem zero_lt_neg_iff {x : pgame} : 0 < -x ↔ x < 0 :=
by rw [lt_neg_iff, pgame.neg_zero]

@[simp] theorem neg_equiv_zero_iff {x : pgame} : -x ≈ 0 ↔ x ≈ 0 :=
by rw [neg_equiv_iff, pgame.neg_zero]

@[simp] theorem neg_fuzzy_zero_iff {x : pgame} : -x ∥ 0 ↔ x ∥ 0 :=
by rw [neg_fuzzy_iff, pgame.neg_zero]

@[simp] theorem zero_equiv_neg_iff {x : pgame} : 0 ≈ -x ↔ 0 ≈ x :=
by rw [←neg_equiv_iff, pgame.neg_zero]

@[simp] theorem zero_fuzzy_neg_iff {x : pgame} : 0 ∥ -x ↔ 0 ∥ x :=
by rw [←neg_fuzzy_iff, pgame.neg_zero]

def add : pgame → pgame → pgame
| x@(mk xl xr xL xR) y@(mk yl yr yL yR) :=
⟨xl ⊕ yl, xr ⊕ yr,
 @sum.rec xl yl (λ _, pgame) (λ i, add (xL i) y) (λ i, add x (yL i)),
 @sum.rec xr yr (λ _, pgame) (λ j, add (xR j) y) (λ j, add x (yR j))⟩
using_well_founded { dec_tac := dec_tac }

def add' : pgame → pgame → pgame :=
begin
  intros x y,
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  change xl → pgame → pgame at IHxl,
  change xr → pgame → pgame at IHxr,
  induction y with yl yr yL yR IHyl IHyr,
  change yl → pgame at IHyl,
  change yr → pgame at IHyr,
  let y := mk yl yr yL yR,
  refine ⟨xl ⊕ yl, xr ⊕ yr, sum.rec _ _, sum.rec _ _⟩,
  { exact λ i, IHxl i y },
  { exact IHyl },
  { exact λ j, IHxr j y },
  { exact IHyr }
end

example (x y : pgame) : add x y = add' x y :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  change ∀ i y, add (xL i) y = add' (xL i) y at IHxl,
  change ∀ j y, add (xR j) y = add' (xR j) y at IHxr,
  let x := mk xl xr xL xR,
  induction y with yl yr yL yR IHyl IHyr,
  change ∀ i, add x (yL i) = add' x (yL i) at IHyl,
  change ∀ j, add x (yR j) = add' x (yR j) at IHyr,
  let y := mk yl yr yL yR,
  let sum.rec' := λ {α β}, @sum.rec α β (λ _, pgame),
  have : sum.rec' (λ i, add (xL i) y) (λ i, add x (yL i))
       = sum.rec' (λ i, add' (xL i) y) (λ i, add' x (yL i)),
  { congr; simp [IHxl, IHyl] },
  have : sum.rec' (λ j, add (xR j) y) (λ j, add x (yR j))
       = sum.rec' (λ j, add' (xR j) y) (λ j, add' x (yR j)),
  { congr; simp [IHxr, IHyr] },
  simp [add, add', *]
end

instance : has_add pgame := ⟨λ x y, begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  induction y with yl yr yL yR IHyl IHyr,
  have y := mk yl yr yL yR,
  refine ⟨xl ⊕ yl, xr ⊕ yr, sum.rec _ _, sum.rec _ _⟩,
  { exact λ i, IHxl i y },
  { exact IHyl },
  { exact λ i, IHxr i y },
  { exact IHyr }
end⟩

example (x y : pgame) : add x y = x + y :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y,
  change ∀ i y, add (xL i) y = xL i + y at IHxl,
  change ∀ j y, add (xR j) y = xR j + y at IHxr,
  let x := mk xl xr xL xR,
  induction y with yl yr yL yR IHyl IHyr,
  change ∀ i, add x (yL i) = x + yL i at IHyl,
  change ∀ j, add x (yR j) = x + yR j at IHyr,
  let y := mk yl yr yL yR,
  let sum.rec' := λ {α β}, @sum.rec α β (λ _, pgame),
  have : sum.rec' (λ i, add (xL i) y) (λ i, add x (yL i))
       = sum.rec' (λ i, xL i + y) (λ i, x + yL i),
  { congr; simp [IHxl, IHyl] },
  have : sum.rec' (λ j, add (xR j) y) (λ j, add x (yR j))
       = sum.rec' (λ j, xR j + y) (λ j, x + yR j),
  { congr; simp [IHxr, IHyr] },
  simp [add, (+), *],
end

@[simp] theorem nat_one : ((1 : ℕ) : pgame) = 0 + 1 := rfl

instance is_empty_left_moves_add (x y : pgame)
  [is_empty x.left_moves] [is_empty y.left_moves] : is_empty (x + y).left_moves :=
begin
  unfreezingI { cases x, cases y },
  apply is_empty_sum.2 ⟨_, _⟩,
  assumption'
end

instance is_empty_right_moves_add (x y : pgame)
  [is_empty x.right_moves] [is_empty y.right_moves] : is_empty (x + y).right_moves :=
begin
  unfreezingI { cases x, cases y },
  apply is_empty_sum.2 ⟨_, _⟩,
  assumption'
end

def add_zero_relabelling : Π (x : pgame), x + 0 ≡r x
| (mk xl xr xL xR) :=
begin
  refine ⟨equiv.sum_empty xl pempty, equiv.sum_empty xr pempty, _, _⟩,
  { rintro (⟨i⟩|⟨⟨⟩⟩),
    apply add_zero_relabelling },
  { rintro j,
    apply add_zero_relabelling }
end

lemma add_zero_equiv (x : pgame) : x + 0 ≈ x :=
(add_zero_relabelling x).equiv

def zero_add_relabelling : Π (x : pgame), 0 + x ≡r x
| (mk xl xr xL xR) :=
begin
  refine ⟨equiv.empty_sum pempty xl, equiv.empty_sum pempty xr, _, _⟩,
  { rintro (⟨⟨⟩⟩|⟨i⟩),
    apply zero_add_relabelling, },
  { rintro j,
    apply zero_add_relabelling, }
end

lemma zero_add_equiv (x : pgame) : 0 + x ≈ x :=
(zero_add_relabelling x).equiv

theorem left_moves_add : ∀ (x y : pgame),
  (x + y).left_moves = (x.left_moves ⊕ y.left_moves)
| ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ := rfl

theorem right_moves_add : ∀ (x y : pgame),
  (x + y).right_moves = (x.right_moves ⊕ y.right_moves)
| ⟨_, _, _, _⟩ ⟨_, _, _, _⟩ := rfl

def to_left_moves_add {x y : pgame} :
  x.left_moves ⊕ y.left_moves ≃ (x + y).left_moves :=
equiv.cast (left_moves_add x y).symm

def to_right_moves_add {x y : pgame} :
  x.right_moves ⊕ y.right_moves ≃ (x + y).right_moves :=
equiv.cast (right_moves_add x y).symm

@[simp] lemma mk_add_move_left_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inl i) =
    (mk xl xr xL xR).move_left i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_left_inl {x : pgame} (y : pgame) (i) :
  (x + y).move_left (to_left_moves_add (sum.inl i)) = x.move_left i + y :=
by { cases x, cases y, refl }

@[simp] lemma mk_add_move_right_inl {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inl i) =
    (mk xl xr xL xR).move_right i + (mk yl yr yL yR) :=
rfl
@[simp] lemma add_move_right_inl {x : pgame} (y : pgame) (i) :
  (x + y).move_right (to_right_moves_add (sum.inl i)) = x.move_right i + y :=
by { cases x, cases y, refl }

@[simp] lemma mk_add_move_left_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_left (sum.inr i) =
    (mk xl xr xL xR) + (mk yl yr yL yR).move_left i :=
rfl
@[simp] lemma add_move_left_inr (x : pgame) {y : pgame} (i) :
  (x + y).move_left (to_left_moves_add (sum.inr i)) = x + y.move_left i :=
by { cases x, cases y, refl }

@[simp] lemma mk_add_move_right_inr {xl xr yl yr} {xL xR yL yR} {i} :
  (mk xl xr xL xR + mk yl yr yL yR).move_right (sum.inr i) =
    (mk xl xr xL xR) + (mk yl yr yL yR).move_right i :=
rfl
@[simp] lemma add_move_right_inr (x : pgame) {y : pgame} (i) :
  (x + y).move_right (to_right_moves_add (sum.inr i)) = x + y.move_right i :=
by { cases x, cases y, refl }

lemma left_moves_add_cases {x y : pgame} (k) {P : (x + y).left_moves → Prop}
  (hl : ∀ i, P $ to_left_moves_add (sum.inl i))
  (hr : ∀ i, P $ to_left_moves_add (sum.inr i)) : P k :=
begin
  rw ←to_left_moves_add.apply_symm_apply k,
  cases to_left_moves_add.symm k with i i,
  { exact hl i },
  { exact hr i }
end

lemma right_moves_add_cases {x y : pgame} (k) {P : (x + y).right_moves → Prop}
  (hl : ∀ j, P $ to_right_moves_add (sum.inl j))
  (hr : ∀ j, P $ to_right_moves_add (sum.inr j)) : P k :=
begin
  rw ←to_right_moves_add.apply_symm_apply k,
  cases to_right_moves_add.symm k with i i,
  { exact hl i },
  { exact hr i }
end

instance is_empty_nat_right_moves : ∀ n : ℕ, is_empty (right_moves n)
| 0 := pempty.is_empty
| (n + 1) := begin
  haveI := is_empty_nat_right_moves n,
  rw [nat.cast_succ, right_moves_add],
  apply_instance
end

def relabelling.add_congr : ∀ {w x y z : pgame}, w ≡r x → y ≡r z → w + y ≡r x + z
| ⟨wl, wr, wL, wR⟩ ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ⟨zl, zr, zL, zR⟩
  ⟨L₁, R₁, hL₁, hR₁⟩ ⟨L₂, R₂, hL₂, hR₂⟩ :=
begin
  let Hwx : ⟨wl, wr, wL, wR⟩ ≡r ⟨xl, xr, xL, xR⟩ := ⟨L₁, R₁, hL₁, hR₁⟩,
  let Hyz : ⟨yl, yr, yL, yR⟩ ≡r ⟨zl, zr, zL, zR⟩ := ⟨L₂, R₂, hL₂, hR₂⟩,
  refine ⟨equiv.sum_congr L₁ L₂, equiv.sum_congr R₁ R₂, _, _⟩;
  rintro (i|j),
  { exact (hL₁ i).add_congr Hyz },
  { exact Hwx.add_congr (hL₂ j) },
  { exact (hR₁ i).add_congr Hyz },
  { exact Hwx.add_congr (hR₂ j) }
end
using_well_founded { dec_tac := dec_tac }

instance : has_sub pgame := ⟨λ x y, x + -y⟩

@[simp] theorem sub_zero (x : pgame) : x - 0 = x + 0 :=
show x + -0 = x + 0, by rw pgame.neg_zero

def relabelling.sub_congr {w x y z : pgame} (h₁ : w ≡r x) (h₂ : y ≡r z) : w - y ≡r x - z :=
h₁.add_congr h₂.neg_congr

def neg_add_relabelling : Π (x y : pgame), -(x + y) ≡r -x + -y
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ :=
begin
  refine ⟨equiv.refl _, equiv.refl _, _, _⟩,
  all_goals {
    exact λ j, sum.cases_on j
      (λ j, neg_add_relabelling _ _)
      (λ j, neg_add_relabelling ⟨xl, xr, xL, xR⟩ _) }
end
using_well_founded { dec_tac := dec_tac }

theorem neg_add_le {x y : pgame} : -(x + y) ≤ -x + -y :=
(neg_add_relabelling x y).le

theorem neg_add_equiv {x y : pgame} : -(x + y) ≈ -x + -y :=
(neg_add_relabelling x y).equiv

def add_comm_relabelling : Π (x y : pgame), x + y ≡r y + x
| (mk xl xr xL xR) (mk yl yr yL yR) :=
begin
  refine ⟨equiv.sum_comm _ _, equiv.sum_comm _ _, _, _⟩;
  rintros (_|_);
  { dsimp [left_moves_add, right_moves_add], apply add_comm_relabelling }
end
using_well_founded { dec_tac := dec_tac }

theorem add_comm_le {x y : pgame} : x + y ≤ y + x :=
(add_comm_relabelling x y).le

theorem add_comm_equiv {x y : pgame} : x + y ≈ y + x :=
(add_comm_relabelling x y).equiv

def add_assoc_relabelling : Π (x y z : pgame), x + y + z ≡r x + (y + z)
| ⟨xl, xr, xL, xR⟩ ⟨yl, yr, yL, yR⟩ ⟨zl, zr, zL, zR⟩ :=
begin
  let x := mk xl xr xL xR,
  let y := mk yl yr yL yR,
  let z := mk zl zr zL zR,
  change x + y + z ≡r x + (y + z),
  refine ⟨equiv.sum_assoc _ _ _, equiv.sum_assoc _ _ _, _, _⟩,
  all_goals
  { rintro (⟨i|i⟩|i) <|> rintro (j|⟨j|j⟩),
    { apply add_assoc_relabelling },
    { apply add_assoc_relabelling x },
    { apply add_assoc_relabelling x y } }
end
using_well_founded { dec_tac := dec_tac }

example (x y z : pgame) : x + y + z ≡r x + (y + z) :=
begin
  induction x with xl xr xL xR IHxl IHxr generalizing y z,
  change ∀ i y z, xL i + y + z ≡r xL i + (y + z) at IHxl,
  change ∀ j y z, xR j + y + z ≡r xR j + (y + z) at IHxr,
  let x := mk xl xr xL xR,
  induction y with yl yr yL yR IHyl IHyr generalizing z,
  change ∀ i z, x + yL i + z ≡r x + (yL i + z) at IHyl,
  change ∀ j z, x + yR j + z ≡r x + (yR j + z) at IHyr,
  let y := mk yl yr yL yR,
  induction z with zl zr zL zR IHzl IHzr,
  change ∀ i, x + y + zL i ≡r x + (y + zL i) at IHzl,
  change ∀ j, x + y + zR j ≡r x + (y + zR j) at IHzr,
  let z := mk zl zr zL zR,
  refine ⟨equiv.sum_assoc _ _ _, equiv.sum_assoc _ _ _, _, _⟩,
  all_goals { rintro (⟨i|i⟩|i) <|> rintro (j|j|j), all_goals { apply_assumption } }
end

theorem add_assoc_equiv {x y z : pgame} : (x + y) + z ≈ x + (y + z) :=
(add_assoc_relabelling x y z).equiv

theorem add_left_neg_le_zero : ∀ (x : pgame), -x + x ≤ 0
| ⟨xl, xr, xL, xR⟩ :=
le_zero.2 $ λ i, begin
  cases i,
  { refine ⟨@to_right_moves_add _ ⟨_, _, _, _⟩ (sum.inr i), _⟩,
    convert @add_left_neg_le_zero (xR i),
    apply add_move_right_inr },
  { refine ⟨@to_right_moves_add ⟨_, _, _, _⟩ _ (sum.inl i), _⟩,
    convert @add_left_neg_le_zero (xL i),
    dsimp,
    apply add_move_right_inl }
end

theorem zero_le_add_left_neg (x : pgame) : 0 ≤ -x + x :=
begin
  rw [←neg_le_neg_iff, pgame.neg_zero],
  exact neg_add_le.trans (add_left_neg_le_zero _)
end

theorem add_left_neg_equiv (x : pgame) : -x + x ≈ 0 :=
⟨add_left_neg_le_zero x, zero_le_add_left_neg x⟩

theorem add_right_neg_le_zero (x : pgame) : x + -x ≤ 0 :=
add_comm_le.trans (add_left_neg_le_zero x)

theorem zero_le_add_right_neg (x : pgame) : 0 ≤ x + -x :=
(zero_le_add_left_neg x).trans add_comm_le

theorem add_right_neg_equiv (x : pgame) : x + -x ≈ 0 :=
⟨add_right_neg_le_zero x, zero_le_add_right_neg x⟩

theorem sub_self_equiv : ∀ x, x - x ≈ 0 :=
add_right_neg_equiv

private lemma add_le_add_right' : ∀ {x y z : pgame} (h : x ≤ y), x + z ≤ y + z
| (mk xl xr xL xR) (mk yl yr yL yR) (mk zl zr zL zR) :=
λ h, begin
  refine le_def.2 ⟨λ i, _, λ i, _⟩;
  cases i,
  { rw le_def at h,
    cases h with h,
    rcases h i with ⟨i', ih⟩ | ⟨j, jh⟩,
    { exact or.inl ⟨to_left_moves_add (sum.inl i'), add_le_add_right' ih⟩ },
    { refine or.inr ⟨to_right_moves_add (sum.inl j), _⟩,
      convert add_le_add_right' jh,
      apply add_move_right_inl } },
  { exact or.inl ⟨@to_left_moves_add _ ⟨_, _, _, _⟩ (sum.inr i), add_le_add_right' h⟩ },
  { rw le_def at h,
    cases h with _ h,
    rcases h i with ⟨i, ih⟩ | ⟨j', jh⟩,
    { refine or.inl ⟨to_left_moves_add (sum.inl i), _⟩,
      convert add_le_add_right' ih,
      apply add_move_left_inl },
    { exact or.inr ⟨to_right_moves_add (sum.inl j'), add_le_add_right' jh⟩ } },
  { exact or.inr ⟨@to_right_moves_add _ ⟨_, _, _, _⟩ (sum.inr i), add_le_add_right' h⟩ }
end
using_well_founded { dec_tac := dec_tac }

instance covariant_class_swap_add_le : covariant_class pgame pgame (function.swap (+)) (≤) :=
⟨λ x y z, add_le_add_right'⟩

instance covariant_class_add_le : covariant_class pgame pgame (+) (≤) :=
⟨λ x y z h, (add_comm_le.trans (add_le_add_right h x)).trans add_comm_le⟩

theorem add_lf_add_right {y z : pgame} (h : y ⧏ z) (x) : y + x ⧏ z + x :=
suffices z + x ≤ y + x → z ≤ y, by { rw ←pgame.not_le at ⊢ h, exact mt this h }, λ w,
  calc z ≤ z + 0        : (add_zero_relabelling _).symm.le
     ... ≤ z + (x + -x) : add_le_add_left (zero_le_add_right_neg x) _
     ... ≤ z + x + -x   : (add_assoc_relabelling _ _ _).symm.le
     ... ≤ y + x + -x   : add_le_add_right w _
     ... ≤ y + (x + -x) : (add_assoc_relabelling _ _ _).le
     ... ≤ y + 0        : add_le_add_left (add_right_neg_le_zero x) _
     ... ≤ y            : (add_zero_relabelling _).le

theorem add_lf_add_left {y z : pgame} (h : y ⧏ z) (x) : x + y ⧏ x + z :=
by { rw lf_congr add_comm_equiv add_comm_equiv, apply add_lf_add_right h }

instance covariant_class_swap_add_lt : covariant_class pgame pgame (function.swap (+)) (<) :=
⟨λ x y z h, begin
  rw lt_iff_le_and_lf at h ⊢,
  exact ⟨add_le_add_right h.1 x, add_lf_add_right h.2 x⟩
end⟩

instance covariant_class_add_lt : covariant_class pgame pgame (+) (<) :=
⟨λ x y z h, begin
  rw lt_iff_le_and_lf at h ⊢,
  exact ⟨add_le_add_left h.1 x, add_lf_add_left h.2 x⟩
end⟩

theorem add_lf_add_of_lf_of_le {w x y z : pgame} (hwx : w ⧏ x) (hyz : y ≤ z) : w + y ⧏ x + z :=
lf_of_lf_of_le (add_lf_add_right hwx y) (add_le_add_left hyz x)

theorem add_lf_add_of_le_of_lf {w x y z : pgame} (hwx : w ≤ x) (hyz : y ⧏ z) : w + y ⧏ x + z :=
lf_of_le_of_lf (add_le_add_right hwx y) (add_lf_add_left hyz x)

theorem add_congr {w x y z : pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w + y ≈ x + z :=
⟨(add_le_add_left h₂.1 w).trans (add_le_add_right h₁.1 z),
  (add_le_add_left h₂.2 x).trans (add_le_add_right h₁.2 y)⟩

theorem add_congr_left {x y z : pgame} (h : x ≈ y) : x + z ≈ y + z :=
add_congr h equiv_rfl

theorem add_congr_right {x y z : pgame} : y ≈ z → x + y ≈ x + z :=
add_congr equiv_rfl

theorem sub_congr {w x y z : pgame} (h₁ : w ≈ x) (h₂ : y ≈ z) : w - y ≈ x - z :=
add_congr h₁ (neg_equiv_neg_iff.2 h₂)

theorem sub_congr_left {x y z : pgame} (h : x ≈ y) : x - z ≈ y - z :=
sub_congr h equiv_rfl

theorem sub_congr_right {x y z : pgame} : y ≈ z → x - y ≈ x - z :=
sub_congr equiv_rfl

theorem le_iff_sub_nonneg {x y : pgame} : x ≤ y ↔ 0 ≤ y - x :=
⟨λ h, (zero_le_add_right_neg x).trans (add_le_add_right h _),
 λ h,
  calc x ≤ 0 + x : (zero_add_relabelling x).symm.le
     ... ≤ y - x + x : add_le_add_right h _
     ... ≤ y + (-x + x) : (add_assoc_relabelling _ _ _).le
     ... ≤ y + 0 : add_le_add_left (add_left_neg_le_zero x) _
     ... ≤ y : (add_zero_relabelling y).le⟩

theorem lf_iff_sub_zero_lf {x y : pgame} : x ⧏ y ↔ 0 ⧏ y - x :=
⟨λ h, (zero_le_add_right_neg x).trans_lf (add_lf_add_right h _),
 λ h,
  calc x ≤ 0 + x : (zero_add_relabelling x).symm.le
     ... ⧏ y - x + x : add_lf_add_right h _
     ... ≤ y + (-x + x) : (add_assoc_relabelling _ _ _).le
     ... ≤ y + 0 : add_le_add_left (add_left_neg_le_zero x) _
     ... ≤ y : (add_zero_relabelling y).le⟩

theorem lt_iff_sub_pos {x y : pgame} : x < y ↔ 0 < y - x :=
⟨λ h, lt_of_le_of_lt (zero_le_add_right_neg x) (add_lt_add_right h _),
 λ h,
  calc x ≤ 0 + x : (zero_add_relabelling x).symm.le
     ... < y - x + x : add_lt_add_right h _
     ... ≤ y + (-x + x) : (add_assoc_relabelling _ _ _).le
     ... ≤ y + 0 : add_le_add_left (add_left_neg_le_zero x) _
     ... ≤ y : (add_zero_relabelling y).le⟩

def star : pgame := ⟨punit, punit, λ _, 0, λ _, 0⟩

@[simp] theorem star_left_moves : star.left_moves = punit := rfl
@[simp] theorem star_right_moves : star.right_moves = punit := rfl

@[simp] theorem star_move_left (x) : star.move_left x = 0 := rfl
@[simp] theorem star_move_right (x) : star.move_right x = 0 := rfl

instance unique_star_left_moves : unique star.left_moves := punit.unique
instance unique_star_right_moves : unique star.right_moves := punit.unique

theorem star_fuzzy_zero : star ∥ 0 :=
⟨by { rw lf_zero, use default, rintros ⟨⟩ }, by { rw zero_lf, use default, rintros ⟨⟩ }⟩

@[simp] theorem neg_star : -star = star :=
by simp [star]

@[simp] theorem zero_lt_one : (0 : pgame) < 1 :=
lt_of_le_of_lf (zero_le_of_is_empty_right_moves 1) (zero_lf_le.2 ⟨default, le_rfl⟩)

instance : zero_le_one_class pgame := ⟨zero_lt_one.le⟩

@[simp] theorem zero_lf_one : (0 : pgame) ⧏ 1 :=
zero_lt_one.lf

end pgame