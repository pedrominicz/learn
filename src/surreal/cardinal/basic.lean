import data.nat.enat data.set.countable
import logic.small
import order.conditionally_complete_lattice order.succ_pred.basic
import set_theory.cardinal.schroeder_bernstein

universes u v w

variables {α β : Type u}

instance cardinal.is_equivalent : setoid (Type u) :=
{ r := λ α β, nonempty (α ≃ β),
  iseqv := ⟨
    λ α, ⟨equiv.refl α⟩,
    λ α β ⟨e⟩, ⟨e.symm⟩,
    λ α β γ ⟨e₁⟩ ⟨e₂⟩, ⟨e₁.trans e₂⟩⟩ }

def cardinal : Type (u+1) := quotient cardinal.is_equivalent

namespace cardinal

def mk (α : Type u) : cardinal := quotient.mk α

prefix `#` := cardinal.mk

instance can_lift_cardinal_Type : can_lift cardinal.{u} (Type u) :=
⟨mk, λ c, true, λ c h, quotient.induction_on c (λ α, ⟨α, rfl⟩)⟩

@[elab_as_eliminator]
lemma induction_on {p : cardinal → Prop} (c : cardinal) : (∀ α, p #α) → p c :=
λ h, quotient.induction_on c h

@[elab_as_eliminator]
lemma induction_on₂ {p : cardinal → cardinal → Prop}
  (c₁ : cardinal.{u}) (c₂ : cardinal.{v}) : (∀ α β, p #α #β) → p c₁ c₂ :=
λ h, quotient.induction_on₂ c₁ c₂ h

@[elab_as_eliminator]
lemma induction_on₃ {p : cardinal → cardinal → cardinal → Prop}
  (c₁ : cardinal.{u}) (c₂ : cardinal.{v}) (c₃ : cardinal.{w}) :
  (∀ α β γ, p #α #β #γ) → p c₁ c₂ c₃ :=
λ h, quotient.induction_on₃ c₁ c₂ c₃ h

protected lemma eq : #α = #β ↔ nonempty (α ≃ β) := quotient.eq

@[simp] theorem mk_def (α : Type u) : @eq cardinal ⟦α⟧ #α := rfl

@[simp] theorem mk_out (c : cardinal) : #c.out = c := quotient.out_eq c

noncomputable def out_mk_equiv : (#α).out ≃ α :=
nonempty.some (cardinal.eq.mp (mk_out #α))

lemma mk_congr (e : α ≃ β) : #α = #β := quotient.sound ⟨e⟩

alias mk_congr ← _root_.equiv.cardinal_eq

def map (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) :
  cardinal.{u} → cardinal.{v} :=
quotient.map f (λ α β ⟨e⟩, ⟨hf α β e⟩)

@[simp] lemma map_mk (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) (α : Type u) :
  map f hf #α = #(f α) := rfl

def map₂ (f : Type u → Type v → Type w) (hf : ∀ α₁ β₁ α₂ β₂, α₁ ≃ β₁ → α₂ ≃ β₂ → f α₁ α₂ ≃ f β₁ β₂) :
  cardinal.{u} → cardinal.{v} → cardinal.{w} :=
quotient.map₂ f (λ α β ⟨e₁⟩ γ δ ⟨e₂⟩, ⟨hf α β γ δ e₁ e₂⟩)

def lift (c : cardinal.{v}) : cardinal.{max v u} :=
map ulift (λ α β e, equiv.ulift.trans (e.trans equiv.ulift.symm)) c

@[simp] theorem mk_ulift (α : Type u) : #(ulift α) = lift #α := rfl

@[simp] theorem lift_umax : lift.{(max u v) u} = lift.{v u} :=
funext (λ c, induction_on c (λ α, mk_congr (equiv.ulift.trans equiv.ulift.symm)))

@[simp] theorem lift_umax' : lift.{(max v u) u} = lift.{v u} := lift_umax

@[simp] theorem lift_id' (c : cardinal.{max u v}) : lift.{u} c = c :=
induction_on c (λ α, mk_congr equiv.ulift)

@[simp] theorem lift_id (c : cardinal.{u}) : lift.{u u} c = c := lift_id'.{u u} c

@[simp] theorem lift_uzero (c : cardinal.{u}) : lift.{0} c = c := lift_id'.{0 u} c

@[simp] theorem lift_lift (c : cardinal.{u}) :
  lift.{w} (lift.{v} c) = lift.{max v w} c :=
induction_on c (λ α, mk_congr (equiv.ulift.trans (equiv.ulift.trans equiv.ulift.symm)))

instance : has_le cardinal.{u} :=
⟨λ c₁ c₂, quotient.lift_on₂ c₁ c₂ (λ α β, nonempty (α ↪ β))
  (λ α₁ β₁ α₂ β₂ ⟨e₁⟩ ⟨e₂⟩, propext ⟨λ ⟨e⟩, ⟨e.congr e₁ e₂⟩, λ ⟨e⟩, ⟨e.congr e₁.symm e₂.symm⟩⟩)⟩

instance : partial_order cardinal.{u} :=
{ le          := (≤),
  le_refl     := by { rintros ⟨α⟩, exact ⟨function.embedding.refl α⟩ },
  le_trans    := by { rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨e₁⟩ ⟨e₂⟩, exact ⟨e₁.trans e₂⟩ },
  le_antisymm := by { rintros ⟨α⟩ ⟨β⟩ ⟨e₁⟩ ⟨e₂⟩, exact quotient.sound (e₁.antisymm e₂) } }

theorem le_def (α β : Type u) : #α ≤ #β ↔ nonempty (α ↪ β) :=
iff.rfl

theorem mk_le_of_injective {f : α → β} (hf : function.injective f) :
  #α ≤ #β :=
⟨⟨f, hf⟩⟩

theorem _root_.function.embedding.cardinal_le (f : α ↪ β) : #α ≤ #β := ⟨f⟩

theorem mk_le_of_surjective {f : α → β} (hf : function.surjective f) : #β ≤ #α :=
⟨function.embedding.of_surjective f hf⟩

theorem le_mk_iff_exists_set {c : cardinal} {α : Type u} :
  c ≤ #α ↔ ∃ s : set α, #s = c :=
⟨induction_on c (λ β ⟨⟨f, hf⟩⟩, ⟨set.range f, mk_congr (equiv.of_injective f hf).symm⟩),
 λ ⟨s, hs⟩, hs ▸ ⟨⟨subtype.val, λ a₁ a₂, subtype.eq⟩⟩⟩

theorem mk_subtype_le {α : Type u} (p : α → Prop) : #(subtype p) ≤ #α :=
⟨function.embedding.subtype p⟩

theorem mk_set_le (s : set α) : #s ≤ #α :=
mk_subtype_le s

theorem out_embedding {c₁ c₂ : cardinal} : c₁ ≤ c₂ ↔ nonempty (c₁.out ↪ c₂.out) :=
begin
  transitivity #c₁.out ≤ #c₂.out,
  { conv { to_lhs, rw [←mk_out c₁, ←mk_out c₂] } },
  { refl }
end

theorem lift_mk_le {α : Type u} {β : Type v} :
  lift.{max v w} #α ≤ lift.{max u w} #β ↔ nonempty (α ↪ β) :=
⟨λ ⟨f⟩, ⟨function.embedding.congr equiv.ulift equiv.ulift f⟩,
 λ ⟨f⟩, ⟨function.embedding.congr equiv.ulift.symm equiv.ulift.symm f⟩⟩

theorem lift_mk_le' {α : Type u} {β : Type v} :
  lift.{v} #α ≤ lift.{u} #β ↔ nonempty (α ↪ β) :=
lift_mk_le.{u v 0}

theorem lift_mk_eq {α : Type u} {β : Type v} :
  lift.{max v w} #α = lift.{max u w} #β ↔ nonempty (α ≃ β) :=
quotient.eq.trans
⟨λ ⟨f⟩, ⟨equiv.ulift.symm.trans (f.trans equiv.ulift)⟩,
 λ ⟨f⟩, ⟨equiv.ulift.trans (f.trans equiv.ulift.symm)⟩⟩

theorem lift_mk_eq' {α : Type u} {β : Type v} :
  lift.{v} #α = lift.{u} #β ↔ nonempty (α ≃ β) :=
lift_mk_eq.{u v 0}

@[simp] theorem lift_le {c₁ c₂ : cardinal} : lift c₁ ≤ lift c₂ ↔ c₁ ≤ c₂ :=
induction_on₂ c₁ c₂ (λ α β, lift_umax ▸ lift_mk_le)

@[simps { fully_applied := ff }] def lift_order_embedding :
  cardinal.{v} ↪o cardinal.{max v u} :=
order_embedding.of_map_le_iff lift (λ c₁ c₂, lift_le)

theorem lift_injective : function.injective lift.{u v} :=
lift_order_embedding.injective

@[simp] theorem lift_inj {c₁ c₂ : cardinal} : lift c₁ = lift c₂ ↔ c₁ = c₂ :=
lift_injective.eq_iff

@[simp] theorem lift_lt {c₁ c₂ : cardinal} : lift c₁ < lift c₂ ↔ c₁ < c₂ :=
lift_order_embedding.lt_iff_lt

theorem lift_strict_mono : strict_mono lift :=
λ c₁ c₂, lift_lt.mpr

theorem lift_monotone : monotone lift :=
lift_strict_mono.monotone

instance : has_zero cardinal := ⟨#pempty⟩

instance : inhabited cardinal := ⟨0⟩

lemma mk_eq_zero (α : Type u) [is_empty α] : #α = 0 :=
mk_congr (equiv.equiv_pempty α)

@[simp] theorem lift_zero : lift 0 = 0 := mk_congr (equiv.equiv_pempty (ulift pempty))

@[simp] theorem lift_eq_zero {c : cardinal} : lift c = 0 ↔ c = 0 :=
lift_injective.eq_iff' lift_zero

lemma mk_eq_zero_iff {α : Type u} : #α = 0 ↔ is_empty α :=
⟨λ h, let ⟨e⟩ := quotient.exact h in equiv.is_empty e, @mk_eq_zero α⟩

theorem mk_ne_zero_iff {α : Type u} : #α ≠ 0 ↔ nonempty α :=
(not_iff_not.mpr mk_eq_zero_iff).trans not_is_empty_iff

@[simp] lemma mk_ne_zero (α : Type u) [nonempty α] : #α ≠ 0 :=
mk_ne_zero_iff.mpr infer_instance

instance : has_one cardinal := ⟨#punit⟩

instance : nontrivial cardinal := ⟨⟨1, 0, mk_ne_zero punit⟩⟩

lemma mk_eq_one (α : Type u) [unique α] : #α = 1 :=
mk_congr (equiv.equiv_punit α)

theorem le_one_iff_subsingleton {α : Type u} : #α ≤ 1 ↔ subsingleton α :=
⟨λ ⟨f⟩, ⟨λ a₁ a₂, f.injective (subsingleton.elim (f a₁) (f a₂))⟩,
 λ ⟨h⟩, ⟨⟨λ a, punit.star, λ a₁ a₂ h', h a₁ a₂⟩⟩⟩

instance : has_add cardinal := ⟨map₂ sum (λ α₁ β₁ α₂ β₂, equiv.sum_congr)⟩

theorem add_def (α β : Type u) : #α + #β = #(α ⊕ β) := rfl

instance : has_nat_cast cardinal := ⟨nat.unary_cast⟩

@[simp] lemma mk_sum (α : Type u) (β : Type v) :
  #(α ⊕ β) = lift #α + lift.{u} #β :=
mk_congr (equiv.ulift.symm.sum_congr equiv.ulift.symm)

@[simp] theorem mk_option {α : Type u} : #(option α) = #α + 1 :=
mk_congr (equiv.option_equiv_sum_punit α)

@[simp] lemma mk_psum (α : Type u) (β : Type v) :
  #(psum α β) = lift #α + lift.{u} #β :=
(mk_congr (equiv.psum_equiv_sum α β)).trans (mk_sum α β)

@[simp] lemma mk_fintype (α : Type u) [hα : fintype α] : #α = fintype.card α :=
begin
  refine fintype.induction_empty_option' _ _ _ α,
  { intros α β hβ e h,
    let hα := @fintype.of_equiv α β hβ e.symm,
    rwa [mk_congr e, @fintype.card_congr α β hα hβ e] at h },
  { refl },
  { intros α hα h,
    simp only [h, mk_option, @fintype.card_option α hα],
    refl }
end

instance : has_mul cardinal := ⟨map₂ prod (λ α₁ β₁ α₂ β₂, equiv.prod_congr)⟩

theorem mul_def (α β : Type u) : #α * #β = #(α × β) := rfl

@[simp] lemma mk_prod (α : Type u) (β : Type v) :
  #(α × β) = lift #α * lift.{u} #β :=
mk_congr (equiv.ulift.symm.prod_congr equiv.ulift.symm)

private theorem mul_comm' (c₁ c₂ : cardinal.{u}) : c₁ * c₂ = c₂ * c₁ :=
induction_on₂ c₁ c₂ (λ α β, mk_congr (equiv.prod_comm α β))

instance : has_pow cardinal.{u} cardinal.{u} :=
⟨map₂ (λ α β, β → α) (λ α₁ β₁ α₂ β₂, flip equiv.arrow_congr)⟩

local infixr ` ^ ` := @has_pow.pow cardinal cardinal cardinal.has_pow
local infixr ` ^ℕ `:80 := @has_pow.pow cardinal ℕ monoid.has_pow

theorem power_def (α β : Type u) : #α ^ #β = #(β → α) := rfl

theorem mk_arrow (α : Type u) (β : Type v) : #(α → β) = lift.{u} #β ^ lift.{v} #α :=
mk_congr (equiv.ulift.symm.arrow_congr equiv.ulift.symm)

@[simp] theorem lift_power (c₁ c₂ : cardinal) : lift (c₁ ^ c₂) = lift c₁ ^ lift c₂ :=
induction_on₂ c₁ c₂ (λ α β, mk_congr (equiv.ulift.trans (equiv.ulift.arrow_congr equiv.ulift).symm))

@[simp] theorem power_zero {c : cardinal} : c ^ 0 = 1 :=
induction_on c (λ α, mk_congr (equiv.pempty_arrow_equiv_punit α))

@[simp] theorem power_one {c : cardinal} : c ^ 1 = c :=
induction_on c (λ α, mk_congr (equiv.punit_arrow_equiv α))

theorem power_add {c₁ c₂ c₃ : cardinal} : c₁ ^ (c₂ + c₃) = c₁ ^ c₂ * c₁ ^ c₃ :=
induction_on₃ c₁ c₂ c₃ (λ α β γ, mk_congr (equiv.sum_arrow_equiv_prod_arrow β γ α))

instance : comm_semiring cardinal.{u} :=
{ zero          := 0,
  one           := 1,
  add           := (+),
  mul           := (*),
  zero_add      := λ c, induction_on c (λ α, mk_congr (equiv.empty_sum pempty α)),
  add_zero      := λ c, induction_on c (λ α, mk_congr (equiv.sum_empty α pempty)),
  add_assoc     := λ c₁ c₂ c₃, induction_on₃ c₁ c₂ c₃ (λ α β γ, mk_congr (equiv.sum_assoc α β γ)),
  add_comm      := λ c₁ c₂, induction_on₂ c₁ c₂ (λ α β, mk_congr (equiv.sum_comm α β)),
  zero_mul      := λ c, induction_on c (λ α, mk_congr (equiv.pempty_prod α)),
  mul_zero      := λ c, induction_on c (λ α, mk_congr (equiv.prod_pempty α)),
  one_mul       := λ c, induction_on c (λ α, mk_congr (equiv.punit_prod α)),
  mul_one       := λ c, induction_on c (λ α, mk_congr (equiv.prod_punit α)),
  mul_assoc     := λ c₁ c₂ c₃, induction_on₃ c₁ c₂ c₃ (λ α β γ, mk_congr (equiv.prod_assoc α β γ)),
  mul_comm      := mul_comm',
  left_distrib  := λ c₁ c₂ c₃, induction_on₃ c₁ c₂ c₃ (λ α β γ, mk_congr (equiv.prod_sum_distrib α β γ)),
  right_distrib := λ c₁ c₂ c₃, induction_on₃ c₁ c₂ c₃ (λ α β γ, mk_congr (equiv.sum_prod_distrib α β γ)),
  npow          := λ n c, c ^ n,
  npow_zero'    := @power_zero,
  npow_succ'    := λ n c, show c ^ (n + 1) = c * c ^ n, by rw [power_add, power_one, mul_comm'] }

theorem power_bit0 (c₁ c₂ : cardinal) : c₁ ^ (bit0 c₂) = c₁ ^ c₂ * c₁ ^ c₂ :=
power_add

theorem power_bit1 (c₁ c₂ : cardinal) : c₁ ^ (bit1 c₂) = c₁ ^ c₂ * c₁ ^ c₂ * c₁ :=
by rw [bit1, ←power_bit0, power_add, power_one]

@[simp] theorem one_power {c : cardinal} : 1 ^ c = 1 :=
induction_on c (λ α, mk_congr (equiv.arrow_punit_equiv_punit α))

@[simp] theorem mk_bool : #bool = 2 := by simp

@[simp] theorem mk_Prop : #Prop = 2 := by simp

@[simp] theorem zero_power {c : cardinal} : c ≠ 0 → 0 ^ c = 0 :=
induction_on c (λ α h, mk_eq_zero_iff.mpr
  (is_empty_pi.mpr ⟨classical.choice (mk_ne_zero_iff.mp h), pempty.is_empty⟩))

theorem power_ne_zero {c₁ : cardinal.{u}} (c₂ : cardinal.{u}) : c₁ ≠ 0 → c₁ ^ c₂ ≠ 0 :=
induction_on₂ c₁ c₂
  (λ α β h, mk_ne_zero_iff.mpr ⟨λ b, classical.choice (mk_ne_zero_iff.mp h)⟩)

theorem mul_power {c₁ c₂ c₃ : cardinal} : (c₁ * c₂) ^ c₃ = c₁ ^ c₃ * c₂ ^ c₃ :=
induction_on₃ c₁ c₂ c₃ (λ α β γ, mk_congr (equiv.arrow_prod_equiv_prod_arrow α β γ))

theorem power_mul {c₁ c₂ c₃ : cardinal} : c₁ ^ (c₂ * c₃) = (c₁ ^ c₂) ^ c₃ :=
begin
  rw [mul_comm c₂ c₃],
  exact induction_on₃ c₁ c₂ c₃ (λ α β γ, mk_congr (equiv.curry γ β α))
end

@[simp] lemma pow_cast_right (c : cardinal) (n : ℕ) : c ^ n = c ^ℕ n :=
rfl

@[simp] theorem lift_one : lift 1 = 1 :=
mk_congr (equiv.ulift.trans equiv.punit_equiv_punit)

@[simp] theorem lift_add (c₁ c₂) : lift (c₁ + c₂) = lift c₁ + lift c₂ :=
induction_on₂ c₁ c₂
  (λ α β, mk_congr (equiv.ulift.trans (equiv.sum_congr equiv.ulift equiv.ulift).symm))

@[simp] theorem lift_mul (c₁ c₂) : lift (c₁ * c₂) = lift c₁ * lift c₂ :=
induction_on₂ c₁ c₂
  (λ α β, mk_congr (equiv.ulift.trans (equiv.prod_congr equiv.ulift equiv.ulift).symm))

@[simp] theorem lift_bit0 (c : cardinal) : lift (bit0 c) = bit0 (lift c) :=
lift_add c c

@[simp] theorem lift_bit1 (c : cardinal) : lift (bit1 c) = bit1 (lift c) :=
by simp [bit1]

theorem lift_two : lift 2 = 2 := by simp

@[simp] theorem mk_set {α : Type u} : #(set α) = 2 ^ #α := by simp [set, mk_arrow]

@[simp] theorem mk_powerset {α : Type u} (s : set α) : #(set.powerset s) = 2 ^ #s :=
(mk_congr (equiv.set.powerset s)).trans mk_set

theorem lift_two_power (c : cardinal) : lift (2 ^ c) = 2 ^ lift c := by simp

protected theorem zero_le (c : cardinal) : 0 ≤ c :=
induction_on c (λ α, ⟨function.embedding.of_is_empty⟩)

private theorem add_le_add' : ∀ {c₁ c₂ c₃ c₄ : cardinal}, c₁ ≤ c₂ → c₃ ≤ c₄ → c₁ + c₃ ≤ c₂ + c₄ :=
by { rintros ⟨α⟩ ⟨β⟩ ⟨γ⟩ ⟨δ⟩ ⟨e₁⟩ ⟨e₂⟩, exact ⟨function.embedding.sum_map e₁ e₂⟩ }

instance add_covariant_class : covariant_class cardinal cardinal (+) (≤) :=
⟨λ c₁ c₂ c₃, add_le_add' le_rfl⟩

instance add_swap_covariant_class :
  covariant_class cardinal cardinal (function.swap (+)) (≤) :=
⟨λ c₁ c₂ c₃ h, add_le_add' h le_rfl⟩

theorem exists_add_of_le {c₁ c₂ : cardinal} : c₁ ≤ c₂ → ∃ c₃, c₂ = c₁ + c₃ :=
begin
  classical,
  refine induction_on₂ c₁ c₂ _,
  rintros α β ⟨⟨f, hf⟩⟩,
  have h : α ⊕ ↥(set.range f)ᶜ ≃ β,
  { transitivity ↥(set.range f) ⊕ ↥(set.range f)ᶜ,
    { exact equiv.sum_congr (equiv.of_injective f hf) (equiv.refl ↥(set.range f)ᶜ) },
    { exact equiv.set.sum_compl (set.range f) } },
  exact ⟨#↥(set.range f)ᶜ, mk_congr h.symm⟩
end

theorem le_self_add {c₁ c₂ : cardinal} : c₁ ≤ c₁ + c₂ :=
begin
  transitivity c₁ + 0,
  { exact eq.ge (add_zero c₁) },
  { exact add_le_add_left (cardinal.zero_le c₂) c₁ }
end

theorem eq_zero_or_eq_zero_of_mul_eq_zero (c₁ c₂ : cardinal) :
  c₁ * c₂ = 0 → c₁ = 0 ∨ c₂ = 0 :=
begin
  refine induction_on₂ c₁ c₂ (λ α β, _),
  simpa only [mul_def, mk_eq_zero_iff, is_empty_prod] using id
end

instance : canonically_ordered_comm_semiring cardinal.{u} :=
{ bot                               := 0,
  bot_le                            := cardinal.zero_le,
  add_le_add_left                   := λ c₁ c₂, add_le_add_left,
  exists_add_of_le                  := @exists_add_of_le,
  le_self_add                       := @le_self_add,
  eq_zero_or_eq_zero_of_mul_eq_zero := eq_zero_or_eq_zero_of_mul_eq_zero,
  ..cardinal.comm_semiring, ..cardinal.partial_order }

@[simp] theorem zero_lt_one : (0 : cardinal) < 1 :=
lt_of_le_of_ne (zero_le 1) zero_ne_one

lemma zero_power_le (c : cardinal.{u}) : (0 : cardinal.{u}) ^ c ≤ 1 :=
begin
  by_cases h : c = 0,
  { rw [h, power_zero] },
  { rw [zero_power h],
    exact zero_le 1 }
end

theorem power_le_power_left {c₁ c₂ c₃ : cardinal} :
  c₁ ≠ 0 → c₂ ≤ c₃ → c₁ ^ c₂ ≤ c₁ ^ c₃ :=
begin
  refine induction_on₃ c₁ c₂ c₃ _,
  rintros α β γ h ⟨e⟩,
  haveI hα := classical.inhabited_of_nonempty (mk_ne_zero_iff.mp h),
  exact ⟨function.embedding.arrow_congr_left e⟩
end

theorem self_le_power (c₁ : cardinal) {c₂ : cardinal} (h₂ : 1 ≤ c₂) : c₁ ≤ c₁ ^ c₂ :=
begin
  by_cases h₁ : c₁ = 0,
  { exact h₁.symm ▸ zero_le (0 ^ c₂) },
  { convert power_le_power_left h₁ h₂,
    rw power_one }
end

theorem cantor (c : cardinal) : c < 2 ^ c :=
begin
  refine induction_on c (λ α, _),
  rw ←mk_set,
  refine ⟨⟨⟨singleton, λ a₁ a₂, set.singleton_eq_singleton_iff.mp⟩⟩, _⟩,
  rintro ⟨⟨f, hf⟩⟩,
  exact function.cantor_injective f hf
end

instance : no_max_order cardinal :=
{ exists_gt := λ c, ⟨2 ^ c, cantor c⟩ }

noncomputable instance : canonically_linear_ordered_add_monoid cardinal :=
{ le_total     := λ c₁ c₂, induction_on₂ c₁ c₂ (λ α β, function.embedding.total α β),
  decidable_le := classical.dec_rel (≤),
  ..cardinal.canonically_ordered_comm_semiring, ..cardinal.partial_order }

noncomputable instance : distrib_lattice cardinal := infer_instance

theorem one_lt_iff_nontrivial {α : Type u} : 1 < #α ↔ nontrivial α :=
by rw [←not_le, le_one_iff_subsingleton, ←not_nontrivial_iff_subsingleton, not_not]

theorem power_le_max_power_one {c₁ c₂ c₃ : cardinal} (h : c₂ ≤ c₃) :
  c₁ ^ c₂ ≤ max (c₁ ^ c₃) 1 :=
begin
  by_cases h₁ : c₁ = 0,
  { rw [h₁, max_eq_right (zero_power_le c₃)],
    exact zero_power_le c₂ },
  { transitivity c₁ ^ c₃,
    { exact power_le_power_left h₁ h },
    { exact le_max_left (c₁ ^ c₃) 1 } }
end

theorem power_le_power_right {c₁ c₂ c₃ : cardinal} : c₁ ≤ c₂ → c₁ ^ c₃ ≤ c₂ ^ c₃ :=
induction_on₃ c₁ c₂ c₃ (λ α β γ ⟨e⟩, ⟨function.embedding.arrow_congr_right e⟩)

protected theorem lt_wf : @well_founded cardinal (<) :=
begin
  refine ⟨λ c, _⟩,
  by_contra hc,
  let α := {c : cardinal // ¬ acc (<) c},
  haveI hα : nonempty α := ⟨⟨c, hc⟩⟩,
  obtain ⟨⟨c, hc⟩, ⟨h⟩⟩ := function.embedding.min_injective (λ a : α, a.val.out),
  refine hc ⟨c, _⟩,
  rintros c' ⟨h₁, h₂⟩,
  by_contra hc',
  refine h₂ _,
  replace h : #c.out ≤ #c'.out := ⟨h ⟨c', hc'⟩⟩,
  simpa using h
end

instance : has_well_founded cardinal := ⟨(<), cardinal.lt_wf⟩

instance wo : @is_well_order cardinal (<) := ⟨cardinal.lt_wf⟩

noncomputable instance : conditionally_complete_linear_order_bot cardinal :=
is_well_order.conditionally_complete_linear_order_bot cardinal

@[simp] theorem Inf_empty : Inf (∅ : set cardinal) = 0 :=
begin
  classical,
  exact dif_neg set.not_nonempty_empty
end

noncomputable instance : succ_order cardinal :=
begin
  refine succ_order.of_succ_le_iff (λ c, Inf {c' | c < c'}) _,
  intros c₁ c₂,
  refine ⟨_, _⟩,
  { let s : set cardinal := {c | c₁ < c},
    have h : set.nonempty s := exists_gt c₁,
    replace h : Inf s ∈ s := Inf_mem h,
    exact lt_of_lt_of_le h },
  { exact cInf_le' }
end

theorem succ_def (c : cardinal) : order.succ c = Inf {c' | c < c'} := rfl

theorem add_one_le_succ (c : cardinal) : c + 1 ≤ order.succ c :=
begin
  refine induction_on c (λ α, _),
  let s : set cardinal := {c | #α < c},
  have h : set.nonempty s := exists_gt #α,
  rw [succ_def, le_cInf_iff'' h],
  intro c,
  refine induction_on c (λ β h', _),
  change #α < #β at h',
  cases le_of_lt h' with f,
  have hf : ¬ function.surjective f,
  { exact λ hf, not_le_of_lt h' (mk_le_of_surjective hf) },
  simp only [function.surjective, not_forall] at hf,
  cases hf with b hb,
  rw ←mk_option,
  exact ⟨function.embedding.option_elim f b hb⟩
end

lemma succ_pos (c : cardinal) : 0 < order.succ c := order.bot_lt_succ c

lemma succ_ne_zero (c : cardinal) : order.succ c ≠ 0 := ne.symm (ne_of_lt (succ_pos c))

def sum {ι : Type u} (f : ι → cardinal.{v}) : cardinal.{max u v} := #(Σ i, (f i).out)

theorem le_sum {ι : Type u} (f : ι → cardinal.{max u v}) (i : ι) : f i ≤ sum f :=
mk_out (f i) ▸ ⟨⟨λ x, ⟨i, x⟩, λ x₁ x₂ h, eq_of_heq (by injection h)⟩⟩

@[simp] theorem mk_sigma {ι : Type u} (f : ι → Type v) :
  #(Σ i, f i) = sum (λ i, #(f i)) :=
mk_congr (equiv.sigma_congr_right (λ i, out_mk_equiv.symm))

@[simp] theorem sum_const (ι : Type u) (c : cardinal.{v}) :
  sum (λ i : ι, c) = lift #ι * lift.{u} c :=
begin
  refine induction_on c (λ α, mk_congr _),
  transitivity ι × (#α).out,
  { exact equiv.sigma_equiv_prod ι (#α).out },
  { exact equiv.ulift.symm.prod_congr (out_mk_equiv.trans equiv.ulift.symm) }
end

theorem sum_const' (ι : Type u) (c : cardinal.{u}) : sum (λ i : ι, c) = #ι * c :=
by simp

@[simp] theorem sum_add_distrib {ι : Type u} (f g : ι → cardinal.{v}) :
  sum (f + g) = sum f + sum g :=
begin
  have h := mk_congr (equiv.sigma_sum_distrib (quotient.out ∘ f) (quotient.out ∘ g)),
  simpa [mk_sigma, mk_sum, mk_out, lift_id] using h
end

@[simp] theorem sum_add_distrib' {ι : Type u} (f g : ι → cardinal.{v}) :
  sum (λ i, f i + g i) = sum f + sum g :=
sum_add_distrib f g

@[simp] theorem lift_sum {ι : Type u} (f : ι → cardinal.{v}) :
  lift.{w} (sum f) = sum (λ i, lift.{w} (f i)) :=
begin
  refine mk_congr _,
  transitivity Σ i, (f i).out,
  { exact equiv.ulift },
  { refine equiv.sigma_congr_right (λ i, classical.choice _),
    rw [←lift_mk_eq, mk_out, mk_out, lift_lift] }
end

theorem sum_le_sum {ι : Type u} (f g : ι → cardinal.{v}) (h : ∀ i, f i ≤ g i) :
  sum f ≤ sum g :=
begin
  refine ⟨function.embedding.sigma_map _ (λ i, classical.choice _)⟩,
  { exact function.embedding.refl ι },
  { specialize h i,
    rwa [←mk_out (f i), ←mk_out (g i)] at h }
end

lemma mk_le_mk_mul_of_mk_preimage_le {c : cardinal} (f : α → β) :
  (∀ b, #(f ⁻¹' {b}) ≤ c) → #α ≤ #β * c :=
begin
  simp only [←mk_congr (@equiv.sigma_fiber_equiv α β f), mk_sigma, ←sum_const'],
  exact sum_le_sum (λ b, #(f ⁻¹' {b})) (λ b, c)
end

theorem bdd_above_range {ι : Type u} (f : ι → cardinal.{max u v}) :
  bdd_above (set.range f) :=
⟨sum f, by { rintros c ⟨i, rfl⟩, exact le_sum f i }⟩

instance (c : cardinal.{u}) : small.{u} (set.Iic c) :=
begin
  rw ←mk_out c,
  let f : set c.out → set.Iic #c.out := λ s, ⟨#s, mk_set_le s⟩,
  refine @small_of_surjective (set c.out) (set.Iic #c.out) infer_instance f _,
  rintro ⟨c', h⟩,
  change c' ≤ #c.out at h,
  simp only [subtype.mk_eq_mk],
  rwa le_mk_iff_exists_set at h
end

theorem bdd_above_iff_small {s : set cardinal.{u}} : bdd_above s ↔ small.{u} s :=
begin
  split,
  { rintro ⟨c, hc⟩,
    change ∀ c', c' ∈ s → c' ≤ c at hc,
    exact @small_subset cardinal (set.Iic c) s hc infer_instance },
  { rintro ⟨ι, ⟨e⟩⟩,
    let f : ι → cardinal := λ i : ι, subtype.val (e.symm i),
    suffices h : set.range f = s,
    { exact h ▸ bdd_above_range.{u u} f },
    ext c,
    split,
    { rintro ⟨i, rfl⟩,
      exact subtype.prop (e.symm i) },
    { intro hc,
      use e ⟨c, hc⟩,
      dsimp only [f],
      rw [equiv.symm_apply_apply] } }
end

theorem bdd_above_image (f : cardinal.{u} → cardinal.{max u v}) {s : set cardinal.{u}}
  (hs : bdd_above s) : bdd_above (f '' s) :=
begin
  rw bdd_above_iff_small at ⊢ hs,
  exactI small_lift ↥(f '' s)
end

theorem bdd_above_range_comp {ι : Type u} {f : ι → cardinal.{v}}
  (hf : bdd_above (set.range f)) (g : cardinal.{v} → cardinal.{max v w}) :
  bdd_above (set.range (g ∘ f)) :=
by { rw set.range_comp, exact bdd_above_image g hf }

theorem supr_le_sum {ι : Type u} (f : ι → cardinal.{max u v}) : supr f ≤ sum f :=
csupr_le' (le_sum f)

theorem sum_le_supr_lift {ι : Type u} (f : ι → cardinal.{max u v}) :
  sum f ≤ lift #ι * supr f :=
begin
  rw [←lift_id (supr f), ←lift_umax, lift_umax.{(max u v) u}, ←sum_const],
  exact sum_le_sum f (λ i, supr f) (le_csupr (bdd_above_range f))
end

theorem sum_le_supr {ι : Type u} (f : ι → cardinal.{u}) : sum f ≤ #ι * supr f :=
lift_id #ι ▸ sum_le_supr_lift f

theorem sum_nat_eq_add_sum_succ (f : ℕ → cardinal.{u}) :
  sum f = f 0 + sum (λ i, f (i + 1)) :=
begin
  transitivity #((f 0).out ⊕ Σ i, (f (i + 1)).out),
  { exact mk_congr (equiv.sigma_nat_succ (λ i, (f i).out)) },
  { simp only [mk_sum, mk_out, mk_sigma, lift_id] }
end

@[simp] protected theorem supr_of_empty {ι : Type u} (f : ι → cardinal.{v}) [is_empty ι] :
  supr f = 0 :=
csupr_of_empty f

@[simp] lemma lift_mk_shrink (α : Type u) [small.{v} α] :
  lift.{max u w} #(shrink α) = lift.{max v w} #α :=
lift_mk_eq.mpr ⟨(equiv_shrink α).symm⟩

@[simp] lemma lift_mk_shrink' (α : Type u) [small.{v} α] :
  lift.{u} #(shrink α) = lift.{v} #α :=
lift_mk_shrink.{u v 0} α

@[simp] lemma lift_mk_shrink'' (α : Type (max u v)) [small.{v} α] :
  lift.{u} #(shrink α) = #α :=
by rw [←lift_umax', lift_mk_shrink'.{(max u v) v} α, ←lift_umax, lift_id]

def prod {ι : Type u} (f : ι → cardinal.{v}) : cardinal.{max u v} := #(Π i, (f i).out)

@[simp] theorem mk_pi {ι : Type u} (f : ι → Type v) :
  #(Π i, f i) = prod (λ i, #(f i)) :=
mk_congr (equiv.Pi_congr_right (λ i, out_mk_equiv.symm))

@[simp] theorem prod_const (ι : Type u) (c : cardinal.{v}) :
  prod (λ i : ι, c) = lift.{u} c ^ lift.{v} #ι :=
begin
  refine induction_on c (λ α, mk_congr (equiv.Pi_congr _ _)),
  { exact equiv.ulift.symm },
  { intro i,
    transitivity α,
    { exact out_mk_equiv },
    { exact equiv.ulift.symm } }
end

theorem prod_const' (ι : Type u) (c : cardinal.{u}) : prod (λ i : ι, c) = c ^ #ι :=
by simp

theorem prod_le_prod {ι : Type u} (f g : ι → cardinal.{v}) (h : ∀ i, f i ≤ g i) :
  prod f ≤ prod g :=
begin
  refine ⟨function.embedding.Pi_congr_right (λ i, classical.choice _)⟩,
  specialize h i,
  rwa [←mk_out (f i), ←mk_out (g i)] at h
end

@[simp] theorem prod_eq_zero {ι : Type u} (f : ι → cardinal.{v}) :
  prod f = 0 ↔ ∃ i, f i = 0 :=
begin
  lift f to ι → Type v using λ i, trivial,
  simp only [mk_eq_zero_iff, ←mk_pi, is_empty_pi]
end

theorem prod_ne_zero {ι : Type u} (f : ι → cardinal.{v}) : prod f ≠ 0 ↔ ∀ i, f i ≠ 0 :=
by simp [prod_eq_zero]

@[simp] theorem lift_prod {ι : Type u} (f : ι → cardinal.{v}) :
  lift.{w} (prod f) = prod (λ i, lift.{w} (f i)) :=
begin
  lift f to ι → Type v using λ i, trivial,
  simp only [←mk_pi, ←mk_ulift],
  refine mk_congr _,
  transitivity Π i, f i,
  { exact equiv.ulift },
  { exact equiv.Pi_congr_right (λ i, equiv.ulift.symm) }
end

@[simp] theorem lift_Inf (s : set cardinal) : lift (Inf s) = Inf (lift '' s) :=
begin
  cases set.eq_empty_or_nonempty s with hs hs,
  { rw [hs, Inf_empty, lift_zero, set.image_empty, Inf_empty] },
  { exact lift_monotone.map_Inf hs }
end

@[simp] theorem lift_infi {ι : Type u} (f : ι → cardinal.{v}) :
  lift (infi f) = infi (λ i, lift (f i)) :=
begin
  unfold infi,
  convert lift_Inf (set.range f),
  rw set.range_comp
end

theorem lift_down {c₁ : cardinal.{u}} {c₂ : cardinal.{max u v}} :
  c₂ ≤ lift c₁ → ∃ c₃, lift c₃ = c₂ :=
begin
  refine induction_on₂ c₁ c₂ (λ α β, _),
  rw [←lift_id #β, ←lift_umax, ←lift_umax.{u}, lift_mk_le],
  rintro ⟨f⟩,
  use #(set.range f),
  rw [eq_comm, lift_mk_eq],
  refine ⟨function.embedding.equiv_of_surjective _ _⟩,
  { exact function.embedding.cod_restrict (set.range f) f set.mem_range_self },
  { rintro ⟨a, ⟨b, h⟩⟩,
    simp only [function.embedding.cod_restrict_apply, subtype.mk_eq_mk],
    exact ⟨b, h⟩ }
end

theorem le_lift_iff {c₁ : cardinal.{u}} {c₂ : cardinal.{max u v}} :
  c₂ ≤ lift c₁ ↔ ∃ c₃, lift c₃ = c₂ ∧ c₃ ≤ c₁ :=
begin
  split,
  { intro h,
    rcases lift_down h with ⟨c₃, rfl⟩,
    rw lift_le at h,
    exact ⟨c₃, rfl, h⟩ },
  { rintro ⟨c₃, rfl, h⟩,
    rwa lift_le }
end

theorem lt_lift_iff {c₁ : cardinal.{u}} {c₂ : cardinal.{max u v}} :
  c₂ < lift c₁ ↔ ∃ c₃, lift c₃ = c₂ ∧ c₃ < c₁ :=
begin
  split,
  { intro h,
    rcases lift_down (le_of_lt h) with ⟨c₃, rfl⟩,
    rw lift_lt at h,
    exact ⟨c₃, rfl, h⟩ },
  { rintro ⟨c₃, rfl, h⟩,
    rwa lift_lt }
end

@[simp] theorem lift_succ (c : cardinal) : lift (order.succ c) = order.succ (lift c) :=
begin
  refine le_antisymm (le_of_not_gt _) _,
  { intro h,
    rcases lt_lift_iff.mp h with ⟨c', h₁, h₂⟩,
    rw [order.lt_succ_iff, ←lift_le, h₁, ←not_lt] at h₂,
    exact h₂ (order.lt_succ c.lift) },
  { refine order.succ_le_of_lt _,
    rw lift_lt,
    exact order.lt_succ c }
end

@[simp] theorem lift_umax_eq {c₁ : cardinal.{u}} {c₂ : cardinal.{v}} :
  lift.{max v w} c₁ = lift.{max u w} c₂ ↔ lift.{v} c₁ = lift.{u} c₂ :=
by rw [←lift_lift, ←lift_lift, lift_inj]

@[simp] theorem lift_min {c₁ c₂ : cardinal} :
  lift (min c₁ c₂) = min (lift c₁) (lift c₂) :=
lift_monotone.map_min

@[simp] theorem lift_max {c₁ c₂ : cardinal} :
  lift (max c₁ c₂) = max (lift c₁) (lift c₂) :=
lift_monotone.map_max

lemma lift_Sup {s : set cardinal} (hs : bdd_above s) :
  lift (Sup s) = Sup (lift '' s) :=
begin
  refine le_antisymm _ _,
  { rw le_cSup_iff' (bdd_above_image lift hs),
    intros c hc,
    by_contra h,
    obtain ⟨c, rfl⟩ := lift_down (le_of_not_le h),
    rw [lift_le, cSup_le_iff' hs] at h,
    refine h _,
    intros c' hc',
    change ∀ c', c' ∈ lift '' s → c' ≤ c.lift at hc,
    specialize hc (lift c') (set.mem_image_of_mem lift hc'),
    rwa lift_le at hc },
  { refine cSup_le' _,
    rintros c ⟨c, hc, rfl⟩,
    rw lift_le,
    exact le_cSup hs hc }
end

lemma lift_supr {ι : Type u} {f : ι → cardinal.{v}} (hf : bdd_above (set.range f)) :
  lift (supr f) = supr (λ i, lift (f i)) :=
by rw [supr, supr, lift_Sup hf, set.range_comp lift]

@[simp] lemma lift_supr_le_iff {ι : Type u} {f : ι → cardinal.{v}} {t : cardinal.{max v w}} :
  bdd_above (set.range f) → (lift (supr f) ≤ t ↔ ∀ i, lift (f i) ≤ t) :=
begin
  intro hf,
  rw lift_supr hf,
  exact csupr_le_iff' (bdd_above_range_comp hf lift)
end

lemma lift_supr_le {ι : Type u} {f : ι → cardinal.{v}} {t : cardinal.{max v w}} :
  bdd_above (set.range f) → (∀ i, lift (f i) ≤ t) → lift (supr f) ≤ t :=
by { intro hf, simp [hf] }

lemma {u' v'} lift_supr_le_lift_supr
  {ι : Type u} {ι' : Type u'} {f : ι → cardinal.{v}} {f' : ι' → cardinal.{v'}}
  (hf : bdd_above (set.range f)) (hf' : bdd_above (set.range f'))
  {g : ι → ι'} (h : ∀ i, lift.{v'} (f i) ≤ lift.{v} (f' (g i))) :
  lift.{v'} (supr f) ≤ lift.{v} (supr f') :=
begin
  rw [lift_supr hf, lift_supr hf'],
  refine csupr_mono' (bdd_above_range_comp hf' lift) _,
  intro i,
  use g i,
  exact h i
end

lemma lift_supr_le_lift_supr'
  {ι : Type u} {ι' : Type v} {f : ι → cardinal.{u}} {f' : ι' → cardinal.{v}}
  (hf : bdd_above (set.range f)) (hf' : bdd_above (set.range f'))
  {g : ι → ι'} (h : ∀ i, lift.{v} (f i) ≤ lift.{u} (f' (g i))) :
  lift.{v} (supr f) ≤ lift.{u} (supr f') :=
lift_supr_le_lift_supr hf hf' h

def aleph_0 : cardinal.{u} := lift #ℕ

notation `ℵ₀` := cardinal.aleph_0

lemma mk_nat : #ℕ = ℵ₀ := eq.symm (lift_id #ℕ)

theorem aleph_0_ne_zero : ℵ₀ ≠ 0 := mk_ne_zero (ulift ℕ)

theorem aleph_0_pos : 0 < ℵ₀ := pos_iff_ne_zero.mpr aleph_0_ne_zero

@[simp] theorem lift_aleph_0 : lift ℵ₀ = ℵ₀ := lift_lift #ℕ

@[simp] theorem aleph_0_le_lift {c : cardinal} : ℵ₀ ≤ lift c ↔ ℵ₀ ≤ c :=
by rw [←lift_aleph_0, lift_le]

@[simp] theorem lift_le_aleph_0 {c : cardinal} : lift c ≤ ℵ₀ ↔ c ≤ ℵ₀ :=
by rw [←lift_aleph_0, lift_le]

@[simp] theorem mk_fin (n : ℕ) : #(fin n) = n := by simp

@[simp] theorem lift_nat_cast (n : ℕ) : lift.{v} (n : cardinal.{u}) = n :=
begin
  induction n with n ih,
  { rw [nat.cast_zero, nat.cast_zero, lift_zero] },
  { rw [nat.cast_succ, nat.cast_succ, lift_add, lift_one, ih] }
end

@[simp] lemma lift_eq_nat_iff {c : cardinal.{u}} {n : ℕ} : lift.{v} c = n ↔ c = n :=
by rw [←lift_nat_cast.{u} n, lift_inj]

@[simp] lemma nat_eq_lift_iff {n : ℕ} {c : cardinal.{u}} : ↑n = lift.{v} c ↔ ↑n = c :=
by rw [←lift_nat_cast.{u} n, lift_inj]

theorem lift_mk_fin (n : ℕ) : lift #(fin n) = n := by simp

lemma mk_coe_finset {s : finset α} : #s = finset.card s := by simp

lemma mk_finset_of_fintype [fintype α] : #(finset α) = 2 ^ℕ fintype.card α := by simp

theorem card_le_of_finset (s : finset α) : ↑s.card ≤ #α :=
begin
  rw [show ↑s.card = #s, by rw [cardinal.mk_fintype, fintype.card_coe]],
  exact ⟨function.embedding.subtype (λ a, a ∈ s)⟩
end

@[simp, norm_cast] theorem nat_cast_pow {n m : ℕ} : ↑(pow n m) = n ^ m :=
begin
  induction m with m ih,
  { rw [pow_zero, nat.cast_one, nat.cast_zero, power_zero] },
  { rw [pow_succ', nat.cast_mul, ih, nat.cast_succ, power_add, power_one] }
end

@[simp, norm_cast] theorem nat_cast_le {n m : ℕ} : (n : cardinal) ≤ m ↔ n ≤ m :=
begin
  rw [←lift_mk_fin, ←lift_mk_fin, lift_le],
  split,
  { rintro ⟨⟨f, hf⟩⟩,
    have h : fintype.card (fin n) ≤ fintype.card (fin m),
    { exact fintype.card_le_of_injective f hf },
    rwa [fintype.card_fin n, fintype.card_fin m] at h },
  { intro h,
    obtain ⟨f, hf⟩ : fin n ↪o fin m := fin.cast_le h,
    exact ⟨f⟩ }
end

@[simp, norm_cast] theorem nat_cast_lt {n m : ℕ} : (n : cardinal) < m ↔ n < m :=
by { rw [←not_le, ←not_le, not_iff_not], exact nat_cast_le }

instance : char_zero cardinal := ⟨strict_mono.injective (λ m n, nat_cast_lt.mpr)⟩

theorem nat_cast_inj {n m : ℕ} : (n : cardinal) = m ↔ n = m := nat.cast_inj

lemma nat_cast_injective : function.injective (coe : ℕ → cardinal) :=
nat.cast_injective

@[simp, norm_cast, priority 900] theorem nat_succ (n : ℕ) :
  (n.succ : cardinal) = order.succ n :=
begin
  refine le_antisymm _ _,
  { exact add_one_le_succ n },
  { refine order.succ_le_of_lt _,
    rw nat_cast_lt,
    exact nat.lt_succ_self n }
end

@[simp] theorem succ_zero : order.succ (0 : cardinal) = 1 := by norm_cast

@[simp] theorem succ_one : order.succ (1 : cardinal) = 2 := by norm_cast

theorem card_le_of {n : ℕ} (h : ∀ s : finset α, s.card ≤ n) : #α ≤ n :=
begin
  refine order.le_of_lt_succ (lt_of_not_ge _),
  intro h',
  rw [←nat_succ, ←lift_mk_fin n.succ] at h',
  cases h' with f,
  specialize h (finset.map f finset.univ),
  refine not_lt_of_le h _,
  rw [finset.card_map, ←fintype.card, fintype.card_ulift, fintype.card_fin],
  exact nat.lt_succ_self n
end

theorem cantor' (c₁ : cardinal) {c₂ : cardinal} (hb : 1 < c₂) : c₁ < c₂ ^ c₁ :=
begin
  rw [←order.succ_le_iff, succ_one] at hb,
  calc c₁ < 2 ^ c₁  : cantor c₁
      ... ≤ c₂ ^ c₁ : power_le_power_right hb
end

theorem one_le_iff_pos {c : cardinal} : 1 ≤ c ↔ 0 < c :=
succ_zero ▸ order.succ_le_iff

theorem one_le_iff_ne_zero {c : cardinal} : 1 ≤ c ↔ c ≠ 0 :=
by rw [one_le_iff_pos, pos_iff_ne_zero]

theorem nat_lt_aleph_0 (n : ℕ) : ↑n < ℵ₀ :=
begin
  rw [←order.succ_le_iff, ←nat_succ, ←lift_mk_fin, aleph_0, lift_mk_le.{0 0}],
  exact ⟨⟨coe, λ n m, fin.ext⟩⟩
end

@[simp] theorem one_lt_aleph_0 : 1 < ℵ₀ :=
@nat.cast_one cardinal infer_instance ▸ nat_lt_aleph_0 1

theorem one_le_aleph_0 : 1 ≤ ℵ₀ := le_of_lt one_lt_aleph_0

theorem lt_aleph_0 {c : cardinal} : c < ℵ₀ ↔ ∃ n : ℕ, c = n :=
begin
  split,
  { intro h,
    change c < lift #ℕ at h,
    rw lt_lift_iff at h,
    rcases h with ⟨c, rfl, h, h'⟩,
    rw le_mk_iff_exists_set at h,
    rcases h with ⟨s, rfl⟩,
    suffices h : set.finite s,
    { lift s to finset ℕ using h, simp },
    contrapose! h' with h,
    replace h : infinite s := set.infinite.to_subtype h,
    exactI ⟨infinite.nat_embedding s⟩ },
  { rintro ⟨n, rfl⟩,
    exact nat_lt_aleph_0 n }
end

theorem aleph_0_le {c : cardinal} : ℵ₀ ≤ c ↔ ∀ n : ℕ, ↑n ≤ c :=
begin
  refine ⟨λ h n, _, λ h, le_of_not_lt (λ h', _)⟩,
  { transitivity ℵ₀,
    { exact le_of_lt (nat_lt_aleph_0 n) },
    { exact h } },
  { rw lt_aleph_0 at h',
    rcases h' with ⟨n, rfl⟩,
    specialize h n.succ,
    rw nat_cast_le at h,
    exact not_le_of_lt (nat.lt_succ_self n) h }
end

theorem lt_aleph_0_iff_fintype : #α < ℵ₀ ↔ nonempty (fintype α) :=
begin
  transitivity ∃ n, #α = ↑n,
  { exact lt_aleph_0 },
  { split,
    { rintro ⟨n, h⟩,
      rw ←lift_mk_fin n at h,
      cases quotient.exact h with e,
      exact ⟨fintype.of_equiv (ulift (fin n)) e.symm⟩ },
    { rintro ⟨h⟩,
      exactI ⟨fintype.card α, mk_fintype α⟩ } }
end

theorem lt_aleph_0_of_fintype (α : Type u) [fintype α] : #α < ℵ₀ :=
lt_aleph_0_iff_fintype.mpr ⟨infer_instance⟩

theorem lt_aleph_0_iff_finite {s : set α} : #s < ℵ₀ ↔ s.finite :=
begin
  transitivity nonempty (fintype s),
  { exact lt_aleph_0_iff_fintype },
  { rw set.finite_def }
end

instance can_lift_cardinal_nat : can_lift cardinal ℕ :=
⟨coe, λ c, c < ℵ₀, λ c h, let ⟨n, h⟩ := lt_aleph_0.mp h in ⟨n, h.symm⟩⟩

theorem add_lt_aleph_0 {c₁ c₂ : cardinal} (h₁ : c₁ < ℵ₀) (h₂ : c₂ < ℵ₀) :
  c₁ + c₂ < ℵ₀ :=
begin
  rw lt_aleph_0 at h₁ h₂,
  rcases h₁ with ⟨n, rfl⟩,
  rcases h₂ with ⟨m, rfl⟩,
  rw ←nat.cast_add,
  exact nat_lt_aleph_0 (n + m)
end

lemma add_lt_aleph_0_iff {c₁ c₂ : cardinal} : c₁ + c₂ < ℵ₀ ↔ c₁ < ℵ₀ ∧ c₂ < ℵ₀ :=
begin
  split,
  { refine λ h, ⟨lt_of_le_of_lt _ h, lt_of_le_of_lt _ h⟩,
    { exact self_le_add_right c₁ c₂ },
    { exact self_le_add_left c₂ c₁ } },
  { rintros ⟨h₁, h₂⟩,
    exact add_lt_aleph_0 h₁ h₂ }
end

lemma aleph_0_le_add_iff {c₁ c₂ : cardinal} : ℵ₀ ≤ c₁ + c₂ ↔ ℵ₀ ≤ c₁ ∨ ℵ₀ ≤ c₂ :=
by rw [←not_lt, ←not_lt, ←not_lt, add_lt_aleph_0_iff, not_and_distrib]

lemma nsmul_lt_aleph_0_iff {n : ℕ} {c : cardinal} : n • c < ℵ₀ ↔ n = 0 ∨ c < ℵ₀ :=
begin
  cases n with n,
  { rw [zero_smul, eq_self_iff_true, true_or, iff_true],
    exact nat_lt_aleph_0 0 },
  { simp only [nat.succ_ne_zero, false_or],
    induction n with n ih,
    { rw [nsmul_eq_mul, nat.cast_one, one_mul] },
    { rw [succ_nsmul, add_lt_aleph_0_iff, ih, and_self] } }
end

lemma nsmul_lt_aleph_0_iff_of_ne_zero {n : ℕ} {c : cardinal} (h : n ≠ 0) :
  n • c < ℵ₀ ↔ c < ℵ₀ :=
begin
  transitivity n = 0 ∨ c < ℵ₀,
  { exact nsmul_lt_aleph_0_iff },
  { exact or_iff_right h }
end

theorem mul_lt_aleph_0 {c₁ c₂ : cardinal} (h₁ : c₁ < ℵ₀) (h₂ : c₂ < ℵ₀) :
  c₁ * c₂ < ℵ₀ :=
begin
  rw lt_aleph_0 at h₁ h₂,
  rcases h₁ with ⟨n, rfl⟩,
  rcases h₂ with ⟨m, rfl⟩,
  rw ←nat.cast_mul,
  exact nat_lt_aleph_0 (n * m)
end

lemma mul_lt_aleph_0_iff {c₁ c₂ : cardinal} :
  c₁ * c₂ < ℵ₀ ↔ c₁ = 0 ∨ c₂ = 0 ∨ (c₁ < ℵ₀ ∧ c₂ < ℵ₀) :=
begin
  split,
  { intro h,
    by_cases h₁ : c₁ = 0, exact or.inl h₁, right,
    by_cases h₂ : c₂ = 0, exact or.inl h₂, right,
    rw [←ne, ←one_le_iff_ne_zero] at h₁ h₂,
    split,
    { rw ←mul_one c₁,
      exact lt_of_le_of_lt (mul_le_mul' le_rfl h₂) h },
    { rw ←one_mul c₂,
      exact lt_of_le_of_lt (mul_le_mul' h₁ le_rfl) h } },
  { rintro (rfl | rfl | ⟨h₁, h₂⟩),
    { rw [zero_mul], exact aleph_0_pos },
    { rw [mul_zero], exact aleph_0_pos },
    { exact mul_lt_aleph_0 h₁ h₂ } }
end

lemma aleph_0_le_mul_iff {c₁ c₂ : cardinal} :
  ℵ₀ ≤ c₁ * c₂ ↔ c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ (ℵ₀ ≤ c₁ ∨ ℵ₀ ≤ c₂) :=
begin
  have h := not_congr (@mul_lt_aleph_0_iff c₁ c₂),
  rwa [not_lt, not_or_distrib, not_or_distrib, not_and_distrib, not_lt, not_lt] at h
end

lemma aleph_0_le_mul_iff' {c₁ c₂ : cardinal.{u}} :
  ℵ₀ ≤ c₁ * c₂ ↔ (c₁ ≠ 0 ∧ ℵ₀ ≤ c₂) ∨ (ℵ₀ ≤ c₁ ∧ c₂ ≠ 0) :=
begin
  transitivity c₁ ≠ 0 ∧ c₂ ≠ 0 ∧ (ℵ₀ ≤ c₁ ∨ ℵ₀ ≤ c₂),
  { exact aleph_0_le_mul_iff },
  { have h₁ : ℵ₀ ≤ c₁ → c₁ ≠ 0 := ne_bot_of_le_ne_bot aleph_0_ne_zero,
    have h₂ : ℵ₀ ≤ c₂ → c₂ ≠ 0 := ne_bot_of_le_ne_bot aleph_0_ne_zero,
    tauto }
end

lemma mul_lt_aleph_0_iff_of_ne_zero {c₁ c₂ : cardinal} (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
  c₁ * c₂ < ℵ₀ ↔ c₁ < ℵ₀ ∧ c₂ < ℵ₀ :=
by simp only [mul_lt_aleph_0_iff, h₁, h₂, false_or]

theorem power_lt_aleph_0 {c₁ c₂ : cardinal} (h₁ : c₁ < ℵ₀) (h₂ : c₂ < ℵ₀) :
  c₁ ^ c₂ < ℵ₀ :=
begin
  rw lt_aleph_0 at h₁ h₂,
  rcases h₁ with ⟨n, rfl⟩,
  rcases h₂ with ⟨m, rfl⟩,
  rw ←nat_cast_pow,
  exact nat_lt_aleph_0 (pow n m)
end

lemma eq_one_iff_unique : #α = 1 ↔ subsingleton α ∧ nonempty α :=
begin
  transitivity #α ≤ 1 ∧ 1 ≤ #α,
  { exact le_antisymm_iff },
  { refine and_congr le_one_iff_subsingleton _,
    transitivity #α ≠ 0,
    { exact one_le_iff_ne_zero },
    { exact mk_ne_zero_iff } }
end

lemma eq_one_iff_unique' : #α = 1 ↔ nonempty (unique α) :=
begin
  transitivity subsingleton α ∧ nonempty α,
  { exact eq_one_iff_unique },
  { exact iff.symm (unique_iff_subsingleton_and_nonempty α) }
end

theorem infinite_iff : infinite α ↔ ℵ₀ ≤ #α :=
by rw [←not_lt, lt_aleph_0_iff_fintype, not_nonempty_iff, is_empty_fintype]

@[simp] lemma aleph_0_le_mk (α : Type u) [infinite α] : ℵ₀ ≤ #α :=
infinite_iff.mp infer_instance

lemma encodable_iff : nonempty (encodable α) ↔ #α ≤ ℵ₀ :=
begin
  split,
  { rintro ⟨h⟩,
    refine ⟨_⟩,
    transitivity ℕ,
    { exact @encodable.encode' α h },
    { exact equiv.ulift.symm.to_embedding } },
  { rintro ⟨f⟩,
    replace f : α ↪ ℕ := function.embedding.trans f equiv.ulift.to_embedding,
    exact ⟨encodable.of_inj f (function.embedding.injective f)⟩ }
end

@[simp] lemma mk_le_aleph_0 (α : Type u) [encodable α] : #α ≤ ℵ₀ :=
encodable_iff.mp ⟨infer_instance⟩

lemma denumerable_iff : nonempty (denumerable α) ↔ #α = ℵ₀ :=
begin
  split,
  { rintro ⟨h⟩,
    refine mk_congr _,
    transitivity ℕ,
    { exact @denumerable.eqv α h },
    { exact equiv.ulift.symm } },
  { intro h,
    cases quotient.exact h with e,
    refine ⟨denumerable.mk' _⟩,
    transitivity ulift ℕ,
    { exact e },
    { exact equiv.ulift } }
end

@[simp] lemma mk_denumerable (α : Type u) [denumerable α] : #α = ℵ₀ :=
denumerable_iff.mp ⟨infer_instance⟩

@[simp] lemma mk_set_le_aleph_0 (s : set α) : #s ≤ ℵ₀ ↔ set.countable s :=
begin
  rw [set.countable_iff_exists_injective],
  split,
  { rintro ⟨f⟩,
    obtain ⟨f, hf⟩ : s ↪ ℕ := function.embedding.trans f equiv.ulift.to_embedding,
    exact ⟨f, hf⟩ },
  { rintro ⟨f, hf⟩,
    have f : s ↪ ulift ℕ := function.embedding.trans ⟨f, hf⟩ equiv.ulift.symm.to_embedding,
    exact ⟨f⟩ }
end

@[simp] lemma mk_subtype_le_aleph_0 (p : α → Prop) :
  #{a // p a} ≤ ℵ₀ ↔ set.countable {a | p a} :=
mk_set_le_aleph_0 (set_of p)

@[simp] lemma aleph_0_add_aleph_0 : (ℵ₀ + ℵ₀ : cardinal.{u}) = ℵ₀ :=
mk_denumerable (ulift.{u} ℕ ⊕ ulift.{u} ℕ)

lemma aleph_0_mul_aleph_0 : (ℵ₀ * ℵ₀ : cardinal.{u}) = ℵ₀ :=
mk_denumerable (ulift.{u} ℕ × ulift.{u} ℕ)

@[simp] lemma add_le_aleph_0 {c₁ c₂ : cardinal} : c₁ + c₂ ≤ ℵ₀ ↔ c₁ ≤ ℵ₀ ∧ c₂ ≤ ℵ₀ :=
begin
  split,
  { intro h,
    split,
    { exact le_trans le_self_add h },
    { exact le_trans le_add_self h } },
  { rintro ⟨h₁, h₂⟩,
    exact aleph_0_add_aleph_0 ▸ add_le_add h₁ h₂ }
end

noncomputable def to_nat.to_fun : cardinal → ℕ :=
λ c, if h : c < ℵ₀ then classical.some (lt_aleph_0.mp h) else 0

theorem to_nat.map_zero' : to_nat.to_fun 0 = 0 :=
begin
  unfold to_nat.to_fun,
  have h : 0 < ℵ₀ := nat_lt_aleph_0 0,
  rw [dif_pos h, ←nat_cast_inj, ←classical.some_spec (lt_aleph_0.mp h), nat.cast_zero]
end

noncomputable def to_nat : zero_hom cardinal ℕ :=
{ to_fun := to_nat.to_fun, map_zero' := to_nat.map_zero' }

lemma to_nat_apply_of_lt_aleph_0 {c : cardinal} (h : c < ℵ₀) :
  to_nat c = classical.some (lt_aleph_0.mp h) :=
dif_pos h

lemma to_nat_apply_of_aleph_0_le {c : cardinal} (h : ℵ₀ ≤ c) : to_nat c = 0 :=
dif_neg (not_lt_of_le h)

lemma cast_to_nat_of_lt_aleph_0 {c : cardinal} (h : c < ℵ₀) : ↑(to_nat c) = c :=
by rw [to_nat_apply_of_lt_aleph_0 h, ←classical.some_spec (lt_aleph_0.mp h)]

lemma cast_to_nat_of_aleph_0_le {c : cardinal} (h : ℵ₀ ≤ c) :
  (to_nat c : cardinal) = 0 :=
by rw [to_nat_apply_of_aleph_0_le h, nat.cast_zero]

lemma to_nat_le_iff_le_of_lt_aleph_0 {c₁ c₂ : cardinal} (h₁ : c₁ < ℵ₀) (h₂ : c₂ < ℵ₀) :
  to_nat c₁ ≤ to_nat c₂ ↔ c₁ ≤ c₂ :=
by rw [←nat_cast_le, cast_to_nat_of_lt_aleph_0 h₁, cast_to_nat_of_lt_aleph_0 h₂]

lemma to_nat_lt_iff_lt_of_lt_aleph_0 {c₁ c₂ : cardinal} (h₁ : c₁ < ℵ₀) (h₂ : c₂ < ℵ₀) :
  to_nat c₁ < to_nat c₂ ↔ c₁ < c₂ :=
by rw [←nat_cast_lt, cast_to_nat_of_lt_aleph_0 h₁, cast_to_nat_of_lt_aleph_0 h₂]

lemma to_nat_le_of_le_of_lt_aleph_0 {c₁ c₂ : cardinal} (h₁ : c₂ < ℵ₀) (h₂ : c₁ ≤ c₂) :
  to_nat c₁ ≤ to_nat c₂ :=
by rwa [to_nat_le_iff_le_of_lt_aleph_0 (lt_of_le_of_lt h₂ h₁) h₁]

lemma to_nat_lt_of_lt_of_lt_aleph_0 {c₁ c₂ : cardinal} (h₁ : c₂ < ℵ₀) (h₂ : c₁ < c₂) :
  to_nat c₁ < to_nat c₂ :=
by rwa [to_nat_lt_iff_lt_of_lt_aleph_0 (lt_trans h₂ h₁) h₁]

@[simp] lemma to_nat_cast (n : ℕ) : to_nat n = n :=
begin
  have h : ↑n < ℵ₀ := nat_lt_aleph_0 n,
  rw [to_nat_apply_of_lt_aleph_0 h, ←nat_cast_inj, ←classical.some_spec (lt_aleph_0.mp h)]
end

lemma to_nat_right_inverse : function.right_inverse coe to_nat :=
to_nat_cast

lemma to_nat_surjective : function.surjective to_nat :=
to_nat_right_inverse.surjective

@[simp] lemma mk_to_nat_of_infinite [infinite α] : to_nat #α = 0 :=
dif_neg (not_lt_of_le (infinite_iff.mp infer_instance))

@[simp] theorem aleph_0_to_nat : to_nat ℵ₀ = 0 :=
to_nat_apply_of_aleph_0_le le_rfl

lemma mk_to_nat_eq_card [fintype α] : to_nat #α = fintype.card α := by simp

@[simp] lemma zero_to_nat : to_nat 0 = 0 :=
by rw [←to_nat_cast 0, nat.cast_zero]

@[simp] lemma one_to_nat : to_nat 1 = 1 :=
by rw [←to_nat_cast 1, nat.cast_one]

@[simp] lemma to_nat_eq_one {c : cardinal} : to_nat c = 1 ↔ c = 1 :=
begin
  split,
  { intro h,
    transitivity ↑(to_nat c),
    { replace h : ¬ ℵ₀ ≤ c := one_ne_zero ∘ h.symm.trans ∘ to_nat_apply_of_aleph_0_le,
      rw cast_to_nat_of_lt_aleph_0 (lt_of_not_ge h) },
    { replace h : (to_nat c : cardinal) = ↑1 := congr_arg coe h,
      rwa nat.cast_one at h } },
  { rintro rfl, exact one_to_nat }
end

lemma to_nat_eq_one_iff_unique : to_nat #α = 1 ↔ subsingleton α ∧ nonempty α :=
begin
  transitivity #α = 1,
  { exact to_nat_eq_one },
  { exact eq_one_iff_unique }
end

@[simp] lemma to_nat_lift (c : cardinal) : to_nat (lift c) = to_nat c :=
begin
  refine nat_cast_injective _,
  cases lt_or_ge c ℵ₀ with h₁ h₁,
  { have h₂ : lift c < ℵ₀ := lift_aleph_0 ▸ lift_lt.mpr h₁,
    rw [cast_to_nat_of_lt_aleph_0 h₂, ←lift_nat_cast, cast_to_nat_of_lt_aleph_0 h₁] },
  { have h₂ : ℵ₀ ≤ lift c := lift_aleph_0 ▸ lift_le.mpr h₁,
    rw [cast_to_nat_of_aleph_0_le h₂, cast_to_nat_of_aleph_0_le h₁] }
end

lemma to_nat_congr (e : α ≃ β) : to_nat #α = to_nat #β :=
by rw [←to_nat_lift, lift_mk_eq.mpr ⟨e⟩, to_nat_lift]

@[simp] lemma to_nat_mul (c₁ c₂ : cardinal) :
  to_nat (c₁ * c₂) = to_nat c₁ * to_nat c₂ :=
begin
  rcases eq_or_ne c₁ 0 with rfl | h₁₁,
  { rw [zero_mul, zero_to_nat, zero_mul] },
  rcases eq_or_ne c₂ 0 with rfl | h₂₁,
  { rw [mul_zero, zero_to_nat, mul_zero] },
  cases lt_or_le c₁ ℵ₀ with h₁₂ h₁₂,
  { cases lt_or_le c₂ ℵ₀ with h₂₂ h₂₂,
    { lift c₁ to ℕ using h₁₂,
      lift c₂ to ℕ using h₂₂,
      rw [←nat.cast_mul, to_nat_cast, to_nat_cast, to_nat_cast] },
    { have h : ℵ₀ ≤ c₁ * c₂ := aleph_0_le_mul_iff'.mpr (or.inl ⟨h₁₁, h₂₂⟩),
      rw [to_nat_apply_of_aleph_0_le h₂₂, mul_zero, to_nat_apply_of_aleph_0_le h] } },
  { have h : ℵ₀ ≤ c₁ * c₂ := aleph_0_le_mul_iff'.mpr (or.inr ⟨h₁₂, h₂₁⟩),
    rw [to_nat_apply_of_aleph_0_le h₁₂, zero_mul, to_nat_apply_of_aleph_0_le h] },
end

@[simp] lemma to_nat_add_of_lt_aleph_0 {c₁ : cardinal.{u}} {c₂ : cardinal.{v}} :
  c₁ < ℵ₀ → c₂ < ℵ₀ → to_nat (lift.{v} c₁ + lift.{u} c₂) = to_nat c₁ + to_nat c₂ :=
begin
  intros h₁ h₂,
  refine cardinal.nat_cast_injective _,
  replace h₁ : lift.{v} c₁ < ℵ₀ := lift_aleph_0 ▸ lift_lt.mpr h₁,
  replace h₂ : lift.{u} c₂ < ℵ₀ := lift_aleph_0 ▸ lift_lt.mpr h₂,
  rw [nat.cast_add, ←to_nat_lift c₁, ←to_nat_lift c₂, cast_to_nat_of_lt_aleph_0 h₁, cast_to_nat_of_lt_aleph_0 h₂],
  exact cast_to_nat_of_lt_aleph_0 (add_lt_aleph_0 h₁ h₂)
end

noncomputable def to_enat.to_fun : cardinal → enat :=
λ c, if c < ℵ₀ then to_nat c else ⊤

theorem to_enat.map_zero' : to_enat.to_fun 0 = 0 :=
begin
  unfold to_enat.to_fun,
  have h : 0 < ℵ₀ := nat_lt_aleph_0 0,
  rw [if_pos h, zero_to_nat, nat.cast_zero]
end

theorem to_enat.map_add' (c₁ c₂ : cardinal) :
  to_enat.to_fun (c₁ + c₂) = to_enat.to_fun c₁ + to_enat.to_fun c₂ :=
begin
  unfold to_enat.to_fun,
  by_cases h₁ : c₁ < ℵ₀,
  { by_cases h₂ : c₂ < ℵ₀,
    { obtain ⟨n, rfl⟩ := lt_aleph_0.mp h₁,
      obtain ⟨m, rfl⟩ := lt_aleph_0.mp h₂,
      rw [if_pos (add_lt_aleph_0 h₁ h₂), if_pos h₁, if_pos h₂],
      rw [←nat.cast_add, to_nat_cast, to_nat_cast, to_nat_cast, nat.cast_add] },
    { have h : ¬ c₁ + c₂ < ℵ₀,
      { contrapose! h₂,
        exact lt_of_le_of_lt le_add_self h₂ },
      rw [if_neg h₂, if_neg h, enat.add_top] } },
  { have h : ¬ c₁ + c₂ < ℵ₀,
    { contrapose! h₁,
      exact lt_of_le_of_lt le_self_add h₁ },
    rw [if_neg h₁, if_neg h, enat.top_add] }
end

noncomputable def to_enat : cardinal →+ enat :=
{ to_fun    := to_enat.to_fun,
  map_zero' := to_enat.map_zero',
  map_add'  := to_enat.map_add' }

lemma to_enat_apply_of_lt_aleph_0 {c : cardinal} (h : c < ℵ₀) : to_enat c = to_nat c :=
if_pos h

lemma to_enat_apply_of_aleph_0_le {c : cardinal} (h : ℵ₀ ≤ c) : c.to_enat = ⊤ :=
if_neg (not_lt_of_le h)

@[simp] lemma to_enat_cast (n : ℕ) : to_enat n = n :=
by rw [to_enat_apply_of_lt_aleph_0 (nat_lt_aleph_0 n), to_nat_cast]

@[simp] lemma mk_to_enat_of_infinite [infinite α] : to_enat #α = ⊤ :=
to_enat_apply_of_aleph_0_le (infinite_iff.mp infer_instance)

@[simp] theorem aleph_0_to_enat : to_enat ℵ₀ = ⊤ :=
to_enat_apply_of_aleph_0_le le_rfl

lemma to_enat_surjective : function.surjective to_enat :=
begin
  refine λ n, enat.cases_on n _ (λ n, _),
  { exact ⟨ℵ₀, to_enat_apply_of_aleph_0_le le_rfl⟩ },
  { exact ⟨n, to_enat_cast n⟩ }
end

lemma mk_to_enat_eq_coe_card [fintype α] : to_enat #α = fintype.card α := by simp

lemma mk_int : #ℤ = ℵ₀ := mk_denumerable ℤ

lemma mk_pnat : #ℕ+ = ℵ₀ := mk_denumerable ℕ+

theorem sum_lt_prod {ι : Type u} (f g : ι → cardinal.{v}) (h : ∀ i, f i < g i) :
  sum f < prod g :=
begin
  refine lt_of_not_ge _,
  rintro ⟨F⟩,
  haveI I : nonempty (Π i, (g i).out),
  { refine ⟨λ i, classical.choice (mk_ne_zero_iff.mp _)⟩,
    rw mk_out,
    exact ne_bot_of_gt (h i) },
  let G : (Σ i, (f i).out) → Π i, (g i).out := function.inv_fun F,
  have hG : function.surjective G,
  { exact function.inv_fun_surjective (function.embedding.injective F) },
  have hC : ∀ i, ∃ y, ∀ x, G ⟨i, x⟩ i ≠ y,
  { simp only [←not_exists, ←not_forall],
    change ¬ ∃ i, ∀ y, ∃ x, G ⟨i, x⟩ i = y,
    rintro ⟨i, hi⟩,
    refine not_le_of_lt (h i) _,
    rw [←mk_out (f i), ←mk_out (g i)],
    exact ⟨function.embedding.of_surjective (λ x, G ⟨i, x⟩ i) hi⟩ },
  choose C hC using hC,
  obtain ⟨⟨i, x⟩, h⟩ := hG C,
  exact hC i x (congr_fun h i),
end

namespace choice

def lt (α β : Type u) : Type u :=
pprod (α ↪ β) ((β ↪ α) → false)

noncomputable def lt.of_cardinal_lt : #α < #β → lt α β :=
λ ⟨f, h⟩, ⟨classical.choice f, λ f, h ⟨f⟩⟩

def lt.to_cardinal_lt : lt α β → #α < #β :=
λ ⟨f, h⟩, ⟨⟨f⟩, λ f, nonempty.rec h f⟩

axiom sum_lt_prod {α : Type u} (β₁ : α → Type v) (β₂ : α → Type v) :
  (Π a, lt (β₁ a) (β₂ a)) → lt (Σ a, β₁ a) (Π a, β₂ a)

noncomputable example {α : Type u} (β₁ : α → Type v) (β₂ : α → Type v) :
  (Π a, lt (β₁ a) (β₂ a)) → lt (Σ a, β₁ a) (Π a, β₂ a) :=
begin
  intro h,
  replace h := λ a, lt.to_cardinal_lt (h a),
  replace h := cardinal.sum_lt_prod (λ a, #(β₁ a)) (λ a, #(β₂ a)) h,
  replace h := lt.of_cardinal_lt h,
  dsimp only at h,
  rcases h with ⟨⟨f, hf⟩, h⟩,
  refine ⟨⟨_, _⟩, _⟩,
  { rintros ⟨a₁, b₁⟩ a₂,
    have e := classical.choice (quotient.mk_out (β₁ a₁)),
    exact classical.choice (quotient.mk_out (β₂ a₂)) (f ⟨a₁, e.symm b₁⟩ a₂) },
  { clear h,
    rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h,
    replace h : f ⟨a₁, (classical.choice (quotient.mk_out (β₁ a₁))).symm b₁⟩ = f ⟨a₂, (classical.choice (quotient.mk_out (β₁ a₂))).symm b₂⟩,
    { exact funext (λ a, (classical.choice (quotient.mk_out (β₂ a))).injective (congr_fun h a)) },
    specialize hf h, clear h,
    simp only at hf,
    rcases hf with ⟨rfl, h⟩,
    rw (classical.choice (quotient.mk_out (β₁ a₁))).symm.injective (eq_of_heq h) },
  { clear hf f,
    refine λ h', h _, clear h,
    cases h' with f hf,
    refine ⟨_, _⟩,
    { intro g,
      cases f (λ a, classical.choice (quotient.mk_out (β₂ a)) (g a)) with a b,
      exact ⟨a, (classical.choice (quotient.mk_out (β₁ a))).symm b⟩ },
    { intros g₁ g₂ h,
      dsimp only at h,
      let F : (Σ a, β₁ a) → Σ a, (#(β₁ a)).out := @sigma.rec α β₁ (λ x, Σ a, (#(β₁ a)).out) (λ a b, ⟨a, (classical.choice (quotient.mk_out (β₁ a))).symm b⟩),
      suffices h' : function.injective F,
      { exact funext (λ a, (classical.choice (quotient.mk_out (β₂ a))).injective (congr_fun (hf (h' h)) a)) },
      rintros ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h,
      simp only [F] at h,
      rcases h with ⟨rfl, h⟩,
      rw (classical.choice (quotient.mk_out (β₁ a₁))).symm.injective (eq_of_heq h) } }
end

axiom not_not {p : Prop} : ¬¬p → p

theorem choice {α : Type u} {β : α → Type v} :
  (∀ a, nonempty (β a)) → nonempty (Π a, β a) :=
begin
  intro h,
  suffices : Π a, lt pempty (β a),
  { cases sum_lt_prod (λ a, pempty) β this with f h,
    exact not_not (λ h', h ⟨λ f, false.elim (h' ⟨f⟩), λ f, false.elim (h' ⟨f⟩)⟩) },
  intro a,
  specialize h a,
  refine ⟨⟨pempty.elim, λ x, pempty.elim x⟩, _⟩,
  rintro ⟨f, hf⟩,
  cases h with b,
  exact pempty.elim (f b)
end

theorem choice' {α : Sort u} {β : α → Sort v} :
  (∀ a, nonempty (β a)) → nonempty (Π a, β a) :=
begin
  intro h,
  suffices : ∀ a, nonempty (plift (β (plift.down a))),
  { cases choice this with h,
    exact ⟨λ a, (h ⟨a⟩).down⟩ },
  rintro ⟨a⟩,
  cases h a with h,
  exact ⟨⟨h⟩⟩
end

end choice

end cardinal
