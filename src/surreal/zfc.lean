import tactic

universe u

inductive pSet : Type (u+1)
| mk : ∀ α : Type u, (α → pSet) → pSet

namespace pSet

def equiv : pSet → pSet → Prop
| (mk α fα) (mk β fβ) :=
(∀ a, ∃ b, equiv (fα a) (fβ b)) ∧ (∀ b, ∃ a, equiv (fα a) (fβ b))

/-
def equiv (x y : pSet) : Prop :=
pSet.rec (λ α z m ⟨β, B⟩, (∀ a, ∃ b, m a (B b)) ∧ (∀ b, ∃ a, m a (B b))) x y

#check @pSet.rec
Π {motive : pSet → Sort u},
  (Π α (fα : α → pSet),
    (Π (a : α), motive (fα a)) → motive (mk α fα)) →
  Π (n : pSet), motive n
-/

def equiv' (A B : pSet.{u}) : Prop :=
begin
  refine pSet.rec _ A B,
  refine λ α fα ih, _,
  rintro ⟨β, fβ⟩,
  exact (∀ a, ∃ b, ih a (fβ b)) ∧ (∀ b, ∃ a, ih a (fβ b))
end

def equiv'' (A B : pSet.{u}) : Prop :=
begin
  induction A with α fα ih generalizing B,
  change α → pSet → Prop at ih,
  cases B with β fβ,
  exact (∀ a, ∃ b, ih a (fβ b)) ∧ (∀ b, ∃ a, ih a (fβ b))
end

example (A B : pSet.{u}) : equiv A B ↔ equiv' A B :=
begin
  split,
  all_goals {
    induction A with α fα ih generalizing B,
    change ∀ a B, _ at ih,
    cases B with β fβ,
    rintro ⟨h₁, h₂⟩,
    split,
    { clear h₂, rename h₁ h,
      intro a,
      specialize h a,
      cases h with b hb,
      use b,
      exact ih a (fβ b) hb },
    { clear h₁, rename h₂ h,
      intro b,
      specialize h b,
      cases h with a ha,
      use a,
      exact ih a (fβ b) ha }
  }
end

example (A B : pSet.{u}) : equiv' A B ↔ equiv'' A B :=
by tauto

theorem equiv.refl (A : pSet.{u}) : equiv A A :=
begin
  induction A with α fα ih,
  change ∀ a, equiv (fα a) (fα a) at ih,
  exact ⟨λ a, ⟨a, ih a⟩, λ a, ⟨a, ih a⟩⟩
end

theorem equiv.rfl : ∀ {A : pSet.{u}}, equiv A A := equiv.refl

theorem equiv.symm {A B : pSet.{u}} : equiv A B → equiv B A :=
begin
  induction A with α fα ih generalizing B,
  change ∀ a B, equiv (fα a) B → equiv B (fα a) at ih,
  cases B with β fβ,
  rintro ⟨h₁, h₂⟩,
  split,
  { clear h₁, rename h₂ h,
    intro b,
    specialize h b,
    cases h with a ha,
    use a,
    exact ih a (fβ b) ha },
  { clear h₂, rename h₁ h,
    intro a,
    specialize h a,
    cases h with b hb,
    use b,
    exact ih a (fβ b) hb }
end

theorem equiv.trans {A B C : pSet.{u}} (h₁ : equiv A B) (h₂ : equiv B C) :
  equiv A C :=
begin
  induction A with α fα ih generalizing B C,
  change ∀ a B C, equiv (fα a) B → equiv B C → equiv (fα a) C at ih,
  cases B with β fβ,
  cases C with γ fγ,
  cases h₁ with h₁₁ h₁₂,
  cases h₂ with h₂₁ h₂₂,
  split,
  { clear h₁₂ h₂₂, rename h₁₁ h₁, rename h₂₁ h₂,
    intro a,
    specialize h₁ a,
    cases h₁ with b hb,
    specialize h₂ b,
    cases h₂ with c hc,
    use c,
    exact ih a (fβ b) (fγ c) hb hc },
  { clear h₁₁ h₂₁, rename h₁₂ h₁, rename h₂₂ h₂,
    intro c,
    specialize h₂ c,
    cases h₂ with b hb,
    specialize h₁ b,
    cases h₁ with a ha,
    use a,
    exact ih a (fβ b) (fγ c) ha hb }
end

instance setoid : setoid pSet.{u} :=
⟨pSet.equiv, equiv.refl, @equiv.symm, @equiv.trans⟩

end pSet

def Set : Type (u+1) := quotient pSet.setoid.{u}

/-
inductive pgame : Type (u+1)
| mk : ∀ α β : Type u, (α → pgame) → (β → pgame) → pgame
-/