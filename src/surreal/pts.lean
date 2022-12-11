import tactic.basic

-- Lean version 3.45.0

section

parameters (C : Type) [decidable_eq C]

inductive term : Type
| var : ℕ → term
| const : C → term
| app : term → term → term
| lam : term → term → term
| pi : term → term → term

instance : decidable_eq term :=
begin
  intros a a',
  induction a with x c f a ih₁ ih₂ A b ih₁ ih₂ A B ih₁ ih₂ generalizing a',
  { cases a' with x'; try { apply is_false, intro h, cases h, done },
    by_cases h : x = x',
    { subst h,
      exact is_true rfl },
    { apply is_false,
      intro h',
      cases h',
      exact h rfl } },
  { cases a' with _ c'; try { apply is_false, intro h, cases h, done },
    by_cases h : c = c',
    { subst h,
      exact is_true rfl },
    { apply is_false,
      intro h',
      cases h',
      exact h rfl } },
  { cases a' with _ _ f' a'; try { apply is_false, intro h, cases h, done },
    specialize ih₁ f',
    specialize ih₂ a',
    cases ih₁, apply is_false, intro h, cases h, exact ih₁ rfl,
    cases ih₂, apply is_false, intro h, cases h, exact ih₂ rfl,
    subst ih₁, subst ih₂,
    exact is_true rfl },
  { cases a' with _ _ _ _ A' b'; try { apply is_false, intro h, cases h, done },
    specialize ih₁ A',
    specialize ih₂ b',
    cases ih₁, apply is_false, intro h, cases h, exact ih₁ rfl,
    cases ih₂, apply is_false, intro h, cases h, exact ih₂ rfl,
    subst ih₁, subst ih₂,
    exact is_true rfl },
  { cases a' with _ _ _ _ _ _ A' B'; try { apply is_false, intro h, cases h, done },
    specialize ih₁ A',
    specialize ih₂ B',
    cases ih₁, apply is_false, intro h, cases h, exact ih₁ rfl,
    cases ih₂, apply is_false, intro h, cases h, exact ih₂ rfl,
    subst ih₁, subst ih₂,
    exact is_true rfl }
end

instance has_coe_var : has_coe ℕ term := ⟨term.var⟩
instance has_coe_const : has_coe C term := ⟨term.const⟩

def shift (σ : ℕ → term) : ℕ → term
| 0 := term.var 0
| (x + 1) := σ x

def substs : (ℕ → term) → term → term
| σ (term.var x) := σ x
| σ (term.const c) := term.const c
| σ (term.app f a) := term.app (substs σ f) (substs σ a)
| σ (term.lam A b) := term.lam (substs σ A) (substs (shift σ) b)
| σ (term.pi A B) := term.lam (substs σ A) (substs (shift σ) B)

def subst.weak : term → term :=
substs (term.var ∘ nat.succ)

def subst (a : term) : term → term :=
let σ (x : ℕ) : term :=
  match x with
  | 0 := a
  | (x + 1) := x
  end in
substs σ

parameters (S : set C) (A : set (C × C)) (R : set (C × C × C))
parameters [decidable_pred S] [decidable_pred A] [decidable_pred R]

parameter hA : ∀ {c s}, (c, s) ∈ A → s ∈ S
parameter hR₁ : ∀ {s₁ s₂ s₃}, (s₁, s₂, s₃) ∈ R → s₁ ∈ S
parameter hR₂ : ∀ {s₁ s₂ s₃}, (s₁, s₂, s₃) ∈ R → s₂ ∈ S
parameter hR₃ : ∀ {s₁ s₂ s₃}, (s₁, s₂, s₃) ∈ R → s₃ ∈ S

abbreviation context : Type := list term

inductive entails₁ : context → term → term → Prop
| ax₁ {c s} : (c, s) ∈ A → entails₁ [] ↑c ↑s
| start {Γ A s} : s ∈ S → entails₁ Γ A ↑s → entails₁ (A :: Γ) ↑0 A
| weak {Γ A B C s} : s ∈ S → entails₁ Γ A B → entails₁ Γ C ↑s → entails₁ (C :: Γ) (subst.weak A) (subst.weak B)
| pi {Γ A B s₁ s₂ s₃} : (s₁, s₂, s₃) ∈ R → entails₁ Γ A ↑s₁ → entails₁ (A :: Γ) B ↑s₂ → entails₁ Γ (term.pi A B) ↑s₃
| app {Γ f A B a} : entails₁ Γ f (term.pi A B) → entails₁ Γ a A → entails₁ Γ (term.app f a) (subst a B)
| lam {Γ A b B s} : s ∈ S → entails₁ (A :: Γ) b B → entails₁ Γ (term.pi A B) ↑s → entails₁ Γ (term.lam A b) (term.pi A B)

inductive ctx₁ : context → Prop
| empty : ctx₁ []
| ext {Γ A s} : s ∈ S → entails₁ Γ A ↑s → ctx₁ (A :: Γ)

set_option class.instance_max_depth 5
set_option trace.class_instances true
lemma ctx₁_of_entails₁ {Γ A B} : entails₁ Γ A B → ctx₁ Γ :=
begin
  sorry
end

-- This lemma is not true because `Γ` can be literally anything, including an
-- invalid context.
lemma entails₁.ax₂ {Γ c s} : (c, s) ∈ A → entails₁ Γ ↑c ↑s :=
begin
  intro h,
  induction Γ with B Γ ih,
  { exact entails₁.ax₁ h },
  { refine entails₁.weak _ ih _,
    sorry
  }
end

end
