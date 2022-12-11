import tactic.basic

-- Lean version 3.45.0

@[derive decidable_eq] inductive prop : Type
| and : prop → prop → prop
| true : prop
| impl : prop → prop → prop
| other : ℕ → prop

abbreviation context : Type := list prop

inductive entails₁ : context → prop → Prop
| refl₁ {Γ A} : entails₁ (A :: Γ) A
| trans {Γ A C} : entails₁ (A :: Γ) C → entails₁ Γ A → entails₁ Γ C
| weak {Γ A C} : entails₁ Γ C → entails₁ (A :: Γ) C
| contr {Γ A C} : entails₁ (A :: A :: Γ) C → entails₁ (A :: Γ) C
| exch {Γ A B C} : entails₁ (B :: A :: Γ) C → entails₁ (A :: B :: Γ) C
| and_intro {Γ A B} : entails₁ Γ A → entails₁ Γ B → entails₁ Γ (prop.and A B)
| and_elim₁ {Γ A B} : entails₁ Γ (prop.and A B) → entails₁ Γ A
| and_elim₂ {Γ A B} : entails₁ Γ (prop.and A B) → entails₁ Γ B
| true_intro {Γ} : entails₁ Γ prop.true
| impl_intro {Γ A B} : entails₁ (A :: Γ) B → entails₁ Γ (prop.impl A B)
| impl_elim {Γ A B} : entails₁ Γ (prop.impl A B) → entails₁ Γ A → entails₁ Γ B

inductive entails₂ : context → prop → Prop
| refl₂ {Γ A} : list.mem A Γ → entails₂ Γ A
| and_intro {Γ A B} : entails₂ Γ A → entails₂ Γ B → entails₂ Γ (prop.and A B)
| and_elim₁ {Γ A B} : entails₂ Γ (prop.and A B) → entails₂ Γ A
| and_elim₂ {Γ A B} : entails₂ Γ (prop.and A B) → entails₂ Γ B
| true_intro {Γ} : entails₂ Γ prop.true
| impl_intro {Γ A B} : entails₂ (A :: Γ) B → entails₂ Γ (prop.impl A B)
| impl_elim {Γ A B} : entails₂ Γ (prop.impl A B) → entails₂ Γ A → entails₂ Γ B

lemma entails₁.refl₂ {Γ A} : list.mem A Γ → entails₁ Γ A :=
begin
  intro h,
  induction Γ with B Γ ih,
  { cases h },
  { by_cases h' : A = B,
    { subst h',
      exact entails₁.refl₁ },
    { replace h : list.mem A Γ,
      { cases h, exact false.elim (h' h), exact h },
      specialize ih h, clear h h',
      exact entails₁.weak ih } }
end

lemma entails₂.refl₁ {Γ A} : entails₂ (A :: Γ) A :=
begin
  exact entails₂.refl₂ (list.mem_cons_self A Γ)
end

lemma aux {Γ₁ Γ₂ C} (hΓ : ∀ (A : prop), list.mem A Γ₁ → list.mem A Γ₂) :
  entails₂ Γ₁ C → entails₂ Γ₂ C :=
begin
  intro h,
  induction h with Γ₁ C h Γ₁ A B h₁ h₂ ih₁ ih₂ Γ₁ A B h ih Γ₁ A B h ih Γ₁ Γ₁ A B h ih Γ₁ A B h₁ h₂ ih₁ ih₂ generalizing Γ₂,
  any_goals { specialize ih₁ hΓ, specialize ih₂ hΓ },
  { exact entails₂.refl₂ (hΓ C h) },
  { exact entails₂.and_intro ih₁ ih₂ },
  { exact entails₂.and_elim₁ (ih hΓ) },
  { exact entails₂.and_elim₂ (ih hΓ) },
  { exact entails₂.true_intro },
  { replace hΓ : ∀ B, list.mem B (A :: Γ₁) → list.mem B (A :: Γ₂),
    { intro B,
      by_cases h : B = A,
      { subst h,
        intro h',
        exact or.inl rfl },
      { intro h',
        cases h', exact false.elim (h h'),
        exact or.inr (hΓ B h') } },
    exact entails₂.impl_intro (ih hΓ) },
  { exact entails₂.impl_elim ih₁ ih₂ }
end

lemma entails₂.exch {Γ A B C} :
  entails₂ (B :: A :: Γ) C → entails₂ (A :: B :: Γ) C :=
begin
  apply aux; clear C,
  intro C,
  by_cases h₁ : C = A,
  { subst h₁,
    intro h,
    exact or.inl rfl },
  { by_cases h₂ : C = B,
    { subst h₂,
      intro h,
      exact or.inr (or.inl rfl) },
    { intro h,
      cases h, exact false.elim (h₂ h),
      cases h, exact false.elim (h₁ h),
      exact or.inr (or.inr h) } }
end

lemma entails₂.weak {Γ A C} : entails₂ Γ C → entails₂ (A :: Γ) C :=
begin
  intro h,
  induction h with Γ C h Γ B C h₁ h₂ ih₁ ih₂ Γ C B h ih Γ B C h ih Γ Γ B C h ih Γ B C h₁ h₂ ih₁ ih₂,
  { exact entails₂.refl₂ (or.inr h) },
  { exact entails₂.and_intro ih₁ ih₂ },
  { exact entails₂.and_elim₁ ih },
  { exact entails₂.and_elim₂ ih },
  { exact entails₂.true_intro },
  { exact entails₂.impl_intro (entails₂.exch ih) },
  { exact entails₂.impl_elim ih₁ ih₂ }
end

lemma entails₂.trans {Γ A C} :
  entails₂ (A :: Γ) C → entails₂ Γ A → entails₂ Γ C :=
begin
  intros H₁ H₂,
  have hΓ : ∀ (B : prop), list.mem B (A :: Γ) → B = A ∨ list.mem B Γ,
  { intros B h, exact h },
  induction H₁ with Γ' C h Γ' A' B h₁ h₂ ih₁ ih₂ Γ' A' B h ih Γ' A' B h ih Γ' Γ' A' B h ih Γ' A' B h₁ h₂ ih₁ ih₂ generalizing Γ,
  any_goals { specialize ih₁ H₂ hΓ, specialize ih₂ H₂ hΓ },
  { by_cases h' : C = A,
    { subst h',
      exact H₂ },
    { replace hΓ : list.mem C Γ,
      { specialize hΓ C h,
        cases hΓ,
        { exact false.elim (h' hΓ) },
        { exact hΓ } },
      exact entails₂.refl₂ hΓ } },
  { exact entails₂.and_intro ih₁ ih₂ },
  { exact entails₂.and_elim₁ (ih H₂ hΓ) },
  { exact entails₂.and_elim₂ (ih H₂ hΓ) },
  { exact entails₂.true_intro },
  { replace H₂ : entails₂ (A' :: Γ) A := entails₂.weak H₂,
    replace hΓ : ∀ (B : prop), list.mem B (A' :: Γ') → B = A ∨ list.mem B (A' :: Γ),
    { clear_dependent B,
      intros B h,
      cases h,
      { subst h,
        exact or.inr (or.inl rfl) },
      { specialize hΓ B h,
        cases hΓ,
        { subst hΓ,
          exact or.inl rfl },
        { exact or.inr (or.inr hΓ) } } },
    exact entails₂.impl_intro (ih H₂ hΓ) },
  { exact entails₂.impl_elim ih₁ ih₂ }
end

lemma entails₂.contr {Γ A C} :
  entails₂ (A :: A :: Γ) C → entails₂ (A :: Γ) C :=
begin
  apply aux; clear C,
  intro B,
  by_cases h : B = A,
  { subst h,
    intro h',
    exact or.inl rfl },
  { intro h',
    cases h', exact false.elim (h h'),
    cases h', exact false.elim (h h'),
    exact or.inr h' }
end

theorem entails₁_iff_entails₂ {Γ C} :
  entails₁ Γ C ↔ entails₂ Γ C :=
begin
  split; intro h,
  { induction h with Γ A Γ A C h₁ h₂ ih₁ ih₂ Γ A C h ih Γ A C h ih Γ A B C h ih Γ A B h₁ h₂ ih₁ ih₂ Γ A B h ih Γ A B h ih Γ Γ A B h ih Γ A B h₁ h₂ ih₁ ih₂,
    { exact entails₂.refl₁ },
    { exact entails₂.trans ih₁ ih₂ },
    { exact entails₂.weak ih },
    { exact entails₂.contr ih },
    { exact entails₂.exch ih },
    { exact entails₂.and_intro ih₁ ih₂ },
    { exact entails₂.and_elim₁ ih },
    { exact entails₂.and_elim₂ ih },
    { exact entails₂.true_intro },
    { exact entails₂.impl_intro ih },
    { exact entails₂.impl_elim ih₁ ih₂ } },
  { induction h with Γ C h Γ A B h₁ h₂ ih₁ ih₂ Γ A B h ih Γ A B h ih Γ Γ A B h ih Γ A B h₁ h₂ ih₁ ih₂,
    { exact entails₁.refl₂ h },
    { exact entails₁.and_intro ih₁ ih₂ },
    { exact entails₁.and_elim₁ ih },
    { exact entails₁.and_elim₂ ih },
    { exact entails₁.true_intro },
    { exact entails₁.impl_intro ih },
    { exact entails₁.impl_elim ih₁ ih₂ } }
end

#print axioms entails₁_iff_entails₂ -- no axioms
