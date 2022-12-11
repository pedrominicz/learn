import tactic

variables {α β : Type}
variables {rα : α → α → Prop} {rβ : β → β → Prop}

theorem no_infinite_descending_chain_of_wf (H : well_founded rα) :
  ¬ ∃ f : ℕ → α, ∀ n : ℕ, rα (f n.succ) (f n) :=
begin
  rintro ⟨f, hf⟩,
  cases H.min_mem _ (set.range_nonempty f) with n hn,
  apply H.not_lt_min,
  { show f _ ∈ set.range f, simp },
  { rw ←hn, exact hf n }
end

namespace wf_of_no_infinite_descending_chain

noncomputable def not_acc_aux {a : α} (ha : ¬ acc rα a) :
  Σ' b, rα b a ∧ ¬ acc rα b :=
begin
  suffices : ∃ b, rα b a ∧ ¬ acc rα b,
  { exact ⟨classical.some this, classical.some_spec this⟩ },
  by_contra h,
  push_neg at h,
  exact ha ⟨_, h⟩
end

noncomputable def f {a : α} (ha : ¬ acc rα a) : ℕ → Σ' b, ¬ acc rα b :=
λ n, nat.rec ⟨a, ha⟩ (λ n a, ⟨(not_acc_aux a.snd).fst, (not_acc_aux a.snd).snd.right⟩) n

theorem _root_.wf_of_no_infinite_descending_chain :
  (¬ ∃ f : ℕ → α, ∀ n : ℕ, rα (f n.succ) (f n)) → well_founded rα :=
begin
  by_contra h,
  simp only [not_forall, exists_prop] at h,
  cases h with h' h, apply h', clear h',
  have : ¬ ∀ a, acc rα a := h ∘ well_founded.intro, clear h, rename this h,
  push_neg at h,
  cases h with a ha,
  exact ⟨λ n, (f ha n).fst, λ n, (not_acc_aux (f ha n).snd).snd.left⟩
end

end wf_of_no_infinite_descending_chain 

def f {A : set α} (h : Π a : α, a ∈ A → Σ' b : α, b ∈ A ∧ rα b a) {a : α} (ha : a ∈ A) :
  ℕ → Σ' b, b ∈ A :=
λ n, nat.rec ⟨a, ha⟩ (λ n a, ⟨(h a.fst a.snd).fst, (h a.fst a.snd).snd.left⟩) n

example (H : well_founded rα) {A : set α} :
  (Π a : α, a ∈ A → Σ' b : α, b ∈ A ∧ rα b a) → A = ∅ :=
begin
  intro h,
  ext a,
  simp only [set.mem_empty_eq, iff_false],
  intro ha,
  apply no_infinite_descending_chain_of_wf H,
  use λ n, (f h ha n).fst,
  intro n,
  suffices : (f h ha n).fst ∈ A ∧ rα (f h ha n.succ).fst (f h ha n).fst,
  { exact this.right },
  induction n with n ih,
  { exact ⟨ha, (h a ha).snd.right⟩ },
  { cases ih with ih₁ ih₂,
    let b := (h (f h ha n).fst ih₁).fst,
    let hb : b ∈ A := (h (f h ha n).fst ih₁).snd.left,
    exact ⟨hb, (h b hb).snd.right⟩ }
end

theorem set_without_min_eq_empty_of_wf (H : well_founded rα) {A : set α} :
  (∀ a ∈ A, ∃ b ∈ A, rα b a) → A = ∅ :=
begin
  intro h,
  ext a,
  rw [set.mem_empty_eq, iff_false],
  intro ha,
  rcases h _ (H.min_mem _ _) with ⟨b, hb, hb'⟩,
  exact H.not_lt_min _ (set.nonempty_of_mem ha) hb hb'
end

theorem wf_of_set_without_min_eq_empty :
  (∀ A : set α, (∀ a ∈ A, ∃ b ∈ A, rα b a) → A = ∅) → well_founded rα :=
begin
  by_contra h,
  simp only [exists_prop, not_forall] at h,
  have := mt (@wf_of_no_infinite_descending_chain _ rα),
  push_neg at this,
  cases h with h₁ h₂,
  specialize this h₂, clear h₂,
  cases this with f hf,
  let A := set.range f,
  suffices : ∀ a, a ∈ A → ∃ b, b ∈ A ∧ rα b a,
  { specialize h₁ A this, finish },
  clear h₁,
  intros a ha,
  have : ∃ n, f n = a,
  { finish },
  rcases this with ⟨n, rfl⟩,
  use f n.succ,
  finish
end

example [iα : is_trichotomous α rα] (Hβ : well_founded rβ)
  {eq : α ≃ β} (h : ∀ a₁ a₂ : α, rα a₁ a₂ → rβ (eq a₁) (eq a₂)) :
  ∀ b₁ b₂ : β, rβ b₁ b₂ → rα (eq.symm b₁) (eq.symm b₂) :=
begin
  intros b₁ b₂ hb,
  cases eq with to_fun inv_fun left_inv right_inv,
  change ∀ a, inv_fun (to_fun a) = a at left_inv,
  change ∀ b, to_fun (inv_fun b) = b at right_inv,
  change ∀ a₁ a₂, rα a₁ a₂ → rβ (to_fun a₁) (to_fun a₂) at h,
  change rα (inv_fun b₁) (inv_fun b₂),
  unfreezingI { rcases iα with ⟨iα⟩ },
  rcases iα (inv_fun b₁) (inv_fun b₂) with ha | ha | ha,
  { assumption },
  { exfalso,
    suffices : b₁ = b₂,
    { subst this, rename b₁ b,
      exact (Hβ.is_irrefl.irrefl : ∀ _, ¬ _) b hb },
    rw [←right_inv b₁, ha, right_inv] },
  { exfalso,
    specialize h _ _ ha,
    rw [right_inv, right_inv] at h,
    apply Hβ.not_gt_of_lt h hb }
end

inductive ordinal : Type 1
| mk {α : Type} (lt : α → α → Prop) [is_well_order α lt] : ordinal

namespace ordinal

def equiv : ordinal → ordinal → Prop :=
begin
  rintros ⟨α, ltα, iα⟩ ⟨β, ltβ, iβ⟩,
  exact ∃ eq : α ≃ β, ∀ a₁ a₂ : α, ltα a₁ a₂ ↔ ltβ (eq a₁) (eq a₂)
end

theorem equiv.refl (α : ordinal) : equiv α α :=
begin
  cases α with α ltα iα,
  use equiv.refl α,
  simp
end

theorem equiv.rfl : ∀ {α : ordinal}, equiv α α := equiv.refl

theorem equiv.symm {α β : ordinal} : equiv α β → equiv β α :=
begin
  cases α with α ltα iα,
  cases β with β ltβ iβ,
  rintro ⟨⟨to_fun, inv_fun, left_inv, right_inv⟩, h⟩,
  change ∀ a, inv_fun (to_fun a) = a at left_inv,
  change ∀ b, to_fun (inv_fun b) = b at right_inv,
  change ∀ a₁ a₂, ltα a₁ a₂ ↔ ltβ (to_fun a₁) (to_fun a₂) at h,
  use ⟨inv_fun, to_fun, right_inv, left_inv⟩, clear iα iβ,
  change ∀ b₁ b₂, ltβ b₁ b₂ ↔ ltα (inv_fun b₁) (inv_fun b₂),
  intros b₁ b₂,
  specialize h (inv_fun b₁) (inv_fun b₂),
  rw [right_inv, right_inv] at h,
  symmetry,
  assumption
end

theorem equiv.trans {α β γ : ordinal} (h₁ : equiv α β) (h₂ : equiv β γ) :
  equiv α γ :=
begin
  cases α with α ltα iα,
  cases β with β ltβ iβ,
  cases γ with γ ltγ iγ,
  rcases h₁ with ⟨⟨to_fun₁, inv_fun₁, left_inv₁, right_inv₁⟩, h₁⟩,
  change ∀ a, inv_fun₁ (to_fun₁ a) = a at left_inv₁,
  change ∀ b, to_fun₁ (inv_fun₁ b) = b at right_inv₁,
  change ∀ a₁ a₂, ltα a₁ a₂ ↔ ltβ (to_fun₁ a₁) (to_fun₁ a₂) at h₁,
  rcases h₂ with ⟨⟨to_fun₂, inv_fun₂, left_inv₂, right_inv₂⟩, h₂⟩,
  change ∀ b, inv_fun₂ (to_fun₂ b) = b at left_inv₂,
  change ∀ c, to_fun₂ (inv_fun₂ c) = c at right_inv₂,
  change ∀ b₁ b₂, ltβ b₁ b₂ ↔ ltγ (to_fun₂ b₁) (to_fun₂ b₂) at h₂,
  change ∃ _, _,
  use ⟨
    λ a, to_fun₂ (to_fun₁ a),
    λ c, inv_fun₁ (inv_fun₂ c),
    function.left_inverse.comp left_inv₂ left_inv₁,
    function.right_inverse.comp right_inv₂ right_inv₁⟩,
  intros a₁ a₂,
  change ltα a₁ a₂ ↔ ltγ (to_fun₂ (to_fun₁ a₁)) (to_fun₂ (to_fun₁ a₂)),
  transitivity,
  { exact h₁ a₁ a₂ },
  { exact h₂ (to_fun₁ a₁) (to_fun₁ a₂) }
end

instance : setoid ordinal :=
⟨equiv, equiv.refl, @equiv.symm, @equiv.trans⟩

end ordinal

def Ordinal : Type 1 := quotient ordinal.setoid