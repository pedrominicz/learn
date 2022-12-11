import order.fixed_points order.zorn

universes u v

namespace function
namespace embedding

variable {α : Type u}

theorem schroeder_bernstein {β : Type v} {f : α → β} {g : β → α} :
  injective f → injective g → ∃ H : α → β, bijective H :=
begin
  classical,
  intros hf hg,
  casesI is_empty_or_nonempty β with hβ hβ,
  { have hα := @equiv.equiv_empty α (function.is_empty f),
    have hβ := equiv.equiv_empty β,
    have h := hα.trans hβ.symm,
    exact ⟨h, h.bijective⟩ },
  let F' : set α → set α := λ s, (g '' (f '' s)ᶜ)ᶜ,
  have hF' : monotone F',
  { intros s₁ s₂ h,
    have h := set.image_subset f h,
    rw ←set.compl_subset_compl at h,
    have h := set.image_subset g h,
    rwa ←set.compl_subset_compl at h },
  let F : set α →o set α := ⟨F', hF'⟩,
  let s : set α := order_hom.lfp F,
  have hs : (g '' (f '' s)ᶜ)ᶜ = s := order_hom.map_lfp F,
  have hs : g '' (f '' s)ᶜ = sᶜ := compl_injective (by rw [hs, compl_compl]),
  let g' : α → β := inv_fun g,
  have hg' : left_inverse g' g := left_inverse_inv_fun hg,
  refine ⟨set.piecewise s f g', _, _⟩,
  { rw set.injective_piecewise_iff,
    refine ⟨set.inj_on_of_injective hf s, _, _⟩,
    { intros a₁ ha₁ a₂ ha₂ h,
      obtain ⟨b₁, hb₁, rfl⟩ : a₁ ∈ g '' (f '' s)ᶜ, by rwa hs,
      obtain ⟨b₂, hb₂, rfl⟩ : a₂ ∈ g '' (f '' s)ᶜ, by rwa hs,
      rw [hg', hg'] at h,
      rw h },
    { intros a ha a' ha' h,
      obtain ⟨b, hb, rfl⟩ : a' ∈ g '' (f '' s)ᶜ, by rwa hs,
      rw hg' at h,
      exact hb ⟨a, ha, h⟩ } },
  { rw [←set.range_iff_surjective, set.range_piecewise],
    have h : inv_fun g '' sᶜ = (f '' s)ᶜ,
    { rw [←hs, left_inverse.image_image hg'] },
    rw [h, set.union_compl_self] }
end

def i {β : Type v} (f : α → β) (g : β → α) (n : ℕ) : α → α := (g ∘ f)^[n]

def s {β : Type v} {f g' : α → β} {g f' : β → α}
  (hf : left_inverse f' f) (hg : left_inverse g' g) : set α :=
set_of (λ a, ∃ n a', a = i f g n a' ∧ a' ∉ set.range g)

axiom dec (p : Prop) : decidable p

theorem not_not {p : Prop} : ¬¬p → p :=
decidable.rec (λ h h', false.elim (h' h)) (λ h h', h) (dec p)

lemma hs₁ {β : Type v} {f g' : α → β} {g f' : β → α} {a : α}
  {hf : left_inverse f' f} {hg : left_inverse g' g} :
  a ∉ s hf hg → a ∈ set.range g :=
λ h₁, not_not (λ h₂, h₁ ⟨0, a, rfl, h₂⟩)

lemma iterate_succ' (f : α → α) (n : ℕ) : ∀ a, f^[n + 1] a = f (f^[n] a) :=
nat.rec (λ a, rfl) (λ n ih a, ih (f a)) n

lemma hs₂ {β : Type v} {f g' : α → β} {g f' : β → α} {a₁ a₂ : α}
  {hf : left_inverse f' f} {hg : left_inverse g' g} :
  a₁ ∉ s hf hg → a₂ ∈ s hf hg → g' a₁ ≠ f a₂ :=
begin
  intros ha₁ ha₂ h,
  rcases hs₁ ha₁ with ⟨b, rfl⟩, rename ha₁ hb, rename a₂ a, rename ha₂ ha,
  rw hg at h,
  subst h,
  rcases ha with ⟨n, a, rfl, h⟩,
  refine hb ⟨n + 1, a, _, h⟩, clear hb hf hg f' g' h,
  unfold i,
  rw iterate_succ'
end

lemma hs₃ {β : Type v} {f g' : α → β} {g f' : β → α} {b : β}
  {hf : left_inverse f' f} {hg : left_inverse g' g} :
  g b ∈ s hf hg → f' b ∈ s hf hg ∧ b ∈ set.range f :=
begin
  rintro ⟨n, a, h₁, h₂⟩,
  cases n with n,
  { exact false.elim (h₂ ⟨b, h₁⟩) },
  { unfold i at h₁,
    rw [iterate_succ', ←i] at h₁,
    rw [left_inverse.injective hg h₁, hf],
    exact ⟨⟨n, a, rfl, h₂⟩, ⟨i f g n a, rfl⟩⟩ }
end

theorem schroeder_bernstein' {β : Type v} {f g' : α → β} {g f' : β → α} :
  left_inverse f' f → left_inverse g' g → ∃ H : α → β, bijective H :=
begin
  intros hf hg,
  let s : set α := s hf hg,
  let H : α → β := λ a, @ite β (a ∈ s) (dec (a ∈ s)) (f a) (g' a),
  refine ⟨H, _, _⟩,
  { intros a₁ a₂ h,
    change ite _ _ _ = ite _ _ _ at h,
    clear H,
    cases dec (a₁ ∈ s) with h₁ h₁; cases dec (a₂ ∈ s) with h₂ h₂,
    { rw [@if_neg _ (is_false _) h₁, @if_neg _ (is_false _) h₂] at h,
      replace h₁ := hs₁ h₁,
      replace h₂ := hs₁ h₂,
      rcases h₁ with ⟨b₁, rfl⟩,
      rcases h₂ with ⟨b₂, rfl⟩,
      rw [hg, hg] at h,
      rw h },
    { rw [@if_neg _ (is_false _) h₁, @if_pos _ (is_true _) h₂] at h,
      exact false.elim (hs₂ h₁ h₂ h) },
    { rw [@if_pos _ (is_true _) h₁, @if_neg _ (is_false _) h₂] at h,
      exact false.elim (hs₂ h₂ h₁ h.symm) },
    { exact left_inverse.injective hf h } },
  { intro b,
    change ∃ b', ite _ _ _ = _,
    clear H,
    cases dec (g b ∈ s) with hb hb,
    { exact ⟨g b, by rw [@if_neg _ (dec _) hb, hg]⟩ },
    { refine ⟨f' b, _⟩,
      rcases hs₃ hb with ⟨hb, a, rfl⟩,
      rw [@if_pos _ (dec _) hb, hf] } }
end

theorem antisymm {β : Type v} : (α ↪ β) → (β ↪ α) → nonempty (α ≃ β)
| ⟨f, hf⟩ ⟨g, hg⟩ :=
  let ⟨h, hh⟩ := schroeder_bernstein hf hg in
  ⟨equiv.of_bijective h hh⟩

@[reducible] private def sets (β : α → Type v) : set (set (Π a, β a)) :=
{s : set (Π a, β a) | ∀ (f g ∈ s) a, (f : Π a, β a) a = g a → f = g}

theorem min_injective (β : α → Type v) [hα : nonempty α] :
  ∃ a, nonempty (∀ a', β a ↪ β a') :=
begin
  obtain ⟨S, hS₁, hS₂⟩ : ∃ s ∈ sets β, ∀ s' ∈ sets β, s ⊆ s' → s' = s,
  { refine zorn_subset (sets β) _,
    intros S hS₁ hS₂,
    change ∀ s, _ at hS₁,
    simp only [set.mem_set_of_eq] at hS₁,
    refine ⟨⋃₀ S, _, λ _, set.subset_sUnion_of_mem⟩,
    simp only [set.mem_set_of_eq],
    intros f hf g hg a h,
    rcases hf with ⟨s₁, hs₁, hf⟩,
    rcases hg with ⟨s₂, hs₂, hg⟩,
    cases is_chain.total hS₂ hs₁ hs₂ with h' h',
    { exact hS₁ s₂ hs₂ f (h' hf) g hg a h },
    { exact hS₁ s₁ hs₁ f hf g (h' hg) a h } },
  change ∀ (f g ∈ S) a, (f : Π a, β a) a = g a → f = g at hS₁,
  obtain ⟨a, ha⟩ : ∃ a, ∀ b, ∃ f ∈ S, (f : Π a, β a) a = b,
  { by_contra h,
    push_neg at h,
    obtain ⟨f, hf⟩ : ∃ f : Π a, β a, ∀ a g, g ∈ S → (g : Π a, β a) a ≠ f a,
    { exact classical.axiom_of_choice h },
    suffices h : f ∈ S,
    { exact hf (classical.arbitrary α) f h rfl },
    suffices h : insert f S ∈ sets β,
    { rw ←hS₂ (insert f S) h (set.subset_insert f S),
      exact set.mem_insert f S },
    intros g₁ hg₁ g₂ hg₂,
    rcases hg₁ with rfl | hg₁; rcases hg₂ with rfl | hg₂; intros a ha,
    { refl },
    { exfalso, exact hf a g₂ hg₂ ha.symm },
    { exfalso, exact hf a g₁ hg₁ ha },
    { exact hS₁ g₁ hg₁ g₂ hg₂ a ha } },
  obtain ⟨f, hf⟩ : ∃ f : β a → Π a, β a, ∀ b : β a, f b ∈ S ∧ f b a = b,
  { simpa using classical.axiom_of_choice ha },
  refine ⟨a, ⟨λ a', ⟨_, _⟩⟩⟩,
  { exact λ b, f b a' },
  { intros b₁ b₂ h,
    cases hf b₁ with hfb₁ hb₁,
    cases hf b₂ with hfb₂ hb₂,
    rw [←hb₁, ←hb₂, hS₁ (f b₁) hfb₁ (f b₂) hfb₂ a' h] }
end

theorem total (α : Type u) (β : Type v) : nonempty (α ↪ β) ∨ nonempty (β ↪ α) :=
match min_injective (λ b, cond b (ulift α) (ulift.{max u v} β)) with
| ⟨ff, ⟨f⟩⟩ := or.inr ⟨embedding.congr equiv.ulift equiv.ulift (f tt)⟩
| ⟨tt, ⟨f⟩⟩ := or.inl ⟨embedding.congr equiv.ulift equiv.ulift (f ff)⟩
end

end embedding
end function