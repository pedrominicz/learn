#check (λ (A : Type) (x : A), x : Π {A : Type}, A → A)
#check (λ {A : Type} (x : A), x : Π (A : Type), A → A)
#check expr
#exit

axiom A : Type
axiom B : Type 1
axioms x y : A

#check A → B
#check B → A
#check (B → (A : Type))
#check (B → A : Type 1)
#check (λ x, x : A → A)
#check (λ x, x : A → A)

#check λ x y x
#exit

-- Parse:
#check λ y : A, (λ x y : A, x) y
-- Eval:
#check λ y : A, (λ x y : A, x) y
#check λ y : A, (λ y : A, y)
-- Beaufity:
#check λ y : A, (λ y_1 : A, y)
-- Print:
#reduce λ y : A, (λ x y : A, x) y
#check λ y y_1 : A, y
example : (λ y : A, (λ x y : A, x) y) = (λ y y_1 : A, y) := rfl


-- Parse:
#check λ y : A, (λ x y : A, y) y -- Note, the body of the inner lambda is `y`.
-- Eval:
#check λ y : A, (λ x y : A, y) y
#check λ y : A, (λ y : A, y)
-- Beaufity:
#check λ y : A, (λ y : A, y)
-- Print:
#check λ y y : A, y
#reduce λ y : A, (λ x y : A, y) y
example : (λ y y : A, y) = (λ y : A, (λ x y : A, y) y) := rfl


-- Parse:
#check (λ x y : A, x) y
-- Eval:
#check (λ y : A, y)
-- Beaufity:
#check (λ y_1 : A, y)
-- Print:
#check λ y_1 : A, y
#reduce (λ x y : A, x) y
example : (λ y_1 : A, y) = ((λ x y : A, x) y) := rfl


-- Parse:
#check λ (y : A → B), (λ (f : A → B) (y : A), (λ (x y : A), f x) y) y
-- Eval:
#check λ (y : A → B), (λ (f : A → B) (y : A), (λ (x y : A), f x) y) y
#check λ (y : A → B), (λ (f : A → B) (y : A), (λ (y : A), f y)) y
-- Beautify:
#check λ (y : A → B), (λ (y_1 : A), (λ (y_2 : A), y y_1))
-- Print:
#check λ (y : A → B) (y_1 y_2 : A), y y_1
#reduce λ (y : A → B), (λ (f : A → B) (y : A), (λ (x y : A), f x) y) y
example : (λ (y : A → B) (y_1 y_2 : A), y y_1) = (λ (y : A → B), (λ (f : A → B) (y : A), (λ (x y : A), f x) y) y) := rfl


-- Parse:
#check λ (y : A → B), (λ (f : A → B) (y y : A), f y) y
-- Eval:
#check λ (y : A → B), (λ (f : A → B) (y y : A), f y) y
-- Beautify:
#check λ (y : A → B), (λ (y_1 y_1 : A), y y_1)
-- Print:
#check λ (y : A → B) (y_1 y_1 : A), y y_1
#reduce λ (y : A → B), (λ (f : A → B) (y y : A), f y) y
example : (λ (y : A → B) (y_1 y_1 : A), y y_1) = (λ (y : A → B), (λ (f : A → B) (y y : A), f y) y) := rfl











-- Variable shadowing
#reduce λ y : A, (λ x y : A, x) y
#reduce λ y : A, (λ x y y_1 : A, x) y
#reduce λ y : A, (λ (x y : A) (y_1 : A → A), y_1 x) y
#reduce λ y : A, (λ (x : A) (y_1 y : A → A), y_1 x) y
#reduce λ y : A, (λ (x : A) (y_1 : A → A) (y : A) , y_1 x) y
#reduce λ y : A, (λ (x : A) (y_1 y : A → A) (y : A) , y_1 x) y
-- Normalization
axiom F : A → A → Type
#check λ (x : A) (y : (λ A : Type, A) A), x
#check Π (x : A) (y : (λ A : Type, A) A), A
#check Π (x : A) (y : (λ A : Type, A) A), F x y
#check Π (A : Type) (B : (λ A : Type 1, A) Type), A × B
#reduce λ (x : A) (y : (λ A : Type, A) A), x
#reduce Π (x : A) (y : (λ A : Type, A) A), A
#reduce Π (x : A) (y : (λ A : Type, A) A), F x y
#reduce Π (A : Type) (B : (λ A : Type 1, A) Type), A × B
-- Long lines
axioms B C D E : Type
#check λ(a:A)(b:B),a
#check λ(a1 a2 a3 a4:A)(b1 b2 b3 b4:B),a1
#check λ(a1 a2 a3 a4:A)(b1 b2 b3 b4:B)(c1 c2 c3 c4:C),a1
#check λ(a1 a2 a3 a4:A)(b1 b2 b3 b4:B)(c1 c2 c3 c4:C)(d1 d2 d3 d4:D),a1
#check λ(a1 a2 a3 a4:A)(b1 b2 b3 b4:B)(c1 c2 c3 c4:C)(d1 d2 d3 d4:D)(e1 e2 e3 e4:E),a1
axiom F1 : A → B → Type
#check Π(a:A)(b:B),F1 a b
axiom F2 (a1 a2 a3 a4:A)(b1 b2 b3 b4:B):Type
#check Π(a1 a2 a3 a4:A)(b1 b2 b3 b4:B),F2 a1 a2 a3 a4 b1 b2 b3 b4
/-
#check Π(a1 a2 a3 a4:A)(b1 b2 b3 b4:B)(c1 c2 c3 c4:C),a1
#check Π(a1 a2 a3 a4:A)(b1 b2 b3 b4:B)(c1 c2 c3 c4:C)(d1 d2 d3 d4:D),a1
#check f a
#check f a1 a2 a3 a4 a5
#check f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10
#check f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
#check f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20
#check f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25
#check f (g a1 a2 a3 a4 a5)
#check f (g a1 a2 a3 a4 a5) (g a1 a2 a3 a4 a5)
#check f (g a1 a2 a3 a4 a5) (g a1 a2 a3 a4 a5) (g a1 a2 a3 a4 a5)
#check f (g a1 a2 a3 a4 a5) (g a1 a2 a3 a4 a5) (g a1 a2 a3 a4 a5) (g a1 a2 a3 a4 a5)
#check f (g a1 a2 a3 a4 a5) (g a1 a2 a3 a4 a5) (g a1 a2 a3 a4 a5) (g a1 a2 a3 a4 a5) (g a1 a2 a3 a4 a5)
#check A -> B
#check (A -> B) -> B
#check (A -> B) -> (A -> B)
#check A1 -> A2 -> A3 -> A4 -> A5 -> B
#check A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> B
#check A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> B
#check A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> B
#check A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> A7 -> A8 -> A9 -> A10 -> A11 -> A12 -> A13 -> A14 -> A15 -> A16 -> A17 -> A18 -> A19 -> A20 -> A21 -> A22 -> A23 -> A24 -> A25 -> B
#check (A1 -> A2 -> A3 -> A4 -> A5) -> B
#check (A1 -> A2 -> A3 -> A4 -> A5) -> (A1 -> A2 -> A3 -> A4 -> A5) -> B
#check (A1 -> A2 -> A3 -> A4 -> A5) -> (A1 -> A2 -> A3 -> A4 -> A5) -> (A1 -> A2 -> A3 -> A4 -> A5) -> B
#check (A1 -> A2 -> A3 -> A4 -> A5) -> (A1 -> A2 -> A3 -> A4 -> A5) -> (A1 -> A2 -> A3 -> A4 -> A5) -> (A1 -> A2 -> A3 -> A4 -> A5) -> B
#check (A1 -> A2 -> A3 -> A4 -> A5) -> (A1 -> A2 -> A3 -> A4 -> A5) -> (A1 -> A2 -> A3 -> A4 -> A5) -> (A1 -> A2 -> A3 -> A4 -> A5) -> (A1 -> A2 -> A3 -> A4 -> A5) -> B

-/
#exit
import data.W.basic

-- The following is based on the book Homotopy Type Theory: Univalent
-- Foundations of Mathematics.

universes u v w

section

parameters {α : Type u} (r : α → α → Prop) (a : α)

-- Definition 10.3.1. Accessibility.
inductive acc' : α → Type u
| intro (x : α) (h : Π y, r y x → acc' y) : acc' x

-- Lemma 10.3.2. Accessibility is a mere property.
instance : subsingleton (acc' a) :=
begin
  refine ⟨λ s₁ s₂, _⟩,
  induction s₁ with _ _ ih,
  induction s₂ with _ h _,
  congr,
  ext a ha,
  exact ih a ha (h a ha)
end

-- Definition 10.3.3. Well-foundedness.
inductive wf : Type u
| intro (apply : Π a, acc' a) : wf

def wf.apply : wf → Π a, acc' a
| (wf.intro h) := h

-- Lemma 10.3.4. Well-foundedness is a mere property.
instance : subsingleton wf :=
⟨λ s₁ s₂, by { cases s₁, cases s₂, congr }⟩

-- Example 10.3.5. The usual strict ordering on `ℕ` is well-founded.
example {p : ℕ → Type u} (h : ∀ n, (∀ m, m < n → p m) → p n) : ∀ n, p n :=
begin
  suffices h : ∀ n m, m < n → p m,
  { exact λ n, h n.succ n (nat.lt_succ_self n) },
  intro n,
  induction n with n ih,
  { intros m h', exfalso, cases h' },
  { intros m h',
    apply or.by_cases (decidable.lt_or_eq_of_le (nat.le_of_lt_succ h')),
    { exact ih m },
    { rintro rfl, exact h m ih } }
end

section

parameters {β : α → Type v}

def W : Type (max u v) := W_type β

def lt : W → W → Prop
| w ⟨a, f⟩ := ∃ b, w = f b

-- Example 10.3.6. A well-founded relation on W-types.
example : well_founded lt :=
begin
  refine ⟨λ w, _⟩,
  induction w with a f ih,
  refine ⟨⟨a, f⟩, λ w h, _⟩,
  rcases h with ⟨b, rfl⟩,
  exact ih b
end

end

parameters {β : Type u} (g : set β → β) (h : wf)

def f_aux : Π a, acc' a → β :=
@acc'.rec (λ a ha, β) (λ a f ih, g (λ b, ∃ a' h, b = ih a' h))

def f (a : α) : β := f_aux a (wf.apply h a)

-- Lemma 10.3.7. Suppose we have a function `g : set β → β`, then there a
-- function `f : α → β` such that for all `a : α` we have
-- `f a = g {f a′ | a′ < a}`.
example : f a = g (λ b, ∃ a', r a' a ∧ b = f a') :=
begin
  simp only [f, f_aux],
  cases wf.apply h a with a ha,
  simp only,
  congr,
  ext b,
  rw ←f_aux,
  split; rintro ⟨a', h', rfl⟩; exact ⟨a', h', by congr⟩
end

-- Lemma 10.3.8. Assuming excluded middle, `<` is well-founded if and only if
-- every nonempty set `s : set α` merely has a minimal element.
example (h : wf) (s : set α) (hs : set.nonempty s) :
  ∃ a ∈ s, ∀ a' ∈ s, ¬ r a' a :=
begin
  cases hs with a ha,
  by_contra h',
  push_neg at h',
  suffices : ∀ a, acc' a → a ∉ s,
  { exact this a (wf.apply h a) ha },
  clear ha a,
  intros a ha,
  induction ha with a' f ih, clear a, rename a' a,
  dsimp only at ih,
  intro ha,
  specialize h' a ha,
  rcases h' with ⟨a', h₁, h₂⟩,
  exact ih a' h₂ h₁
end

noncomputable def strong_not_not {α : Type u} : ((α → false) → false) → α :=
begin
  classical,
  intro h,
  by_cases h' : nonempty α,
  { exact classical.choice h' },
  { exact false.elim (h (λ a, h' ⟨a⟩)) }
end

noncomputable example (h : ∀ s : set α, set.nonempty s → ∃ a ∈ s, ∀ a' ∈ s, ¬ r a' a) :
  wf :=
begin
  let s : set α := {a | acc' a → false},
  by_cases hs : set.nonempty s,
  { specialize h s hs,
    simp only [exists_prop] at h,
    let a := classical.some h,
    obtain ⟨ha₁, ha₂⟩ : a ∈ s ∧ ∀ a', a' ∈ s → ¬ r a' a := classical.some_spec h,
    change acc' a → false at ha₁,
    change ∀ a', (acc' a' → false) → ¬ r a' a at ha₂,
    replace ha₂ : Π a', r a' a → acc' a' := λ a' ha', strong_not_not (λ h, ha₂ a' h ha'),
    exact false.elim (ha₁ ⟨a, ha₂⟩) },
  { refine ⟨λ a, _⟩,
    simp [s, set.nonempty] at hs,
    exact classical.some (hs a) }
end

-- Definition 10.3.9. Extensional well-founded relation.
def ext (rα : α → α → Prop) : Prop :=
∀ ⦃a₁ a₂⦄, (∀ a, rα a a₁ ↔ rα a a₂) → a₁ = a₂

-- Theorem 10.3.10. The type of extensional well-founded relations is a set.
example (h₁ : ext r) (h₂ : wf) {f f' : α → α} :
  (∀ a₁ a₂, r a₁ a₂ ↔ r (f a₁) (f a₂)) → function.right_inverse f' f → f = id :=
begin
  intros hf₁ hf₂,
  ext a,
  change f a = a,
  have ha := wf.apply h₂ a, clear h₂,
  induction ha with a' f' ih, clear a, rename a' a,
  dsimp only at ih, clear f',
  apply h₁, clear h₁,
  intro a',
  refine ⟨λ ha', _, λ ha', _⟩,
  { suffices : r (f' a') a,
    { specialize ih (f' a') this,
      specialize hf₁ (f' a') a,
      rwa [←hf₂ a', ih, hf₁, hf₂ a'] },
    specialize hf₁ (f' a') a,
    specialize hf₂ a',
    rwa [hf₁, hf₂] },
  { specialize hf₁ a' a,
    rw ih a' ha' at hf₁,
    rwa ←hf₁ }
end

end

section

parameters {α : Type u} {rα : α → α → Prop}
parameters {β : Type v} {rβ : β → β → Prop}
parameters {f g : α → β}

-- Definition 10.3.11. Simulation.
def simulation (rα : α → α → Prop) (rβ : β → β → Prop) (f : α → β) : Prop :=
(∀ a₁ a₂, rα a₁ a₂ → rβ (f a₁) (f a₂)) ∧
 ∀ a b, rβ b (f a) → ∃ a', rα a' a ∧ b = f a'

-- Lemma 10.3.12. Any simulation is injective.
theorem simulation.injective (h₁ : ext rα) (h₂ : well_founded rα) :
  simulation rα rβ f → function.injective f :=
begin
  intro hf,
  refine λ x, h₂.induction x (λ a ih₁, _),
  refine λ x, h₂.induction x (λ b ih₂, _),
  refine λ h, h₁ (λ c, _), clear h₁ h₂,
  cases hf with hf₁ hf₂,
  split; intro hc,
  { rcases hf₂ b (f c) (h ▸ hf₁ c a hc) with ⟨c', _, hc'⟩,
    rwa ih₁ c hc hc' },
  { rcases hf₂ a (f c) (h.symm ▸ hf₁ c b hc) with ⟨c', hc, hc'⟩,
    rwa ←ih₁ c' hc hc'.symm }
end

def is_initial_seg (C : set β) :=
∀ c b, c ∈ C → rβ b c → b ∈ C

example (hf : simulation rα rβ f) : is_initial_seg (set.range f) :=
begin
  unfold set.range,
  intros c b hc hb,
  change ∃ a, f a = c at hc,
  rcases hc with ⟨a, rfl⟩,
  change ∃ a, f a = b,
  cases hf with hf' hf, clear hf',
  specialize hf a b hb, clear hb rβ,
  rcases hf with ⟨a', ha', rfl⟩, clear ha' rα a, rename a' a,
  exact ⟨a, rfl⟩
end

end

variables {α : Type u} {rα : α → α → Prop}
variables {β : Type v} {rβ : β → β → Prop}
variables {γ : Type w} {rγ : γ → γ → Prop}

-- Theorem 10.3.14. For a set `α`, let `p α` be the type of extensional
-- well-founded relations on `α`. If `rα : p α` and `rβ : p β` and `f : α → β`,
-- let `h rα rβ f` be the mere proposition that `f` is a simulation. Then
-- `⟨p, h⟩` is a standard notion of structure over Set in the sense of §9.8.
example {rα₁ : α → α → Prop} {rα₂ : α → α → Prop} :
  simulation rα₁ rα₂ id → simulation rα₂ rα₁ id → rα₁ = rα₂ :=
begin
  rintros ⟨h₁, h⟩ ⟨h₂, h⟩, clear h h,
  ext a₁ a₂,
  exact ⟨h₁ a₁ a₂, h₂ a₁ a₂⟩
end

-- Corollary 10.3.15. There is a category whose objects are sets equipped with
-- extensional well-founded relations, and whose morphisms are simulations.
theorem simulation.id : simulation rα rα id :=
begin
  split,
  { exact λ a₁ a₂ h, h },
  { exact λ a₁ a₂ h, ⟨a₂, h, rfl⟩ }
end

theorem simulation.comp {g : β → γ} {f : α → β} :
  simulation rβ rγ g → simulation rα rβ f → simulation rα rγ (g ∘ f) :=
begin
  rintros ⟨hg₁, hg₂⟩ ⟨hf₁, hf₂⟩,
  split,
  { clear hf₂ hg₂, rename hf₁ hf, rename hg₁ hg,
    intros a₁ a₂ h,
    replace h := hf a₁ a₂ h, clear hf,
    replace h := hg (f a₁) (f a₂) h, clear hg,
    exact h },
  { clear hf₁ hg₁, rename hf₂ hf, rename hg₂ hg,
    intros a c h,
    replace h := hg (f a) c h, clear hg,
    rcases h with ⟨b, h, rfl⟩,
    replace h := hf a b h, clear hf,
    rcases h with ⟨a', h, rfl⟩,
    exact ⟨a', h, rfl⟩ }
end

-- Lemma 10.3.16. There is at most one simulation `f : α → β`.
theorem simulation.unique {f₁ f₂ : α → β} (hα : well_founded rα) (hβ : ext rβ) :
  simulation rα rβ f₁ → simulation rα rβ f₂ → f₁ = f₂ :=
begin
  intros hf₁ hf₂,
  ext x,
  refine hα.induction x (λ a ih, _), clear hα x,
  change ∀ a', rα a' a → f₁ a' = f₂ a' at ih,
  refine hβ (λ b, _), clear hβ,
  cases hf₁ with hf₁₁ hf₁₂,
  cases hf₂ with hf₂₁ hf₂₂,
  split; intro h,
  { clear hf₁₁ hf₂₂, rename hf₁₂ hf₁, rename hf₂₁ hf₂,
    specialize hf₁ a b h, clear h,
    rcases hf₁ with ⟨a', ha', rfl⟩,
    specialize hf₂ a' a ha',
    specialize ih a' ha', clear ha' rα,
    rwa ih },
  { clear hf₁₂ hf₂₁, rename hf₁₁ hf₁, rename hf₂₂ hf₂,
    specialize hf₂ a b h, clear h,
    rcases hf₂ with ⟨a', ha', rfl⟩,
    specialize hf₁ a' a ha',
    specialize ih a' ha', clear ha' rα,
    rwa ←ih }
end

theorem simulation.left_inverse {f : α → β} {g : β → α}
  (hα₁ : ext rα) (hα₂ : well_founded rα) :
  simulation rβ rα g → simulation rα rβ f → function.left_inverse g f :=
begin
  intros hg hf a,
  change g (f a) = id a,
  rw ←simulation.unique hα₂ hα₁ (hg.comp hf) simulation.id
end

def well_order (rα : α → α → Prop) :=
ext rα ∧ well_founded rα ∧ transitive rα

def well_order.ext : well_order rα → ext rα
| ⟨hα₁, hα₂, hα₃⟩ := hα₁

def well_order.wf : well_order rα → well_founded rα
| ⟨hα₁, hα₂, hα₃⟩ := hα₂

def well_order.trans : well_order rα → transitive rα
| ⟨hα₁, hα₂, hα₃⟩ := hα₃

inductive ordinal' : Type (u+1)
| mk {α : Type u} {rα : α → α → Prop} : well_order rα → ordinal'

namespace ordinal'

def r : ordinal'.{u} → ordinal'.{u} → Prop
| (@ordinal'.mk α rα hα) (@ordinal'.mk β rβ hβ) :=
  (∃ f, simulation rα rβ f) ∧ ∃ g, simulation rβ rα g

theorem r.reflexive : reflexive r :=
begin
  rintro ⟨α, rα, hα⟩,
  refine ⟨⟨id, simulation.id⟩, ⟨id, simulation.id⟩⟩,
end

theorem r.symmetric : symmetric r :=
begin
  rintros ⟨α, rα, hα⟩ ⟨β, rβ, hβ⟩ ⟨hf, hg⟩,
  exact ⟨hg, hf⟩
end

theorem r.trans : transitive r :=
begin
  rintros ⟨α, rα, hα⟩ ⟨β, rβ, hβ⟩ ⟨γ, rγ, hγ⟩ ⟨⟨f₁, hf₁⟩, ⟨g₁, hg₁⟩⟩ ⟨⟨f₂, hf₂⟩, ⟨g₂, hg₂⟩⟩,
  exact ⟨⟨f₂ ∘ f₁, hf₂.comp hf₁⟩, ⟨g₁ ∘ g₂, hg₁.comp hg₂⟩⟩
end

theorem r.equivalence : equivalence r :=
⟨r.reflexive, r.symmetric, r.trans⟩

instance setoid : setoid ordinal' :=
{ r := r, iseqv := r.equivalence }

end ordinal'

def ordinal : Type (u+1) := quotient ordinal'.setoid.{u}

namespace ordinal

def mk (hα : well_order rα) : ordinal := quotient.mk ⟨hα⟩

namespace ω

def r : ulift.{u} ℕ → ulift.{u} ℕ → Prop
| ⟨n⟩ ⟨m⟩ := n < m

theorem r.ext : ext r :=
begin
  rintros ⟨n₁⟩ ⟨n₂⟩ h,
  replace h : ∀ m, m < n₁ ↔ m < n₂ := λ m, h ⟨m⟩,
  congr,
  by_contra h',
  cases ne.lt_or_lt h' with h' h',
  { rw ←h at h', exact nat.lt_asymm h' h' },
  { rw h at h', exact nat.lt_asymm h' h' }
end

theorem r.wf : well_founded r :=
begin
  suffices h : ∀ n m, r m n → acc r m,
  { exact ⟨λ ⟨n⟩, h ⟨n + 1⟩ ⟨n⟩ (nat.lt_succ_self n)⟩ },
  rintro ⟨n⟩,
  induction n with n ih,
  { rintros ⟨m⟩ h', exfalso, cases h' },
  { rintros ⟨m⟩ h',
    cases decidable.lt_or_eq_of_le (nat.le_of_lt_succ h'),
    { exact ih ⟨m⟩ h },
    { subst h, exact ⟨⟨m⟩, λ n h, ih n h⟩ } }
end

theorem r.trans : transitive r :=
λ ⟨n₁⟩ ⟨n₂⟩ ⟨n₃⟩ h₁ h₂, lt_trans h₁ h₂

theorem r.well_order : well_order r :=
⟨r.ext, r.wf, r.trans⟩

end ω

-- Example 10.3.18. The least transfinite ordinal `ω`.
def ω : ordinal.{u} :=
ordinal.mk ω.r.well_order

namespace initial_seg

def carrier (rα : α → α → Prop) (a : α) : Type u :=
{b // rα b a}

def r (rα : α → α → Prop) (a : α) (b₁ b₂ : carrier rα a) : Prop :=
rα b₁.val b₂.val

theorem r.ext (hα₁ : ext rα) (hα₂ : transitive rα) (a : α) : ext (r rα a) :=
begin
  rintros ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ h,
  congr,
  refine hα₁ (λ b, ⟨λ hb, _, λ hb, _⟩),
  { specialize hα₂ hb hb₁,
    specialize h ⟨b, hα₂⟩,
    unfold r at h,
    rwa ←h },
  { specialize hα₂ hb hb₂,
    specialize h ⟨b, hα₂⟩,
    unfold r at h,
    rwa h }
end

theorem r.wf (hα : well_founded rα) (a : α) : well_founded (r rα a) :=
begin
  refine ⟨_⟩,
  rintro ⟨b, hb⟩,
  suffices h : ∀ hb, acc (r rα a) ⟨b, hb⟩,
  { exact h hb },
  refine hα.induction b _, clear hb b,
  intros b ih hb,
  refine ⟨⟨b, hb⟩, _⟩,
  rintro ⟨b', hb'⟩ h,
  exact ih b' h hb'
end

theorem r.trans (hα : transitive rα) (a : α) : transitive (r rα a) :=
begin
  rintros ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ ⟨b₃, hb₃⟩ h₁ h₂,
  exact hα h₁ h₂
end

theorem r.well_order (hα : well_order rα) (a : α) : well_order (r rα a) :=
begin
  rcases hα with ⟨hα₁, hα₂, hα₃⟩,
  exact ⟨r.ext hα₁ hα₃ a, r.wf hα₂ a, r.trans hα₃ a⟩
end

end initial_seg

def initial_seg (hα : well_order rα) (a : α) : ordinal :=
mk (initial_seg.r.well_order hα a)

namespace initial_seg

theorem injective {hα : well_order rα} :
  function.injective (initial_seg hα) :=
begin
  intros a₁ a₂ h,
  refine hα.ext (λ b, _),
  let i₁ : carrier rα a₁ → α := subtype.val,
  let i₂ : carrier rα a₂ → α := subtype.val,
  suffices h : b ∈ set.range i₁ ↔ b ∈ set.range i₂,
  { split; intro hb,
    { replace hb : b ∈ set.range i₂,
      { rw ←h, exact ⟨⟨b, hb⟩, rfl⟩ },
      rcases hb with ⟨⟨b, hb⟩, rfl⟩,
      exact hb },
    { replace hb : b ∈ set.range i₁,
      { rw h, exact ⟨⟨b, hb⟩, rfl⟩ },
      rcases hb with ⟨⟨b, hb⟩, rfl⟩,
      exact hb } },
  unfold initial_seg mk at h,
  rw quotient.eq at h,
  rcases h with ⟨⟨f, hf⟩, ⟨g, hg⟩⟩,
  have h : function.right_inverse g f,
  { exact simulation.left_inverse (r.ext hα.ext hα.trans a₂) (r.wf hα.wf a₂) hf hg },
  rw ←h.surjective.range_comp i₂, clear h,
  have hi₁ : simulation (r rα a₁) rα i₁,
  { refine ⟨λ b₁ b₂ h, h, λ ⟨b₁, hb₁⟩ b₂ hb₂, ⟨⟨b₂, hα.trans hb₂ hb₁⟩, hb₂, rfl⟩⟩ },
  have hi₂ : simulation (r rα a₂) rα i₂,
  { refine ⟨λ b₁ b₂ h, h, λ ⟨b₁, hb₁⟩ b₂ hb₂, ⟨⟨b₂, hα.trans hb₂ hb₁⟩, hb₂, rfl⟩⟩ },
  rw simulation.unique (r.wf hα.wf a₁) hα.ext hi₁ (hi₂.comp hf)
end

end initial_seg

def lt' (α : ordinal) : ordinal' → Prop
| (@ordinal'.mk β rβ hβ) := ∃ b, α = initial_seg hβ b

-- Definition 10.3.19. For ordinals `α` and `β`, a simulation `f : α → β` is
-- said to be bounded if there exists `b : β` such that `α = initial_seg b`.
def lt (α β : ordinal) : Prop :=
begin
  refine quotient.lift (lt' α) _ β, clear β,
  rintros ⟨β₁, rβ₁, hβ₁⟩ ⟨β₂, rβ₂, hβ₂⟩ h,
  rcases h with ⟨⟨f, hf⟩, ⟨g, hg⟩⟩,
  have hf₃ : function.left_inverse g f := hg.left_inverse hβ₁.ext hβ₁.wf hf,
  have hg₃ : function.left_inverse f g := hf.left_inverse hβ₂.ext hβ₂.wf hg,
  cases hf with hf₁ hf₂,
  cases hg with hg₁ hg₂,
  ext,
  split,
  { rintro ⟨b, rfl⟩,
    refine ⟨f b, quotient.sound ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩⟩,
    { exact λ c, ⟨f c.val, hf₁ c.val b c.property⟩ },
    { exact λ ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩, hf₁ c₁ c₂ },
    { rintros ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ h,
      simp only [subtype.mk_eq_mk],
      change rβ₂ c₂ (f c₁) at h,
      specialize hf₂ b c₂ hc₂, clear hc₂,
      rcases hf₂ with ⟨c₂, hc₂, rfl⟩,
      refine ⟨⟨c₂, hc₂⟩, _, rfl⟩,
      change rβ₁ c₂ c₁,
      specialize hg₁ (f c₂) (f c₁) h,
      rwa [hf₃, hf₃] at hg₁ },
    { refine λ c, ⟨g c.val, _⟩,
      specialize hg₁ c.val (f b) c.property,
      rwa hf₃ at hg₁ },
    { exact λ ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩, hg₁ c₁ c₂ },
    { rintros ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ h,
      simp only [subtype.mk_eq_mk],
      change ∃ c, rβ₂ _ c₁ ∧ _,
      change rβ₁ c₂ (g c₁) at h,
      specialize hg₂ c₁ c₂ h, clear hc₁ h,
      rcases hg₂ with ⟨c₂, hc₁, rfl⟩,
      replace hc₂ := hf₁ (g c₂) b hc₂,
      rw hg₃ at hc₂,
      exact ⟨⟨c₂, hc₂⟩, hc₁, rfl⟩ } },
  { rintro ⟨b, rfl⟩,
    refine ⟨g b, quotient.sound ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩⟩,
    { exact λ c, ⟨g c.val, hg₁ c.val b c.property⟩ },
    { exact λ ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩, hg₁ c₁ c₂ },
    { rintros ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ h,
      simp only [subtype.mk_eq_mk],
      change rβ₁ c₂ (g c₁) at h,
      specialize hg₂ b c₂ hc₂, clear hc₂,
      rcases hg₂ with ⟨c₂, hc₂, rfl⟩,
      refine ⟨⟨c₂, hc₂⟩, _, rfl⟩,
      change rβ₂ c₂ c₁,
      specialize hf₁ (g c₂) (g c₁) h,
      rwa [hg₃, hg₃] at hf₁ },
    { refine λ c, ⟨f c.val, _⟩,
      specialize hf₁ c.val (g b) c.property,
      rwa hg₃ at hf₁ },
    { exact λ ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩, hf₁ c₁ c₂ },
    { rintros ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ h,
      simp only [subtype.mk_eq_mk],
      change ∃ c, rβ₁ _ c₁ ∧ _,
      change rβ₂ c₂ (f c₁) at h,
      specialize hf₂ c₁ c₂ h, clear hc₁ h,
      rcases hf₂ with ⟨c₂, hc₁, rfl⟩,
      replace hc₂ := hg₁ (f c₂) b hc₂,
      rw hf₃ at hc₂,
      exact ⟨⟨c₂, hc₂⟩, hc₁, rfl⟩ } }
end

theorem initial_seg.lt (hα : well_order rα) (a : α) :
  lt (initial_seg hα a) (mk hα) :=
⟨a, rfl⟩

-- XXX: there is probably a way of proving this using choice instead of
-- univalence.
theorem lt.ext : ext lt :=
begin
  rintros ⟨α, rα, hα⟩ ⟨β, rβ, hβ⟩ h,
  change ∀ γ, (∃ a, _) ↔ ∃ a, _ at h,
  change mk hα = mk hβ,
  suffices h : α = β,
  { subst h,
    congr,
    ext a₁ a₂,
    split; intro ha,
    { specialize h (initial_seg hα a₂),
      replace h : ∃ a, initial_seg hα a₂ = initial_seg hβ a := h.mp ⟨a₂, rfl⟩,
      cases h with a h,
      unfold initial_seg at h,
      generalize_proofs h₁ h₂ at h,
      sorry
    },
    sorry
  },
  sorry

  -- XXX: incomplete proof using choice instead of univalence
  /-
  rintros ⟨α, rα, hα⟩ ⟨β, rβ, hβ⟩ h,
  change ∀ γ, lt γ (mk hα) ↔ lt γ (mk hβ) at h,
  change mk hα = mk hβ,
  refine quotient.sound ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩,
  { intro a,
    specialize h (initial_seg hα a),
    replace h : lt (initial_seg hα a) (mk hβ) := h.mp (initial_seg.lt hα a),
    -- In a homotopy type theory proof assistant, I would use univalence
    -- elsewhere to avoid using choice here.
    exact classical.some h },
  { intros a₁ a₂ ha,
    let α₁ : ordinal := initial_seg hα a₁,
    let α₂ : ordinal := initial_seg hα a₂,
    have h₁ : ∃ b₁, α₁ = initial_seg hβ b₁ := (h α₁).mp (initial_seg.lt hα a₁),
    have h₂ : ∃ b₂, α₂ = initial_seg hβ b₂ := (h α₂).mp (initial_seg.lt hα a₂),
    let b₁ : β := classical.some h₁,
    let β₁ : ordinal := initial_seg hβ b₁,
    have hb₁ : α₁ = β₁ := classical.some_spec h₁,
    let b₂ : β := classical.some h₂,
    let β₂ : ordinal := initial_seg hβ b₂,
    have hb₂ : α₂ = β₂ := classical.some_spec h₂,
    change rβ b₁ b₂,
    clear_value b₁ b₂,
    clear h₁ h₂,
    sorry
  }
  -/
end

theorem lt.wf : well_founded lt :=
begin
  refine ⟨_⟩,
  rintro ⟨α, rα, hα⟩,
  suffices h : ∀ a, acc lt (initial_seg hα a),
  { refine ⟨mk hα, λ β hβ, _⟩,
    rcases hβ with ⟨b, rfl⟩,
    exact h b },
  intro a,
  refine hα.wf.induction a _, clear a,
  intros a ih,
  refine ⟨initial_seg hα a, λ β hβ, _⟩,
  rcases hβ with ⟨⟨b, hb⟩, rfl⟩,
  specialize ih b hb,
  rename hb hb,
  unfold initial_seg at ⊢ ih,
  generalize_proofs hβ hαβ at ⊢ ih,
  suffices h : mk hαβ = mk hβ,
  { rw h, exact ih },
  clear ih,
  refine quotient.sound ⟨⟨_, _, _⟩, ⟨_, _, _⟩⟩,
  { exact λ c, ⟨c.val.val, c.property⟩ },
  { exact λ c₁ c₂ h, h },
  { rintros ⟨⟨c₁, hc₁₁⟩, hc₁₂⟩ ⟨c₂, hc₂⟩ h,
    exact ⟨⟨⟨c₂, hα.trans hc₂ hb⟩, hc₂⟩, h, rfl⟩ },
  { exact λ c, ⟨⟨c.val, hα.trans c.property hb⟩, c.property⟩ },
  { exact λ c₁ c₂ h, h },
  { rintro ⟨c₁, hc₁⟩ ⟨⟨c₂, hc₂₁⟩, hc₂₂⟩ h,
    exact ⟨⟨c₂, hc₂₂⟩, h, rfl⟩ }
end

theorem lt.trans : transitive lt :=
sorry

theorem lt.well_order : well_order lt :=
⟨lt.ext, lt.wf, lt.trans⟩

-- Theorem 10.3.20. `(ordinal, <)` is an ordinal.
def ordinal : ordinal :=
mk lt.well_order

end ordinal
