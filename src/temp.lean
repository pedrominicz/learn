import tactic.basic

variable {α : Type*}
variables a b c d : set α

example : ∀ x, x ∈ a ∩ c → x ∈ a ∪ b :=
by { rintros _ ⟨ha, _⟩, left, assumption }

example : ∀ x, x ∈ -(a ∪ b) → x ∈ -a :=
by { intros _ h _, apply h, left, assumption }

section

  def disjoint := ∀ ⦃x⦄, x ∈ a → ¬ x ∈ b

  lemma disjoint_refl {a b : set α} (h : disjoint a b) : disjoint b a :=
  by { intros x in_b in_a, apply h; assumption }

  example (h : disjoint a b) (hc : c ⊆ a) (hd : d ⊆ b) : disjoint c d :=
  begin
    intros _ in_c in_d,
    apply h,
    { apply hc, assumption },
    { apply hd, assumption },
  end

  variable {i : Type*}
  variables (p q : i → set α)

  def union := { x | ∃ i, x ∈ p i }
  def inter := { x | ∀ i, x ∈ p i }

  notation `⋃` binders `,` r:(scoped f, union f) := r
  notation `⋂` binders `,` r:(scoped f, inter f) := r

  

end