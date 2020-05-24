import tuto_lib

/-
This file continues the elementary study of limits of sequences. 
It can be skipped if the previous file was too easy, it won't introduce
any new tactic or trick.

Remember useful lemmas:

abs_le (x y : ℝ) : |x| ≤ y ↔ -y ≤ x ∧ x ≤ y

abs_add (x y : ℝ) : |x + y| ≤ |x| + |y|

abs_sub (x y : ℝ) : |x - y| = |y - x|

ge_max_iff (p q r) : r ≥ max p q  ↔ r ≥ p ∧ r ≥ q

le_max_left p q : p ≤ max p q

le_max_right p q : q ≤ max p q

and the definition:

def seq_limit (u : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| ≤ ε

You can also use a property proved in the previous file:

unique_limit : seq_limit u l → seq_limit u l' → l = l'

def extraction (φ : ℕ → ℕ) := ∀ n m, n < m → φ n < φ m
-/

variable {φ : ℕ → ℕ}

example : extraction φ → ∀ n, n ≤ φ n :=
begin
  intros h n,
  induction n with n hn,
  { exact nat.zero_le _ },
  { specialize h n (n+1) (by linarith),
    exact nat.succ_le_of_lt (by linarith [h]) },
end

/-
The next lemma is proved by an easy induction, but we haven't seen induction
in this tutorial. If you did the natural number game then you can delete 
the proof below and try to reconstruct it.
-/
/-- An extraction is greater than id -/
lemma id_le_extraction' : extraction φ → ∀ n, n ≤ φ n :=
begin
  intros hyp n,
  induction n with n hn,
  { exact nat.zero_le _ },
  { exact nat.succ_le_of_lt (by linarith [hyp n (n+1) (by linarith)]) },
end

/-- Extractions take arbitrarily large values for arbitrarily large 
inputs. -/
-- 0039
lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N :=
begin
  intros h N N',
  use max N N',
  split,
  { exact le_sup_right },
  { transitivity max N N',
    { exact id_le_extraction' h (max N N') },
    { exact le_sup_left } }
end

/-- A real number `a` is a cluster point of a sequence `u` 
if `u` has a subsequence converging to `a`. 

def cluster_point (u : ℕ → ℝ) (a : ℝ) :=
∃ φ, extraction φ ∧ seq_limit (u ∘ φ) a
-/

variables {u : ℕ → ℝ} {a l : ℝ}

/-
In the exercise, we use `∃ n ≥ N, ...` which is the abbreviation of
`∃ n, n ≥ N ∧ ...`.
Lean can read this abbreviation, but displays it as the confusing:
`∃ (n : ℕ) (H : n ≥ N)`
One gets used to it. Alternatively, one can get rid of it using the lemma
  exists_prop {p q : Prop} : (∃ (h : p), q) ↔ p ∧ q
-/

/-- If `a` is a cluster point of `u` then there are values of
`u` arbitrarily close to `a` for arbitrarily large input. -/
-- 0040
lemma near_cluster (h : cluster_point u a) :
  ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε :=
begin
  intros ε ε_pos N,
  rcases h with ⟨φ, h, hu⟩,
  cases hu ε ε_pos with N' hN',
  rcases extraction_ge h N N' with ⟨n, h, hn⟩,
  exact ⟨φ n, hn, hN' n h⟩
end

/-
The above exercice can be done in five lines. 
Hint: you can use the anonymous constructor syntax when proving
existential statements.
-/

--lemma extraction_ge : extraction φ → ∀ N N', ∃ n ≥ N', φ n ≥ N :=
/-- If `u` tends to `l` then its subsequences tend to `l`. -/
-- 0041
lemma subseq_tendsto_of_tendsto' (h : seq_limit u l) (hφ : extraction φ) :
seq_limit (u ∘ φ) l :=
begin
  intros ε ε_pos,
  cases h ε ε_pos with N hN,
  use N,
  intros n hn,
  apply hN,
  calc
    N ≤ n   : hn
  ... ≤ φ n : id_le_extraction hφ n
end

#find _ → (_ : ℝ) = _

/-- If `u` tends to `l` all its cluster points are equal to `l`. -/
-- 0042
lemma cluster_limit (hl : seq_limit u l) (ha : cluster_point u a) : a = l :=
begin
  -- I will leave this proof unpolished and document my thought process. This
  -- should be a simple question of applying the lemmas above. First, I will
  -- unfold the definitions because I always struggle to remember them.
  unfold seq_limit at hl,
  unfold cluster_point at ha,
  -- There is no reason why `ha` shouldn't be cased (except if you want to make
  -- the proof small).
  rcases ha with ⟨φ, hφ, hu⟩,
  -- I just realized I don't know how to an `ℝ` equality. To the mathlib docs!
  -- ...okay, the quick skim through the docs wasn't fruitful, neither was the
  -- `#find` above.
  --
  -- And I cheated, I took a glimpse at the solution and it uses a lemma
  -- used in the previous tutorial... Darn, I should have thought!
  apply unique_limit hu,
  -- Okay, now the problem got interesting!
  unfold seq_limit at hu,
  -- `seq_limit` in goal that means... `intros` time!
  intros ε ε_pos,
  cases hl ε ε_pos with N hN,
  use φ N,
  intros n hn,
  -- Okay, everything from the last comment to here was pretty straight
  -- forward. Now, it looks like the trick from the last lemma will suffice.
  apply hN,
  -- Firstly, `ge` sucks.
  unfold ge at *,
  calc
    N ≤ φ N : id_le_extraction hφ N
  ... ≤ n   : hn
  ... ≤ φ n : id_le_extraction hφ n
  -- After writing `calc`, it was just a question of adding `by
  -- library_search` at each step and accepting the solutions, because I am
  -- lazy.
end

/-- Cauchy_sequence sequence -/
def cauchy_sequence (u : ℕ → ℝ) := ∀ ε > 0, ∃ N, ∀ p q, p ≥ N → q ≥ N → |u p - u q| ≤ ε

-- 0043
example : (∃ l, seq_limit u l) → cauchy_sequence u :=
begin
  rintros ⟨l, hl⟩ ε ε_pos,
  unfold seq_limit at hl,
  cases hl (ε/2) (by linarith) with N hN,
  use N,
  intros p q hp hq,
  have := hN p hp,
  have := hN q hq,
  calc
  |u p - u q| ≤ |(u p - l) + (l - u q)| : by ring
  ...         ≤ |u p - l| + |l - u q|   : by apply abs_add
  ...         ≤ |u p - l| + |u q - l|   : by rw abs_sub (u q) l
  ...         ≤ ε                       : by linarith,
end


/- 
In the next exercise, you can reuse
 near_cluster : cluster_point u a → ∀ ε > 0, ∀ N, ∃ n ≥ N, |u n - a| ≤ ε
-/
-- 0044
example (hu : cauchy_sequence u) (hl : cluster_point u l) : seq_limit u l :=
begin
  intros ε ε_pos,
  unfold cluster_point at hl,
  cases hu (ε/2) (by linarith) with N hN,
  rcases near_cluster hl (ε/2) (by linarith) N with ⟨N', hNN', hN'⟩,
  use N,
  intros n hn,
  have := hN n N' hn hNN',
  calc
  |u n - l| ≤ |(u n - u N') + (u N' - l)| : by ring
  ...       ≤ |u n - u N'| + |u N' - l|   : by apply abs_add
  ...       ≤ ε                           : by linarith,
end

