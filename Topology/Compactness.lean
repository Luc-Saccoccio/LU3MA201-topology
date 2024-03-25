import Topology.Basic

universe u v w

-- III Compacité
-- 1. théorie

section compacite

-- a) suite extraite

variable {X : Type u} [MetricSpace X]

def converge (x : ℕ → X) := ∃ l, lim x l
-- convergence dans X

def converge_in (U : Set X) (x : ℕ → X) (l : X) := (∀ n : ℕ, x n ∈ U ) ∧ (lim x l) ∧ l ∈ U
-- convergence dans une partie de X

def strictement_croissante (f : ℕ → ℕ ) : Prop := ∀ n m : ℕ, n > m -> f n > f m

def croissante (f : ℕ → ℕ) : Prop := ∀ n m : ℕ, n >= m → f n >= f m

lemma stricte_croissante_to_croissante (f : ℕ → ℕ) : strictement_croissante f → croissante f :=
  by
    intro hf n m hnm
    apply Or.elim (Nat.eq_or_lt_of_le hnm)
    . exact Nat.le_of_eq ∘ congrArg f
    . exact Nat.le_of_lt ∘ hf n m

lemma stricte_croissance_geq (f : ℕ → ℕ) : strictement_croissante f → ∀ n : ℕ, f n >= n :=
  by
    intro h n
    induction' n with n hi
    . exact Nat.zero_le (f 0)
    . exact Nat.succ_le_of_lt ∘ Nat.lt_of_le_of_lt hi $ h (n + 1) n (Nat.lt_succ_self n)

lemma unicite_limite  (x : ℕ → X) (l : X) (l' : X) (hl: lim x l) (hl': lim x l') : l = l':= by
  choose N hN using hl
  choose N' hN' using hl'

  sorry

lemma limite_suite_extraite (x : ℕ → X) (l : X) (f : ℕ → ℕ) : lim x l ∧ strictement_croissante f -> lim (x ∘ f) l :=
  by
    rintro ⟨hx, hf⟩ ε hε
    obtain ⟨N, hN ⟩ := hx ε hε
    use N
    intro n hn
    have t : f n >= f N := stricte_croissante_to_croissante f hf n N hn
    apply hN
    have sup_N: f N >= N := stricte_croissance_geq f hf N
    linarith [t, stricte_croissance_geq f]


-- b) compacité

def is_compact (K : Set X) : Prop := ∀ x : ℕ → X, ∃ f : ℕ → ℕ, ∃ l ∈ K, strictement_croissante f ∧ converge_in K (x ∘ f) l

lemma compact_is_closed : ∀ K : Set X, is_compact K → is_closed K :=
  by
    intro K h
    contrapose! h
    have diff : Closure K ≠ K := by
      intro absurde
      have j : is_closed (Closure K) := by exact closure_is_closed
      rw [absurde] at j
      apply h at j
      exact j

    have c : K ⊂ Closure K :=
      Set.ssubset_iff_subset_ne.mpr ⟨sub_closure, diff.symm⟩
    have l_in_closure_not_in_K : ∃ l : X, l ∈ Closure K ∧ l ∉ K :=
      Set.exists_of_ssubset c

    rcases l_in_closure_not_in_K with ⟨l, l_in_closure, l_not_in_K⟩
    obtain ⟨x, hx⟩ := (sequential_closure K l).mp l_in_closure

    intro compacite
    choose f l' hl' hf conv_l' using compacite x
    have lim_l : lim (x ∘ f) l := limite_suite_extraite x l f ⟨hx.2, hf⟩
    have egalite: l=l':= by apply unicite_limite (x∘f) l l' lim_l conv_l'.2.1
    rw [egalite] at l_not_in_K
    apply l_not_in_K at hl'
    exact hl'


lemma subcompact_closed_is_compact (K H: Set X) (k_compact : is_compact K) (h_sub: H  ⊆ K) (h_closed : is_closed H)  : is_compact H := by
  intro x
  let h :ℕ → Prop := λn ↦  x n ∈ H
  obtain ⟨ f, l, l_in_k, croiss_f,suite_in_K, hl,_⟩ := k_compact x
  have suite_in_H :  ∀ (n : ℕ), (x ∘ f) n ∈ H :=  by
    intro n
    -- il faut utiliser h (f n)
    sorry
  have l_in_h : l ∈ Closure H := by apply (sequential_closure H l).mpr  ⟨ x∘f,suite_in_H, hl⟩
  rw [closure_closed_is_closed] at l_in_h
  use f
  use l

  have h3 : converge_in H (x ∘ f) l := by
    exact ⟨ suite_in_H , hl,l_in_h⟩

  exact ⟨ l_in_h, croiss_f, h3⟩
  exact h_closed



--("L'image continue d'un compact est compacte") Soit f : X ! Y
--une application continue entre deux espaces metriques. Si X est compact, alors f(X) est compact.

--Si (X; dX) et (Y; dY ) sont deux espaces metriques homeomorphes,
-- le premier est compact si et seulement si le second est compact.

--Si f : X ! Y est une bijection continue entre deux espaces metriques, et si (X; dX) est compact,
--alors sa reciproque f􀀀1 est continue, et f est un homeomorphisme.

--(c) Compacite dans RN
--(d) Compacite et recouvrements
--(e) Continuite uniforme
