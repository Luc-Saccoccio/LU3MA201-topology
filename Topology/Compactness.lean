import Topology.Basic

universe u v w


-- III Compacité
-- 1. théorie

section compacite

-- a) suite extraite

variable {X Y : Type u} [MetricSpace X] [MetricSpace Y]


def converge_in (K : Set X) (x : ℕ → K) (l : X) := (lim  x l) ∧ l ∈ K
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

lemma unicite_limite  ( K:Set X) (x : ℕ → K) (l : X) (l' : X) (hl: lim  x l) (hl': lim  x l') : l = l':= by
  choose N hN using hl
  choose N' hN' using hl'

  sorry

lemma limite_suite_extraite ( K:Set X) (x : ℕ → K) (l : X) (f : ℕ → ℕ) : lim  x l ∧ strictement_croissante f -> lim  (x ∘ f) l :=
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

def is_compact (K : Set X) : Prop := ∀ x : ℕ → K, ∃ f : ℕ → ℕ, ∃ l ∈ K, strictement_croissante f ∧ converge_in K (x ∘ f) l


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
    have lim_l : lim (x ∘ f) l := limite_suite_extraite K x l f ⟨hx, hf⟩
    have egalite: l=l':= by apply unicite_limite K (x∘f) l l' lim_l conv_l'.1
    rw [egalite] at l_not_in_K
    apply l_not_in_K at hl'
    exact hl'
 

lemma subcompact_closed_is_compact (K H: Set X) (k_compact : is_compact K) (h_sub: H  ⊆ K) (h_closed : is_closed H)  : is_compact H := by
  intro x
  have x_in_k : ∀ (n : ℕ), (x n : X) ∈ K := by
    intro n
    apply Set.mem_of_subset_of_mem h_sub 
    apply (x n).2

  let y : ℕ → K := λ n ↦ ⟨x n, x_in_k n⟩
  obtain ⟨ f, l, _, croiss_f,conv_in_K⟩ := k_compact y
  
  have l_in_h : l ∈ Closure H := by apply (sequential_closure H l).mpr  ⟨ x∘f,conv_in_K.1⟩
  rw [closure_closed_is_closed] at l_in_h
  use f,l, l_in_h, croiss_f
  have eg : ∀ n , x n = (y n :X):= by
    intro n
    rfl
  have lim_xf : lim (x∘f) l := by 
    intro ε hε 
    obtain ⟨ N, hN⟩ := conv_in_K.1 ε hε 
    use N
    intros n hn
    specialize hN n hn
    have eg : x (f n) = (y (f n) : X) := eg (f n)
    rw [Function.comp_apply]
    rw [Function.comp_apply] at hN
    rw [<- eg] at hN
    exact hN
    
  exact ⟨ lim_xf,l_in_h⟩
  exact h_closed





lemma image_continuous_compact (f : X → Y ) (f_continuous: Continuous f) (univ_compact : is_compact (univ : Set X)) : is_compact (Set.image f univ) := by
  intro y 
  have hn : ∀ n, ∃ xn ∈ univ, f (xn ) = y n := by
    intro n 
    exact ( (Set.mem_image f univ ( y n)).mp (y n).2 )

  choose x hx using hn

  let x' : ℕ → univ := λ n ↦ ⟨x n, (hx n).1 ⟩
  obtain ⟨ j, l, _, croiss_f,conv_in_univ⟩ := univ_compact x'

  sorry -- j'ai besoin du lemme  sequential_continous
  

def lim_X (x : ℕ → X) (l : X) := ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, d l (x n) < ε -- ici j'ai besoin de prendre une suite de N dans X pour ensuite la composer par f : X → Y  dans le lemme suivant 

lemma sequential_continous (f : X → Y ) (x₀ : X) :  continuous_on f x₀ ↔   ∀ (x : ℕ → X) , lim_X x x₀ →  lim_X ( f ∘ x ) (f x₀ ):= by 
  sorry
-- est ce que je drevrais plutot travailler avec f : (univ : Set X) → Y et ainsi utiliser la définition lim de Basic.lean ? 


-- j'aurais besoin également des définitions suivantes

def inverse  ( f: X → Y )  (h: Function.Bijective f ) := sorry  -- je cherche comment définir la fonction inverse qui à une fonction bijective associe son inverse

def homeomorphisme ( f: X → Y ) (h1: Continuous f) (h2: Function.Bijective f ):= Continuous (inverse f h2) 


--Si (X; dX) et (Y; dY ) sont deux espaces metriques homeomorphes,
-- le premier est compact si et seulement si le second est compact.

--Si f : X ! Y est une bijection continue entre deux espaces metriques, et si (X; dX) est compact,
--alors sa reciproque f􀀀1 est continue, et f est un homeomorphisme.

--(c) Compacite dans RN
--(d) Compacite et recouvrements
--(e) Continuite uniforme
