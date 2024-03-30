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





def lim_X (x : ℕ → X) (l : X) := ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, d l (x n) < ε


lemma sequential_continous (f : X → Y ) (x₀ : X) :  continuous_on f x₀ ↔   ∀ (x : ℕ → X) , lim_X x x₀ →  lim_X ( f ∘ x ) (f x₀ ):= by
  sorry



lemma image_continuous_compact (f : X → Y ) (f_continuous: Continuous f) (univ_compact : is_compact (Set.univ : Set X)) : is_compact (Set.image f Set.univ) := by

-- is_compact prend un argument de type Set X, de même Set.image prend en argument f et un objet de type Set X, on utilise donc Set.univ quand on ne peut pas utiliser X directement
-- concilier ces deux types a alourdi la preuve...

  intro y
  have hn : ∀ n, ∃ xn ∈ Set.univ, f (xn ) = y n := by
    intro n
    exact ( (Set.mem_image f Set.univ ( y n)).mp (y n).2 )

  choose x hx using hn

  let x' : ℕ → Set.univ := λ n ↦ ⟨x n, (hx n).1 ⟩  -- première adaptation, ceci permet d'appliquer la définition de la compacité à x' à valeurs dans Set.univ au lieu de X
  obtain ⟨ j, l, _, croiss_j,conv_in_univ⟩ := univ_compact x'

  use j, (f l) 

  have hf : ∀ (t : X), f t ∈ f '' Set.univ := by
    intro t
    apply (Set.mem_image f Set.univ ( f t)).mpr
    use t
    apply And.intro
    exact Set.mem_univ t
    rfl
    
  apply And.intro
  exact hf l 
  apply And.intro
  exact croiss_j

-- la dernière proposition du goal se montre en plusieurs étapes

  have limite : lim_X (f ∘ x ∘ j) (f l) := by -- d'abord on doit montrer lim_X car f prend ses antécédents dans X, donc on ne peut la composer qu'avec x qui est a valeur dans X et non x' qui est à valeur dans Set.univ
    apply ( sequential_continous f l).mp (f_continuous  l ) (x∘j)
    intro ε hε 
    obtain ⟨ N, hN ⟩ := conv_in_univ.1 ε hε
    use N 
    have eg : ∀ n, x n = x' n := by  
      intro n 
      rfl 
    intro n
    rw [Function.comp_apply]
    rw[eg (j n)]
    exact hN n

  --en revenant aux ε on montre facilement que lim_X et lim sont équivalentes
  apply And.intro
  · intro ε hε
    obtain ⟨ N, hN ⟩ :=  limite ε hε
    use N
    intro n hn
    rw [Function.comp_apply]
    rw [←  (hx (j n)).2]
    specialize hN n hn
    rw [ Function.comp_apply] at hN 
    exact hN

  · exact hf l 

  


def inverse  ( f: X → Y )  (h2: Function.Bijective f ):=

def homeomorphisme ( f: X → Y ) (h1: Continuous f) (h2: Function.Bijective f ):= 


--Si (X; dX) et (Y; dY ) sont deux espaces metriques homeomorphes,
-- le premier est compact si et seulement si le second est compact.

--Si f : X ! Y est une bijection continue entre deux espaces metriques, et si (X; dX) est compact,
--alors sa reciproque f􀀀1 est continue, et f est un homeomorphisme.

--(d) Compacite et recouvrements
--(e) Continuite uniforme
