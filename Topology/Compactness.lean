import Topology.Basic

universe u v w

open MetricSpace

-- III Compacité
-- 1. théorie

section compacite

-- a) suite extraite

variable {X Y : Type u} [MetricSpace X] [MetricSpace Y]

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

-- cette seconde définition de la limite me permettra de d'étudier la convergence dans différents espaces métriques, la distance utilisée dans cette définition dépendra bien de l'espace métrique su lequelle elle est défini
def lim' (x : ℕ → α) (l : α ) [MetricSpace α  ] := ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, d l (x n) < ε

def Compact (K : Type v) [MetricSpace K]  : Prop := ∀ x : ℕ → K , ∃ f : ℕ → ℕ,  ∃ l,  (strictement_croissante f ∧  lim' ( x ∘ f) l)

-- definition d'une partie compact de X
def is_compact (K : Set X) : Prop := ∀ x : ℕ → K, ∃ f : ℕ → ℕ, ∃ l ∈ K, strictement_croissante f ∧ lim (x ∘ f) l

-- tout compact est fermé
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
    choose f l' hl' hf lim_l' using compacite x
    have lim_l : lim (x ∘ f) l := limite_suite_extraite K x l f ⟨hx, hf⟩
    have egalite: l=l':= by apply unicite_limite K (x∘f) l l' lim_l lim_l'
    rw [egalite] at l_not_in_K
    apply l_not_in_K at hl'
    exact hl'

-- toute partie fermé de X compact est compact
lemma subcompact_closed_is_compact (K H: Set X) (k_compact : is_compact K) (h_sub: H  ⊆ K) (h_closed : is_closed H)  : is_compact H := by
  intro x
  have x_in_k : ∀ (n : ℕ), (x n : X) ∈ K := by
    intro n
    apply Set.mem_of_subset_of_mem h_sub
    apply (x n).2

  let y : ℕ → K := λ n ↦ ⟨x n, x_in_k n⟩
  obtain ⟨ f, l, _, croiss_f,lim_in_K⟩ := k_compact y

  have l_in_h : l ∈ Closure H := by apply (sequential_closure H l).mpr  ⟨ x∘f,lim_in_K⟩
  rw [closure_closed_is_closed] at l_in_h
  use f,l, l_in_h, croiss_f
  have eg : ∀ n , x n = (y n :X):= by
    intro n
    rfl
  have lim_xf : lim (x∘f) l := by
    intro ε hε
    obtain ⟨ N, hN⟩ := lim_in_K ε hε
    use N
    intros n hn
    specialize hN n hn
    have eg : x (f n) = (y (f n) : X) := eg (f n)
    rw [Function.comp_apply]
    rw [Function.comp_apply] at hN
    rw [<- eg] at hN
    exact hN

  exact  lim_xf
  exact h_closed


-- dans un espace metrique compact, toute partie fermée est compact
lemma closed_incompact_iscompact (hX : Compact X) ( K :  Set X) (hK : is_closed K) : is_compact K := by
  intro x
  let x' : ℕ → X := λ n ↦ x n
  obtain ⟨ f, l, hf,limite⟩ := hX x'
  use f
  have eg : ∀ n , x n = x' n:= by
    intro n
    rfl
  have limite2 : lim (x ∘ f) l := by
    intro ε hε
    obtain ⟨ N , hN⟩ := limite ε hε
    use N
    intro n hn
    specialize hN n hn
    rw [Function.comp_apply]
    rw [Function.comp_apply] at hN
    rw [eg]
    exact hN
  have hl :l ∈ Closure K  := (sequential_closure K l).mpr ⟨ x∘f ,limite2⟩
  rw [closure_closed_is_closed hK] at hl
  use l




lemma sequential_continous (f : X → Y ) (x₀ : X) :  continuous_on f x₀ ↔   ∀ (x : ℕ → X) , lim' x x₀ →  lim' ( f ∘ x ) (f x₀ ):= by
  
  apply Iff.intro
  · intro H x l ε hε 
    specialize H ε hε 
    obtain ⟨ δ, hδ, continu ⟩ := H
    obtain ⟨ N, hN⟩ := l δ hδ 
    use N
    intro n hn
    specialize hN n hn
    specialize continu (x n)
    apply continu
    exact hN
  

  · contrapose
    intro h 
    unfold continuous_on at h
    push_neg at h
    push_neg
    obtain ⟨ ε, hε, H ⟩ := h
    unfold lim'
    let δ : ℕ → ℝ := λ n ↦ 1/n
    have δ_pos: ∀n, δ n > 0:= sorry -- voir dans mathlib 1/n > 0
    have suite: ∀ n:ℕ, ∃ xn, d_[X] x₀ xn < (δ n) ∧ ε ≤ d_[Y] (f x₀) (f xn):= by
      intro n
      exact H ( δ n ) (δ_pos n)
    choose x hx using suite
    use x  
    apply And.intro
    · intro e he
      have hl: ∃ N, ∀ n ≥ N, δ n < e:= by sorry 
        -- use N en posant N= [e] + 1, voir dans mathlib notation partie entière
      obtain ⟨ N, hN⟩ := hl
      use N
      intro n hn
      exact lt_trans (hx n).1 (hN n hn )

    · push_neg
      use ε, hε 
      intro N
      use N, le_rfl
      apply (hx N).2 


  apply Iff.intro
  · intro H x l ε hε
    sorry

  · sorry


lemma image_continuous_compact (f : X → Y ) (f_continuous: Continuous f) (univ_compact : is_compact (Set.univ : Set X)) : is_compact (Set.image f Set.univ) := by

-- is_compact prend un argument de type Set X, de même Set.image prend en argument f et un objet de type Set X, on utilise donc Set.univ quand on ne peut pas utiliser X directement
-- je fait de jongler entre ces deux types a un peu alourdi la preuve qui suit

  intro y
  have hn : ∀ n, ∃ xn ∈ Set.univ, f (xn ) = y n := by
    intro n
    exact ( (Set.mem_image f Set.univ ( y n)).mp (y n).2 )

  choose x hx using hn

  let x' : ℕ → Set.univ := λ n ↦ ⟨x n, (hx n).1 ⟩  -- ceci permet d'appliquer la définition de la compacité à x' à valeurs dans Set.univ au lieu de X
  obtain ⟨ j, l, _, croiss_j,lim_in_univ⟩ := univ_compact x'

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
  have limite : lim' (f ∘ x ∘ j) (f l) := by -- d'abord on doit montrer lim' car f prend ses antécédents dans X, donc on ne peut la composer qu'avec x qui est a valeur dans X
    apply ( sequential_continous f l).mp (f_continuous  l ) (x∘j)
    intro ε hε
    obtain ⟨ N, hN ⟩ := lim_in_univ ε hε
    use N
    have eg : ∀ n, x n = x' n := by
      intro n
      rfl
    intro n
    rw [Function.comp_apply]
    rw[eg (j n)]
    exact hN n

  --en revenant aux ε on montre facilement que lim' et lim sont équivalentes
  intro ε hε
  obtain ⟨ N, hN ⟩ :=  limite ε hε
  use N
  intro n hn
  rw [Function.comp_apply]
  rw [←  (hx (j n)).2]
  specialize hN n hn
  rw [ Function.comp_apply] at hN
  exact hN




-- je n'ai pas su formuler les deux définitions qui suivent, la première est une application qui prend en entrée une fonction bijective et renvoit son inverse

--def inverse  ( f: X → Y )  (h2: Function.Bijective f ):=
--def homeomorphisme ( f: X → Y ) (h1: Continuous f) (h2: Function.Bijective f ):= Continuous (inverse f)

-- ensuite je montrerai:

--Si (X; dX) et (Y; dY ) sont deux espaces metriques homeomorphes, le premier est compact si et seulement si le second est compact.

--Si f : X ! Y est une bijection continue entre deux espaces metriques, et si (X; dX) est compact, alors sa reciproque f􀀀1 est continue, et f est un homeomorphisme.


def CauchySeq (u : ℕ → X) := ∀ ε > 0, ∃ N : ℕ , ∀ m ≥ N,∀ n ≥ N,  d (u m) (u n) < ε

def Complet (K : Type v) [MetricSpace K] := ∀ u : ℕ → K, CauchySeq u → ∃ l : K, lim' u l  -- j'ai repris la def de Charles, pourquoi type v au lieu de type u? il semnle que ça ne change rien

lemma Cauchy_val_adherence_conv (u : ℕ → X) (l : X) (f : ℕ → ℕ) (h1 : strictement_croissante f) (h2 : lim' (u∘f) l) (h3 :  CauchySeq u): lim' u l := by
  intro ε hε
  specialize h3 (ε/2) (half_pos hε)
  specialize h2 (ε/2) (half_pos hε)
  obtain ⟨ N1, hN1 ⟩ := h2
  obtain ⟨ N2, hN2 ⟩ := h3
  use Nat.max N1 N2
  intro n hn
  have h : d l (u n) ≤  d l ( u (f n)) + d (u (f n)) (u n) := dist_triangle
  have ineq1: Nat.max N1 N2 ≥ N1 := Nat.le_max_left  N1 N2
  have ineq2: Nat.max N1 N2 ≥ N2 := Nat.le_max_right  N1 N2

  specialize hN1 n (le_trans ineq1 hn )
  specialize hN2 n (le_trans ineq2 hn )
  specialize hN2 (f n) ( le_trans (le_trans ineq2 hn )  (stricte_croissance_geq f h1 n)  )
  rw [Function.comp_apply] at hN1
  rw [dist_symm] at hN2

  linarith



lemma compact_is_complet (K : Type v) [MetricSpace K] : Compact K -> Complet K := by
  intro h x hx
  obtain ⟨ f, l, croiss_f,lim_l⟩ := h x
  use l
  apply Cauchy_val_adherence_conv x l f croiss_f lim_l hx


--(d) Compacite et recouvrements



lemma recouvrement_fini (hX: Compact X) (α : ℝ )(hα : α > 0) : ∃ n , ∃ x: Fin n → X, Set.univ ⊆ ( ⋃ xi ∈ List.ofFn x, B( xi , α ) ):= by

  contrapose hX -- on suppose que la conclusion n'est pas vérifiée et on montre que X n'est pas conmpact
  push_neg at hX

  -- on obtient une suite d'élément u tel que ∀n, et pour toute famille (x i)i≤ n, u n ∉ ⋃(i≤n) B(xi,α)
  have h : ∀n, ∀ x : Fin n → X,  ∃ un ∈ Set.univ , un ∉ ⋃ xi ∈ List.ofFn x, B(xi,α) := by
    intro n xn
    apply (Set.not_subset_iff_exists_mem_not_mem).mp (hX n xn)
  unfold Compact
  push_neg

  --on construit une suite x par récurence sur n
  have suite :∀n, ∃ x : Fin n → X, ∀  p , ∀ m > p, d (x p ) (x m ) >= α := by
    intro n

    induction n with
    | zero => simp -- pour n=0,  Fin n = ∅ donc pour n'importe quelle suite x, la conclusion est trivialement vérifiée ∀ m,p ∈ ∅,

    --l'hypothese de reccurence nous donne une suite x: Fin n -> X, défini pour t< n, on la complète avec le terme x n = un par h
    | succ n ih =>
      obtain ⟨ x, hx ⟩ := ih
      specialize h n x
      obtain ⟨ un, hun⟩ := h
      let x' :  Fin (Nat.succ n) → X := λt ↦ if h: t < n then x ⟨ t.val, h⟩  else un
      use x'

      --il faut alors montrer que la suite obtenu convient
      intro p m hpm

      have ip : p < n := lt_of_lt_of_le hpm (Nat.le_of_lt_succ m.2)
      have im : m < n ∨ ↑m =n := lt_or_eq_of_le (Nat.le_of_lt_succ m.2 )

      have egp : x' p = if (p < n) then x ⟨p.val, ip⟩ else un := rfl
      rw [if_pos ip ]at egp -- ceci prouve que x'(p)=x(p)

      cases im with -- mais pour prouver que x'(m)=x(m) il faut faire une disonction de cas, m < n ou m =n

      | inl hm1 =>  --cas m < n
        specialize hx ⟨ p.val , ip⟩ ⟨ m.val, hm1⟩ hpm
        have egm : x' m = if (m < n) then x ⟨m.val, hm1⟩ else un := rfl
        rw [if_pos hm1 ]at egm --ceci prouve que x'(m)=x(m)
        rw [<- egp, <- egm] at hx
        exact hx
        -- ce cas se prouve donc simplement par les égalités x'(m)=x(m) , x'(p)=x(p) puis l'hypoyhèse de recurrence hx

      | inr hm2 => -- cas m = n
        have eg_un: x' m = if h:(m < n) then x ⟨m.val, h ⟩ else un := rfl -- on reprend la définition de x'
        have neg : ¬(m<n) := not_lt_of_ge (((le_antisymm_iff).mp hm2).2)
        have hx': x' ⟨m, (Nat.lt_succ).mpr ((le_antisymm_iff).mp hm2).1⟩  = un := by simp [eg_un, neg] --ceci prouve que x'(m)=un
        rw [egp, hx' ] -- montrer que d(x'm,x'p) ≥ α revient donc à montrer que d(un, x p)≥ α
        have union: ¬∃ i, un ∈ ⋃ (_ : i ∈ List.ofFn x), B(i,α) := (Iff.not Set.mem_iUnion ).mp hun.2
        push_neg at union
        simp at union --
        apply union (x ⟨ p, ip ⟩)
        exact
      -- ce cas se vérifie donc par la propriété de non appartenance a une union, donc a chaque boule de l'union, en particulier cette propriété est vrai pour la boule de centre x(p)

    --donc ∀ n, il existe n premiers termes d'une suite dont tous les termes sont a distance ≥ α les uns des autres, donc c'est vrai pour une infinité de termes

  -- il reste à montrer que cette suite n'admet pas de valeurs d'adhérence

sorry




--(e) Continuite uniforme



