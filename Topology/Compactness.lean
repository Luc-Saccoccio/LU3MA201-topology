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
    let δ : ℕ → ℝ := λ n ↦ 1/ ( n + 1)
    have δ_pos: ∀n, δ n > 0:= by 
      intro n
      apply one_div_pos.mpr
      norm_cast
      apply Nat.zero_lt_succ n
    have suite: ∀ n:ℕ, ∃ xn, d_[X] x₀ xn < (δ n) ∧ ε ≤ d_[Y] (f x₀) (f xn):= by
      intro n
      exact H ( δ n ) (δ_pos n)
    choose x hx using suite
    use x  
    
    apply And.intro
    · intro e he
      have hl [FloorSemiring ℝ ]: ∃ N, ∀ n ≥ N, δ n < e:= by
        --use ⌈(1 / e)⌉₊  
        use Nat.ceil (1/e)
        intro n hn
        simp [δ ]
        simp at hn
        have i:=  lt_of_le_of_lt hn (lt_add_one (n:ℝ))
        exact inv_lt_of_inv_lt he i

      obtain ⟨ N, hN⟩ := hl
      use N
      intro n hn
      exact lt_trans (hx n).1 (hN n hn )

    · push_neg
      use ε, hε 
      intro N
      use N, le_rfl
      apply (hx N).2 
    

 

  
lemma image_continuous_compact (f : X → Y ) (f_continuous: Continuous f) (h_compact : Compact  X) : is_compact (Set.image f Set.univ) := by
-- is_compact prend un argument de type Set X, de même Set.image prend en argument f et un objet de type Set X, on utilise donc Set.univ quand on ne peut pas utiliser X directement
-- concilier ces deux types a alourdi la preuve
  intro y
  have hn : ∀ n, ∃ xn ∈ Set.univ, f (xn ) = y n := by
    intro n
    exact ( (Set.mem_image f Set.univ ( y n)).mp (y n).2 )

  choose x hx using hn
  
  obtain ⟨ j, l, croiss_j,lim_in_univ⟩ := h_compact x

  use j, (f l) 

  have hf :  f l ∈ f '' Set.univ := by
    
    apply (Set.mem_image f Set.univ ( f l)).mpr
    use l
    apply And.intro
    exact Set.mem_univ l
    rfl
    
  apply And.intro
  exact hf 
  apply And.intro
  exact croiss_j

-- la dernière proposition du goal se montre en plusieurs étapes
  have limite : lim' (f ∘ x ∘ j) (f l) := by -- d'abord on doit montrer lim' car f prend ses antécédents dans X, donc on ne peut la composer qu'avec x qui est a valeur dans X
    apply ( sequential_continous f l).mp (f_continuous  l ) (x∘j)
    intro ε hε 
    obtain ⟨ N, hN ⟩ := lim_in_univ ε hε
    use N 

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

theorem Converg_Cauchy (u : ℕ → X) : lim' u l → CauchySeq u := by
  intro hl
  unfold lim' at hl
  unfold CauchySeq
  intro ε ε_pos
  specialize hl (ε/2) (half_pos ε_pos) 
  obtain ⟨N, hN⟩ := hl 
  use N
  intro m hm
  intro n hn
  have hd : d (u n) (u m) ≤ d (u n) l + d l (u m)  :=  dist_triangle
  have h₁ : d (u n) l < ε/2 := @dist_symm X _ _ _ ▸ hN n hn
  have h₂ : d (u m) l < ε/2 := @dist_symm X _ _ _ ▸ hN m hm
  have hε := add_lt_add h₁ h₂
  have h : d (u n) (u m) < ε/2 + ε/2 := by
    nth_rewrite 2 [dist_symm] at hε 
    apply lt_of_le_of_lt hd hε
  have H : d (u n) (u m) < ε := by
    linarith 
  rw [dist_symm]
  exact H



--exemple "minimal" du problème de construction de suite : comment construire une suite injective dans un ensemble X, à partir de l'hypothèse qu'à chaque fois qu'on a une partie finie de X, on peut trouver un nouvel élément ?



lemma h_suite (X: Type) (H: (∀ A: Finset X, ∃ x: X, x ∉ A)): (∃ u: ℕ → X, ∀k l, k<l → (u k ≠ u l)) := by 
  classical
  choose new h_new using H
  let f := λ (s : Finset X) ↦ insert (new s) s
  let f_set := λ n ↦ Nat.iterate f n ∅
  
  have h_rec: ∀ n: ℕ , f_set (n + 1) = f (f_set n) := by
    simp only [f_set]
    intro n
    apply  Function.iterate_succ_apply' f
  use new ∘ f_set
  intro k l h_kl  
  have inclu: new (f_set k)  ∈ f_set l:= by 
    induction l with
    | zero =>  cases h_kl  

    | succ n ih => 
      rw [h_rec]
      simp only [f]
      have h := lt_or_eq_of_le ((Nat.lt_succ_iff ).mp h_kl)
      rw [Finset.insert_eq]
      cases h with
      | inl h1 => 
        apply ih at h1
        exact Finset.mem_union_right {new (f_set n)} h1
        
      | inr h2 => 
        rw [h2]
        exact Finset.mem_union_left (f_set n) (Finset.mem_singleton_self (new (f_set n)))
  simp
  push_neg
  intro j 
  rw [j] at inclu
  apply h_new ( f_set l) at inclu
  exact inclu


lemma recouvrement_fini (hX: Compact X) (α : ℝ )(hα : α > 0) : ∃ n , ∃ x: Fin n → X, Set.univ ⊆ ( ⋃ xi ∈ List.ofFn x, B( xi , α ) ):= by
  contrapose hX 
  push_neg at hX
  have h : ∀n, ∀ xn : Fin n → X,  ∃ un ∈ Set.univ , un ∉ ⋃ xn_i ∈ List.ofFn xn, B(xn_i,α) := by
    intro n xn
    apply (Set.not_subset_iff_exists_mem_not_mem).mp (hX n xn)
  unfold Compact
  push_neg
  have H: ∀ A: Finset X, ∃ a ∈ Set.univ , a ∉ ⋃ xn_i ∈ A, B(xn_i,α) := by
    intro A
    let s:= Finset.toList A
    specialize h s.length
    let x : Fin s.length  → X := λ n ↦ s.get n 
    specialize h x
    obtain ⟨ a, ha, hna⟩ := h
    use a
    apply And.intro
    exact ha
    push_neg  
    have eg1: s=  List.ofFn x:= by 
      apply  List.ext_get
      rw [List.length_ofFn]
      intro n h1 h2
      simp [x]
    rw [<- eg1] at hna
    simp [s] at hna
    simp
    exact hna

  have h': ∃ u: ℕ → X, ∀k l, k<l → (u k ≠ u l) ∧ d ( u k) (u l) >= α := by
    classical
    choose new h_new using H 
    let f := λ (s : Finset X) ↦ insert (new s) s
    let f_set := λ n ↦ Nat.iterate f n ∅
    existsi new ∘ f_set
    intro k l h_kl
    have h_rec: ∀ n: ℕ , f_set (n + 1) = f (f_set n) := by
      simp only [f_set]
      intro n
      apply  Function.iterate_succ_apply' f 
    have h_in: new (f_set k)  ∈ f_set l:= by 
      induction l with
      | zero =>  cases h_kl  
      | succ n ih => 
        rw [h_rec]
        simp only [f]
        have h := lt_or_eq_of_le ((Nat.lt_succ_iff ).mp h_kl)
        rw [Finset.insert_eq]
        cases h with
      | inl h1 => 
        apply ih at h1
        exact Finset.mem_union_right {new (f_set n)} h1 
      | inr h2 => 
        rw [h2]
        exact Finset.mem_union_left (f_set n) (Finset.mem_singleton_self (new (f_set n)))
    simp
    push_neg
    apply And.intro
    intro j 
    rw [j] at h_in
    have g: ((f_set l): Set X) ⊆ ⋃ xn_i ∈( f_set l), B(xn_i,α):= by
      rw [Set.subset_def ]
      intro t ht
      simp
      use t
      apply And.intro
      exact ht
      rw [dist_sep_eq_zero]
      exact hα 
    apply Set.not_mem_subset g ((h_new) ( f_set l)).2 at h_in
    exact h_in
    have not_in_ball: (new (f_set l)) ∉ B((new (f_set k)),α):= by 
      have h:=  (h_new (f_set l)).2
      simp
      simp at h 
      exact h (new (f_set k)) h_in
    simp at not_in_ball
    exact not_in_ball

  obtain ⟨ x, hx⟩ :=   h'
  use x
  intro f l hf h_lim 
  have h_cauchy := Converg_Cauchy ( x∘f) (h_lim )
  specialize h_cauchy α hα 
  obtain ⟨ N, hN⟩ := h_cauchy
  specialize hN N ( Nat.le_refl N) (N+1) ( Nat.le_succ N)
  simp at hN
  unfold strictement_croissante at hf
  have contradiction:= (hx (f N) (f ( N+1)) (hf (N+1) N (Nat.lt_succ_self N))  ).2 
  linarith
















