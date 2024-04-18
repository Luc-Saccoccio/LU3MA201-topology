import Topology.Basic

universe u v w

open MetricSpace

variable {X Y : Type u} [MetricSpace X] [MetricSpace Y]

def Closed {Y : Set X } := ∀ x : ℕ → X, ∀ l, (∀ n, x n ∈ Y ∧ lim x l) -> l ∈  Y

def CauchySeq (u : ℕ → X) := ∀ ε > 0, ∃ N : ℕ , ∀ m ≥ N,∀ n ≥ N,  d (u m) (u n) < ε

def Bornee ( u :ℕ -> X) := ∃ M:ℝ ,∀ n : ℕ, u n ∈ B( u 0, M )

def Converg (x : ℕ → X) := ∃! l : X , lim x l

def Complet (Y : Type v) [MetricSpace Y] := ∀ u : ℕ → Y, CauchySeq u → Converg u

theorem Converg_Cauchy (u : ℕ → X) : Converg u → CauchySeq u :=
  by
    intro ⟨l, hl⟩
    intro ε ε_pos
    have Hε : 0 < ε / 2 := by linarith
    obtain ⟨N, hN⟩ := hl.1 ε/2
    use N
    intro m hm
    intro n hn
    have hd : d (u n) (u m) ≤ d (u n) l + d l (u m) := dist_triangle
    have h₁ : d (u n) l < ε/2 := @dist_symm X _ _ _ ▸ hN n hn
    have h₂ : d (u m) l < ε/2 := @dist_symm X _ _ _ ▸ hN m hm
    have hε := add_lt_add h₁ h₂
    have h : d (u n) (u m) < ε/2 + ε/2 := lt_trans hd hε
    have E : ε/2 + ε/2 = ε := by linarith
    have H : d (u n) (u m) < ε
    sorry



def strictement_croissante (f : ℕ → ℕ ) : Prop := ∀ n m : ℕ, n > m -> f n > f m

lemma stricte_croissance_geq (f : ℕ → ℕ) : strictement_croissante f → ∀ n : ℕ, f n >= n :=
  by
  intro h n
  induction' n with n hi
  . exact Nat.zero_le (f 0)
  . exact Nat.succ_le_of_lt ∘ Nat.lt_of_le_of_lt hi $ h (n + 1) n (Nat.lt_succ_self n)


lemma Cauchy_val_adherence_conv (u : ℕ → X) (l : X) (f : ℕ → ℕ) (h1 : strictement_croissante f) (h2 : lim (u∘f) l) (h3 :  CauchySeq u): lim u l := by
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

lemma Cauchy_borne ( u : ℕ → X ) : (h : CauchySeq u ) → Bornee u := by

    unfold CauchySeq
    unfold Bornee
    intro h
    specialize h ( 1: ℝ )
    have h1 : (1:ℝ) >0 := by
      simp
    specialize h h1
    obtain ⟨N, hN⟩ := h
    have D := { d (u N) (u n) | n : Fin (N-1)}
    -- il reste a montrer que D est finit pour lui appliquer le max
    --have M := D.max

    sorry


def contractant ( f : X -> Y ):= ∃ k <1,∀ x y : X, d_[Y] (f x) (f y) ≤ k * d_[X] x y

lemma Contractant_lipschitz( f : X ->Y) : contractant f -> Lipschitz f :=
  by
  unfold Lipschitz
  unfold contractant
  intro h
  obtain ⟨k,hk⟩ := h
  sorry

theorem Point_Fixe_Contractant (f : X -> X ) : (Complet X ∧ contractant f ∧ ∀ u :ℕ -> X,  ∀ n , f (u n) = u (Nat.succ n )) -> (∃!x:X,f x =x ∧ lim u x) :=
  by
    unfold contractant
    have C := d ( u 0 ) ( u 1)
    intro H
    obtain ⟨k, hk⟩ := H.2
    have h : ∀ n : ℕ , d (u (Nat.succ n)) (u n) < k^n*C := sorry
    -- cf exercice 50 du poly de topo
    have l : ∀ ε>0 ,∃ N , ∀ n > N ,d (u (Nat.succ n)) (u n) < ε := sorry
    -- preuve que k^n*C tend vers zero puis thm des gendarmes
    have hp : ∀ n p : ℕ , d (u n) (u (n + p)) < ((k^n)/(1-k))*C := sorry
    -- IT generalisée et recurrence sur p
    have lp : ∀ ε>0 ,∃ N ,∀ p  ≥ N,∀ n ≥ N, d (u p) (u n) < ε := sorry
    -- encore une preuve de convergence vers 0
    have Cauchy : CauchySeq u := by exact lp
    have Conv : Converge u := by exact H.1 u Cauchy
