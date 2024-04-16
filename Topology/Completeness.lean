import Topology.Basic

universe u v w

open MetricSpace

variable {X : Type u} [MetricSpace X]

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
    obtain ⟨N, hN⟩ := (hl.1 ε/2)
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
    --  have f := D ∈ Finset ℝ
    have M := D.max
    intro n


def contractant ( f : X -> X ):= ∃ k < 1 ,∀ x y : X, d ( f x ) (f y ) < k * ( d ( f x) (f y) )

lemma Contractant_Continue ( f : X -> X ) : contractant f -> Lipschitz f := sorry

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
