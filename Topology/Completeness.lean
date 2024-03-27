import Topology.Basic

universe u v w

open MetricSpace

variable {X : Type u} [MetricSpace X]

def Closed {Y : Set X } := ∀ x : ℕ → X, ∀ l, (∀ n, x n ∈ Y ∧ lim x l) -> l ∈  Y

def CauchySeq (u : ℕ → X) := ∀ ε > 0, ∃ N : ℕ , ∀ m ≥ N,∀ n ≥ N,  d (u m) (u n) < ε

def Converg (x : ℕ → X) := ∃ l : X , lim x l

def Complet (Y : Type v) [MetricSpace Y] := ∀ u : ℕ → Y, CauchySeq u → ∃ l : Y, lim u l

theorem Converg_Cauchy (u : ℕ → X) : Converg u → CauchySeq u :=
  by
    intro ⟨l, hl⟩
    intro ε ε_pos
    have Hε : 0 < ε / 2 := by linarith
    obtain ⟨N, hN⟩ := hl (ε/2) Hε
    use N
    intro m hm
    intro n hn
    have hd : d (u n) (u m) ≤ d (u n) l + d l (u m) := dist_triangle
    have h₁ : d (u n) l < ε/2 := @dist_symm X _ _ _ ▸ hN n hn
    have h₂ : d (u m) l < ε/2 := @dist_symm X _ _ _ ▸ hN m hm
    have hε := add_lt_add h₁ h₂


lemma Cauchy_borne ( u : ℕ → X ) : (∀ ε > 0, ∃ N : ℕ , ∀ m ≥ N,∀ n ≥ N,  d (u m) (u n) < ε) → ∃ M:ℝ ,∀ n : ℕ, u n ∈ B( u 0, M ):=
  by
  intro ε = 1


theorem ℝ_complet : Complet ℝ := by
  . sorry

theorem sub_Ferme_complet : {Y : Set X}
