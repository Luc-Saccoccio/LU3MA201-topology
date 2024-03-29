import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Linarith.Frontend

universe u v w

-- I.1 Théorie
--- (a) Ouverts, intérieur

class MetricSpace (α : Type u) where
  dist : α → α → ℝ
  dist_pos : ∀ {x y : α}, 0 ≤ dist x y
  dist_sep : ∀ {x y : α}, dist x y = 0 ↔ x = y
  dist_symm : ∀ {x y : α}, dist x y = dist y x
  dist_triangle : ∀ {x y z : α}, dist x z ≤ dist x y + dist y z

open MetricSpace

def dist' (α : Type u) [MetricSpace α] : α → α → ℝ :=
  fun x y => dist x y

notation "d" => dist
notation "d_[" α "]" => dist' α


section Fundamentals

variable {X : Type u} [MetricSpace X]

lemma dist_str_pos {x y : X} : x ≠ y → d_[X] x y > 0 :=
  by
    contrapose!
    intro d_neg
    exact Iff.mp dist_sep (antisymm d_neg dist_pos)

def open_ball (x : X) (r : ℝ) : Set X := {y | d x y < r}

notation "B(" x "," r ")" => open_ball x r

/- LEMMES DE SIMPLIFICATION -/

@[simp]
lemma dist_sep_eq_zero (x : X) : d x x = 0 := dist_sep.mpr rfl

@[simp]
lemma mem_open_ball (x : X) (r : ℝ) (y : X) : y ∈ B(x, r) ↔ dist x y < r := Iff.rfl

@[simp]
lemma center_in_ball (x : X) (r : ℝ) : r > 0 → x ∈ B(x, r) := by
  intro r_pos
  simpa [open_ball]

def is_open (U : Set X) : Prop := ∀ x ∈ U, ∃ r > 0, B(x, r) ⊆ U

-- Exercice 1
lemma open_ball_is_open : ∀ x : X, ∀ r > 0, is_open B(x, r) :=
  by
    intros x r _ y y_in
    set ε := r - d x y with hε
    use ε
    apply And.intro
    . simp [open_ball] at y_in
      linarith only [hε, y_in]
    . intros z z_in
      rw [mem_open_ball] at *
      have p : d x z ≤ d x y + d y z := dist_triangle
      linarith only [p, z_in, y_in, hε]

/- Les trois lemmes qui suivent montre qu'un espace métrique est bien topologique pour
   la topologie induite par la distanace
-/
lemma union_open_is_open (I : Set (Set X)) : (∀ U ∈ I, is_open U) → is_open (⋃₀ I) :=
  by
    intro U_opens x ⟨U, U_app_I, x_app_U⟩
    obtain ⟨r, r_pos, ball_in_U⟩ : ∃ r > 0, B(x, r) ⊆ U :=
      (U_opens U) U_app_I x x_app_U
    use r, r_pos
    . exact Set.Subset.trans ball_in_U (Set.subset_sUnion_of_mem U_app_I)

/- lemma union_open_is_open' : ∀ U V : Set X, is_open U → is_open V → is_open (U ∪ V) :=
  by
    intro U V U_open V_open
    have h := union_open_is_open {U, V} (by simp; exact ⟨U_open, V_open⟩)
    rw [Set.sUnion_pair] at h
    exact h -/

lemma inter_open_is_open : ∀ U V : Set X, is_open U → is_open V → is_open (U ∩ V) :=
  by
    intro U V U_open V_open x ⟨x_in_U, x_in_V⟩
    obtain ⟨rᵤ, rᵤ_pos, ball_in_U⟩ : ∃ rᵤ > 0, B(x, rᵤ) ⊆ U := U_open x x_in_U
    obtain ⟨rᵥ, rᵥ_pos, ball_in_V⟩ : ∃ rᵥ > 0, B(x, rᵥ) ⊆ V := V_open x x_in_V
    use min rᵤ rᵥ, lt_min rᵤ_pos rᵥ_pos
    . intro y y_in_ball
      simp at y_in_ball
      apply And.intro
      . exact ball_in_U y_in_ball.left
      . exact ball_in_V y_in_ball.right

lemma space_open : is_open (Set.univ : Set X) :=
  fun x _ => ⟨1, (And.intro zero_lt_one (Set.subset_univ B(x, 1)))⟩

def Interior (E : Set X) := ⋃₀ {U : Set X | is_open U ∧ U ⊆ E}

lemma interior_is_open {E : Set X} : is_open (Interior E) := union_open_is_open {U : Set X | is_open U ∧ U ⊆ E} (by simp_all)

@[simp]
lemma metric_interior {E : Set X} {x : X} : x ∈ Interior E ↔ ∃ r > 0, B(x, r) ⊆ E :=
  by
    apply Iff.intro
    . intro x_in_E
      rcases x_in_E with ⟨U, ⟨U_open, U_sub_E⟩, x_in_U⟩
      obtain ⟨r, r_pos, ball_in_U⟩ : ∃ r > 0, B(x, r) ⊆ U := U_open x x_in_U
      use r, r_pos
      trans U <;> assumption
    . rintro ⟨r, r_pos, ball_in_E⟩
      have ball_open : is_open B(x, r) := open_ball_is_open x r r_pos
      use B(x, r)
      simp_all

end Fundamentals

--- (b) Applications continues

section Continuity

variable {X Y : Type u} [MetricSpace X] [MetricSpace Y]

def continuous_on (f : X → Y) (x₀ : X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, d_[X] x₀ x < δ → d_[Y] (f x₀) (f x) < ε

def Continuous (f : X → Y) : Prop := ∀ x : X, continuous_on f x

theorem topologic_continuity (f : X → Y) : Continuous f ↔ (∀ U, is_open U → is_open (f ⁻¹' U)) :=
  by
    apply Iff.intro
    . intro h U U_open x₀ x₀_in_reci_f
      obtain ⟨ε, ε_pos, ball_in_U⟩ : ∃ ε > 0, B(f x₀, ε) ⊆ U := U_open (f x₀) x₀_in_reci_f
      rcases (h x₀) ε ε_pos with ⟨δ, δ_pos, H⟩
      use δ, δ_pos
      intro x hx
      suffices hh : f x ∈ B(f x₀, ε) from ball_in_U hh
      exact H x hx
    . intro H₁ x₀ ε ε_pos
      let U : Set Y := B(f x₀, ε)
      have U_open := open_ball_is_open (f x₀) ε ε_pos
      have recU_open := H₁ U U_open
      have x_in_recU: x₀ ∈ f⁻¹' U := by simpa
      obtain ⟨δ, δ_pos, H₂⟩ : ∃ δ > 0, B(x₀, δ) ⊆ f⁻¹' U := recU_open x₀ x_in_recU
      use δ, δ_pos
      intro x hx
      exact H₂ hx

variable {Z : Type u} [MetricSpace Z]

theorem comp_continuous (f : X → Y) (g : Y → Z) : Continuous f → Continuous g → Continuous (g ∘ f) :=
  by
    intro f_cont g_cont
    rw [topologic_continuity]
    intro V V_open
    let U := g⁻¹' V
    have U_open : is_open U := Iff.mp (topologic_continuity g) g_cont V V_open
    exact Iff.mp (topologic_continuity f) f_cont U U_open

def Lipschitz (f : X → Y) : Prop :=
  ∃ k > 0, ∀ x x' : X, d_[Y] (f x) (f x') ≤ k * d_[X] x x'

theorem lipschitz_implies_continuous (f : X → Y) : Lipschitz f → Continuous f :=
  by
    intro ⟨k, k_pos, h⟩
    intro x₀  ε ε_pos
    use ε / k, div_pos ε_pos k_pos
    intro x hdx
    have h₁ : d_[Y] (f x₀) (f x) < k * (ε / k) := lt_of_le_of_lt (h x₀ x) (mul_lt_mul_of_pos_left hdx k_pos)
    rw [mul_div_cancel' ε] at h₁
    . exact h₁
    . linarith -- meh

end Continuity

--- (c) Applications continues

section closed

variable {X : Type u} [MetricSpace X]

def is_closed (F : Set X) := is_open Fᶜ

lemma union_closed_is_closed : ∀ F G : Set X, is_closed F → is_closed G → is_closed (F ∪ G) :=
  by
    intro F G F_closed G_closed
    rw [is_closed, Set.compl_union F G]
    exact inter_open_is_open Fᶜ Gᶜ F_closed G_closed

-- TODO: clean proof
lemma inter_closed_is_closed (I : Set (Set X)) : (∀ F ∈ I, is_closed F) → is_closed (⋂₀ I) :=
  by
    intro h
    rw [is_closed, Set.compl_sInter I]
    have h₁ : ∀ U ∈ compl '' I, is_open U :=
      by
        intro U hU
        dsimp [Set.image] at hU
        obtain ⟨F, hF⟩ := hU
        rw [←hF.right]
        exact h F hF.left
    exact union_open_is_open (compl '' I) h₁

def Closure (E : Set X) : Set X := ⋂₀ {F : Set X | is_closed F ∧ E ⊆ F}

-- Ensemble de petits résultats sur l'adhérence
@[simp]
lemma closure_is_closed {E : Set X} : is_closed (Closure E) := inter_closed_is_closed {F : Set X | is_closed F ∧ E ⊆ F} fun _ => And.left

lemma sub_closure {E : Set X} : E ⊆ Closure E := Set.subset_sInter fun _ => And.right

lemma closure_sub_closed {E F : Set X} : is_closed F → E ⊆ F → Closure E ⊆ F :=
  fun hClosed hSub => Set.sInter_subset_of_mem ⟨hClosed, hSub⟩

lemma closure_monotone {A B : Set X} (h : A ⊆ B) : Closure A ⊆ Closure B := closure_sub_closed closure_is_closed (Set.Subset.trans h sub_closure)

lemma closure_closed_is_closed {E : Set X} (h : is_closed E) : Closure E = E :=
  Set.Subset.antisymm (closure_sub_closed h (Set.Subset.refl E)) sub_closure

lemma closure_closure_eq_closure {E : Set X} : Closure (Closure E) = Closure E := closure_closed_is_closed closure_is_closed


/-
  PREUVE ILLISIBLE
-/
@[simp]
lemma metric_closure {E : Set X} {x : X} : x ∈ Closure E ↔ ∀ r > 0, B(x, r) ∩ E ≠ ∅ :=
  by
    apply Iff.intro
    . contrapose!
      intro hr hx
      obtain ⟨r, r_pos, hB⟩ := hr
      have h₁ : is_closed B(x, r)ᶜ :=
        by
          rw [is_closed, compl_compl]
          exact open_ball_is_open x r r_pos
      have h₂ : E ⊆ B(x, r)ᶜ :=
        fun y hy h => (Set.mem_empty_iff_false y).mp (hB ▸ ⟨h , hy⟩)
      have h₃ : x ∈ B(x, r)ᶜ := Set.mem_sInter.mp hx B(x, r)ᶜ ⟨h₁, h₂⟩
      exact (Set.mem_compl_iff B(x, r) x).mp h₃ (center_in_ball x r r_pos)
    . intro h F ⟨F_closed, E_sub_F⟩
      by_contra hx
      rw [is_closed] at F_closed
      apply Set.mem_compl at hx
      obtain ⟨ε, ε_pos, h_complF⟩ := F_closed x hx
      have h₁ : B(x, ε) ∩ F ≠ ∅ :=
        by
          obtain ⟨z, ⟨hz₁, hz₂⟩⟩ := Set.nonempty_iff_ne_empty.mpr (h ε ε_pos)
          exact Set.nonempty_iff_ne_empty.mp ⟨z, ⟨hz₁, Set.mem_of_mem_of_subset hz₂ E_sub_F⟩⟩
      have h₂ : B(x, ε) ∩ F = ∅ :=
        by
          apply Set.eq_empty_of_forall_not_mem
          intro z hz
          have h₃ : z ∈ F := by simp_all
          have h₃' : z ∈ Fᶜ := Set.mem_of_mem_of_subset (Set.mem_of_mem_inter_left hz) h_complF
          exact Set.not_mem_compl_iff.mpr h₃ h₃'
      exact h₁ h₂



def Dense (E : Set X) : Prop := Closure E = X

def frontier (E : Set X) : Set X := Closure E ∩ Closure (Eᶜ)

prefix:100 "∂" => frontier

-- TODO: Propriétés usuelles de la frontière

end closed

-- (d) Suites

section sequences

variable {X : Type u} [MetricSpace X]

-- On définit une suite comme une fonction u : ℕ → X

def lim {K:Set X} (x : ℕ → K) (l : X) := ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, d l (x n) < ε

lemma sequential_closure (E : Set X) (l : X) : l ∈ Closure E ↔ ∃ x : ℕ → E , lim x l :=
  by
    apply Iff.intro
    . sorry
    . sorry

end sequences
