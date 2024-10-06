import Algebra.Group

variable {T : Type}

namespace Group
  structure Subgroup (G : Group T) where
    carrier : Set T
    one_mem : one ∈ carrier
    mul_mem : ∀ (g₁ g₂ : T), g₁ ∈ carrier → g₂ ∈ carrier → g₁ * g₂ ∈ carrier
    inv_mem : ∀ (g : T), g ∈ carrier → inv g ∈ carrier

  def isNorm {G : Group T} (H : Subgroup G) : Prop :=
    ∀ (g : T) (h : T), h ∈ H.carrier → g * h * inv g ∈ H.carrier

  theorem conjugation_is_norm {G : Group T} {H : Subgroup G} (norm : isNorm H) :
    ∀ (g x : T), g * x * inv g ∈ H.carrier → x ∈ H.carrier := by
    intro g x
    intro conjugation_h
    rw [isNorm] at norm
    have h : inv g * (g * x * inv g) * g ∈ H.carrier := by
      have h2 := norm (inv g) (g * x * inv g) conjugation_h
      rw [inv_of_inv] at h2
      exact h2
    simp only [← mul_assoc, inv_mul, one_mul] at h
    rw [mul_assoc] at h
    simp only [inv_mul, mul_one] at h
    exact h

  theorem comm_of_norm {G : Group T} {H : Subgroup G} (norm : isNorm H) :
    ∀ (a b : T), (a * b ∈ H.carrier) = (b * a ∈ H.carrier) := by
    have t : ∀ (a b : T), a * b ∈ H.carrier → b * a ∈ H.carrier := by
      intro a b
      intro a_b_in_h
      have h : b * (a * b) * inv b ∈ H.carrier := by
        exact norm b (a * b) a_b_in_h
      simp only [mul_assoc, mul_inv, mul_one] at h
      exact h
    intro a b
    apply propext
    constructor
    . exact fun a_1 ↦ t a b (t b a (t a b a_1))
    . exact fun a_1 ↦ t b a (t a b (t b a a_1))

  /-- Equivalence class b ∈ aH -/
  def left_coset_equivalence {G : Group T} (H : Subgroup G) (b a : T) : Prop :=
    inv a * b ∈ H.carrier

  section left_coset_equivalence_proof
    variable {G : Group T}

    theorem lce_refl (H : Subgroup G) :
      ∀ (x : T), left_coset_equivalence H x x := by
      intro x
      rw [left_coset_equivalence]
      rw [inv_mul]
      exact H.one_mem

    theorem lce_symm (H : Subgroup G) :
      ∀ {a b : T}, left_coset_equivalence H a b → left_coset_equivalence H b a := by
      intro a b
      intro a_eq_b
      repeat rw [left_coset_equivalence] at *
      have h := H.inv_mem (inv b * a) a_eq_b
      rw [inv_of_product] at h
      rw [inv_of_inv] at h
      exact h

    theorem lce_trans (H : Subgroup G) :
      ∀ {a b c : T}, left_coset_equivalence H a b → left_coset_equivalence H b c → left_coset_equivalence H a c := by
      intro a b c
      intro a_eq_b
      intro b_eq_c
      repeat rw [left_coset_equivalence] at *
      have h : (inv c * b) * (inv b * a) ∈ H.carrier := by
        exact H.mul_mem (inv c * b) (inv b * a) b_eq_c a_eq_b
      rw [← mul_assoc] at h
      rw [mul_assoc (inv c) b (inv b)] at h
      rw [mul_inv] at h
      rw [mul_one] at h
      exact h

    def lce_struct (H : Subgroup G) : Equivalence (left_coset_equivalence H) := {
      refl := lce_refl H,
      symm := lce_symm H,
      trans := lce_trans H
    }
  end left_coset_equivalence_proof

  /-- Equivalence class b ∈ Ha -/
  def right_coset_equivalence {G : Group T} (H : Subgroup G) (b a : T) : Prop :=
    b * inv a ∈ H.carrier

  section right_coset_equivalence_proof
    variable {G : Group T}

    theorem rce_refl (H : Subgroup G) :
      ∀ (x : T), right_coset_equivalence H x x := by
      intro x
      rw [right_coset_equivalence]
      rw [mul_inv]
      exact H.one_mem

    theorem rce_symm (H : Subgroup G) :
      ∀ {a b : T}, right_coset_equivalence H a b → right_coset_equivalence H b a := by
      intro a b
      intro a_eq_b
      repeat rw [right_coset_equivalence] at *
      have h := H.inv_mem (a * inv b) a_eq_b
      rw [inv_of_product] at h
      rw [inv_of_inv] at h
      exact h

    theorem rce_trans (H : Subgroup G) :
      ∀ {a b c : T}, right_coset_equivalence H a b → right_coset_equivalence H b c → right_coset_equivalence H a c := by
      intro a b c
      intro a_eq_b
      intro b_eq_c
      repeat rw [right_coset_equivalence] at *
      have h : (a * inv b) * (b * inv c) ∈ H.carrier := by
        exact H.mul_mem (a * inv b) (b * inv c) a_eq_b b_eq_c
      rw [← mul_assoc] at h
      rw [mul_assoc a (inv b) b] at h
      rw [inv_mul] at h
      rw [mul_one] at h
      exact h

    def rce_struct (H : Subgroup G) : Equivalence (right_coset_equivalence H) := {
      refl := rce_refl H,
      symm := rce_symm H,
      trans := rce_trans H
    }
  end right_coset_equivalence_proof

  /-- Subgroup is normal iff left cosets the same as right cosets -/
  theorem subgroup_normal_iff_cosets_eq {G : Group T} {H : Subgroup G} :
    isNorm H ↔ left_coset_equivalence H = right_coset_equivalence H := by
    constructor
    . intro h
      funext a b
      rw [left_coset_equivalence]
      rw [right_coset_equivalence]
      rw [comm_of_norm]
      exact h
    . intro eq
      rw [isNorm]
      intro g h
      intro h_in_H
      have eq : ∀ (a b : T), left_coset_equivalence H a b = right_coset_equivalence H a b := by
        exact fun a b ↦ congrFun (congrFun eq a) b
      simp only [left_coset_equivalence, right_coset_equivalence] at eq
      have h2 : inv g * (g * h) ∈ H.carrier := by
        simp only [← mul_assoc, inv_mul, one_mul]
        exact h_in_H
      rw [← inv_of_inv (g * h)]
      rw [eq]
      simp only [inv_of_inv, ← mul_assoc, inv_mul, one_mul]
      exact h_in_H
end Group
