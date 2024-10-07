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

  structure NormalSubgroup (G : Group T) extends Subgroup G where
    norm : isNorm this

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

  /-- For a normal subgroup, a * b ∈ H ↔ b * a ∈ H -/
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

    def lce_eq_struct (H : Subgroup G) : Equivalence (left_coset_equivalence H) := {
      refl := lce_refl H,
      symm := lce_symm H,
      trans := lce_trans H
    }

    def lce_setoid (H : Subgroup G) : Setoid T := {
      r := left_coset_equivalence H,
      iseqv := lce_eq_struct H
    }

    def lce_quotient (H: Subgroup G) := Quotient (lce_setoid H)
    def lce_quotient_mk (H : Subgroup G) := Quotient.mk (lce_setoid H)
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

    def rce_eq_struct (H : Subgroup G) : Equivalence (right_coset_equivalence H) := {
      refl := rce_refl H,
      symm := rce_symm H,
      trans := rce_trans H
    }

    def rce_setoid (H : Subgroup G) : Setoid T := {
      r := right_coset_equivalence H,
      iseqv := rce_eq_struct H
    }

    def rce_quotient (H: Subgroup G) := Quotient (rce_setoid H)
    def rce_quotient_mk (H : Subgroup G) := Quotient.mk (rce_setoid H)
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
      rw [← inv_of_inv (g * h)]
      rw [eq]
      simp only [inv_of_inv, ← mul_assoc, inv_mul, one_mul]
      exact h_in_H

  theorem subgroup_normal_iff_setoids_same {G : Group T} {H : Subgroup G} :
    isNorm H ↔ lce_setoid H = rce_setoid H := by
    rw [lce_setoid, rce_setoid]
    constructor
    . intro norm
      have h2 := subgroup_normal_iff_cosets_eq.mp norm
      congr
    . intro setoids_eq
      injection setoids_eq with r_eq
      have h2 := subgroup_normal_iff_cosets_eq.mpr r_eq
      congr

  def rce_to_lce {G : Group T} {H : NormalSubgroup G}
    (q : rce_quotient H.toSubgroup) : lce_quotient H.toSubgroup :=
    have h : rce_quotient H.toSubgroup = lce_quotient H.toSubgroup := by
      rw [lce_quotient, rce_quotient]
      rw [subgroup_normal_iff_setoids_same.mp H.norm]
    cast h q

  def lce_to_rce {G : Group T} {H : NormalSubgroup G}
    (q : lce_quotient H.toSubgroup) : rce_quotient H.toSubgroup :=
    have h : lce_quotient H.toSubgroup = rce_quotient H.toSubgroup := by
      rw [lce_quotient, rce_quotient]
      rw [subgroup_normal_iff_setoids_same.mp H.norm]
    cast h q

  def coset_equivalence {G : Group T} (H : NormalSubgroup G) (a b : T) : Prop :=
    a * inv b ∈ H.carrier ∨ inv b * a ∈ H.carrier

  theorem in_both_cosets {G : Group T} (H : NormalSubgroup G) :
    ∀ (a b : T), coset_equivalence H a b ↔ a * inv b ∈ H.carrier ∧ inv b * a ∈ H.carrier := by
    intro a b
    have norm := H.norm (Group T) G


  section coset_equivalence
    variable {G : Group T}

    theorem ce_refl (H : NormalSubgroup G) :
      ∀ (x : T), coset_equivalence H x x := by
      intro x
      rw [coset_equivalence]
      rw [mul_inv]
      left
      exact H.one_mem

    theorem ce_symm (H : NormalSubgroup G) :
      ∀ {a b : T}, coset_equivalence H a b → coset_equivalence H b a := by
      intro a b
      intro a_eq_b
      repeat rw [coset_equivalence] at *
      have h := H.inv_mem (a * inv b) a_eq_b
      rw [inv_of_product] at h
      rw [inv_of_inv] at h
      left
      exact h
  end coset_equivalence

  section quotients
    variable {G : Group T}

    -- theorem mul_respects_equiv :

    instance lce_quotient_mul (H : NormalSubgroup G) : Mul (lce_quotient H.toSubgroup) := {
      mul := fun a b =>
        Quotient.liftOn₂ a b (fun x y => lce_quotient_mk H.toSubgroup (x * y))
        (fun a1 a2 b1 b2 h1 h2 => by
          have norm : isNorm H.toSubgroup := H.norm
          have h22 : inv b2 * a2 ∈ H.carrier := by
            exact h2
          have h3 : (inv b1 * a1) * (inv b2 * a2) ∈ H.carrier :=
            H.mul_mem (inv b1 * a1) (inv b2 * a2) h1 h2
          simp only [← mul_assoc] at h3
          dsimp
          have t : inv (b1 * b2) * (a1 * a2) ∈ H.carrier := by
            simp only [mul_assoc, inv_of_product]
            rw [comm_of_norm]
            rw [← mul_assoc]
            rw [mul_assoc_4]
            refine H.mul_mem (inv b1 * a1) (a2 * inv b2) h1 ?_
            rw [comm_of_norm] at h22
            exact h22
            exact norm
            exact norm
          rw [lce_quotient_mk]
          rw [Quotient.sound]
          exact t
        )
    }

    theorem lce_quotient_mul_id (H : NormalSubgroup G) (a b : T) :
      lce_quotient_mk H.toSubgroup (a * b) = (lce_quotient_mk H.toSubgroup a) * (lce_quotient_mk H.toSubgroup b) := by


    instance rce_quotient_mul (H : NormalSubgroup G) : Mul (rce_quotient H.toSubgroup) := {
      mul := fun a b => lce_to_rce ((rce_to_lce  a) * (rce_to_lce b))
    }

    instance lce_quotient_group (H : NormalSubgroup G) : Group (lce_quotient H.toSubgroup) := {
      mul_assoc := fun a b c => by
        have a_ex := a.exists_rep
        have a' := a_ex.choose_spec
        have b_ex := b.exists_rep
        have b' := b_ex.choose_spec
        have c_ex := c.exists_rep
        have c' := c_ex.choose_spec
        have bc := Quotient.mk (lce_setoid H.toSubgroup) (b_ex.choose * c_ex.choose)
    }
  end quotients
end Group
