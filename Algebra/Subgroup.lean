import Algebra.Group

variable {T : Type}

namespace Group
  structure Subgroup (G : Group T) where
    carrier : Set T
    one_mem : one ∈ carrier
    mul_mem : ∀ (g₁ g₂ : T), g₁ ∈ carrier → g₂ ∈ carrier → g₁ * g₂ ∈ carrier
    inv_mem : ∀ (g : T), g ∈ carrier → inv g ∈ carrier

  structure NormalSubgroup (G : Group T) extends Subgroup G where
    norm : ∀ (g : T) (h : T), h ∈ carrier → g * h * inv g ∈ carrier

  /-- For a normal subgroup, a * b ∈ H ↔ b * a ∈ H -/
  theorem norm_comm {G : Group T} (H : NormalSubgroup G) :
    ∀ (a b : T), (a * b ∈ H.carrier) = (b * a ∈ H.carrier) := by
    have norm := H.norm
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

  def left_coset_equivalence {G : Group T} (H : NormalSubgroup G) (a b : T) : Prop :=
    a * inv b ∈ H.carrier

  def right_coset_equivalence {G : Group T} (H : NormalSubgroup G) (a b : T) : Prop :=
    inv b * a ∈ H.carrier

  def coset_equivalence {G : Group T} (H : NormalSubgroup G) (a b : T) : Prop :=
    a * inv b ∈ H.carrier ∨ inv b * a ∈ H.carrier

  theorem coset_id {G : Group T} (H : NormalSubgroup G) :
    left_coset_equivalence H = right_coset_equivalence H := by
    funext a b
    rw [left_coset_equivalence]
    rw [right_coset_equivalence]
    apply propext
    constructor
    . intro h
      rw [norm_comm]
      exact h
    . intro h
      rw [norm_comm]
      exact h

  theorem coset_eq {G : Group T} (H : NormalSubgroup G) (a b : T) :
    coset_equivalence H a b = ((a * inv b ∈ H.carrier) ∧ (inv b * a ∈ H.carrier)) := by
    apply propext
    rw [coset_equivalence]
    constructor
    . intro ce
      rcases ce with l | r
      . constructor
        . exact l
        . rw [norm_comm]
          exact l
      . constructor
        . rw [norm_comm]
          exact r
        . exact r
    . intro both
      left
      exact both.left

  theorem coset_equivalence.to_eq {G : Group T} {H : NormalSubgroup G} {a b : T}
    (ce : coset_equivalence H a b) : (a * inv b ∈ H.carrier) := by
    rw [coset_eq] at ce
    exact ce.left

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
      intro a_eq_b'
      have a_eq_b := a_eq_b'.to_eq
      repeat rw [coset_equivalence] at *
      have h := H.inv_mem (a * inv b) a_eq_b
      rw [inv_of_product] at h
      rw [inv_of_inv] at h
      left
      exact h

    theorem ce_trans (H : NormalSubgroup G) :
      ∀ {a b c : T}, coset_equivalence H a b → coset_equivalence H b c → coset_equivalence H a c := by
      intro a b c
      intro a_eq_b'
      have a_eq_b := a_eq_b'.to_eq
      intro b_eq_c'
      have b_eq_c := b_eq_c'.to_eq
      rw [coset_equivalence] at *
      left
      have h : a * inv b * (b * inv c) ∈ H.carrier :=
        H.mul_mem (a * inv b) (b * inv c) a_eq_b b_eq_c
      rw [← mul_assoc] at h
      rw [mul_assoc a (inv b) b] at h
      rw [inv_mul, mul_one] at h
      exact h

    abbrev FactorSetoid (H : NormalSubgroup G) : Setoid T := {
      r := coset_equivalence H,
      iseqv := {
        refl := ce_refl H,
        symm := ce_symm H,
        trans := ce_trans H
      }
    }

    abbrev FactorGroup (H : NormalSubgroup G) :=
      Quotient (FactorSetoid H)

    def FactorGroup.mk (H : NormalSubgroup G) := Quotient.mk (FactorSetoid H)

    theorem factor_mul_eq (H : NormalSubgroup G) (a1 a2 b1 b2 : T) :
      (coset_equivalence H a1 b1) → (coset_equivalence H a2 b2) → (coset_equivalence H (a1 * a2) (b1 * b2)) := by
      intro a1_eq_b1'
      have a1_eq_b1 := a1_eq_b1'.to_eq
      rw [norm_comm] at a1_eq_b1
      intro a2_eq_b2'
      have a2_eq_b2 := a2_eq_b2'.to_eq
      rw [coset_equivalence] at *
      left
      rw [inv_of_product, ← mul_assoc]
      rw [norm_comm]
      simp only [← mul_assoc]
      rw [mul_assoc]
      exact H.mul_mem (inv b1 * a1) (a2 * inv b2) a1_eq_b1 a2_eq_b2

    theorem factor_inv_eq (H : NormalSubgroup G) (a b : T) :
      (coset_equivalence H a b) = (coset_equivalence H (inv a) (inv b)) := by
      have t : ∀ (a b : T), (coset_equivalence H a b) → (coset_equivalence H (inv a) (inv b)) := by
        intro a b
        intro h
        have h' := h.to_eq
        right
        simp only [inv_of_inv]
        rw [← inv_of_inv a] at h'
        rw [← inv_of_product] at h'
        have h'' := H.inv_mem (inv (b * inv a)) h'
        simp only [inv_of_inv] at h''
        exact h''
      apply propext
      constructor
      . intro h
        exact t a b h
      . intro h
        have h' := t (inv a) (inv b) h
        simp only [inv_of_inv] at h'
        exact h'

    instance factor_group_mul {H : NormalSubgroup G} : Mul (FactorGroup H) := {
      mul := fun a b =>
        Quotient.liftOn₂ a b (fun x y => FactorGroup.mk H (x * y))
        (fun a1 a2 b1 b2 h1 h2 => by
          dsimp
          rw [FactorGroup.mk]
          refine Quotient.sound ?_
          exact factor_mul_eq H a1 a2 b1 b2 h1 h2
        )
    }

    theorem factor_group_one_mul {H : NormalSubgroup G} :
      ∀ (g : FactorGroup H), FactorGroup.mk H one * g = g := by
      intro g
      have g' := g.exists_rep
      rcases g' with ⟨w, h⟩
      rw [← h]
      nth_rewrite 2 [← one_mul w]
      rfl

    theorem factor_group_mul_one {H : NormalSubgroup G} :
      ∀ (g : FactorGroup H), g * FactorGroup.mk H one = g := by
      intro g
      have g' := g.exists_rep
      rcases g' with ⟨w, h⟩
      rw [← h]
      nth_rewrite 2 [← mul_one w]
      rfl

    def factor_group_inv {H : NormalSubgroup G} (g : FactorGroup H) :=
      Quotient.lift (s := FactorSetoid H) (fun x => FactorGroup.mk H (inv x)) (fun a b => by
        intro a_eq_b'
        dsimp
        have a_eq_b : coset_equivalence H a b := by
          exact a_eq_b'
        have t := (Eq.to_iff (factor_inv_eq H a b)).mp a_eq_b
        rw [FactorGroup.mk]
        exact Quotient.sound t
      ) g

    instance factor_group_group {H : NormalSubgroup G} : Group (FactorGroup H) := {
      mul_assoc := fun a b c => by
        have a_w := a.exists_rep
        rcases a_w with ⟨a', a'h⟩
        have b_w := b.exists_rep
        rcases b_w with ⟨b', b'h⟩
        have c_w := c.exists_rep
        rcases c_w with ⟨c', c'h⟩
        rw [← a'h, ← b'h, ← c'h]
        have a_b_c_l : Quotient.mk (FactorSetoid H) a' * Quotient.mk (FactorSetoid H) b' * Quotient.mk (FactorSetoid H) c' = Quotient.mk (FactorSetoid H) (a' * b' * c') := rfl
        rw [a_b_c_l]
        have a_b_c_r : Quotient.mk (FactorSetoid H) a' * (Quotient.mk (FactorSetoid H) b' * Quotient.mk (FactorSetoid H) c') = Quotient.mk (FactorSetoid H) (a' * (b' * c')) := rfl
        rw [a_b_c_r]
        rw [mul_assoc]
      one := FactorGroup.mk H one
      one_mul := factor_group_one_mul
      mul_one := factor_group_mul_one
      inv := factor_group_inv
      inv_mul := fun g => by
        have g' := g.exists_rep
        rcases g' with ⟨w, h⟩
        rw [← h]
        have h' : factor_group_inv (Quotient.mk (FactorSetoid H) w) = Quotient.mk (FactorSetoid H) (inv w) := by
          exact rfl
        rw [h']
        rw [← inv_mul w]
        rfl
    }

    theorem mul_instances_eq {H : NormalSubgroup G} : factor_group_mul (H := H) = factor_group_group.toMul := by
      exact rfl

    theorem mul_operations_eq {H : NormalSubgroup G} {a b : FactorGroup H} : (factor_group_mul (H := H)).mul a b = factor_group_group.toMul.mul a b := by
      exact rfl

  end coset_equivalence

  def factor_group_natural_hom {G : Group T} (H : NormalSubgroup G) [F : Group (FactorGroup H)] : Hom G F := {
    f := FactorGroup.mk H
    hom := fun (g1 g2 : T) => by
      have h : FactorGroup.mk H (g1 * g2) = (FactorGroup.mk H g1) * (FactorGroup.mk H g2) := by
        rfl
      repeat rw [HMul.hMul] at h
      repeat rw [instHMul] at h
      dsimp at h
      rw [mul_operations_eq (Mul.mul g₁ g₂)] at h
      repeat rw [HMul.hMul]
      rw [instHMul]
      dsimp
      rw []
  }
end Group
