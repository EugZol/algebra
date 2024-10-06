import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Contrapose
import Mathlib.Data.Set.Defs

class Group (T : Type) extends Mul T where
  mul_assoc: ∀ a b c : T, (a * b) * c = a * (b * c)
  one : T
  one_mul : ∀ g : T, one * g = g
  mul_one : ∀ g : T, g * one = g
  inv : T → T
  inv_mul : ∀ g : T, inv g * g = one

instance {T : Type} [G : Group T] : OfNat T 1 where
  ofNat := G.one

namespace Group
  section TrivialFacts
    variable {T : Type}
    variable [G : Group T]
    variable (g : T)

    @[simp low] theorem mul_assoc_simp (g k l : T) : g * (k * l) = g * k * l := (mul_assoc g k l).symm
    @[simp high] theorem one_eq_one_simp : (1 : T) = one := rfl
    @[simp high] theorem one_mul_simp : one * g = g := one_mul g
    @[simp high] theorem mul_one_simp : g * one = g := mul_one g
    @[simp high] theorem inv_mul_simp : inv g * g = one := inv_mul g

    /-- Inverse of one is one -/
    @[simp high] theorem inv_one_eq_one : inv G.one = G.one := by
      rw [← mul_one (inv one)]
      exact inv_mul one

    /-- Inverse of the inverse of g is g -/
    @[simp high] theorem inv_of_inv : inv (inv g) = g := by
      have h : inv (inv g) * inv g = one := by
        apply inv_mul
      have h1 : inv (inv g) * inv g * g = one * g := by
        exact congrFun (congrArg HMul.hMul h) g
      rw [mul_assoc] at h1
      rw [inv_mul] at h1
      rw [mul_one] at h1
      rw [h1]
      exact one_mul g

    /-- Product of inverses is one -/
    @[simp high] theorem mul_inv : g * inv g = one := by
      nth_rewrite 1 [← inv_of_inv g]
      apply inv_mul (inv g)

    /-- Inverse operation and cancellation on both sides of equality -/
    theorem inv_congr (g k : T) : g = k ↔ inv g = inv k := by
      constructor
      . exact fun a ↦ congrArg inv a
      . intro h1
        have h2 : inv (inv g) = inv (inv k) := by
          exact congrArg inv h1
        rw [inv_of_inv] at h2
        rw [inv_of_inv] at h2
        exact h2

    /-- Inverse is symmetric -/
    theorem inv_symm (g k : T) : inv g = k → inv k = g := by
      intro h
      rw [inv_congr]
      simp
      exact h.symm

    /-- Cancel right operand of multiplication equality -/
    @[simp low] theorem mul_right_cancel (a b c : T) : a * c = b * c ↔ a = b := by
      apply Iff.intro
      intro there
      have h1 : a * c * inv c = b * c * inv c := by
        exact congrFun (congrArg HMul.hMul there) (inv c)
      rw [mul_assoc] at h1
      rw [mul_assoc] at h1
      simp at h1
      exact h1
      intro back
      exact congrFun (congrArg HMul.hMul back) c

    /-- Cancel left operand of multiplication equality -/
    @[simp low] theorem mul_left_cancel (a b c : T) : c * a = c * b ↔ a = b := by
      apply Iff.intro
      intro there
      have h1 : inv c * (c * a) = inv c * (c * b) := by
        exact congrArg (HMul.hMul (inv c)) there
      rw [← mul_assoc] at h1
      rw [← mul_assoc] at h1
      simp at h1
      exact h1
      intro back
      exact congrArg (HMul.hMul c) back

    /-- Any left one is the one -/
    @[simp high] theorem single_one_left (alt_one : T) : alt_one * g = g → alt_one = one := by
      intro h
      nth_rewrite 2 [← one_mul g] at h
      rw [mul_right_cancel] at h
      exact h

    /-- Any right one is the one -/
    @[simp high] theorem single_one_right (alt_one : T) : g * alt_one = g → alt_one = one := by
      intro h
      nth_rewrite 2 [← mul_one g] at h
      rw [mul_left_cancel] at h
      exact h

    @[simp high] theorem single_one_same_squared (alt_one : T) : alt_one * alt_one = alt_one → alt_one = one := by
      intro h
      exact single_one_right alt_one alt_one h

    /-- Inverse of product: (g * k)⁻¹ = k⁻¹ * g⁻¹ -/
    @[simp high] theorem inv_of_product (g k : T) : inv (g * k) = inv k * inv g := by
      refine inv_symm (inv k * inv g) (g * k) ?_
      symm
      rw [← mul_right_cancel (g * k) (inv (inv k * inv g)) (inv k * inv g)]
      rw [← mul_assoc]
      rw [mul_assoc g k (inv k)]
      rw [mul_inv]
      rw [mul_one]
      rw [mul_inv]
      rw [inv_mul]

    /-- If product equals one then factors are mutual inverses -/
    theorem mul_of_inv_eq_one_right (g k : T) : g * k = one → g = inv k := by
      intro h
      rw [← mul_right_cancel (g * k) one (inv k)] at h
      rw [mul_assoc] at h
      rw [mul_inv] at h
      rw [mul_one] at h
      rw [one_mul] at h
      exact h

    /-- If product equals one then factors are mutual inverses -/
    theorem mul_of_inv_eq_one_left (g k : T) : g * k = one → k = inv g := by
      intro h
      rw [← mul_left_cancel (g * k) one (inv g)] at h
      rw [← mul_assoc] at h
      rw [inv_mul] at h
      rw [mul_one] at h
      rw [one_mul] at h
      exact h

  end TrivialFacts
  section Homomorphism
    variable {T₁ T₂ : Type}

    def isHom [_G₁ : Group T₁] [_G₂ : Group T₂] (f : T₁ → T₂) : Prop :=
      ∀g₁ g₂ : T₁, f (g₁ * g₂) = f g₁ * f g₂

    structure Hom (G₁ : Group T₁) (G₂ : Group T₂) where
      f : T₁ → T₂
      hom : isHom f

    def isKer {G₁ : Group T₁} {G₂ : Group T₂} (hom : Hom G₁ G₂) (S : Set T₁) : Prop :=
      ∀ (s : T₁), s ∈ S ↔ hom.f s = one

    structure Ker {G₁ : Group T₁} {G₂ : Group T₂} (hom : Hom G₁ G₂) where
      carrier : Set T₁
      ker : isKer hom carrier

    def isMono {G₁ : Group T₁} {G₂ : Group T₂} (hom : Hom G₁ G₂) : Prop :=
      ∀ (g₁ g₂ : T₁), hom.f g₁ = hom.f g₂ → g₁ = g₂

    theorem hom_one_to_one {G₁ : Group T₁} {G₂ : Group T₂}
      (hom : Hom G₁ G₂) : hom.f G₁.one = G₂.one := by
      have h := hom.hom
      rw [isHom] at h
      have h2 := h one one
      simp at h2
      have h3 := single_one_same_squared (hom.f one) h2.symm
      exact h3

    theorem hom_inv_eq_inv_hom {G₁ : Group T₁} {G₂ : Group T₂}
      (hom : Hom G₁ G₂) : ∀ (g : T₁), hom.f (inv g) = inv (hom.f g) := by
      intro g
      have homomorphism := hom.hom
      rw [isHom] at homomorphism
      have h1 : hom.f (g * inv g) = one := by
        rw [mul_inv]
        exact hom_one_to_one hom
      have h2 := homomorphism g (inv g)
      rw [h1] at h2
      symm at h2
      exact mul_of_inv_eq_one_left (hom.f g) (hom.f (inv g)) h2

    theorem mono_hom_trivial_ker {G₁ : Group T₁} {G₂ : Group T₂}
      (hom : Hom G₁ G₂) (ker : Ker hom) : isMono hom ↔ ker.carrier = {G₁.one} := by
      have kernel := ker.ker
      rw [isKer] at kernel
      have homomorphism := hom.hom
      rw [isHom] at homomorphism
      constructor
      . intro monomorphism
        rw [isMono] at monomorphism
        refine Set.ext ?mp.h
        intro x
        constructor
        . intro x_in_kernel
          have kernel := (kernel x).mp x_in_kernel
          have h := hom_one_to_one hom
          have h2 : hom.f one = hom.f x := by
            rw [h]
            rw [kernel]
          exact monomorphism x one (id (Eq.symm h2))
        . intro x_is_one
          have x_is_one : x = one := by
            exact monomorphism x one (congrArg hom.f (monomorphism x one (congrArg hom.f x_is_one)))
          apply (kernel x).mpr
          rw [x_is_one]
          exact hom_one_to_one hom
      . intro triv_ker
        rw [isMono]
        intro g₁ g₂
        intro same_image
        have h : hom.f (g₁ * inv g₂) = one := by
          rw [homomorphism g₁ (inv g₂)]
          rw [hom_inv_eq_inv_hom]
          rw [same_image]
          exact mul_inv (hom.f g₂)
        have h2 : g₁ * inv g₂ ∈ ker.carrier := by
          apply (kernel (g₁ * inv g₂)).mpr
          exact h
        rw [triv_ker] at h2
        have h3 : g₁ = inv (inv g₂) := by
          exact mul_of_inv_eq_one_right g₁ (inv g₂) h2
        rw [inv_of_inv] at h3
        exact h3
  end Homomorphism
end Group
