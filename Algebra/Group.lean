import Aesop
import Mathlib.Tactic.NthRewrite
import Mathlib.Data.Set.Defs

class Group (T : Type) extends Mul T where
  mul_assoc: ∀ a b c : T, (a * b) * c = a * (b * c)
  one : T
  one_mul : ∀ g : T, one * g = g
  mul_one : ∀ g : T, g * one = g
  inv : T → T
  mul_left_inv : ∀ g : T, inv g * g = one

structure Subgroup {T : Type} (G : Group T) where
  carrier : Set T
  one_mem : G.one ∈ carrier
  mul_mem : ∀ g₁ g₂, g₁ ∈ carrier → g₂ ∈ carrier → g₁ * g₂ ∈ carrier
  inv_mem : ∀ g, g ∈ carrier → G.inv g ∈ carrier

instance {T : Type} [G : Group T] : Coe (Subgroup G) (Set T) where
  coe H := H.carrier

instance {T : Type} {G : Group T} : Membership T (Subgroup G) where
  mem H x := x ∈ H.carrier

instance {T : Type} [G : Group T] : OfNat T 1 where
  ofNat := G.one

namespace Group
  section TrivialFacts
    variable {T : Type}
    variable [G : Group T]
    variable (g : T)

    @[simp] theorem one_eq_one_simp : (1 : T) = one := rfl
    @[simp] theorem one_mul_simp : one * g = g := one_mul g
    @[simp] theorem mul_one_simp : g * one = g := mul_one g
    @[simp] theorem mul_left_inv_simp : inv g * g = one := mul_left_inv g

    /-- Inverse of the inverse of g is g -/
    @[simp] theorem inv_of_inv : inv (inv g) = g := by
      have h : inv (inv g) * inv g = one := by
        apply mul_left_inv
      have h1 : inv (inv g) * inv g * g = one * g := by
        exact congrFun (congrArg HMul.hMul h) g
      rw [mul_assoc] at h1
      rw [mul_left_inv] at h1
      rw [mul_one] at h1
      rw [h1]
      exact one_mul g

    @[simp] theorem mul_right_inv : g * inv g = one := by
      nth_rewrite 1 [← inv_of_inv g]
      apply mul_left_inv (inv g)

    /-- Cancel right operand of multiplication equality -/
    @[simp] theorem mul_right_cancel (a b c : T) : a * c = b * c ↔ a = b := by
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
    @[simp] theorem mul_left_cancel (a b c : T) : c * a = c * b ↔ a = b := by
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

    /-- Any left unity is the unity -/
    @[simp] theorem single_one_left (alt_one : T) : alt_one * g = g → alt_one = one := by
      intro h
      nth_rewrite 2 [← one_mul g] at h
      rw [mul_right_cancel] at h
      exact h

    /-- Any right unity is the unity -/
    @[simp] theorem single_one_right (alt_one : T) : g * alt_one = g → alt_one = one := by
      intro h
      nth_rewrite 2 [← mul_one g] at h
      rw [mul_left_cancel] at h
      exact h

    @[simp] theorem single_one_same_squared (alt_one : T) : alt_one * alt_one = alt_one → alt_one = one := by
      intro h
      exact single_one_right alt_one alt_one h

  end TrivialFacts
  section Homomorphism
    variable {T₁ T₂ : Type}

    def isHom [_G₁ : Group T₁] [_G₂ : Group T₂] (f : T₁ → T₂) : Prop :=
      ∀g₁ g₂ : T₁, f (g₁ * g₂) = f g₁ * f g₂

    structure Hom (G₁ : Group T₁) (G₂ : Group T₂) where
      f : T₁ → T₂
      hom : isHom f

    def isKer {G₁ : Group T₁} {G₂ : Group T₂} (hom : Hom G₁ G₂) (S : Set T₁) : Prop :=
      ∀ (s : T₁), s ∈ S → hom.f s = one

    structure Ker {G₁ : Group T₁} {G₂ : Group T₂} (hom : Hom G₁ G₂) where
      carrier : Set T₁
      ker : isKer hom carrier

    def isMono {G₁ : Group T₁} {G₂ : Group T₂} (hom : Hom G₁ G₂) : Prop :=
      ∀ (g₁ g₂ : T₁), hom.f g₁ = hom.f g₂ → g₁ = g₂

    theorem hom_one_to_one {G₁ : Group T₁} {G₂ : Group T₂} (hom : Hom G₁ G₂) : hom.f G₁.one = G₂.one := by
      have h := hom.hom
      rw [isHom] at h
      have h2 := h one one
      simp at h2
      have h3 := single_one_same_squared (hom.f one) h2.symm
      exact h3

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
          have kernel := kernel x x_in_kernel
          have h := hom_one_to_one hom
          have h2 : hom.f one = hom.f x := by
            aesop
          have h3 := monomorphism one x



  end Homomorphism
end Group
