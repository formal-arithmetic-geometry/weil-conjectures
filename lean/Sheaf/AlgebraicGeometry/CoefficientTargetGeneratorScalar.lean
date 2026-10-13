/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.AlgebraicGeometry.FiniteAffineCechCoefficientComparisonMap

/-! # Scalar compatibility of supported coefficient generators

Source: Stacks Project, Tags 02KG, 01I9, 01IA and 0097.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The supported pullback-unit section is linear over the global ring of U.
Only scalar compatibility is asserted; neither affineness nor bijectivity is needed.
Source: Stacks Project, Tags 0096 and 0097, module pullback units and restriction.
(blueprint: lem-pc-coefficient-target-generator-scalar).

Proof: The source A-action is restriction along GammaSpecIso.inv followed by
(f restricted to U followed by U.toSpecGamma).appTop, and then to Z.
The isomorphism F.restrictAppIso transports this action to the structural action
on the image of Z in X. Linearity of the pullback adjunction unit transports
it by gprime.app; restriction to W and then W intersect fprime inverse image B
transports it by the corresponding restriction ring maps. Under the support
identification, multiplication by r in Gamma(Tprime,B) is multiplication by
fprime.app(B)(r) restricted to that intersection. Set r = g.appLE(top,B)(a).
Naturality of the structure maps and w identify this with the transported
source scalar: GammaSpecIso cancels the canonical chart U.toSpecGamma, leaving
f followed by the restriction to U. Thus applying coefficientSupportIso.hom
makes both expressions identical. Its injectivity gives the equation below.
All maps exist for empty opens and zero modules; no flatness is used. -/
theorem coefficientTarget_generator_scalar
    {X T : Scheme.{u}} (f : X ⟶ T)
    (F : X.Modules)
    (U : T.Opens)
    (Z : (f ⁻¹ᵁ U).toScheme.Opens)
    {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
    (w : g' ≫ f = f' ≫ (g ≫ U.ι))
    (W : X'.Opens) (hW : W = g' ⁻¹ᵁ ((f ⁻¹ᵁ U).ι ''ᵁ Z))
    (B : T'.Opens) :
    letI : Algebra Γ(U.toScheme, ⊤) Γ(T', B) :=
      (g.appLE ⊤ B (by simp)).hom.toAlgebra
    let N := (ModuleCat.restrictScalars
      (((Scheme.ΓSpecIso Γ(U.toScheme, ⊤)).inv ≫
        ((f ∣_ U) ≫ U.toScheme.toSpecΓ).appTop).hom)).obj
          ((F.restrict (f ⁻¹ᵁ U).ι).presheafModuleCat.obj (op Z))
    let M := (pullback g').obj F
    ∀ (a : Γ(U.toScheme, ⊤)) (s : N),
      (coefficientSupportIso f' M W B).inv
        (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
          (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW (a • s))) =
      (algebraMap Γ(U.toScheme, ⊤) Γ(T', B) a) •
        (coefficientSupportIso f' M W B).inv
          (M.presheaf.map (homOfLE (inf_le_left : W ⊓ f' ⁻¹ᵁ B ≤ W)).op
            (coefficientPullbackGenerator F (f ⁻¹ᵁ U) Z g' W hW s)) := by sorry

end
end AlgebraicGeometry.Scheme.Modules
