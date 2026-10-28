/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M5
-/
module

public import Sheaf.SixFunctors.IntegralDualizingRoosModel
public import Sheaf.Algebra.Homology.RingedSiteGlobalRHomModel

/-! # Integral scalar global Hom on a fixed K-injective target

Source: Stacks 0B6E, 0A95, 0A96 and 08JA. The representative here involves no tower
and no inverse limit. Its first variable is the entire category of complexes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Integral scalars as actual compatible sections of the completed structure ring.
Source: Stacks 0B6E (blueprint: lem-coef-integral-dualizing-resolved-global-hom). -/
def integralDualizingScalarSections : integralDualizingCoefficients l E →+*
    RingCat.sectionsSubring (completedIntegralCoefficientSheafUnrestricted l E X).obj :=
  (RingHom.pi (integralDualizingScalar l E X)).codRestrict _ (fun a ↦ by
    intro U V f
    let η := Functor.whiskerRight
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (integralDualizingCoefficients l E))))
      (forget₂ CommRingCat RingCat) ≫
        (integralConstantToCompletionOfUniverses.{u, u} l E X).hom
    exact (ConcreteCategory.congr_hom (η.naturality f) a).symm)

/-- The signed global Hom complex, retaining the specified integral scalar action.
Source: Stacks 0B6E, 08JA
(blueprint: lem-coef-integral-dualizing-resolved-global-hom). -/
def integralDualizingResolvedHom :
    (CochainComplex (scalarReductionSource l E X) ℤ)ᵒᵖ ⥤
      CochainComplex (scalarReductionSource l E X) ℤ ⥤
        CochainComplex (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) ℤ :=
  homComplexFunctor (R := completedIntegralCommRingSheafUnrestricted l E X) ⋙
    (Functor.whiskeringRight _ _ _).obj
      ((RingedSiteGlobalRHom.sections
        (completedIntegralCommRingSheafUnrestricted l E X)
        (integralDualizingCoefficients l E) (integralDualizingScalarSections l E X))
          |>.mapHomologicalComplex (.up ℤ))

/-- Global Hom before restriction to constructible inputs.
Source: Stacks 0B6E
(blueprint: lem-coef-integral-dualizing-resolved-global-hom). -/
def integralDualizingAmbientGlobalHom (M : DerivedCategory (scalarReductionSource l E X)) :
    (DerivedCategory (scalarReductionSource l E X))ᵒᵖ ⥤
      DerivedCategory (ModuleCat.{u + 1} (integralDualizingCoefficients l E)) :=
  (Functor.curry.obj (derivedInternalHomOfUniverses.{u + 1, u, u}
    (Scheme.ProEt.topology X) (completedIntegralCommRingSheafUnrestricted l E X))).flip.obj M ⋙
      integralDualizingDerivedSections l E X

/-- On a fixed K-injective target, global derived Hom is represented by the signed
ordinary global Hom complex, naturally in every source complex.

Source: Stacks 0B6E, 0A95, 0A96 and 08JA; the representative comparison in the first
step of lem-sfb-ringed-site-global-rhom-derived-limits.
(blueprint: lem-coef-integral-dualizing-resolved-global-hom).

Proof: identify compatible sections with sections at the final pro-etale object;
scalar restriction uses precisely integralDualizingScalarSections evaluated there.
The replacement-normalized internal-Hom comparison identifies RHom(QP,QI) with
Q Hom(P,I), naturally in P. For flat-term K-flat P, Hom(P,I) is K-injective, so
ordinary sections compute derived sections. For arbitrary P, take a flat-term
K-flat resolution P' to P. Precomposition is a quasi-isomorphism both on sheaf Hom
and on its ordinary global Hom complex because I is K-injective. Naturality of
the derived-sections unit transfers invertibility from P' to P. Thus the canonical
comparison is a natural isomorphism on all complexes, without a bound on P or I.
The same argument includes the zero complex and the empty scheme. -/
theorem integralDualizing_resolved_globalHom
    (I : CochainComplex (scalarReductionSource l E X) ℤ) [I.IsKInjective] :
    Nonempty (DerivedCategory.Q.op ⋙
      integralDualizingAmbientGlobalHom l E X (DerivedCategory.Q.obj I) ≅
        (integralDualizingResolvedHom l E X).flip.obj I ⋙ DerivedCategory.Q) := by sorry

end WeilConjectures
