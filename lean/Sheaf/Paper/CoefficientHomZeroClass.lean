/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.Paper.CoefficientHomRepresentativeEvaluation
public import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # Canonical zero-cycle class in derived global Hom

Source: Stacks Project, Tags 08JA and 079P
(blueprint: def-coef-hom-zero-cycle-class).

## Main definitions

- `coefficientGlobalSections`: the recorded total derived section functor.
- `coefficientHomZeroClass`: the actual zero-cycle class via the derived unit.
- `coefficientHomZeroEvaluation`: evaluation by the fixed product projections.
- `coefficientHomZeroEquiv`: the uniquely normalized recorded H⁰ RHom identification.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u c v a b w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

/-- Total derived global sections on the original site and coefficient ring.
Source: Stacks 08JA (blueprint: def-coef-hom-zero-cycle-class).
This is the derived functor underlying the recorded zeroth hypercohomology. -/
noncomputable def coefficientGlobalSections
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))] :
    DerivedCategory (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ⥤
        @DerivedCategory AddCommGrpCat.{max c v u} _ _ (HasDerivedCategory.standard _) :=
  letI : IsGrothendieckAbelian.{max c v u} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J A).1
  letI := HasDerivedCategory.standard AddCommGrpCat.{max c v u}
  let F := preadditiveCoyoneda.obj (op (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)))
  F.rightDerivedFunctor

/-- The ordinary global-sections functor, written using Mathlib's module unit.
Source: Stacks 08JA (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable abbrev coefficientOrdinarySections
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u}) :=
  preadditiveCoyoneda.obj (op (SheafOfModules.unit
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)))

/-- The universal right-derived comparison on complexes, before inverting it on
K-injectives. It is used to fix global-section comparisons on simultaneous resolutions.
Source: Stacks 079P (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable def coefficientRightDerivedComparison
    {A : Type a} {B : Type b} [Category.{v} A] [Abelian A] [Category.{w} B] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  ((DerivedCategory.quotientCompQhIso _).app _).inv ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso _).app K).hom

/-- The canonical site-global-sections comparison, with the Grothendieck instance
at the correct coefficient universe.
Source: Stacks 079P, 08JA (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable def coefficientSiteSectionsComparison
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
    (A : Sheaf J CommRingCat.{max c v u})
    [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]
    (K : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :
    (@DerivedCategory.Q AddCommGrpCat.{max c v u} _ _ (HasDerivedCategory.standard _)).obj
        (((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⟶
      (coefficientGlobalSections.{u, c, v} J A).obj (DerivedCategory.Q.obj K) :=
  letI := HasDerivedCategory.standard AddCommGrpCat.{max c v u}
  letI : IsGrothendieckAbelian.{max c v u} (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{c, v, u}
      J A).1
  coefficientRightDerivedComparison (coefficientOrdinarySections.{u, c, v} J A) K

section HomZeroRepresentatives

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (A : Sheaf J CommRingCat.{max c v u})
  [HasDerivedCategory.{w} (SheafOfModules.{max c v u}
    ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A))]

/-- Ordinary sections of the fixed representative Hom complex.
Source: Stacks 08JA (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable def coefficientHomSectionComplex
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ) :=
  ((coefficientOrdinarySections.{u, c, v} J A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (homComplex.{c, v, max c v u, max c v u} (R := A) L
          ((coefficientHomResolution.{u, c, v} J A).obj M))

/-- A zero cycle's actual class in the global derived Hom, via the universal derived unit.
Source: Stacks 08JA (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable def coefficientHomZeroClass
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0) :=
  (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0).map
    (coefficientSiteSectionsComparison.{u, c, v} J A
      (homComplex.{c, v, max c v u, max c v u} (R := A) L
          ((coefficientHomResolution.{u, c, v} J A).obj M)) ≫
      (coefficientGlobalSections.{u, c, v} J A).map
        (coefficientHomResolutionIso.{u, c, v, w} J A L M).inv)
    ((@DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0).inv.app _
      (((coefficientHomSectionComplex.{u, c, v} J A L M).homologyπ 0) z))

/-- Evaluate a zero cycle on a local section using the actual product projection.
Source: Stacks 08JA, 0A8X (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable def coefficientHomZeroEvaluation
    (L M : CochainComplex (SheafOfModules.{max c v u}
      ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ)
    (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0)
    (p : ℤ) (U : Cᵒᵖ) (y : (L.X p).val.obj U) :
    (((coefficientHomResolution.{u, c, v} J A).obj M).X p).val.obj U :=
  let a := ((coefficientHomSectionComplex.{u, c, v} J A L M).iCycles 0 z).val.app U
    (1 : A.obj.obj U)
  let f := (coefficientHomComponent.{u, c, v} J A L
    ((coefficientHomResolution.{u, c, v} J A).obj M) 0 p p (add_zero p)).val.app U
      a
  (f.app (op (Over.mk (𝟙 U.unop)))).hom y

/-- The H⁰ RHom identification is uniquely fixed by taking a cycle to its chain map.
Source: Stacks 08JA (blueprint: def-coef-hom-zero-cycle-class).
Proof: on a K-flat L and the fixed K-injective replacement I(M), sections of Hom(L,I(M))
have zero cycles the chain maps and boundaries the null-homotopic maps. The universal
sections comparison and the actual Hom localization factorization give the displayed
class. Send it to Q(f) followed by the inverse of Q(M to I(M)). K-injectivity gives an
additive bijection. K-flat resolutions and localization naturality extend it uniquely to
all derived inputs, independently of the chosen resolution. Every cycle determines one
chain map by the product projections, and every derived morphism has such a representative;
these facts also prove uniqueness. This is the recorded rhom-global-sections comparison
with its representative normalization made explicit, not a second cohomology notion. -/
theorem coefficientHomZeroEquiv_exists :
    ∃! e : ∀ P Q : DerivedCategory (SheafOfModules.{max c v u}
        ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)),
      ((@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
      (HasDerivedCategory.standard _) 0).obj
        ((coefficientGlobalSections.{u, c, v} J A).obj
          ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj (op P, Q)))) ≃+ (P ⟶ Q),
      (∀ (P Q P' Q' : DerivedCategory (SheafOfModules.{max c v u}
          ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)))
        (f : P' ⟶ P) (g : Q ⟶ Q')
        (x : (@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
          (HasDerivedCategory.standard _) 0).obj
            ((coefficientGlobalSections.{u, c, v} J A).obj
              ((derivedInternalHomOfUniverses.{c, v, u, w} J A).obj (op P, Q)))),
        e P' Q'
          ((@DerivedCategory.homologyFunctor AddCommGrpCat.{max c v u} _ _
            (HasDerivedCategory.standard _) 0).map
              ((coefficientGlobalSections.{u, c, v} J A).map
                ((derivedInternalHomOfUniverses.{c, v, u, w} J A).map
                  (Prod.mkHom f.op g))) x) = f ≫ e P Q x ≫ g) ∧
      (∀ (L M : CochainComplex (SheafOfModules.{max c v u}
          ((sheafCompose J (forget₂ CommRingCat.{max c v u} RingCat.{max c v u})).obj A)) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v u}
          (J := J) (R := A) L →
        ∀ (f : L ⟶ (coefficientHomResolution.{u, c, v} J A).obj M)
          (z : (coefficientHomSectionComplex.{u, c, v} J A L M).cycles 0),
          (∀ (p : ℤ) (U : Cᵒᵖ) (y : (L.X p).val.obj U),
            coefficientHomZeroEvaluation.{u, c, v} J A L M z p U y = (f.f p).val.app U y) →
          e _ _ (coefficientHomZeroClass.{u, c, v, w} J A L M z) =
            DerivedCategory.Q.map f ≫ coefficientHomResolutionInverse.{u, c, v, w} J A M) := by
  sorry

/-- The uniquely normalized version of the recorded H⁰ RHom equivalence.
Source: Stacks 08JA (blueprint: def-coef-hom-zero-cycle-class). -/
noncomputable def coefficientHomZeroEquiv :=
  (coefficientHomZeroEquiv_exists.{u, c, v, w} J A).choose

end HomZeroRepresentatives

end WeilConjectures
