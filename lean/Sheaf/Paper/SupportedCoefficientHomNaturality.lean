/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q124
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.ForgetModuleCohomology
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology
public import Sheaf.Paper.SupportedHomPullback
public import Sheaf.SixFunctors.GeoCartierCoeffExtension
public import Sheaf.Paper.SupportedHomCocycleNormalization

/-! # Normalized support-Hom under coefficient and site change

Source: Milne, Section 9, Example 9.5 and the Ext proof of Theorem 9.4;
Stacks 03FD, 093X and 099R.
(blueprint: lem-pur-supported-coefficient-hom-naturality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor ChangeOfRings
namespace AlgebraicGeometry

/-- The existing etale supported-Hom pair with an arbitrary fixed coefficient ring.
Source: Milne, Section 9, Example 9.5, and the scalar-extension paragraph of
lem-amb-cartier-kummer-map.proof.md.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
abbrev rootScalarSupportPair (A : Type (u + 1)) [CommRing A]
    {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] : SupportHomPair A where
  Site := T.Etale
  topology := T.smallEtaleTopology
  terminal := Scheme.Etale.mk (𝟙 T)
  isTerminal := MorphismProperty.Over.mkIdTerminal _ _
  complement := Scheme.Etale.mk i.openComplement.ι
  restriction := Etale.supportRestrictionArrow i
  supported := Etale.supportedConstantModule (A := A) i
  constantRestriction := Etale.supportedHomConstantRestriction A i

namespace SupportedRootScalar

/-- Degree-zero bounded-below witness; this is used before any site comparison.
Source: blueprint scalar-extension paragraph; Stacks 099R.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def singlePlus {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 1} C] (M : C) : DerivedCategory.Plus C :=
  ⟨SheafExactDegreeZero.obj C M, by
    unfold SheafExactDegreeZero.obj
    exact ((DerivedCategory.Plus.singleFunctor C 0).obj M).property⟩

section CoefficientSupport

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
variable {A B : Type (u + 2)} [Category.{u + 1} A] [Category.{u + 1} B]
variable [Abelian A] [Abelian B] (F : A ⥤ B) [F.Additive]
variable [HasSheafify J A] [HasSheafify J B] [J.HasSheafCompose F]
variable {V W : C} (j : W ⟶ V)

/-- The actual kernel comparison for changing the coefficient category.
It is induced by preservation of kernels, not by any choice of a support map.
Source: Stacks 03FD and 093X; Milne, Section 9.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def kernelComparison :
    Sheaf.supportedSectionsFunctor J A j ⋙ F ⟶
      sheafCompose J F ⋙ Sheaf.supportedSectionsFunctor J B j where
  app M := CategoryTheory.Limits.kernelComparison (M.obj.map j.op) F
  naturality {M N} f :=
    (kernelComparison_comp_kernel_map (M.obj.map j.op) F (N.obj.map j.op)
      (f.hom.app (op V)) (f.hom.app (op W)) (f.hom.naturality j.op)).symm

variable [dA : HasDerivedCategory.{u + 1} A] [dB : HasDerivedCategory.{u + 1} B]
variable [dSA : HasDerivedCategory.{u + 1} (Sheaf J A)]
variable [dSB : HasDerivedCategory.{u + 1} (Sheaf J B)]
variable [EnoughInjectives (Sheaf J A)] [EnoughInjectives (Sheaf J B)]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
variable [(sheafCompose J F).Additive]
variable [PreservesFiniteLimits (sheafCompose J F)]
variable [PreservesFiniteColimits (sheafCompose J F)]

/-- The canonical derived coefficient comparison on the full supported object.
Its underived transformation is the preceding kernel comparison. In particular no
injectivity of a restricted injective resolution is assumed.
Source: Stacks 03FD and 093X; Milne, Section 9.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def derivedCoefficientComparison :
    (Sheaf.supportedSectionsFunctor J A j).rightDerivedFunctorPlus ⋙
        F.mapDerivedCategoryPlus ⟶
      (sheafCompose J F).mapDerivedCategoryPlus ⋙
        (Sheaf.supportedSectionsFunctor J B j).rightDerivedFunctorPlus :=
  Functor.rightDerivedFunctorPlusBaseChange (kernelComparison J F j)

/-- The induced map on supported groups, including the exact-functor homology comparison.
Source: Stacks 03FD and 093X; Milne, Section 9.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def coefficientGroupMap (K : DerivedCategory.Plus (Sheaf J A)) (a : ℤ) :
    F.obj ((Sheaf.supportHypercohomologyFunctor.{u + 1, u, u + 2, u + 1, u + 1, u + 1}
        J A j a).obj K) ⟶
      (Sheaf.supportHypercohomologyFunctor.{u + 1, u, u + 2, u + 1, u + 1, u + 1}
        J B j a).obj
        ((sheafCompose J F).mapDerivedCategoryPlus.obj K) :=
  (F.mapDerivedCategoryPlusHomologyFunctorIso a).hom.app
      ((Sheaf.supportedSectionsFunctor J A j).rightDerivedFunctorPlus.obj K) ≫
    (DerivedCategory.Plus.homologyFunctor.{u + 1, u + 2, u + 1} B a).map
      ((derivedCoefficientComparison J F j).app K)

end CoefficientSupport

/-- The actual Hom space with its ordinary derived-category hom universe fixed.
This is a type alias, not a new Hom construction. Source: Milne, Section 9, Example 9.5.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
abbrev zeroHom {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (M : Sheaf S.topology (ModuleCat.{u + 1} A)) : Type (u + 1) :=
  SheafExactDegreeZero.obj _ S.supported ⟶ (SheafExactDegreeZero.obj _ M)⟦(2 : ℤ)⟧

/-- Transport a single-source arrow to the named degree-zero presentation.
Source: the canonical degree-zero comparison in Milne, Section 9.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
@[irreducible] def fromSingle {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 1} C] (M : C) (K : DerivedCategory C)
    (f : (DerivedCategory.singleFunctor C 0).obj M ⟶ K) :
    SheafExactDegreeZero.obj C M ⟶ K :=
  eqToHom (SheafExactDegreeZero.obj_eq M) ≫ f

/-- Transport a named degree-zero source back to the canonical single source.
Source: the canonical degree-zero comparison in Milne, Section 9.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
@[irreducible] def toSingle {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 1} C] (M : C) (K : DerivedCategory C)
    (f : SheafExactDegreeZero.obj C M ⟶ K) :
    (DerivedCategory.singleFunctor C 0).obj M ⟶ K :=
  eqToHom (SheafExactDegreeZero.obj_eq M).symm ≫ f

/-- The canonical bijection between the two degree-zero source presentations.
Source: the exact degree-zero object comparison.
(blueprint: lem-pur-supported-coefficient-hom-naturality) -/
def presentationEquiv {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 1} C] (M : C) (K : DerivedCategory C) :
    ((DerivedCategory.singleFunctor C 0).obj M ⟶ K) ≃
      (SheafExactDegreeZero.obj C M ⟶ K) :=
  Equiv.cast (congrArg (fun X : DerivedCategory C ↦ X ⟶ K)
    (SheafExactDegreeZero.obj_eq M).symm)

/-- The bounded-below witness has the specified underlying object.
Source: the degree-zero single construction.
(blueprint: lem-pur-supported-coefficient-hom-naturality) -/
theorem singlePlus_obj {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
    [HasDerivedCategory.{u + 1} C] (M : C) :
    (singlePlus M).obj = SheafExactDegreeZero.obj C M := rfl

/-- Equality of the two fixed source presentations of derived morphisms.
Source: the canonical single-object and degree-zero comparisons.
(blueprint: lem-pur-supported-coefficient-hom-naturality) -/
theorem homPresentation {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (M : Sheaf S.topology (ModuleCat.{u + 1} A)) :
    S.derivedHom (singlePlus M) 2 = zeroHom S M := by
  unfold SupportHomPair.derivedHom zeroHom
  rw [singlePlus_obj, SheafExactDegreeZero.obj_eq S.supported]

/-- Evaluation-normalized realization as a bijection of the fixed Hom types.
Source: the support-Hom identification and the degree-zero source comparison.
(blueprint: lem-pur-supported-coefficient-hom-naturality) -/
def realizationEquiv {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (chi : S.Identification) (M : Sheaf S.topology (ModuleCat.{u + 1} A)) :
    S.group (singlePlus M) 2 ≃ zeroHom S M :=
  (chi.chi (singlePlus M) 2).toEquiv.trans (Equiv.cast (homPresentation S M))

/-- Express the normalized supported-Hom realization using the named degree-zero objects.
Source: Milne, Section 9, evaluation at one and the signed support cone.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def realize {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (chi : S.Identification) (M : Sheaf S.topology (ModuleCat.{u + 1} A))
    (beta : S.group (singlePlus M) 2) :
    zeroHom S M :=
  cast (homPresentation S M) (chi.chi (singlePlus M) 2 beta)

/-- The realization map is the forward map of its canonical equivalence.
Source: composition of the normalized identification with its presentation cast.
(blueprint: lem-pur-supported-coefficient-hom-naturality) -/
theorem realizationEquiv_apply {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (chi : S.Identification) (M : Sheaf S.topology (ModuleCat.{u + 1} A))
    (beta : S.group (singlePlus M) 2) :
    realizationEquiv S chi M beta = realize S chi M beta := rfl

/-- The inverse change of the same single-object presentation.
Source: the ordinary module derived-category convention; no class or lift is chosen.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def homFromZero {A : Type (u + 1)} [CommRing A] (S : SupportHomPair A)
    (M : Sheaf S.topology (ModuleCat.{u + 1} A))
    (b : zeroHom S M) : S.derivedHom (singlePlus M) 2 :=
  cast (homPresentation S M).symm b

private theorem cast_cancel {X Y : Type (u + 1)} (h : X = Y) (x : X) :
    cast h.symm (cast h x) = x := by cases h; rfl

/-- Realization and the inverse source presentation recover the normalized Hom class.
Source: the inverse laws of the canonical degree-zero presentation comparison.
(blueprint: lem-pur-supported-coefficient-hom-naturality) -/
theorem homFromZero_realize {A : Type (u + 1)} [CommRing A]
    (S : SupportHomPair A) (chi : S.Identification)
    (M : Sheaf S.topology (ModuleCat.{u + 1} A))
    (beta : S.group (singlePlus M) 2) :
    homFromZero S M (realize S chi M beta) = chi.chi _ 2 beta :=
  cast_cancel (homPresentation S M) (chi.chi (singlePlus M) 2 beta)

/-- Agreement of an evaluation-normalized identification with the signed relative cone.
This uses the existing cone-agreement predicate, rather than changing its boundary sign.
Source: Milne, Section 9; blueprint lem-pur-divisor-relative-cone.
(blueprint: lem-pur-supported-root-scalar-site-comparison) -/
def SignedIdentification {A : Type (u + 1)} [CommRing A]
    (S : SupportHomPair A) (chi : S.Identification) : Prop :=
  ∃ N : SupportedHomCocycleNormalization S.topology A S.isTerminal S.restriction
      S.supported S.constantRestriction,
    N.chi = chi.chi ∧ N.ConeAgreement

/-- Evaluation at one identifies the actual derived restriction-kernel comparison
with precomposition by the supported coefficient unit. The signed normalization is
compatible with the canonical etale to pro-etale support transport.

Source: Milne, Section 9, Example 9.5 and the Ext proof of Theorem 9.4;
Stacks 03FD, 093X and 099R.
(blueprint: lem-pur-supported-coefficient-hom-naturality)

Proof: construct the evaluation-normalized support-Hom identifications over R and A
from the cokernel presentation of the closed constant. On injective resolutions,
precomposition by the coefficient unit preserves evaluation since 1_R maps to 1_A.
Compare a restricted A-injective resolution with an R-injective resolution using the
K-injective comparison principle. The canonical kernel comparison identifies the
resulting cocycles and their boundaries; restricted injectives need not be injective.
The module-to-abelian kernel comparison is invertible. Factoring coefficient
forgetting through restriction of scalars and cancelling the two abelian comparisons
proves invertibility for restriction as well. The same argument on the pro-etale
site gives its coefficient-forgetting comparison. Kernel inclusion into the signed
relative cone commutes with coefficient maps on both components, including the
negative boundary component. The canonical site transport is evaluation normalized;
apply supported-Hom pullback to B[0]. Its kernel inclusion gives the same signed
relative cone and the asserted compatible pro-etale identification. -/
theorem supportedCoefficientHomNaturality
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (R : Type (u + 1)) [CommRing R] [Finite R] (phi : R →+* P.Coefficient)
    (T : Scheme.{u}) {Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i] :
    ∃ chiR : (rootScalarSupportPair R i).Identification,
    ∃ chiA : (etaleSupportHomPair P i).Identification,
    ∃ chiP : (proEtaleSupportHomPair P i).Identification,
    ∃ v : siteSupportHomTransport P i,
      SignedIdentification (rootScalarSupportPair R i) chiR ∧
      SignedIdentification (etaleSupportHomPair P i) chiA ∧
      SignedIdentification (proEtaleSupportHomPair P i) chiP ∧
      ∀ (M : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))
        (B : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))
        (theta : M ⟶ (Sheaf.restrictScalars T.smallEtaleTopology phi).obj B),
      IsIso ((derivedCoefficientComparison
        (dA := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} R))
        (dB := HasDerivedCategory.ofIsGrothendieckAbelian AddCommGrpCat.{u + 1})
        T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1})
          (Etale.supportRestrictionArrow i)).app (singlePlus M)) ∧
      IsIso ((derivedCoefficientComparison
        (dA := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} P.Coefficient))
        (dB := HasDerivedCategory.ofIsGrothendieckAbelian AddCommGrpCat.{u + 1})
        T.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})
          (Etale.supportRestrictionArrow i)).app (singlePlus B)) ∧
      IsIso ((derivedCoefficientComparison
        (dA := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} P.Coefficient))
        (dB := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} R))
        T.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} phi)
          (Etale.supportRestrictionArrow i)).app (singlePlus B)) ∧
      IsIso ((derivedCoefficientComparison
        (dA := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} P.Coefficient))
        (dB := HasDerivedCategory.ofIsGrothendieckAbelian AddCommGrpCat.{u + 1})
        (Scheme.ProEt.topology T)
        (forget₂ (ModuleCat.{u + 1} P.Coefficient) AddCommGrpCat.{u + 1})
          (ProEtale.supportRestrictionArrow i)).app
            ((ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategoryPlus.obj
              (singlePlus B))) ∧
      v.Compatible (hB := Scheme.isContinuous_toProEt T) chiA chiP (singlePlus B) 2 ∧
      ∀ (beta : (rootScalarSupportPair R i).group (singlePlus M) 2)
        (gamma : (etaleSupportHomPair P i).group (singlePlus B) 2),
        (coefficientGroupMap
          (dA := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} P.Coefficient))
          (dB := HasDerivedCategory.ofIsGrothendieckAbelian (ModuleCat.{u + 1} R))
          T.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} phi)
          (Etale.supportRestrictionArrow i) (singlePlus B) 2).hom gamma =
          ((Sheaf.supportHypercohomologyFunctor T.smallEtaleTopology
            (ModuleCat.{u + 1} R) (Etale.supportRestrictionArrow i) 2).map
              (ObjectProperty.homMk
                (SheafExactDegreeZero.scalarUnit T.smallEtaleTopology phi M B theta))).hom beta
        ↔ Etale.coefficientUnitDerived phi i ≫
            (Sheaf.derivedRestrictScalars T.smallEtaleTopology phi).map
              (realize (etaleSupportHomPair P i) chiA B gamma) =
          realize (rootScalarSupportPair R i) chiR M beta ≫
            (SheafExactDegreeZero.scalarUnit T.smallEtaleTopology phi M B theta)⟦(2 : ℤ)⟧' ≫
              ((Sheaf.derivedRestrictScalars T.smallEtaleTopology phi).commShiftIso
                (2 : ℤ)).inv.app (SheafExactDegreeZero.obj _ B) := by
  sorry

end SupportedRootScalar
end AlgebraicGeometry
