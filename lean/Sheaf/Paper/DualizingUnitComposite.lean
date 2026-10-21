/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.Paper.CohomologicalSmoothnessFiniteComparison
public import Sheaf.Paper.PurityFiniteExceptionalComposition
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import Sheaf.Paper.ProjectionMateExact
import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula

/-! # Dualizing unit and composite tensor identifications

Source: main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality.proof.md, Step 1
(blueprint: lem-pur-dualizing-unit-composite).

We use the canonical etale-origin coordinates of def-pur-co-smoothness. In these
coordinates the published tensor transpose has source W tensor pullback K: it already
includes the symmetry in the node's definition of sigma. The exceptional compositor
is the published conjugate of the actual compact-support compositor. Comparison
pullback identifies these maps with the maps on the small pro-etale Dctf categories.
The rho hypothesis below is restricted to Dctf, not to an ambient derived category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The coefficient unit as an object of Dctf in the canonical etale coordinates.
Its property is assembled from the existing constructible-single and flat-single results.
Source: purity conventions, coefficient unit (blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingUnitModel (X : Scheme.{u}) :
    Etale.DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X :=
  ⟨𝟙_ _,
    (Etale.DerivedCategory.boundedConstructible _ X).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (Etale.DerivedCategory.boundedConstructible_singleFunctor_obj _ 0),
    0, 0, (Etale.DerivedCategory.torAmplitudeIn _ X 0 0).prop_of_iso
      (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩

/-- The coefficient-unit component of the specified exceptional conjugate.
Source: Step 1, c at A (blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingCompositeConjugate {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [HasCompactification a] [HasCompactification b] [HasCompactification (a ≫ b)]
    [QuasiCompact a] [QuasiCompact (a ≫ b)] :
    Etale.dualizingComplex (ModuleCat.{u + 1} Λ) (a ≫ b) ≅
      (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) a).obj
        (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) b) :=
  (finiteExceptionalComposition Λ a b).app
    (𝟙_ (_root_.DerivedCategory (Sheaf Z.smallEtaleTopology
      (ModuleCat.{u + 1} Λ))))

/-- The specified sigma, with the tensor-transpose symmetry already included upstream.
Source: Step 1, dualizing composition formula
(blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingCompositeSigma {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [HasCompactification a] [HasCompactification b] [HasCompactification (a ≫ b)]
    [QuasiCompact a] [QuasiCompact (a ≫ b)] :
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) a)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor.obj
          (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) b)) ⟶
      Etale.dualizingComplex (ModuleCat.{u + 1} Λ) (a ≫ b) :=
  Etale.dualizingComplexTensorMap Λ a
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) b) ≫
    (dualizingCompositeConjugate Λ a b).inv

/-- The specified t for any trivialization eta, including the pullback-unit comparison.
Source: Step 1, arbitrary trivialization formula
(blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingCompositeTrivialization {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [HasCompactification a] [HasCompactification b]
    (eta : Etale.dualizingComplex (ModuleCat.{u + 1} Λ) b ≅ 𝟙_ _) :
    ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) a)).obj
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor.obj
          (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) b)) ≅
      Etale.dualizingComplex (ModuleCat.{u + 1} Λ) a :=
  ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) a)).mapIso
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor.mapIso eta ≪≫
        Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) a) ≪≫
    Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) a)

/-- Unit normalization of the specified counit transpose, in W-first coordinates.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite).
Proof: the proper projection mate at the coefficient unit is the identity after unit
comparisons (lem-weil-pbc-ringed-projection-mate-exact). The normalized open projection
has the same property by adjunct uniqueness (lem-sf-open-tensor-normalization). Their
compactification composite therefore has this property. Transpose its inverse followed
by the counit. The adjunction triangle identifies the result with the displayed unitor.
No separatedness of either scheme over k is used. Apply open restriction to the equality;
functoriality and the stipulated operation/unit comparisons identify the result with
the restricted formula (node proof Step 7). -/
def dualizingUnitAssertion {X Y : Scheme.{u}} (a : X ⟶ Y)
    [HasCompactification a] : Prop :=
    Etale.dualizingComplexTensorMap Λ a (𝟙_ _) =
      ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) a)).map
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) a).hom ≫
      (Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X
            (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) a)).hom ∧
    ∀ (V : Scheme.{u}) (j : V ⟶ X) [IsOpenImmersion j],
      (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
          (Etale.dualizingComplexTensorMap Λ a (𝟙_ _)) =
        (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
          (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
            (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) a)).map
            (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) a).hom) ≫
        (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
          (Etale.derivedTensorRightUnitor (ModuleCat.{u + 1} Λ) X
            (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) a)).hom

/-- The specified inverse formula for every eta, without a normalization on eta.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite).
Proof: inverse-projection naturality gives G(v) theta_K = theta_L (P(v) tensor 1).
Transpose using def-weil-exceptional-inverse-image. Apply this to eta and use the unit
normalization just above. Cancel the conjugate compositor c to obtain
sigma followed by c followed by G(eta) = t. Both t and c followed by G(eta) are
invertible, hence sigma is invertible. Postcompose this equality by its inverse.
The compact-support compositor and its conjugate are isomorphisms by
thm-sf-comp-composition and def-weil-pbc-adjunction-conjugate. The finite projection
formula supplies precisely the natural invertible projection components used here.
For open restriction, apply its functor to the equation and both inverse equations;
compatibility of the given data identifies these with the restricted maps (Step 7). -/
def dualizingInverseAssertion {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    [HasCompactification a] [HasCompactification b] [HasCompactification (a ≫ b)]
    [QuasiCompact a] [QuasiCompact (a ≫ b)]
    (eta : Etale.dualizingComplex (ModuleCat.{u + 1} Λ) b ≅ 𝟙_ _) : Prop :=
    ∃ s :
      ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) a)).obj
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) a).leftDerivedFunctor.obj
            (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) b)) ≅
        Etale.dualizingComplex (ModuleCat.{u + 1} Λ) (a ≫ b),
      s.hom = dualizingCompositeSigma Λ a b ∧
        s.inv ≫ (dualizingCompositeTrivialization Λ a b eta).hom =
          (dualizingCompositeConjugate Λ a b).hom ≫
            (Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) a).map eta.hom ∧
        ∀ (V : Scheme.{u}) (j : V ⟶ X) [IsOpenImmersion j],
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.mapIso s).inv ≫
              (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
                (dualizingCompositeTrivialization Λ a b eta).hom =
            (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
                ((dualizingCompositeConjugate Λ a b).hom) ≫
              (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
                ((Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) a).map
                  eta.hom)

/-- The unit trivialization eta_e induced by rho on exactly the Dctf domain.
Source: Step 1, rho normalization (blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingRhoUnit {U X : Scheme.{u}} (e : U ⟶ X) [HasCompactification e]
    (rho :
      Etale.DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ⋙
          Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) e ≅
        Etale.DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ⋙
          (Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor) :
    Etale.dualizingComplex (ModuleCat.{u + 1} Λ) e ≅
      𝟙_ (_root_.DerivedCategory (Sheaf U.smallEtaleTopology
        (ModuleCat.{u + 1} Λ))) :=
  rho.app (dualizingUnitModel Λ X) ≪≫
    Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} Λ) e

/-- The given normalization on exactly Dctf.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingRhoNormalized {U X : Scheme.{u}} (e : U ⟶ X) [HasCompactification e]
    (rho :
      Etale.DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ⋙
          Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) e ≅
        Etale.DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ⋙
          (Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor)
 : Prop :=
  ∀ K : Etale.DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) X,
      Etale.dualizingComplexTensorMap Λ e K.obj ≫ rho.hom.app K =
        ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) U).map
          (dualizingRhoUnit Λ e rho).hom).app
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor.obj K.obj) ≫
        (Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor.obj K.obj)).hom

/-- Source cancellation for a normalized exceptional/pullback comparison on Dctf.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite).
Proof: expand E and sigma, cancel the inverse compositor against its hom, and
apply the assumed rho normalization at W_h. In the upstream W-first ordering
this is exactly the displayed left unitor after eta_e tensor 1. The latter is
invertible, as are rho and the compositor, hence sigma is invertible. Neither e
nor h has been assumed smooth or oriented. Apply open restriction to these equations
and inverse equations; the stipulated compatibility of rho and the operation data
identifies them with the restricted equations (node proof Step 7). -/
def dualizingSourceAssertion {U X S : Scheme.{u}} (e : U ⟶ X) (h : X ⟶ S)
    [HasCompactification e] [HasCompactification h] [HasCompactification (e ≫ h)]
    [QuasiCompact e] [QuasiCompact (e ≫ h)]
    (hW : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X
      (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) h))
    (rho :
      Etale.DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ⋙
          Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} Λ) e ≅
        Etale.DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} Λ) X ⋙
          (Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor)
 : Prop :=
    dualizingCompositeSigma Λ e h ≫
        (dualizingCompositeConjugate Λ e h).hom ≫
        rho.hom.app ⟨Etale.dualizingComplex (ModuleCat.{u + 1} Λ) h, hW⟩ =
      ((Etale.derivedTensor (ModuleCat.{u + 1} Λ) U).map
        (dualizingRhoUnit Λ e rho).hom).app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor.obj
          (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) h)) ≫
        (Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor.obj
            (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) h))).hom ∧
      IsIso (dualizingCompositeSigma Λ e h) ∧
      ∀ (V : Scheme.{u}) (j : V ⟶ U) [IsOpenImmersion j],
        (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
            (dualizingCompositeSigma Λ e h) ≫
          (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
            ((dualizingCompositeConjugate Λ e h).hom) ≫
          (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
            (rho.hom.app ⟨Etale.dualizingComplex (ModuleCat.{u + 1} Λ) h, hW⟩) =
          (Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
            (((Etale.derivedTensor (ModuleCat.{u + 1} Λ) U).map
                (dualizingRhoUnit Λ e rho).hom).app
                ((Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor.obj
                  (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) h)) ≫
              (Etale.derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) U
                ((Etale.upperStar (ModuleCat.{u + 1} Λ) e).leftDerivedFunctor.obj
                  (Etale.dualizingComplex (ModuleCat.{u + 1} Λ) h))).hom) ∧
        IsIso ((Etale.upperStar (ModuleCat.{u + 1} Λ) j).leftDerivedFunctor.map
          (dualizingCompositeSigma Λ e h))


/-- The dualizing object as an object of the stated finite-Tor constructible domain.
This is the existing exceptional preservation theorem applied to the coefficient unit.
Source: purity conventions and Dctf stability
(blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingCompositeModel (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [QuasiCompact f]
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY] :
    Etale.DerivedCategoryFiniteTor (ModuleCat.{u + 1} P.Coefficient) X :=
  letI := finiteComparedInvertibleExponent P aY
  ⟨Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) f,
    Etale.constructibleFiniteTor_dualizingComplex P.Coefficient aY f
      (dualizingUnitModel P.Coefficient Y).property⟩


/-- The unit clause with Nagata compactification supplied from the node's hypotheses.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingFiniteUnitAssertion (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (a : X ⟶ Y) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] : Prop :=
  letI := (P.finiteComparedCompactification a (Y ↘ Spec (.of P.field.k))).hasCompactification
  dualizingUnitAssertion P.Coefficient a

/-- The arbitrary-trivialization clause with canonical compactification data.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingFiniteInverseAssertion (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (a : X ⟶ Y) (b : Y ⟶ Z)
    [a.IsOver (Spec (.of P.field.k))] [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b] : Prop :=
  letI := (P.finiteComparedCompactification a (Y ↘ Spec (.of P.field.k))).hasCompactification
  letI := (P.finiteComparedCompactification b (Z ↘ Spec (.of P.field.k))).hasCompactification
  letI := (P.finiteComparedCompactification (a ≫ b)
    (Z ↘ Spec (.of P.field.k))).hasCompactification
  ∀ eta : Etale.dualizingComplex (ModuleCat.{u + 1} P.Coefficient) b ≅ 𝟙_ _,
    dualizingInverseAssertion P.Coefficient a b eta

/-- The conditional source clause on precisely Dctf, with no extra compactification input.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite). -/
def dualizingFiniteSourceAssertion (P : PurityFiniteSetting.{u}) {U X S : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) (h : X ⟶ S)
    [e.IsOver (Spec (.of P.field.k))] [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] : Prop :=
  letI := (P.finiteComparedCompactification e (X ↘ Spec (.of P.field.k))).hasCompactification
  letI := (P.finiteComparedCompactification h (S ↘ Spec (.of P.field.k))).hasCompactification
  letI := (P.finiteComparedCompactification (e ≫ h)
    (S ↘ Spec (.of P.field.k))).hasCompactification
  ∀ (rho :
      Etale.DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} P.Coefficient) X ⋙
          Etale.rightDerivedUpperShriek (ModuleCat.{u + 1} P.Coefficient) e ≅
        Etale.DerivedCategoryFiniteTor.ι (ModuleCat.{u + 1} P.Coefficient) X ⋙
          (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) e).leftDerivedFunctor),
    dualizingRhoNormalized P.Coefficient e rho →
      dualizingSourceAssertion P.Coefficient e h
        (P.dualizingCompositeModel h (S ↘ Spec (.of P.field.k))).property rho

/-- Unit normalization of the actual tensor transpose at the fixed purity coefficients.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite).
Proof: normalize the proper projection mate at the unit by the ringed projection-mate
lemma. The normalized open projection is the identity at the unit: its inverse and the
identity have the same open-adjunction adjunct. Their compactification composite is
therefore the identity at the unit. In the defining tensor transpose its inverse drops
out, and the exceptional-adjunction triangle makes the remaining adjunct the canonical
unitor with the pullback-unit comparison. Apply each compatible open restriction functor
to the equality and use its composition law and the supplied data compatibilities. -/
theorem dualizingTensor_unit (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (a : X ⟶ Y) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a] :
    dualizingFiniteUnitAssertion P a := by
  sorry

/-- The inverse of the specified sigma, for every trivialization of W_b.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite).
Proof: the finite compact projection theorem makes the projection components used in
theta invertible. Naturality of their inverses, of the counit and of tensor symmetry,
transposed by the natural adjunction bijection, gives naturality of theta. Apply it to
eta, then apply the unit normalization. The conjugate of the compact-support compositor
is invertible, and cancellation gives sigma followed by c followed by a!(eta) equal to
the specified t. The last two arrows and t are invertible, so sigma is invertible;
compose with its inverse to get the displayed inverse equation. For compatible open
restriction apply the functor to the equality and the two inverse equations. It preserves
compositions and identities, so the restricted inverse and equation are the specified ones. -/
theorem dualizingComposite_inverse (P : PurityFiniteSetting.{u}) {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))] [Y.Over (Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (a : X ⟶ Y) (b : Y ⟶ Z)
    [a.IsOver (Spec (.of P.field.k))] [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b] :
    dualizingFiniteInverseAssertion P a b := by
  sorry

/-- Source cancellation for the given normalized comparison on Dctf.
Source: Step 1 (blueprint: lem-pur-dualizing-unit-composite).
Proof: the coefficient unit is constructible of finite Tor dimension; exceptional
preservation puts W_h in Dctf. Expand E and sigma, cancel c inverse followed by c, and
apply rho's assumed normalization at W_h. Symmetry naturality and the unit constraint
identify this with the left unitor after eta_e tensor identity. That map is invertible,
as are rho and c, so sigma is invertible. No smoothness, orientation or twist enters.
Applying compatible open restriction preserves both the equation and the inverse
identities; the supplied tensor, counit and operation comparisons identify the results
with the corresponding restricted formulas. -/
theorem dualizingComposite_sourceCancellation (P : PurityFiniteSetting.{u}) {U X S : Scheme.{u}}
    [U.Over (Spec (.of P.field.k))] [X.Over (Spec (.of P.field.k))]
    [S.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    (e : U ⟶ X) (h : X ⟶ S)
    [e.IsOver (Spec (.of P.field.k))] [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] :
    dualizingFiniteSourceAssertion P e h := by
  sorry

end WeilConjectures.PurityFiniteSetting
