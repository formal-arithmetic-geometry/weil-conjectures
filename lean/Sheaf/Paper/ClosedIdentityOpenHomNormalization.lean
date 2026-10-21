/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q04
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt
public import Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import Sheaf.Paper.BoundaryExceptionalComparisonData
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ProperBasic
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # The closed identity-open exceptional Hom chain

Source: main-20261015 blueprint, thm-sf-ambient-adjoint-class.proof.md, displayed
four-factor Hom chain at (id_Z,i)
(blueprint: lem-coef-closed-identity-open-hom-normalization).

The identity-open identifications below are constructed by adjunction uniqueness and
termwise descent. The property retains the actual comparison maps and Hom bijection.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Remove identity etale extension by zero using its specified adjunction.
Source: identity-open specialization of thm-sf-ambient-adjoint-class.proof.md
(blueprint: lem-coef-closed-identity-open-hom-normalization). -/
def closedIdentityOpenEtaleIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z P : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i] :
    Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper i) ≅
      (Etale.lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
          (Adjunction.leftAdjointIdIso
            (Etale.openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 Z))
            (Etale.upperStarId (ModuleCat.{u + 1} A) Z)) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫
    Functor.leftUnitor _

/-- Remove identity pro-etale extension by zero using its specified adjunction.
Source: identity-open specialization of thm-sf-ambient-adjoint-class.proof.md
(blueprint: lem-coef-closed-identity-open-hom-normalization). -/
def closedIdentityOpenProEtaleIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z P : Scheme.{u}} (i : Z ⟶ P) [IsClosedImmersion i] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
        (Compactification.ofIsProper i) ≅
      (lowerStar (ModuleCat.{u + 1} A) i).rightDerivedFunctor :=
  Functor.isoWhiskerRight
      (Functor.mapDerivedCategoryNatIso
          (Adjunction.leftAdjointIdIso
            (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) (𝟙 Z))
            (upperStarId (ModuleCat.{u + 1} A) Z)) ≪≫
        Functor.mapDerivedCategoryIdIso _) _ ≪≫
    Functor.leftUnitor _

/-- The exact assertions of the identity-open normalization, in the fixed ordinary
constant-module presentation. The scalar lift is only the site's coefficient-size
convention. All functors, units, comparisons and relative bijections are existing
specified constructions; the two right adjoints are identified by the counit-compatible
adjunction comparison. Source: displayed chain in thm-sf-ambient-adjoint-class.proof.md
(blueprint: lem-coef-closed-identity-open-hom-normalization). -/
def closedIdentityOpenHomNormalizationProperty
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {Z P : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of D.k)) (aP : P ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    [LocallyOfFiniteType aP] [QuasiCompact aP] [IsSeparated aP]
    (i : Z ⟶ P) [IsClosedImmersion i] : Prop :=
  let A := ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)
  letI : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  letI : Finite A := inferInstance
  letI : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace aP
  let c := Compactification.ofIsProper i
  let C := ModuleCat.{u + 1} A
  let F := (Etale.lowerStar C i).rightDerivedFunctor
  let Q := (lowerStar C i).rightDerivedFunctor
  let I := F.rightAdjoint
  let SZ := (comparisonUpperStar C Z).mapDerivedCategory
  let SP := (comparisonUpperStar C P).mapDerivedCategory
  let UP := (comparisonLowerStar C P).rightDerivedFunctor
  let J := UP ⋙ I ⋙ SZ
  let β := Adjunction.ofIsLeftAdjoint F
  let η := (derivedComparisonAdjunction C P).unit
  let e := closedIdentityOpenEtaleIso A i
  let q := closedIdentityOpenProEtaleIso A i
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A c
  let adjc := Adjunction.ofIsLeftAdjoint
    (Etale.rightDerivedLowerShriekOfCompactification C c)
  let r := (adjc.ofNatIsoLeft e).rightAdjointUniq β
  ∀ (H : DerivedCategory.Plus (Sheaf P.smallEtaleTopology C))
    (hIH : DerivedCategory.TStructure.t.plus (I.obj H.obj)),
    DerivedCategory.TStructure.t.plus (I.obj (UP.obj (SP.obj H.obj))) ∧
    IsIso (SZ.map (I.map (η.app H.obj))) ∧
    (∃ hJ : DerivedCategory.TStructure.t.plus (J.obj (SP.obj H.obj)),
      ∃ W : Scheme.FixedEtaleOriginWitness Z A ⟨J.obj (SP.obj H.obj), hJ⟩,
        W.complex = ⟨I.obj H.obj, hIH⟩ ∧
        HEq W.iso.hom (SZ.map (I.map (η.app H.obj)))) ∧
    ∀ L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology C),
      q.inv.app (SZ.obj L.obj) ≫ (compactSupportSiteComparison A c).hom.app L ≫
          SP.map (e.hom.app L.obj) = (fixedDirectImageComparisonIso A i).inv.app L ∧
      ∀ g : Q.obj (SZ.obj L.obj) ⟶ SP.obj H.obj,
        specifiedExceptionalHomEquiv A c
            ((siteComparisonDerivedPullbackPlus Z A).obj L)
            ⟨L, Iso.refl _⟩ ((siteComparisonDerivedPullbackPlus P A).obj H)
            (q.hom.app (SZ.obj L.obj) ≫ g) ≫
          SZ.map (r.hom.app (UP.obj (SP.obj H.obj))) =
        SZ.map ((β.homEquiv L.obj (UP.obj (SP.obj H.obj)))
          (η.app (F.obj L.obj) ≫
            UP.map ((fixedDirectImageComparisonIso A i).hom.app L ≫ g)))

/-- Identity-open normalization and domains of the closed exceptional Hom chain.
Source: main-20261015 blueprint, thm-sf-ambient-adjoint-class.proof.md, displayed
four-factor chain (blueprint: lem-coef-closed-identity-open-hom-normalization).

Proof:
1. The coefficient quotient is finite. The closed immersion is proper, hence qcqs;
   the identity-open compactification applies. Finite type over k gives finite
   dimension (including the empty source) and quasi-compactness of P.
2. The actual comparison unit at H is invertible. Applying I identifies IU_PS_PH
   with the assumed bounded-below IH. Applying exact S_Z gives alpha and its inverse,
   with retained antecedent IH, and proves boundedness of its target.
3. Composition coherence for the exact open comparison makes its identity-open
   component idempotent; invertibility makes it the identity. Thus the forward
   compact-support comparison is precisely the named direct-image counit mate delta,
   and the comparison in the statement is delta inverse.
4. Expand the specified relative bijection at the identity witness. Its factors are
   precomposition by delta, the comparison adjunction with formula eta followed by
   U_P on morphisms, the ordinary exceptional adjunction beta, and S_Z on morphisms.
   The counit-compatible uniqueness comparison identifies the two etale adjoints.
   The intermediate target IU_PS_PH is bounded below by step 2, and FL is bounded
   below by ordinary direct image, so full faithfulness applies. These are exactly
   the four factors of the boundary exceptional Hom transport, with no conjugation
   from the identity witness. -/
theorem closedIdentityOpenHomNormalization
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) {Z P : Scheme.{u}}
    (aZ : Z ⟶ Spec (.of D.k)) (aP : P ⟶ Spec (.of D.k))
    [LocallyOfFiniteType aZ] [QuasiCompact aZ] [IsSeparated aZ]
    [LocallyOfFiniteType aP] [QuasiCompact aP] [IsSeparated aP]
    (i : Z ⟶ P) [IsClosedImmersion i] (_hi : i ≫ aP = aZ) :
    closedIdentityOpenHomNormalizationProperty D l E n hn aZ aP i := by
  sorry

end AlgebraicGeometry.ProEtale
