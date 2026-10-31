/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityAffineLineOrientationData

/-! # Site comparison and affine-line open localization

Source: the coordinate localization in the affine-line purity proof.
(blueprint: lem-pur-orientation-open-localization-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- The explicit Gysin localization map on an arbitrary open cohomology class.
Source: the localization used in gysinKummerSection.
(blueprint: lem-pur-orientation-open-localization-comparison). -/
def orientationOpenClassTransport (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (D : OrientationSupportData P h Y) :
    (hyper P (Punctured Y) 1).obj (P.derivedSheaf h (Punctured Y) true) ⟶
      (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology (Line Y)) (Modules P)
        (Scheme.ProEt.mk (zeroSection Y).openComplement.ι) 1).obj (P.gysinInput h Y) :=
  let j := openImmersion Y
  let V := upperStar (Modules P) j
  let E := globalSectionsFunctor (Modules P) (Punctured Y)
  letI := (openImmersionLowerShriekUpperStarAdjunction (Modules P) j).preservesKInjectiveComplexes
  let e := Functor.isoWhiskerRight V.rightDerivedFunctorIsoMapDerivedCategory.symm
      E.rightDerivedFunctor ≪≫
    Functor.rightDerivedFunctorCompIso' V E (openSectionsIso P j)
  (DerivedCategory.homologyFunctor (Modules P) 1).map
      (E.rightDerivedFunctor.map D.openCoefficient.inv ≫
        e.hom.app (P.gysinInput h Y).obj) ≫
    (sectionPlusIso P (Line Y) (Scheme.ProEt.mk j) 1).hom.app (P.gysinInput h Y) ≫
    (complementSectionsIso P (zeroSection Y) j D.comparison.complement 1).hom.app
      (P.gysinInput h Y)

/-- The etale localization map on an arbitrary H1 class of the root coefficient.
Source: the localization used in coordinateEtaleOpenClass.
(blueprint: lem-pur-orientation-open-localization-comparison). -/
def coordinateEtaleOpenClassTransport (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (eU : Scheme.Etale.mk (openImmersion Y) ≅
      Scheme.Etale.mk (zeroSection Y).openComplement.ι) :
    (Sheaf.sectionHypercohomologyFunctor (Punctured Y).smallEtaleTopology (Modules P)
      (Scheme.Etale.mk (𝟙 (Punctured Y))) 1).obj
        (P.coordinateEtaleInput h (Punctured Y)) ⟶
      (Sheaf.sectionHypercohomologyFunctor (Line Y).smallEtaleTopology (Modules P)
        (Scheme.Etale.mk (zeroSection Y).openComplement.ι) 1).obj
          (P.coordinateEtaleInput h (Line Y)) :=
  let j := openImmersion Y
  let E := Etale.sectionsFunctor (Modules P) (Punctured Y)
  letI := P.isIso_twistEtalePullback h j
    (P.exponent_isUnit (Line Y) (lineProjection Y ≫ a))
  let b := (DerivedCategory.Plus.singleFunctor _ 0).map
      (inv (P.twistEtalePullback h j)) ≫
    (Functor.mapDerivedCategoryPlusSingleFunctor (Etale.upperStar (Modules P) j)
      0).inv.app (P.twistEtale h (Line Y))
  (DerivedCategory.Plus.homologyFunctor (Modules P) 1).map
      (E.rightDerivedFunctorPlus.map b ≫
        (P.coordinateOpenDerivedIso j).hom.app (P.coordinateEtaleInput h (Line Y))) ≫
    (Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusNatIso
        (F := sheafToPresheaf (Line Y).smallEtaleTopology (Modules P) ⋙
          (evaluation _ _).obj (op (Scheme.Etale.mk j)))
        (G := sheafToPresheaf (Line Y).smallEtaleTopology (Modules P) ⋙
          (evaluation _ _).obj (op (Scheme.Etale.mk (zeroSection Y).openComplement.ι)))
        ((sheafSections (Line Y).smallEtaleTopology (Modules P)).mapIso eU.op).symm)
      (DerivedCategory.Plus.homologyFunctor (Modules P) 1)).hom.app
        (P.coordinateEtaleInput h (Line Y))

/-- Localization and the canonical finite site comparison commute as maps on H1.
This statement concerns all input cohomology classes, independently of the Kummer
Ext evaluation and of either supported boundary.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
thm-pur-affine-line-orientation.proof.md, coordinate localization and finite
etale-origin transport; Stacks, Tag 099W.
Proof: write both section comparison maps as the right-derived base change of the
comparison adjunction unit. The underived open square commutes by the canonical
comparisonUpperStarCompUpperStarIso: both mates are restriction of this same unit.
Apply uniqueness of right-derived transformations to the etale section functor.
The unit factorization equations of derived base change and derived composition
reduce equality to the underived open square followed by the target derived unit.
The exact open inverse images preserve injectives, as they have exact left adjoints;
this supplies the required composition isomorphisms on both sites. This argument does
not require comparison inverse image to preserve injectives. Use
D.openCoefficient_spec to replace its coefficient map
by the canonical root-pullback composite; invert its isomorphism and use naturality
of the comparison on the twist. The exact single-complex comparisons and the
bounded-below/unbounded compatibility cancel. Finally the two identifications of the
open complement agree by uniqueness of the isomorphism over the line. Taking H1 gives
the displayed equality of module morphisms.
(blueprint: lem-pur-orientation-open-localization-comparison). -/
theorem orientation_open_localization_comparison (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (D : OrientationSupportData P h Y) (M : CoordinateBoundaryModel P Y) :
    (finiteComparisonSectionHypercohomology (Punctured Y) P.Coefficient
        (Scheme.Etale.mk (𝟙 (Punctured Y))) 1).app
          (P.coordinateEtaleInput h (Punctured Y)) ≫
      (Sheaf.sectionHypercohomologyFunctor (Scheme.ProEt.topology (Punctured Y))
        (Modules P) (Scheme.ProEt.mk (𝟙 (Punctured Y))) 1).map
          (((comparisonUpperStar (Modules P) (Punctured Y)).mapDerivedCategoryPlusSingleFunctor
            0).hom.app (P.twistEtale h (Punctured Y))) ≫
      (sectionPlusIso P (Punctured Y) (Scheme.ProEt.mk (𝟙 (Punctured Y))) 1).inv.app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj (P.twist h (Punctured Y))) ≫
      P.orientationOpenClassTransport h Y D =
    P.coordinateEtaleOpenClassTransport h Y a M.complementIso ≫
      (finiteComparisonSectionHypercohomology (Line Y) P.Coefficient
        (Scheme.Etale.mk (zeroSection Y).openComplement.ι) 1).app
          (P.coordinateEtaleInput h (Line Y)) := by
  sorry

end WeilConjectures.PurityFiniteSetting
