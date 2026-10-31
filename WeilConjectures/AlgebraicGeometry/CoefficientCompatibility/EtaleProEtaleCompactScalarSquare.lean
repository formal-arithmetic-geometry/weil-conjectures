/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
import all WeilConjectures.AlgebraicGeometry.Sp.SpDirectImageEtaleMate
import all WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedCompactScalarNormalization

/-! # The normalized compact-support scalar/site equation

Source: Stacks Project, Tag 0GL6, and the proper/open mate pasting of the
Charts paragraph of the blueprint's reduction-exceptional proof.
(blueprint: lem-sp-transported-compact-scalar-site-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

attribute [local irreducible] transportedRecordedReductionDirectImageComparison
  compactSupportSiteComparison comparisonUpperStar pbcComparisonReduction
  Etale.compactScalarMap Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor pbcFixedScalarExtension DerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.TStructure.t

private theorem proEtEssentiallySmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

attribute [local instance] proEtEssentiallySmall

-- The bounded-below compact comparison uses the same ambient proper counit mate.
private theorem compactComparison_inv
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (compactSupportSiteComparison A c).inv.app L =
      (directImageComparisonAmbient A c.g).app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
            L.obj) ≫
        (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map
          ((mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} A) c.i).hom.app L.obj) := by
  rw [← compactSupportComparisonNormalization]
  have h := sp_comparison_hom A c.g
    ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
      L.obj)
    (Etale.exact_open_preserves_plus A c.i L)
  have hh : (spDirectImageComparisonIso A c.g
      ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
        L.obj) (Etale.exact_open_preserves_plus A c.i L)).hom =
      (directImageComparisonAmbient A c.g).app
        ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj
          L.obj) := by
    simpa only [BoundaryComparison.directImageMate, BoundaryComparison.pullbackSquare,
      directImageComparisonAmbient, directImageComparisonAmbientPullbackIso,
      leftDerivedUpperStarIsoMapDerivedCategory, Etale.leftDerivedUpperStarIsoMapDerivedCategory,
      BoundaryComparison.comparison, TwoSquare.mk, TwoSquare.natTrans] using h
  rw [← hh]
  simp only [fixedCompactSupportComparisonIso, fixedDirectImageComparisonIso,
    spDirectImageComparisonIso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.map_comp, Functor.mapIso_hom,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id, Category.assoc,
    asIso_hom, mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso]
  rw [← Functor.mapDerivedCategoryNatIso_symm]
  dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift, Functor.comp_obj,
    DerivedCategory.Plus.ι, ObjectProperty.ι_obj]
  simp only [Iso.symm_symm_eq, Category.id_comp]
  erw [((Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor ⋙
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory).map_id]
  erw [(lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor.map_id]
  erw [((comparisonUpperStar (ModuleCat.{u + 1} A) c.Z).mapDerivedCategory ⋙
    (lowerStar (ModuleCat.{u + 1} A) c.g).rightDerivedFunctor).map_id]
  repeat erw [Category.id_comp]

private def fixedCompactScalarMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        pbcFixedScalarExtension.{u} (Scheme.ProEt.topology Y) a ⟶
      pbcFixedScalarExtension.{u} (Scheme.ProEt.topology X) a ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c :=
  whiskerLeft (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
      (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) c.g)
        (TwoSquare.mk _ _ _ _ (scalarPullbackProEtaleIso a c.g).hom)).natTrans ≫
    whiskerRight (OpenScalarSite.scalarOpen a c.i).hom
      (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor

private theorem fixedCompactScalar_site_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (a : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hLB : DerivedCategory.TStructure.t.plus ((Etale.scalarExtension a X).obj L.obj)) :
    (pbcFixedScalarExtension.{u} (Scheme.ProEt.topology Y) a).map
        ((compactSupportSiteComparison A c).inv.app L) ≫
      (fixedCompactScalarMap a c).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c).map
        ((pbcComparisonReduction X a).hom.app L.obj) =
    (pbcComparisonReduction Y a).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj
          L.obj) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} B) Y).mapDerivedCategory.map
        ((Etale.compactScalarMap a c).app L.obj) ≫
      (compactSupportSiteComparison B c).inv.app
        ⟨(Etale.scalarExtension a X).obj L.obj, hLB⟩ := by
  let JA := (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
  let RB := (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor
  let T := pbcFixedScalarExtension.{u} (Scheme.ProEt.topology Y) a
  let γ := (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) c.g)
    (TwoSquare.mk _ _ _ _ (scalarPullbackProEtaleIso a c.g).hom)).natTrans
  let oA := (mapDerivedCategoryOpenImmersionLowerShriekComparisonUpperStarIso
    (ModuleCat.{u + 1} A) c.i).hom.app L.obj
  let eB := (Etale.ExceptionalCoefficients.openIso a c.i).hom.app L.obj
  have hJ := Etale.exact_open_preserves_plus A c.i L
  have hBJ := Etale.scalar_open_preserves_plus a c.i L hLB
  have hm := etaleProEtale_scalar_mate a c.g (JA.obj L.obj) hJ hBJ
  have hp := congrArg (fun q ↦ T.map
    ((directImageComparisonAmbientIso A c.g (JA.obj L.obj) hJ).hom) ≫ q) hm
  dsimp only [T] at hp
  simp only [directImageComparisonAmbientIso, asIso_hom, asIso_inv,
    ← Functor.map_comp_assoc, IsIso.hom_inv_id] at hp
  erw [(pbcFixedScalarExtension.{u} (Scheme.ProEt.topology Y) a).map_id,
    Category.id_comp] at hp
  have ho := OpenScalarSite.scalar_site_square_aux a c.i L.obj
  rw [← Etale.compactScalarOpen_eq] at ho
  have hn := γ.naturality oA
  dsimp only [Functor.comp_map] at hn
  have hb := (directImageComparisonAmbient B c.g).naturality eB
  dsimp only [Functor.comp_map] at hb
  rw [compactComparison_inv, compactComparison_inv]
  dsimp only [fixedCompactScalarMap, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, rightDerivedLowerShriekOfCompactification, Functor.comp_map]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [← RB.map_comp, ← RB.map_comp, ho]
  simp only [Functor.map_comp]
  rw [reassoc_of% hp]
  rw [← reassoc_of% hb]
  simp only [Etale.compactScalarMap, Etale.ExceptionalCoefficients.compactSupportMap,
    Etale.scalarMate, scalarPullbackEtaleIso, Functor.map_comp, Category.assoc, eB, JA, RB,
    Etale.scalarExtension, Etale.rightDerivedLowerShriekOfCompactification, Functor.comp_obj]

/-- The genuine intrinsic coefficient arrow, transported to fixed modules, obeys
proper/open scalar/site pasting on a bounded-below input whose actual scalar
extension is also bounded below. This asserts equality of the specified maps only;
it asserts neither coefficient arrow is invertible and needs no arithmetic or
constructibility hypothesis.

Source: Stacks Project, more-etale.tex, Tag 0GL6; blueprint
sk-lem-sp-reduction-exceptional, Charts; Steps 2--4 of
lem-sp-et-proet-coefficient-compatibility.
(blueprint: lem-sp-transported-compact-scalar-site-square).

Proof: put J = j_!L. Exact open extension makes J bounded below. The scalar/open
isomorphism identifies the scalar extension of J with j_! of the scalar extension
of L, so that it too is bounded below. Apply etaleProEtale_scalar_mate to J and
the proper map. The ambient direct-image comparison on these inputs is the
bounded-below canonical counit mate: identify their pullback squares using the
exact-derived localization factors, then transpose their counit equations.
Take left mates of the scalar/pullback cube along the two open adjunctions.
Their unit equations identify the open mates with the specified scalar/open and
site/open maps, giving the open scalar/site equation for this input.
Naturality of the proper scalar mate and the proper site mate moves
the open comparisons past them. Expand compactSupportSiteComparison and cancel
the bounded-below inclusion factors; their compatibility isomorphisms preserve
these mates. This yields the scalar/site square for the fixed-module proper mate
followed by the proper image of the open tensor map. To identify that composite
with the transported recorded arrow, apply the fully faithful intrinsic realization
at Y. Expand the defining preimage, supportPresentation and scalarPresentation.
The direct-image presentation is right-adjoint uniqueness through the uniquely
unit-normalized pullback coordinates, so its proper square is the same counit
mate square. The open presentation cancels the realization unit; uniqueness of
left adjoints identifies its open tensor map with reductionOpenScalarIso. The
section-identity restriction comparison fixing scalarPresentation preserves the
scalar unit. Thus the two realized composites are equal by proper counit
transposition and open unit transposition. Faithfulness gives the desired fixed
map equation. None of these operations inverts a coefficient mate; they invert
only the specified site, scalar/site, and presentation isomorphisms. -/
theorem transportedCompactScalar_site_square
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (hLB : DerivedCategory.TStructure.t.plus
      ((Etale.scalarExtension (uliftRingHom φ) X).obj L.obj)) :
    (liftedScalarExtension φ Y).map
        ((compactSupportSiteComparison (ULift.{u + 1, u} A) c).inv.app L) ≫
      (transportedRecordedReductionDirectImageComparison φ c
        (reductionDirectImageComparison φ c.i c.g)).app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj
            L.obj) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).map
        ((pbcComparisonReduction X (uliftRingHom φ)).hom.app L.obj) =
    (pbcComparisonReduction Y (uliftRingHom φ)).hom.app
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj L.obj) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategory.map
        ((Etale.compactScalarMap (uliftRingHom φ) c).app L.obj) ≫
      (compactSupportSiteComparison (ULift.{u + 1, u} B) c).inv.app
        ⟨(Etale.scalarExtension (uliftRingHom φ) X).obj L.obj, hLB⟩ := by
  rw [recordedCompactScalar_fixed_normalization]
  exact fixedCompactScalar_site_square (uliftRingHom φ) c L hLB

end AlgebraicGeometry.ProEtale.CoefficientCompatibility
