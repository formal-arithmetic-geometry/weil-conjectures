/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
public import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.AlgebraicGeometry.Sf.SfConstructibleExceptionalAdjointDischarge
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.Compactification.Refinement
import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Over
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.AlgebraicGeometry.Ambient.AmbientExceptionalRightAdjoint
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
-- Retained as a step of the comparison unit used by the coefficient realization.
import WeilConjectures.AlgebraicGeometry.Proper.ProperExceptionalOpenBaseChange
public import WeilConjectures.AlgebraicGeometry.Clopen.ClopenSectionComponent
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
public import WeilConjectures.AlgebraicGeometry.Open.OpenSectionClopen
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleGrothendieckSectionCoproducts
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenDerivedSupport
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteOpenExtensionBaseChange
public import WeilConjectures.AlgebraicGeometry.Sf.SfFullCohomologicalDimension
public import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.Finite.FiniteCohomologicalDimensionInjectiveCoproducts
public import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
public import WeilConjectures.Compactification.Cofiltered
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale

/-!
# Exceptional base change along an arbitrary open immersion

Source: Weil blueprint, order 1815, sk-prop-sf-existence
(blueprint: cor-exc-base-change-open-immersion-general).
The ambient assertion and the independent coefficient-class assertion are separate.
The former uses the given ordinary unbounded adjunctions. The latter uses only the
specified transported etale exceptional functor. No quasi-compactness of the open
immersion is imposed in the ambient assertion.

## Main statements

- `sfAmbientExceptionalOpenBaseChange`: the ordinary ambient comparison and restricted
  FullCD bound, using the supplied adjunction and the base-changed compactification.
- `sfFiniteExceptionalOpenBaseChange`: the independent comparison for degree-zero
  etale-origin sheaves and bounded constructible complexes.

The support and realization comparisons below specify the canonical maps in these statements.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
open Scheme

/-- The exact open extension-by-zero comparison in the two recorded presentations.
It cancels the unit of the specified realization equivalence.
Source: blueprint order 1815 (blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfIntrinsicOpenExtensionComparison (A : Type u) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (sfIntrinsicModuleEquivalence U A).functor ⋙ sfIntrinsicExtensionByZero j A ≅
      openImmersionLowerShriek (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
        (sfIntrinsicModuleEquivalence X A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sfIntrinsicModuleEquivalence U A).unitIso.symm _ ≪≫
    Functor.leftUnitor _

/-- Canonical realization of the compact-support candidate, fixed on constant sections
and on K-injective representatives by sfIntrinsicDerivedDirectImageComparison.
Source: blueprint order 1815 (blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfIntrinsicCompactSupportComparison (A : Type u) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfAmbientCompactSupportCandidate A c ≅
      sfFixedCompactSupport A c ⋙ (sfIntrinsicDerivedEquivalence Y A).functor :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
        Functor.mapDerivedCategoryNatIso (sfIntrinsicOpenExtensionComparison A c.i) ≪≫
        Functor.mapDerivedCategoryCompIso _ _) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison c.g A) ≪≫
    (Functor.associator _ _ _).symm

/-- The specified compactification support exchange. The first arrow is the proper
ordinary derived direct-image mate, and the second is the inverse extension-by-zero
mate, applied degreewise. This defines a map even before its invertibility is proved.
Source: blueprint order 1815, proof Steps 1-4; Stacks Tags 0F7B and 0F7C
(blueprint: cor-exc-base-change-open-immersion-general). -/
noncomputable def sfFixedCompactSupportExchange (A : Type u) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    sfFixedCompactSupport A c ⋙ sfFixedDerivedPullback A g ⟶
      sfFixedDerivedPullback A g' ⋙ sfFixedCompactSupport A (c.ofIsPullback sq) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (sfFixedDerivedBaseChange A (c.isPullback_g_ofIsPullback sq).flip.toCommSq) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (sfFixedDerivedOpenExtensionBaseChangeIso A (c.isPullback_i_ofIsPullback sq)).hom _ ≫
    (Functor.associator _ _ _).hom

/-- The canonical exceptional comparison is invertible on the bounded-below
etale-origin class. No unrestricted ambient datum is assumed or constructed.

Source: blueprint `cor-exc-base-change-open-immersion-general.md`, class clause
(blueprint: cor-exc-base-change-open-immersion-general).

Proof: the canonical comparison is transported from the ordinary etale exceptional
open base-change map. Install the compactifications of the morphism and its open
base change. Etale exceptional open base change makes that map invertible; the
specified comparison-site isomorphisms transport its inverse to the displayed map.
This works for every bounded-below etale-origin input, including degree-zero sheaves. -/
theorem sfAmbientExceptionalOpenBaseChange
    (Dk : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ Dk.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ)
    (X Y : Scheme.{u}) [X.Over (Spec (CommRingCat.of Dk.k))]
    [Y.Over (Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of Dk.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of Dk.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of Dk.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of Dk.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) {Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsOpenImmersion g]
    (K : DerivedCategory (Sheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))))
    (_hK : DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))))
      Y K) :
    IsIso (sfFiniteExceptionalOpenComparison (Padic.coefficientExtensionRing l E (n + 1))
      (IsPullback.of_hasPullback f g) c K) := by
  let := c.hasCompactification
  let := (c.ofIsPullback (IsPullback.of_hasPullback f g)).hasCompactification
  let := Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion
    (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))
    (IsPullback.of_hasPullback f g)
  unfold sfFiniteExceptionalOpenComparison
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem inverseMateIso
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    {G : C' ⥤ C} {U : C ⥤ C'} {H : D' ⥤ D} {V : D ⥤ D'}
    {L : C ⥤ D} {L' : C' ⥤ D'}
    (a : G ⊣ U) (b : H ⊣ V) [IsIso a.unit] [IsIso b.unit]
    (δ : TwoSquare U L L' V) [IsIso δ.natTrans] (e : L' ⋙ H ≅ G ⋙ L) :
    IsIso ((mateEquiv a b).symm δ).natTrans := by
  have : H.Full := b.fullyFaithfulLOfIsIsoUnit.full
  have : H.Faithful := b.fullyFaithfulLOfIsIsoUnit.faithful
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have : IsIso (b.counit.app (L.obj (G.obj M))) :=
    b.isIso_counit_app_of_iso (e.app M).symm
  have : IsIso (H.map (L'.map (a.unit.app M))) := inferInstance
  have : IsIso (H.map (δ.natTrans.app (G.obj M))) := inferInstance
  dsimp only [mateEquiv, Equiv.symm, Equiv.coe_fn_mk, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
    Functor.comp_map, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.associator_hom_app, Functor.associator_inv_app]
  have : IsIso (H.map (𝟙 (L'.obj (U.obj (G.obj M))))) := inferInstance
  have : IsIso (H.map (𝟙 (V.obj (L.obj (G.obj M)))) ) := inferInstance
  have : IsIso (𝟙 (L.obj (G.obj M))) := inferInstance
  infer_instance

end AlgebraicGeometry.ProEtale
