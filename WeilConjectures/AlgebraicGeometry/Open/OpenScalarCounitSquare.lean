/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
public import WeilConjectures.AlgebraicGeometry.OpenScalarTensor.OpenScalarTensorData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZero
import WeilConjectures.AlgebraicGeometry.Open.OpenScalarRestrictionUnit
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Open extension preserves the normalized scalar counit

Source: Stacks Project, sites-modules.tex, Tag 0E8I; sites-cohomology.tex, Tag 07A6;
blueprint, det-sp-tower-gluing, Levels paragraph
(blueprint: lem-sp-open-scalar-counit-square).

All categories are ordinary uncompleted unbounded constant-ring module derived categories.
The open extension, scalar restriction square and tensor square are the published ones.
Unit equations express identity comparisons on the open without identifying distinct
functors by definitional equality. Naturality is retained at the natural-transformation level.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

set_option backward.defeqAttrib.useBackward true in

/-- The exact open adjunction in the recorded sheafified extension coordinates.
The coordinate change is the unit-preserving uniqueness map `reductionOpenModel`.
Consequently this unit is the sectionwise open unit, descended termwise.
Source: Stacks Tags 03DI, 03DJ and 07A6
(blueprint: lem-sp-open-scalar-counit-square). -/
def openScalarCounitAdjunction (R : Type u) [CommRing R] [Finite R]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (sfIntrinsicExtensionByZero j R).mapDerivedCategory ⊣ constantPullback (A := R) j :=
  (OpenScalarTensor.openAdj R j).ofNatIsoLeft (reductionOpenModel R j).symm

private theorem scalarOpenTranspose
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {LA : C ⥤ D} {JA : D ⥤ C} {LB : E ⥤ F} {JB : F ⥤ E}
    {SX : D ⥤ F} {RX : F ⥤ D} {SU : C ⥤ E} {RU : E ⥤ C}
    (a : LA ⊣ JA) (b : LB ⊣ JB) (x : SX ⊣ RX) (u : SU ⊣ RU)
    (q : JB ⋙ RU ≅ RX ⋙ JA) (K : C) :
    b.unit.app (SU.obj K) ≫ JB.map
        (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K) =
      SU.map (a.unit.app K) ≫
        ((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).natTrans.app (LA.obj K) := by
  apply (u.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((u.comp b).ofNatIsoRight q) (a.comp x) K
  change ((u.comp b).ofNatIsoRight q).unit.app K ≫
      (RX ⋙ JA).map
        (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K) =
      (a.comp x).unit.app K at h
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Functor.comp_map,
    Category.assoc] at h
  have hn := q.hom.naturality
    (((a.comp x).leftAdjointUniq ((u.comp b).ofNatIsoRight q)).inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [Functor.comp_obj] at h
  rw [← hn] at h
  have hm := unit_mateEquiv_symm x u (TwoSquare.mk _ _ _ _ q.inv) (LA.obj K)
  change JA.map (x.unit.app (LA.obj K)) ≫ q.inv.app (SX.obj (LA.obj K)) =
    u.unit.app (JA.obj (LA.obj K)) ≫ RU.map
      (((mateEquiv x u).symm (TwoSquare.mk _ _ _ _ q.inv)).natTrans.app (LA.obj K)) at hm
  have hu := u.unit.naturality (a.unit.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj] at hu
  rw [← reassoc_of% hu, ← hm]
  apply (cancel_mono (q.hom.app (SX.obj (LA.obj K)))).1
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj,
    Adjunction.comp_unit_app] using h

private theorem transportTensorUnit
    {UA ZA UB ZB : Type*} [Category UA] [Category ZA] [Category UB] [Category ZB]
    {LA IA : UA ⥤ ZA} {LB IB : UB ⥤ ZB} {vA : ZA ⥤ UA} {vB : ZB ⥤ UB}
    {TZ : ZA ⥤ ZB} {TX : UA ⥤ UB}
    (a : LA ⊣ vA) (b : LB ⊣ vB) (eA : IA ≅ LA) (eB : IB ≅ LB)
    (beta : LA ⋙ TZ ≅ TX ⋙ LB) (lam : TZ ⋙ vB ≅ vA ⋙ TX)
    (h : ∀ K, b.unit.app (TX.obj K) ≫ vB.map (beta.inv.app K) =
      TX.map (a.unit.app K) ≫ lam.inv.app (LA.obj K)) (K : UA) :
    (b.ofNatIsoLeft eB.symm).unit.app (TX.obj K) ≫ vB.map
        ((Functor.isoWhiskerRight eA TZ ≪≫ beta ≪≫
          Functor.isoWhiskerLeft TX eB.symm).inv.app K) =
      TX.map ((a.ofNatIsoLeft eA.symm).unit.app K) ≫ lam.inv.app (IA.obj K) := by
  simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app,
    Iso.symm_hom, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Iso.symm_inv,
    Functor.map_comp, Category.assoc]
  rw [← vB.map_comp_assoc, Iso.inv_hom_id_app, vB.map_id, Category.id_comp, reassoc_of% (h K)]
  have hn := lam.inv.naturality (eA.inv.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hn]

/-- The specified scalar restriction and tensor comparisons restrict to identity
comparisons, written with their canonical open units and scalar/pullback identifications.
Source: Stacks Tags 03DI, 0E8I and 07A6
(blueprint: lem-sp-open-scalar-counit-square).

Proof: openScalarRestrictionUnit supplies the first equation in the prescribed constant
pullback coordinates. For the tensor equation, apply scalarOpenTranspose to the two open
and two scalar adjunctions: the unit equation of left-adjoint uniqueness, the scalar mate
unit equation and naturality identify the inverse open comparison's transpose. Transport
both left adjoints through reductionOpenModel; naturality of inverse lambda and cancellation
of the two B-coordinate changes give precisely the second displayed equation. -/
theorem openScalarCounitRestriction
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (∀ L : proEtaleDerivedCategory X B,
      (openScalarCounitAdjunction A j).unit.app ((scalarRestriction φ X).obj L) ≫
          (constantPullback (A := A) j).map ((sfOpenRestrictionDerived j φ).hom.app L) ≫
          (OpenScalarTensor.rightSquare φ j).inv.app
            ((sfIntrinsicExtensionByZero j B).mapDerivedCategory.obj L) =
        (scalarRestriction φ X).map ((openScalarCounitAdjunction B j).unit.app L)) ∧
    (∀ M : proEtaleDerivedCategory X A,
      (openScalarCounitAdjunction B j).unit.app ((scalarExtensionFunctor φ X).obj M) ≫
          (constantPullback (A := B) j).map ((reductionOpenScalarIso φ j).inv.app M) =
        (scalarExtensionFunctor φ X).map ((openScalarCounitAdjunction A j).unit.app M) ≫
          (tensorPullbackIso φ j).inv.app
            ((sfIntrinsicExtensionByZero j A).mapDerivedCategory.obj M)) := by
  refine ⟨?_, ?_⟩
  · exact openScalarRestrictionUnit φ j
  · intro M
    apply transportTensorUnit (OpenScalarTensor.openAdj A j)
      (OpenScalarTensor.openAdj B j) (reductionOpenModel A j) (reductionOpenModel B j)
      (openScalarIso φ j) (tensorPullbackIso φ j)
    intro K
    exact scalarOpenTranspose (OpenScalarTensor.openAdj A j)
      (OpenScalarTensor.openAdj B j)
      (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) φ))
      (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ))
      (OpenScalarTensor.rightSquare φ j) K

private theorem counitSquareOfUnits
    {UA ZA UB ZB : Type*} [Category UA] [Category ZA] [Category UB] [Category ZB]
    {JA : UA ⥤ ZA} {vA : ZA ⥤ UA} {JB : UB ⥤ ZB} {vB : ZB ⥤ UB}
    {TZ : ZA ⥤ ZB} {rZ : ZB ⥤ ZA} {TX : UA ⥤ UB} {rX : UB ⥤ UA}
    (a : JA ⊣ vA) (b : JB ⊣ vB) (z : TZ ⊣ rZ) (x : TX ⊣ rX)
    (q : vB ⋙ rX ≅ rZ ⋙ vA) (lam : TZ ⋙ vB ≅ vA ⋙ TX)
    (alpha : rX ⋙ JA ≅ JB ⋙ rZ) (beta : JA ⋙ TZ ≅ TX ⋙ JB)
    (ha : ∀ L, a.unit.app (rX.obj L) ≫ vA.map (alpha.hom.app L) ≫
      q.inv.app (JB.obj L) = rX.map (b.unit.app L))
    (hb : ∀ M, b.unit.app (TX.obj M) ≫ vB.map (beta.inv.app M) =
      TX.map (a.unit.app M) ≫ lam.inv.app (JA.obj M))
    (hc : ∀ N, lam.inv.app (rZ.obj N) ≫ vB.map (z.counit.app N) =
      TX.map (q.inv.app N) ≫ x.counit.app (vB.obj N)) (L : UB) :
    TZ.map (alpha.hom.app L) ≫ z.counit.app (JB.obj L) =
      beta.hom.app (rX.obj L) ≫ JB.map (x.counit.app L) := by
  apply (cancel_epi (beta.inv.app (rX.obj L))).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [reassoc_of% (hb (rX.obj L))]
  have hn := lam.inv.naturality (alpha.hom.app L)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn, hc]
  rw [← TX.map_comp_assoc, ← TX.map_comp_assoc, Category.assoc, ha]
  have he := x.counit.naturality (b.unit.app L)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at he
  rw [he]
  exact b.unit.naturality (x.counit.app L)

/-- Open extension and scalar restriction preserve the specified derived scalar counit.
This equality of natural transformations includes the equation at every ambient L and
its naturality, with no boundedness, flatness, constructibility or Tor condition.
Source: Stacks Tags 0E8I and 07A6; det-sp-tower-gluing, Levels paragraph
(blueprint: lem-sp-open-scalar-counit-square).

Proof: put f = epsilon_Z(j!_B L) after T_Z(a_L), and g = j!_B(epsilon_X L) after E.
Inverse lambda is definitionally the inverse scalar-adjunction mate of rightSquare.inv.
The Mathlib mate-counit equation therefore gives its scalar counit formula directly.
Precompose f and g with E inverse, and apply the B-open Hom equivalence. The second
equation of openScalarCounitRestriction rewrites the source unit. Naturality of inverse
lambda, its mate-counit formula, the first restriction equation and scalar-counit
naturality make the adjuncts equal. Injectivity and cancellation give f = g. Componentwise
extensionality gives equality of natural transformations for all unbounded derived objects. -/
theorem openScalarCounitSquare
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    Functor.whiskerRight (sfOpenRestrictionDerived j φ).hom (scalarExtensionFunctor φ Z) ≫
        Functor.whiskerLeft (sfIntrinsicExtensionByZero j B).mapDerivedCategory
          (proEtaleRingDerivedExtensionAdjunction
            (proEtaleConstantRingMap (T := Z) φ)).counit =
      Functor.whiskerLeft (scalarRestriction φ X) (reductionOpenScalarIso φ j).hom ≫
        Functor.whiskerRight (proEtaleRingDerivedExtensionAdjunction
          (proEtaleConstantRingMap (T := X) φ)).counit
            (sfIntrinsicExtensionByZero j B).mapDerivedCategory := by
  ext L
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  apply counitSquareOfUnits (openScalarCounitAdjunction A j)
    (openScalarCounitAdjunction B j)
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) φ))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ))
    (OpenScalarTensor.rightSquare φ j) (tensorPullbackIso φ j)
    (sfOpenRestrictionDerived j φ) (reductionOpenScalarIso φ j)
    (openScalarCounitRestriction φ j).1 (openScalarCounitRestriction φ j).2
  intro N
  exact (mateEquiv_counit_symm
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := Z) φ))
    (proEtaleRingDerivedExtensionAdjunction (proEtaleConstantRingMap (T := X) φ))
    (TwoSquare.mk _ _ _ _ (OpenScalarTensor.rightSquare φ j).inv) N).symm

end AlgebraicGeometry.ProEtale
