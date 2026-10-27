/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q117
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
public import WeilConjectures.AlgebraicGeometry.Cohomology.QuasicoherentExtension
public import Sheaf.AlgebraicGeometry.QuasiCoherentGrothendieckGenerators
import Sheaf.AlgebraicGeometry.SchemeDerivedCoheratorAdjunction
import WeilConjectures.AlgebraicGeometry.SupportedOpenUnitConeProperties
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-! # An affine-open criterion for the unbounded quasi-coherent derived comparison

Source: Stacks Project, Derived Categories of Schemes, Tag 09T6,
`perfect-lemma-argument-proves`
(blueprint: lem-sfb-affine-open-derived-qcoh-criterion).

The abelian structures and exactness instances below express the induced abelian
structures specified in the statement. The localization universes are independent.
The universal property is imposed directly on the supplied pair `(Phi, eta)`;
no K-injective resolution in the quasi-coherent subcategory is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u wA wM u1 u2 u3 u4 u5 u6 u7 u8 v1 v2 v3 v4 v5 v6 v7 v8

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Restrict the actual module direct image to quasi-coherent modules when it
preserves quasi-coherence. This is the full-subcategory lift, on objects and maps.
Source: Stacks Project, Tag 09T6, the functor `j_*` in the hypothesis
(blueprint: lem-sfb-affine-open-derived-qcoh-criterion). -/
noncomputable abbrev quasiCoherentModulePushforward {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    (h : ∀ M : (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory,
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj M.obj).IsQuasicoherent) :
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).lift
    ((SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι ⋙
      RingedSpace.moduleDirectImage f.toLRSHom.toShHom) h

/-- Additivity inherited by the full-subcategory lift of module direct image.
Source: Stacks Project, Tag 09T6, the additive functor `j_*`
(blueprint: lem-sfb-affine-open-derived-qcoh-criterion). -/
instance quasiCoherentModulePushforward_additive {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    (h : ∀ M : (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory,
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj M.obj).IsQuasicoherent) :
    (quasiCoherentModulePushforward f h).Additive :=
  inferInstanceAs
    ((SheafOfModules.isQuasicoherent Y.ringCatSheaf).lift
      ((SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι ⋙
        RingedSpace.moduleDirectImage f.toLRSHom.toShHom) h).Additive

/-- The canonical interchange of termwise direct image with full inclusion.
All components are identities on module sheaves, transported through the termwise
composition comparisons. Source: Stacks Project, Tag 09T6, the inclusion square
(blueprint: lem-sfb-affine-open-derived-qcoh-criterion). -/
noncomputable def quasiCoherentPushforwardComplexIso {Z Y : Scheme.{u}} (f : Z ⟶ Y)
    (h : ∀ M : (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory,
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).obj M.obj).IsQuasicoherent) :
    (quasiCoherentModulePushforward f h).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι.mapHomologicalComplex
          (ComplexShape.up ℤ) ≅
      (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι.mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙
        (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
      (F := quasiCoherentModulePushforward f h)
      (G := (SheafOfModules.isQuasicoherent Y.ringCatSheaf).ι)
      (H := (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι ⋙
        RingedSpace.moduleDirectImage f.toLRSHom.toShHom)
      (Iso.refl _) (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (F := (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι)
      (G := RingedSpace.moduleDirectImage f.toLRSHom.toShHom)
      (H := (SheafOfModules.isQuasicoherent Z.ringCatSheaf).ι ⋙
        RingedSpace.moduleDirectImage f.toLRSHom.toShHom)
      (Iso.refl _) (ComplexShape.up ℤ)).symm

/-- The recorded derived direct image with explicit structure-sheaf module carriers.
Source: Stacks Project, Tags 079V and 09T6
(blueprint: lem-sfb-affine-open-derived-qcoh-criterion). -/
noncomputable abbrev quasiCoherentAmbientDerivedPushforward {Z Y : Scheme.{u}}
    [HasDerivedCategory.{wM} (SheafOfModules.{u} Z.ringCatSheaf)]
    [HasDerivedCategory.{wM} (SheafOfModules.{u} Y.ringCatSheaf)] (f : Z ⟶ Y) :
    DerivedCategory (SheafOfModules.{u} Z.ringCatSheaf) ⥤
      DerivedCategory (SheafOfModules.{u} Y.ringCatSheaf) :=
  schemeDerivedDirectImage f

/-- The canonical module-derived comparison on an arbitrary complex, before
choosing any K-injective representative. For a resolution s to J, composing
with Rj_*(Qs) and the inverse unit at J gives precisely Q(j_*s), by naturality.
Source: Stacks Project, Tags 079V and 09T6, canonical derived comparison
(blueprint: lem-sfb-affine-open-derived-qcoh-criterion). -/
@[irreducible] noncomputable def moduleDirectImageDerivedComparison
    {Z Y : Scheme.{u}}
    [HasDerivedCategory.{wM} (SheafOfModules.{u} Z.ringCatSheaf)]
    [HasDerivedCategory.{wM} (SheafOfModules.{u} Y.ringCatSheaf)]
    (f : Z ⟶ Y) (K : CochainComplex (SheafOfModules.{u} Z.ringCatSheaf) ℤ) :
    DerivedCategory.Q.obj
        (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ⟶
      (quasiCoherentAmbientDerivedPushforward f).obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} Y.ringCatSheaf)).inv.app _ ≫
    DerivedCategory.Qh.map
      (((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).inv.app K) ≫
    (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
    (quasiCoherentAmbientDerivedPushforward f).map
      ((DerivedCategory.quotientCompQhIso (SheafOfModules.{u} Z.ringCatSheaf)).hom.app K)

/-- The exact inclusion applied termwise and localized, with its two localization
universes explicitly fixed. Source: Stacks Project, Tag 09T6, the functor i_T
(blueprint: lem-sfb-affine-open-derived-qcoh-criterion). -/
noncomputable abbrev quasiCoherentDerivedInclusion (T : Scheme.{u})
    [HasDerivedCategory.{wA}
      (SheafOfModules.isQuasicoherent T.ringCatSheaf).FullSubcategory]
    [HasDerivedCategory.{wM} (SheafOfModules.{u} T.ringCatSheaf)] :
    DerivedCategory (SheafOfModules.isQuasicoherent T.ringCatSheaf).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{u} T.ringCatSheaf) :=
  Functor.mapDerivedCategory.{wA, wM}
    (SheafOfModules.isQuasicoherent T.ringCatSheaf).ι

/-- The exact-inclusion comparison on complexes, with fixed localization universes.
Source: Stacks Project, Tag 09T6, the termwise inclusion comparison
(blueprint: lem-sfb-affine-open-derived-qcoh-criterion). -/
noncomputable def quasiCoherentDerivedInclusionFactors (T : Scheme.{u})
    [HasDerivedCategory.{wA}
      (SheafOfModules.isQuasicoherent T.ringCatSheaf).FullSubcategory]
    [HasDerivedCategory.{wM} (SheafOfModules.{u} T.ringCatSheaf)] :
    DerivedCategory.Q ⋙ quasiCoherentDerivedInclusion.{u, wA, wM} T ≅
      (SheafOfModules.isQuasicoherent T.ringCatSheaf).ι.mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.mapDerivedCategoryFactors.{wA, wM}
    (SheafOfModules.isQuasicoherent T.ringCatSheaf).ι

/-- Compatibility of a derived functor square with the actual comparison unit.
This is the pointwise equation, with all exact-localization identifications supplied.
Source: Stacks Project, Tag 09T6, normalized commutative square
(blueprint: lem-sfb-affine-open-derived-qcoh-criterion). -/
def DerivedInclusionSquareCompatible
    {A : Type u1} [Category.{v1} A] {B : Type u2} [Category.{v2} B]
    {M : Type u3} [Category.{v3} M] {N : Type u4} [Category.{v4} N]
    {DA : Type u5} [Category.{v5} DA] {DB : Type u6} [Category.{v6} DB]
    {DM : Type u7} [Category.{v7} DM] {DN : Type u8} [Category.{v8} DN]
    (qA : A ⥤ DA) (qB : B ⥤ DB) (qM : M ⥤ DM) (qN : N ⥤ DN)
    (i : A ⥤ M) (j : B ⥤ N) (S : A ⥤ B) (p : M ⥤ N)
    (IA : DA ⥤ DM) (IB : DB ⥤ DN) (Phi : DA ⥤ DB) (R : DM ⥤ DN)
    (eta : S ⋙ qB ⟶ qA ⋙ Phi)
    (a : qA ⋙ IA ≅ i ⋙ qM) (b : qB ⋙ IB ≅ j ⋙ qN)
    (c : Phi ⋙ IB ≅ IA ⋙ R) (d : S ⋙ j ≅ i ⋙ p)
    (unit : ∀ K : M, qN.obj (p.obj K) ⟶ R.obj (qM.obj K)) : Prop :=
  ∀ F : A,
    b.inv.app (S.obj F) ≫ IB.map (eta.app F) ≫ c.hom.app (qA.obj F) ≫
        R.map (a.hom.app F) =
      qN.map (d.hom.app F) ≫ unit (i.obj F)

/-- The universal derived pair and its normalized inclusion-square isomorphism.
This only packages hypotheses (b) and (c) of the affine-open criterion.
Source: Stacks Project, Tag 09T6
(blueprint: lem-sfb-affine-open-derived-qcoh-criterion). -/
structure DerivedInclusionSquareData
    {A : Type u1} [Category.{v1} A] {B : Type u2} [Category.{v2} B]
    {M : Type u3} [Category.{v3} M] {N : Type u4} [Category.{v4} N]
    {DA : Type u5} [Category.{v5} DA] {DB : Type u6} [Category.{v6} DB]
    {DM : Type u7} [Category.{v7} DM] {DN : Type u8} [Category.{v8} DN]
    (qA : A ⥤ DA) (qB : B ⥤ DB) (qM : M ⥤ DM) (qN : N ⥤ DN)
    (i : A ⥤ M) (j : B ⥤ N) (S : A ⥤ B) (p : M ⥤ N)
    (IA : DA ⥤ DM) (IB : DB ⥤ DN) (R : DM ⥤ DN)
    (a : qA ⋙ IA ≅ i ⋙ qM) (b : qB ⋙ IB ≅ j ⋙ qN)
    (d : S ⋙ j ≅ i ⋙ p)
    (unit : ∀ K : M, qN.obj (p.obj K) ⟶ R.obj (qM.obj K)) where
  /-- The supplied total right derived functor. -/
  Phi : DA ⥤ DB
  /-- Its universal comparison unit. -/
  eta : S ⋙ qB ⟶ qA ⋙ Phi
  /-- The total right derived universal property, without resolution assumptions. -/
  universal : ∀ G : DA ⥤ DB,
    Function.Bijective (fun beta : Phi ⟶ G ↦ eta ≫ Functor.whiskerLeft qA beta)
  /-- The derived inclusion square isomorphism. -/
  comparison : Phi ⋙ IB ≅ IA ⋙ R
  /-- Compatibility with the actual canonical module-derived comparison. -/
  compatible : DerivedInclusionSquareCompatible qA qB qM qN i j S p
    IA IB Phi R eta a b comparison d unit

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.lazyProjDelta false in
set_option backward.isDefEq.lazyWhnfCore false in
/-- The affine-open criterion, retaining the resolution normalization of its
comparison isomorphism. The existential proof `h` in the conclusion merely
corestricts the fixed termwise derived inclusion to quasi-coherent cohomology;
the functor is Mathlib's `ObjectProperty.lift`, not an arbitrary equivalence.

Source: Stacks Project, Tag 09T6, `perfect-lemma-argument-proves`, with the
canonical units of Tag 08D8 made explicit
(blueprint: lem-sfb-affine-open-derived-qcoh-criterion).

Proof:
1. Exactness of the inclusion, from `lem-sfb-qcoh-grothendieck-generators` and
   the kernel, cokernel and sum nodes, identifies its derived cohomology with
   included cohomology, so it detects zero objects. Use
   `lem-weil-pbc-exact-functor-derived-factorization` and the adjunction of
   `lem-sfb-scheme-derived-coherator-adjunction`. It suffices to invert its unit
   everywhere and its counit on quasi-coherent cohomology objects.
2. Induct simultaneously on the number of affine opens covering a closed support
   of the two objects. For zero opens the supported objects are zero; detection
   of zero handles the object in the quasi-coherent derived category as well.
3. Remove the last affine open U. The canonical unit comparison in
   `lem-sfb-flat-derived-coherator-interchange`, with the normalization assumed
   here, identifies the derived quasi-coherent open unit with the ambient unit.
   Complete both units to distinguished triangles (`def-weil-triangulated-category`).
4. By `lem-pc-supported-open-unit-cone-properties`, with the restrictions of
   `def-pc-derived-open-restriction-maps`, both cones have quasi-coherent cohomology
   and closed support in T minus U. The induction hypothesis applies to the cones.
5. `lem-sfb-affine-derived-coherator` inverts the unit and counit on U.
   The first two identities of `lem-sfb-flat-derived-coherator-interchange`
   identify the actual unit and counit on the two direct-image terms with
   composites of these isomorphisms, hence invert them.
6. Apply the unit and counit as morphisms of the cone triangles. Their last
   squares commute by the shift compatibility in
   `lem-sfb-scheme-derived-coherator-adjunction`. Two-out-of-three for triangle
   morphisms (`lem-sf-triangle-morphism-iso`) inverts their remaining components.
7. Choose a finite affine open cover by `lem-weil-pbc-qcqs-finite-affine-open-cover`
   and take the closed support to be all of X. The now invertible unit and counit
   restrict the coherator to a quasi-inverse, giving the claimed equivalence.
-/
theorem affineOpen_derived_quasiCoherent_criterion
    [∀ T : Scheme.{u}, HasDerivedCategory.{wA}
      (SheafOfModules.isQuasicoherent T.ringCatSheaf).FullSubcategory]
    [∀ T : Scheme.{u}, HasDerivedCategory.{wM} (SheafOfModules.{u} T.ringCatSheaf)]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (hQC : ∀ U : X.affineOpens,
      ∀ M : (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).FullSubcategory,
        ((RingedSpace.moduleDirectImage U.1.ι.toLRSHom.toShHom).obj M.obj).IsQuasicoherent)
    (hDerived : ∀ U : X.affineOpens, Nonempty (DerivedInclusionSquareData
      (A := CochainComplex
        (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).FullSubcategory ℤ)
      (B := CochainComplex
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ℤ)
      (M := CochainComplex (SheafOfModules.{u} U.1.toScheme.ringCatSheaf) ℤ)
      (N := CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ)
      (DA := DerivedCategory.{wA}
        (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).FullSubcategory)
      (DB := DerivedCategory.{wA}
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
      (DM := DerivedCategory.{wM} (SheafOfModules.{u} U.1.toScheme.ringCatSheaf))
      (DN := DerivedCategory.{wM} (SheafOfModules.{u} X.ringCatSheaf))
      DerivedCategory.Q.{wA} DerivedCategory.Q.{wA}
      DerivedCategory.Q.{wM} DerivedCategory.Q.{wM}
      ((SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).ι.mapHomologicalComplex
        (ComplexShape.up ℤ))
      ((SheafOfModules.isQuasicoherent X.ringCatSheaf).ι.mapHomologicalComplex
        (ComplexShape.up ℤ))
      ((quasiCoherentModulePushforward U.1.ι (hQC U)).mapHomologicalComplex
        (ComplexShape.up ℤ))
      ((RingedSpace.moduleDirectImage U.1.ι.toLRSHom.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ))
      (quasiCoherentDerivedInclusion.{u, wA, wM} U.1.toScheme)
      (quasiCoherentDerivedInclusion.{u, wA, wM} X)
      (quasiCoherentAmbientDerivedPushforward.{u, wM} U.1.ι)
      (quasiCoherentDerivedInclusionFactors.{u, wA, wM} U.1.toScheme)
      (quasiCoherentDerivedInclusionFactors.{u, wA, wM} X)
      (quasiCoherentPushforwardComplexIso U.1.ι (hQC U))
      (moduleDirectImageDerivedComparison.{u, wM} U.1.ι))) :
    ∃ h : ∀ B : DerivedCategory.{wA}
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory,
      schemeDerivedQCohProperty X
        ((quasiCoherentDerivedInclusion.{u, wA, wM} X).obj B),
      ((schemeDerivedQCohProperty X).lift
        (quasiCoherentDerivedInclusion.{u, wA, wM} X) h).IsEquivalence := by
  sorry

end AlgebraicGeometry.Scheme.Modules
