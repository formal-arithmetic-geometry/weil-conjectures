/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q107
-/
module

public import Sheaf.AlgebraicGeometry.AtlasEtaleRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentAlgebra
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-! # The commutative-ring inverse image for algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 03G1, 03G2, 03G7 and 03G8
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).

This extends the existing enlarged-site construction to commutative-ring sheaves in
the original coefficient universe. Its inverse image is the left adjoint of the existing
direct image, and its structural map has the same scheme-chart normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Scheme restriction is an equivalence also for commutative-ring sheaves in the
original coefficient universe. Source: Stacks 03G1, 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: use the same scheme charts and covering refinements as for
`enlargedRestriction_equivalence`. The comparison lemma works for ring-valued
sheaves: transport multiplication, addition and units through faithful restriction;
their identities, including commutativity, can be checked after restriction. -/
theorem enlargedCommRestriction_equivalence (X : AlgebraicSpace S) :
    (enlargedRestriction X CommRingCat.{u}).IsEquivalence := by
  sorry

/-- The normalized commutative-ring extension equivalence.
Source: Stacks 03H7 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedCommEquivalence (X : AlgebraicSpace S) :
    Sheaf X.enlargedEtaleTopology CommRingCat.{u} ≌
      Sheaf X.etaleTopology CommRingCat.{u} :=
  @Functor.asEquivalence _ _ _ _ (enlargedRestriction X CommRingCat.{u})
    (enlargedCommRestriction_equivalence X)

/-- The extended structure sheaf in commutative rings.
Source: Stacks 03G7, 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedCotangentStructure (X : AlgebraicSpace S) :=
  (enlargedCommEquivalence X).inverse.obj X.commStructureSheaf

/-- Its canonical restriction identification.
Source: Stacks 03H7 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedCotangentRestriction (X : AlgebraicSpace S) :
    (enlargedRestriction X CommRingCat.{u}).obj X.enlargedCotangentStructure ≅
      X.commStructureSheaf :=
  (enlargedCommEquivalence X).counitIso.app _

/-- On a scheme chart the extended structure sheaf is exactly regular functions.
Source: Stacks 03G7, 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def cotangentChartSection (X : AlgebraicSpace S) (U : X.EtaleSite) :
    Scheme.Γ.obj (op ((X.etaleForget).obj U)) ⟶
      X.enlargedCotangentStructure.obj.obj (op ((enlargedSchemeInclusion X).obj U)) :=
  (X.enlargedCotangentRestriction).inv.hom.app (op U)

/-- Scheme-chart normalization of the extended structural map, with no assumption
on the space morphism. Source: Stacks 03G8
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def IsCotangentStructuralMap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (r : Y.enlargedCotangentStructure ⟶
      (enlargedDirectImage f CommRingCat.{u}).obj X.enlargedCotangentStructure) : Prop :=
  ∀ (U : X.EtaleSite) (V : Y.EtaleSite) (g : U.obj.left ⟶ V.obj.left)
    (h : yoneda.map g ≫ V.obj.hom = U.obj.hom ≫ f.hom.hom),
    Y.cotangentChartSection V ≫
      r.hom.app (op ((enlargedSchemeInclusion Y).obj V)) ≫
      X.enlargedCotangentStructure.obj.map (enlargedChartLift f U V g h).op =
        Scheme.Γ.map g.left.op ≫ X.cotangentChartSection U

/-- The structural map is uniquely specified by pullback of functions on charts.
Source: Stacks 03G8 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: pull back a function from a scheme chart of Y to a scheme atlas of its
fibre product with X. The pullbacks agree on overlaps and glue uniquely.
Common refinements give independence and naturality. The ring identities hold
on charts. The sheafification universal property and faithful scheme restriction
give the displayed normalization and uniqueness on the enlarged site. -/
theorem cotangentStructuralMap_existsUnique {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃! r : Y.enlargedCotangentStructure ⟶
        (enlargedDirectImage f CommRingCat.{u}).obj X.enlargedCotangentStructure,
      IsCotangentStructuralMap f r := by
  sorry

/-- The existing direct-image construction with commutative-ring coefficients.
Source: Stacks 03G2 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def cotangentRingDirect {X Y : AlgebraicSpace S} (f : X ⟶ Y) :=
  (enlargedCommEquivalence X).inverse ⋙ enlargedDirectImage f CommRingCat.{u} ⋙
    (enlargedCommEquivalence Y).functor

/-- The commutative-ring direct image has its usual inverse image as left adjoint.
Source: Stacks 03G2, 03G8
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: left Kan extension along `enlargedBaseChange f` followed by ring
sheafification is left adjoint to precomposition. Transport this adjunction
through the two scheme-restriction equivalences. This is also the algebraic
inverse image of the set-topos morphism, by its finite-limit preservation. -/
theorem cotangentRingDirect_rightAdjoint {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (cotangentRingDirect f).IsRightAdjoint := by
  sorry

/-- The canonical commutative-ring inverse-image adjunction.
Source: Stacks 03G2, 03G8
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def cotangentRingAdjunction {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    @Functor.leftAdjoint _ _ _ _ (cotangentRingDirect f)
      (cotangentRingDirect_rightAdjoint f) ⊣ cotangentRingDirect f :=
  @Adjunction.ofIsRightAdjoint _ _ _ _ (cotangentRingDirect f)
    (cotangentRingDirect_rightAdjoint f)

/-- The canonical structural ring map in direct-image form.
Source: Stacks 03G8 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def cotangentDirectRingMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Y.commStructureSheaf ⟶ (cotangentRingDirect f).obj X.commStructureSheaf :=
  ((enlargedCommEquivalence Y).counitIso.app _).inv ≫
    (enlargedCommEquivalence Y).functor.map (cotangentStructuralMap_existsUnique f).choose

/-- The inverse-image ring map `f_small⁻¹ O_Y → O_X`, namely the mate of the
unique chart-normalized structural map. Source: Stacks 03G8
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def cotangentFullRingMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (@Functor.leftAdjoint _ _ _ _ (cotangentRingDirect f)
      (cotangentRingDirect_rightAdjoint f)).obj Y.commStructureSheaf ⟶
        X.commStructureSheaf :=
  ((cotangentRingAdjunction f).homEquiv _ _).symm (cotangentDirectRingMap f)

/-- Restriction of commutative-ring sheaves to the existing small affine model.
Source: Stacks 039Z (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def cotangentSmallRestriction (X : AlgebraicSpace S) :
    Sheaf X.etaleTopology CommRingCat.{u} ⥤
      Sheaf X.smallEtaleModelTopology CommRingCat.{u} :=
  X.smallEtaleInclusion.sheafPushforwardContinuous CommRingCat.{u}
    X.smallEtaleModelTopology X.etaleTopology

/-- Affine-basis restriction is an equivalence for the original commutative rings.
Source: Stacks 039Z (blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: affine open covers refine every chart and its overlaps. Extend a sheaf by
compatible families over affine charts. The sheaf equalizer gives its unique gluings;
ring operations glue sectionwise. Restriction and extension are inverse with unit
and counit the identity on all affine-chart sections. This is the same comparison
as smallModuleEquivalence, applied to commutative-ring sheaves. -/
theorem cotangentSmallRestriction_isEquivalence (X : AlgebraicSpace S) :
    (cotangentSmallRestriction X).IsEquivalence := by
  sorry

/-- The commutative-ring comparison with the specified small model.
Source: Stacks 039Z (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def cotangentSmallEquivalence (X : AlgebraicSpace S) :
    Sheaf X.etaleTopology CommRingCat.{u} ≌
      Sheaf X.smallEtaleModelTopology CommRingCat.{u} :=
  @Functor.asEquivalence _ _ _ _ (cotangentSmallRestriction X)
    (cotangentSmallRestriction_isEquivalence X)

/-- The canonical ring inverse image transported to the existing small affine models.
Source: Stacks 03G2 and 039Z
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def cotangentRingInverse {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf Y.smallEtaleModelTopology CommRingCat.{u} ⥤
      Sheaf X.smallEtaleModelTopology CommRingCat.{u} :=
  (cotangentSmallEquivalence Y).inverse ⋙
    @Functor.leftAdjoint _ _ _ _ (cotangentRingDirect f)
      (cotangentRingDirect_rightAdjoint f) ⋙ (cotangentSmallEquivalence X).functor

/-- The canonical map f⁻¹ O_Y → O_X on the existing small model. The inverse
comparison unit identifies the extended small structure sheaf with the original
regular-functions sheaf before applying the chart-normalized adjoint mate.
Source: Stacks 03G8, 039Z and 08U0
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def cotangentRingMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (cotangentRingInverse f).obj Y.smallStructureSheaf ⟶ X.smallStructureSheaf :=
  (cotangentSmallEquivalence X).functor.map
    ((@Functor.leftAdjoint _ _ _ _ (cotangentRingDirect f)
      (cotangentRingDirect_rightAdjoint f)).map
        ((cotangentSmallEquivalence Y).unitIso.inv.app Y.commStructureSheaf) ≫
      cotangentFullRingMap f)

end AlgebraicGeometry.AlgebraicSpace
