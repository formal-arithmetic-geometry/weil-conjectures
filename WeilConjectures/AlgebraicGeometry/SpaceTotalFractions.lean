/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-! # Total fractions on the affine étale basis of an algebraic space

Source: Stacks Project, Spaces Divisors, Tags 0EN6 and 0ENA
(blueprint: def-sfb-space-total-fractions).

The affine basis is the existing small model, with its original coefficient universe.
The total quotient ring is sheafified, so the construction does not assume normality.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Regular functions on an actual affine étale chart in the existing small basis.
Source: Stacks, Tag 03G7 (blueprint: def-sfb-space-total-fractions). -/
abbrev fractionChartRing (U : X.SmallEtaleModel) :=
  X.smallStructureSheaf.obj.obj (op U)

/-- The literal localization at all non-zero-divisors of the affine chart ring.
Source: Stacks, Tag 0EN6 (blueprint: def-sfb-space-total-fractions). -/
abbrev chartTotalFractionRing (U : X.SmallEtaleModel) :=
  Localization (nonZeroDivisors (fractionChartRing X U))

/-- Restriction between affine étale charts preserves non-zero-divisors.
Source: Stacks, Tag 0EN9, flat case (blueprint: def-sfb-space-total-fractions).
Proof: a morphism of étale scheme charts over the same algebraic space is étale.
Its map of affine coordinate rings is therefore flat. Tensor the injection given
by multiplication by a non-zero-divisor with the flat target ring; the resulting
multiplication map is injective, including when the target is the zero ring. -/
theorem fractionChart_restrict_nonZeroDivisors {U V : X.SmallEtaleModel} (f : U ⟶ V) :
    nonZeroDivisors (fractionChartRing X V) ≤
      (nonZeroDivisors (fractionChartRing X U)).comap
        (X.smallStructureSheaf.obj.map f.op).hom := by
  sorry

/-- Restrict a fraction by restricting its numerator and denominator.
Source: Stacks, Tag 0EN9 (blueprint: def-sfb-space-total-fractions). -/
def chartFractionMap {U V : X.SmallEtaleModel} (f : U ⟶ V) :
    chartTotalFractionRing X V →+* chartTotalFractionRing X U :=
  IsLocalization.map _ (X.smallStructureSheaf.obj.map f.op).hom
    (fractionChart_restrict_nonZeroDivisors X f)

/-- Identity for fraction restriction.
Source: Stacks, Tag 0EN6 (blueprint: def-sfb-space-total-fractions).
Proof: both maps fix the coordinate ring; uniqueness in the localization universal
property makes them equal on all fractions. -/
theorem chartFractionMap_id (U : X.SmallEtaleModel) :
    chartFractionMap X (𝟙 U) = RingHom.id _ := by
  sorry

/-- Composition for fraction restriction.
Source: Stacks, Tag 0EN6 (blueprint: def-sfb-space-total-fractions).
Proof: both homomorphisms send a/b to the iterated restriction of a divided by that
of b. The coordinate-ring presheaf composition law and localization uniqueness apply. -/
theorem chartFractionMap_comp {U V W : X.SmallEtaleModel} (f : U ⟶ V) (g : V ⟶ W) :
    chartFractionMap X (f ≫ g) = (chartFractionMap X f).comp (chartFractionMap X g) := by
  sorry

/-- The total quotient presheaf on the affine étale basis.
Source: Stacks, Tag 0EN6 (blueprint: def-sfb-space-total-fractions). -/
def spaceTotalFractionPresheaf : X.SmallEtaleModelᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (chartTotalFractionRing X U.unop)
  map f := CommRingCat.ofHom (chartFractionMap X f.unop)
  map_id U := congrArg CommRingCat.ofHom (chartFractionMap_id X U.unop)
  map_comp f g := congrArg CommRingCat.ofHom (chartFractionMap_comp X g.unop f.unop)

/-- The meromorphic scalar sheaf: the associated sheaf of the explicit fraction presheaf.
Source: Stacks, Tags 0EN6 and 0ENA (blueprint: def-sfb-space-total-fractions). -/
def spaceTotalFractionSheaf : Sheaf X.smallEtaleModelTopology CommRingCat.{u} :=
  (presheafToSheaf X.smallEtaleModelTopology CommRingCat).obj
    (spaceTotalFractionPresheaf X)

/-- The underlying ring sheaf of meromorphic scalars.
Source: Stacks, Tag 0EN6 (blueprint: def-sfb-space-total-fractions). -/
abbrev spaceTotalFractionRings : Sheaf X.smallEtaleModelTopology RingCat.{u} :=
  (sheafCompose X.smallEtaleModelTopology (forget₂ CommRingCat RingCat)).obj
    (spaceTotalFractionSheaf X)

/-- Localization is natural under chart restriction.
Source: Stacks, Tag 0EN6 (blueprint: def-sfb-space-total-fractions).
Proof: the localization map sends a to a/1, and fraction restriction sends a/1 to
res(a)/1, which is localization after restriction. -/
theorem spaceFractionLocalization_natural {U V : X.SmallEtaleModel} (f : U ⟶ V) :
    (chartFractionMap X f).comp
        (algebraMap (fractionChartRing X V) (chartTotalFractionRing X V)) =
      (algebraMap (fractionChartRing X U) (chartTotalFractionRing X U)).comp
        (X.smallStructureSheaf.obj.map f.op).hom := by
  sorry

/-- The actual localization map before sheafification.
Source: Stacks, Tag 0EN6 (blueprint: def-sfb-space-total-fractions). -/
def spaceFractionLocalization : X.smallStructureSheaf.obj ⟶
    spaceTotalFractionPresheaf X where
  app U := CommRingCat.ofHom (algebraMap (fractionChartRing X U.unop)
    (chartTotalFractionRing X U.unop))
  naturality {_U _V} f :=
    (congrArg CommRingCat.ofHom (spaceFractionLocalization_natural X f.unop)).symm

/-- The canonical structure-sheaf homomorphism into total fractions.
Source: Stacks, Tag 0EN6 (blueprint: def-sfb-space-total-fractions). -/
def spaceToTotalFractions : X.smallStructureRings ⟶ spaceTotalFractionRings X :=
  ⟨Functor.whiskerRight (spaceFractionLocalization X ≫
    toSheafify X.smallEtaleModelTopology (spaceTotalFractionPresheaf X))
      (forget₂ CommRingCat RingCat)⟩

/-- Meromorphic localization of a module, as extension of scalars on the same ringed site.
Source: Stacks, Tag 0EN7 (blueprint: def-sfb-space-total-fractions). -/
def spaceMeromorphicLocalization :
    X.SmallModules ⥤ SheafOfModules.{u} (spaceTotalFractionRings X) :=
  SheafOfModules.pullback (F := 𝟭 X.SmallEtaleModel) (spaceToTotalFractions X)

/-- A nonzero rational section is a generator after extending to the total quotient sheaf.
This includes one generator on each irreducible component and the empty-space case.
Source: Stacks, Tags 0EN7 and 0EPQ (blueprint: def-sfb-space-total-fractions). -/
abbrev SpaceRationalSection (L : X.Modules) :=
  (spaceMeromorphicLocalization X).obj (SheafOfModules.unit X.smallStructureRings) ≅
    (spaceMeromorphicLocalization X).obj (X.smallModuleRestriction.obj L)

/-- A regular section extends the given rational section; the generator condition
is `IsIso a`, so it tests this section, not just the line's isomorphism class.
Source: Stacks, Tag 0EN7 (blueprint: def-sfb-space-total-fractions). -/
def SpaceRationalSection.IsRegularGenerator {L : X.Modules}
    (s : SpaceRationalSection X L) : Prop :=
  ∃ a : SheafOfModules.unit X.smallStructureRings ⟶ X.smallModuleRestriction.obj L,
    IsIso a ∧ (spaceMeromorphicLocalization X).map a = s.hom

/-- Isomorphisms of lines preserving specified rational generators.
Source: Stacks, Tag 0EN7 (blueprint: def-sfb-space-total-fractions). -/
def SpaceRationalSection.Preserves {L M : X.Modules}
    (s : SpaceRationalSection X L) (t : SpaceRationalSection X M) (e : L ≅ M) : Prop :=
  s.hom ≫ (spaceMeromorphicLocalization X).map
    (X.smallModuleRestriction.map e.hom) = t.hom

set_option maxHeartbeats 400000 in
-- Elaborating the scalar adjunction unit unfolds the identity-site pushforward.
/-- Localization of an actual section, via the canonical extension-of-scalars unit.
Source: Stacks, Tag 0EN7 (blueprint: def-sfb-space-total-fractions). -/
def spaceLocalizeSection (M : X.SmallModules) (U : X.SmallEtaleModel)
    (m : M.val.obj (op U)) :
    ((spaceMeromorphicLocalization X).obj M).val.obj (op U) :=
  (((SheafOfModules.pullbackPushforwardAdjunction
    (F := 𝟭 X.SmallEtaleModel) (S := X.smallStructureRings)
    (R := spaceTotalFractionRings X) (spaceToTotalFractions X)).unit.app M).val.app (op U)) m

/-- The value of a rational generator on the localized regular scalar 1.
Source: Stacks, Tag 0EN7 (blueprint: def-sfb-space-total-fractions). -/
def SpaceRationalSection.value {L : X.Modules} (s : SpaceRationalSection X L)
    (U : X.SmallEtaleModel) :
    ((spaceMeromorphicLocalization X).obj (X.smallModuleRestriction.obj L)).val.obj (op U) :=
  s.hom.val.app (op U)
    (spaceLocalizeSection X (SheafOfModules.unit X.smallStructureRings) U
      (1 : X.smallStructureRings.obj.obj (op U)))

end AlgebraicGeometry.AlgebraicSpace
