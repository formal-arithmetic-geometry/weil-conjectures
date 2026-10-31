/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceTotalFractions
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.RingTheory.OrderOfVanishing.Basic

/-! # Divisors on regular algebraic spaces

Source: Stacks Project, Divisors, Tags 0BE2, 0BE3 and 0AGA; Spaces Divisors,
Tags 0EN6 and 0EN7 (blueprint: def-sfb-space-divisors).

Weil divisors have finite support on codimension-one point classes. Cartier divisors
are global sections of the sheafified quotient of meromorphic units by regular units.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- Regular Noetherian separated algebraic spaces are tested on all scheme étale charts.
Noetherianity is the existing scheme class on every chart and separatedness is the
closedness of the diagonal over the terminal scheme. Source: Stacks, Tags 0DMM and 03MM
(blueprint: def-sfb-space-divisors). -/
def IsRegularNoetherianSeparated
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ)))) : Prop :=
  CompactSpace (Point X.obj.obj) ∧
    (∀ U : X.EtaleSite, IsRegularScheme (X.etaleForget.obj U)) ∧
    IsSeparatedPresheafMap (terminal.from X.obj.obj)

/-- Codimension-one point classes, with codimension computed on an étale scheme chart.
Their reduced closures are exactly integral closed subspaces of codimension one.
Source: Stacks, Tag 0BE2 and Properties of Spaces, Tag 04NA
(blueprint: def-sfb-space-divisors). -/
def SpacePrimeDivisor :=
  {x : Point X.obj.obj // ∃ (U : X.EtaleSite) (y : X.etaleForget.obj U),
    schemePointMap U.obj.hom y = x ∧
      ringKrullDim ((X.etaleForget.obj U).presheaf.stalk y) = 1}

/-- Finite integral combinations of the reduced codimension-one closures.
Source: Stacks, Tag 0BE2 (blueprint: def-sfb-space-divisors). -/
abbrev SpaceWeilDivisor := SpacePrimeDivisor X →₀ ℤ

/-- The image of regular units in meromorphic units on one affine basis object.
Source: Stacks, definition of Cartier divisors, Tag 0B8Z
(blueprint: def-sfb-space-divisors). -/
def spaceRegularUnitImage (U : X.SmallEtaleModel) :
    Subgroup (spaceTotalFractionSheaf X |>.obj.obj (op U))ˣ :=
  (Units.map ((spaceToTotalFractions X).hom.app (op U)).hom.toMonoidHom).range

/-- The quotient group of local meromorphic units by local regular units.
Source: Stacks, Tag 0B8Z (blueprint: def-sfb-space-divisors). -/
abbrev spaceCartierQuotient (U : X.SmallEtaleModel) :=
  (spaceTotalFractionSheaf X |>.obj.obj (op U))ˣ ⧸ spaceRegularUnitImage X U

/-- Restriction takes the image of regular units into the image of regular units.
Source: Stacks, Tag 0B8Z (blueprint: def-sfb-space-divisors).
Proof: a regular unit restricts to a regular unit. Naturality of the actual
structure-to-fractions map identifies its meromorphic image with this restriction. -/
theorem spaceRegularUnitImage_map {U V : X.SmallEtaleModel} (f : U ⟶ V) :
    spaceRegularUnitImage X V ≤ (spaceRegularUnitImage X U).comap
      (Units.map ((spaceTotalFractionSheaf X).obj.map f.op).hom.toMonoidHom) := by
  sorry

/-- The actual quotient homomorphism on restriction.
Source: Stacks, Tag 0B8Z (blueprint: def-sfb-space-divisors). -/
def spaceCartierQuotientMap {U V : X.SmallEtaleModel} (f : U ⟶ V) :
    spaceCartierQuotient X V →* spaceCartierQuotient X U :=
  QuotientGroup.map _ _
    (Units.map ((spaceTotalFractionSheaf X).obj.map f.op).hom.toMonoidHom)
    (spaceRegularUnitImage_map X f)

/-- Identity law for the quotient presheaf.
Source: Stacks, Tag 0B8Z (blueprint: def-sfb-space-divisors).
Proof: quotient representatives are meromorphic units, and identity restriction fixes them. -/
theorem spaceCartierQuotientMap_id (U : X.SmallEtaleModel) :
    spaceCartierQuotientMap X (𝟙 U) = MonoidHom.id _ := by
  sorry

/-- Composition law for the quotient presheaf.
Source: Stacks, Tag 0B8Z (blueprint: def-sfb-space-divisors).
Proof: on a meromorphic-unit representative both maps are iterated restriction;
the total fraction sheaf composition law gives equality. -/
theorem spaceCartierQuotientMap_comp {U V W : X.SmallEtaleModel}
    (f : U ⟶ V) (g : V ⟶ W) :
    spaceCartierQuotientMap X (f ≫ g) =
      (spaceCartierQuotientMap X f).comp (spaceCartierQuotientMap X g) := by
  sorry

/-- The quotient presheaf whose associated sheaf defines Cartier divisors.
Source: Stacks, Tag 0B8Z (blueprint: def-sfb-space-divisors). -/
def spaceCartierPresheaf : X.SmallEtaleModelᵒᵖ ⥤ CommGrpCat.{u} where
  obj U := CommGrpCat.of (spaceCartierQuotient X U.unop)
  map f := CommGrpCat.ofHom (spaceCartierQuotientMap X f.unop)
  map_id U := congrArg CommGrpCat.ofHom (spaceCartierQuotientMap_id X U.unop)
  map_comp f g := congrArg CommGrpCat.ofHom (spaceCartierQuotientMap_comp X g.unop f.unop)

/-- The sheaf quotient K×/O× on the affine étale basis.
Source: Stacks, Tag 0B8Z (blueprint: def-sfb-space-divisors). -/
def spaceCartierSheaf : Sheaf X.smallEtaleModelTopology (Type u) :=
  (presheafToSheaf X.smallEtaleModelTopology (Type u)).obj
    (spaceCartierPresheaf X ⋙ forget CommGrpCat)

/-- A Cartier divisor is a global section of the quotient sheaf, not necessarily
a single global meromorphic equation.
Source: Stacks, Tag 0B8Z (blueprint: def-sfb-space-divisors). -/
abbrev SpaceCartierDivisor := (spaceCartierSheaf X).obj.sections

/-- The local Cartier class of an invertible meromorphic function.
Source: Stacks, Tag 0B8Z (blueprint: def-sfb-space-divisors). -/
def spaceLocalCartierClass (U : X.SmallEtaleModel)
    (g : (spaceTotalFractionSheaf X |>.obj.obj (op U))ˣ) :
    (spaceCartierSheaf X).obj.obj (op U) :=
  (toSheafify X.smallEtaleModelTopology
    (spaceCartierPresheaf X ⋙ forget CommGrpCat)).app (op U)
    (QuotientGroup.mk' (spaceRegularUnitImage X U) g)

/-- An equation representing a Cartier divisor on the given affine étale chart.
Source: Stacks, Tag 0B8Z (blueprint: def-sfb-space-divisors). -/
def SpaceCartierDivisor.HasEquation (D : SpaceCartierDivisor X) (U : X.SmallEtaleModel)
    (g : (spaceTotalFractionSheaf X |>.obj.obj (op U))ˣ) : Prop :=
  D.val (op U) = spaceLocalCartierClass X U g

/-- A rational section has local coefficient g if some regular frame e satisfies s=g e.
The frame is an actual isomorphism over the localized site, and g acts through the
meromorphic coefficient ring. This imposes no global trivialization on the line.
Source: Stacks, Tags 0EN7 and 0BE3 (blueprint: def-sfb-space-divisors). -/
def SpaceRationalSection.HasCoefficient {L : X.Modules} (s : SpaceRationalSection X L)
    (U : X.SmallEtaleModel) (g : (spaceTotalFractionSheaf X |>.obj.obj (op U))ˣ) : Prop :=
  ∃ e : SheafOfModules.unit (X.smallStructureRings.over U) ≅
      (SheafOfModules.overFunctor X.smallStructureRings U).obj (X.smallModuleRestriction.obj L),
    s.value X U = (g.val : (spaceTotalFractionRings X).obj.obj (op U)) •
      spaceLocalizeSection X (X.smallModuleRestriction.obj L) U
        (e.hom.val.app (op (Over.mk (𝟙 U)))
          (1 : X.smallStructureRings.obj.obj (op U)))

/-- A Cartier divisor describes the orders of a rational section when its equations
are the coefficients of that section in regular local frames, locally in the étale topology.
Source: Stacks, Tags 0BE3 and 0EN7 (blueprint: def-sfb-space-divisors). -/
def SpaceRationalSection.HasCartierDivisor {L : X.Modules}
    (s : SpaceRationalSection X L) (D : SpaceCartierDivisor X) : Prop :=
  ∀ U : X.SmallEtaleModel, ∃ R : Sieve U, R ∈ X.smallEtaleModelTopology U ∧
    ∀ (V : X.SmallEtaleModel) (f : V ⟶ U), R f →
      ∃ g : (spaceTotalFractionSheaf X |>.obj.obj (op V))ˣ,
        SpaceCartierDivisor.HasEquation X D V g ∧ SpaceRationalSection.HasCoefficient X s V g

end AlgebraicGeometry.AlgebraicSpace
