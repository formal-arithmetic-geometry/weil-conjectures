/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-! # Normalized compact-support restriction data on strict coefficient systems

Source: the coefficient-composition detail of the compact-support finite-field independence
argument; Stacks 03CZ, 03DI, 03DJ, 070Y and 0D6E; Zheng Construction 4.1.
(blueprint: def-sp-system-compact-support-restriction-data).

The categories are module sheaves on the vertical ringed sequence site and their ordinary
unbounded derived categories. The comparison data below include their normalizations,
not just isomorphisms between unnamed functors.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralReductionSiteEssentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction

variable {l : ℕ}

/-- The levels of the existing finite torsion coefficient sequence.
Source: Zheng 4.1 (blueprint: def-sp-system-compact-support-restriction-data). -/
abbrev levels (B : Etale.SystemProjection.Coefficients.{u} l) (n : ℕ) :=
  B.rings.obj (op n)

/-- The actual adjacent maps, with no flatness condition.
Source: Zheng 4.1 (blueprint: def-sp-system-compact-support-restriction-data). -/
abbrev steps (B : Etale.SystemProjection.Coefficients.{u} l) (n : ℕ) :=
  B.rings.map (homOfLE (Nat.le_succ n)).op

/-- A coefficient-system map on the actual pro-etale sequence site.
Source: Zheng 4.1; Stacks 03CZ
(blueprint: def-sp-system-compact-support-restriction-data). -/
def sequenceMap (W : Scheme.{u}) {B C : Etale.SystemProjection.Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) :
    systemRing.{u + 1, u, u + 1} (ProEt.topology W) (VaryingRing.coefficients.{u} (levels B) W)
        (VaryingRing.coefficientTransition.{u} (levels B) (steps B) W) ⟶
      systemRing.{u + 1, u, u + 1} (ProEt.topology W) (VaryingRing.coefficients.{u} (levels C) W)
        (VaryingRing.coefficientTransition.{u} (levels C) (steps C) W) :=
  systemMap.{u + 1, u, u + 1} (ProEt.topology W)
    (VaryingRing.coefficients.{u} (levels B) W)
    (VaryingRing.coefficientTransition.{u} (levels B) (steps B) W)
    (VaryingRing.coefficients.{u} (levels C) W)
    (VaryingRing.coefficientTransition.{u} (levels C) (steps C) W)
    (fun n ↦ (constantSheaf.{u, u + 1, u + 1, u + 2}
      (ProEt.topology W) CommRingCat.{u + 1}).map (a.app (op n)))
    (fun n ↦ by
      dsimp only [VaryingRing.coefficientTransition]
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg
        ((constantSheaf.{u, u + 1, u + 1, u + 2}
          (ProEt.topology W) CommRingCat.{u + 1}).map)
        (a.naturality (homOfLE (Nat.le_succ n)).op).symm)

/-- Exact ordinary restriction changes only the scalar action of each system sheaf.
Source: Stacks 03CZ (blueprint: def-sp-system-compact-support-restriction-data). -/
abbrev restriction (W : Scheme.{u}) {B C : Etale.SystemProjection.Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) := res.{u + 1, u, u + 1} (sequenceMap W a)

/-- Restriction on the ordinary unbounded derived category, by exact localization.
Source: Stacks 05RU (blueprint: def-sp-system-compact-support-restriction-data). -/
abbrev derivedRestriction (W : Scheme.{u}) {B C : Etale.SystemProjection.Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) := (restriction W a).mapDerivedCategory

/-- Finite restriction/evaluation is the existing identity-on-sections localization.
Source: Zheng 4.1; Stacks 03CZ
(blueprint: def-sp-system-compact-support-restriction-data). -/
def restrictionEvaluation (W : Scheme.{u}) {B C : Etale.SystemProjection.Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (n : ℕ) :=
  SemilinearSections.restrictionEvaluation.{u + 1, u, u + 1} (ProEt.topology W)
    (VaryingRing.coefficients.{u} (levels B) W)
    (VaryingRing.coefficientTransition.{u} (levels B) (steps B) W)
    (VaryingRing.coefficients.{u} (levels C) W)
    (VaryingRing.coefficientTransition.{u} (levels C) (steps C) W)
    (fun k ↦ (constantSheaf.{u, u + 1, u + 1, u + 2}
      (ProEt.topology W) CommRingCat.{u + 1}).map (a.app (op k)))
    (fun k ↦ by
      dsimp only [VaryingRing.coefficientTransition]
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg
        ((constantSheaf.{u, u + 1, u + 1, u + 2}
          (ProEt.topology W) CommRingCat.{u + 1}).map)
        (a.naturality (homOfLE (Nat.le_succ k)).op).symm) n

/-- Proper/open compact support, on the entire derived system category.
Source: the compactification formula in the blueprint
(blueprint: def-sp-system-compact-support-restriction-data). -/
abbrev support (B : Etale.SystemProjection.Coefficients.{u} l)
    {X Z Y : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) :=
  VaryingRing.J (levels B) (steps B) j ⋙ VaryingRing.P (levels B) (steps B) p

/-- Normalized restriction identifications. All their ordinary section maps are identities;
the derived identifications are their exact localizations, as used below.
Source: Stacks 03CZ (blueprint: def-sp-system-compact-support-restriction-data). -/
structure RestrictionIdentifications (l : ℕ) where
  comp : ∀ (W : Scheme.{u}) (B C D : Etale.SystemProjection.Coefficients.{u} l)
    (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings),
    restriction W b ⋙ restriction W a ≅ restriction W (a ≫ b)
  comp_sections : ∀ (W : Scheme.{u}) (B C D : Etale.SystemProjection.Coefficients.{u} l)
    (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings)
    (M : VaryingRing.Modules (levels D) (steps D) W) (U : (ℕ × W.ProEt)ᵒᵖ)
    (x : M.val.obj U), ((comp W B C D a b).hom.app M).val.app U x = x
  unit : ∀ (W : Scheme.{u}) (B : Etale.SystemProjection.Coefficients.{u} l),
    restriction W (𝟙 B.rings) ≅ 𝟭 (VaryingRing.Modules (levels B) (steps B) W)
  unit_sections : ∀ (W : Scheme.{u}) (B : Etale.SystemProjection.Coefficients.{u} l)
    (M : VaryingRing.Modules (levels B) (steps B) W) (U : (ℕ × W.ProEt)ᵒᵖ)
    (x : M.val.obj U), ((unit W B).hom.app M).val.app U x = x

/-- The specified rho, localized from its identity carrier maps: the inverse localization
composition comparison followed by the localized ordinary identification.
Source: Stacks 05RU (blueprint: def-sp-system-compact-support-restriction-data). -/
def RestrictionIdentifications.rho (c : RestrictionIdentifications.{u} l)
    (W : Scheme.{u}) {B C D : Etale.SystemProjection.Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings) :=
  (Functor.mapDerivedCategoryCompIso (restriction W b) (restriction W a)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (c.comp W B C D a b)

/-- The canonical derived unit identification, from the same ordinary section identity.
Source: Stacks 05RU (blueprint: def-sp-system-compact-support-restriction-data). -/
def RestrictionIdentifications.derivedUnit (c : RestrictionIdentifications.{u} l)
    (W : Scheme.{u}) (B : Etale.SystemProjection.Coefficients.{u} l) :=
  Functor.mapDerivedCategoryNatIso (c.unit W B) ≪≫
    Functor.mapDerivedCategoryIdIso (VaryingRing.Modules (levels B) (steps B) W)

/-- The geometric restriction square is fixed on every ordinary section. Its pullback
square is the adjunction transpose of that same identity, with no extra automorphism.
Source: Stacks 03CZ, 03D7 (blueprint: def-sp-system-compact-support-restriction-data). -/
structure GeometricSquare {B C : Etale.SystemProjection.Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) {X Y : Scheme.{u}} (f : X ⟶ Y) where
  push : restriction X a ⋙ VaryingRing.push (levels B) (steps B) f ≅
    VaryingRing.push (levels C) (steps C) f ⋙ restriction Y a
  sections : ∀ (M : VaryingRing.Modules (levels C) (steps C) X)
    (U : (ℕ × Y.ProEt)ᵒᵖ)
    (x : M.val.obj ((VaryingRing.baseChange f).op.obj U)),
    ((push.hom.app M).val.app U) x = x
  pull : VaryingRing.pull (levels C) (steps C) f ⋙ restriction X a ≅
    restriction Y a ⋙ VaryingRing.pull (levels B) (steps B) f
  pull_normalized : pull.inv =
    (mateEquiv (VaryingRing.moduleAdj (levels C) (steps C) f)
      (VaryingRing.moduleAdj (levels B) (steps B) f)).symm push.inv

/-- Exact localization of the specified geometric inverse-image square.
Source: Stacks 05RU (blueprint: def-sp-system-compact-support-restriction-data). -/
def GeometricSquare.derivedPull {B C : Etale.SystemProjection.Coefficients.{u} l}
    {a : B.rings ⟶ C.rings} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : GeometricSquare a f) := Functor.mapDerivedCategorySquareIso g.pull

/-- A proper comparison, with the full K-injective resolution equation. The equation
says precisely that its component is the inverse of the localized image of the
resolution map, after the displayed canonical identifications.
Source: Stacks 070Y and 0D6E
(blueprint: def-sp-system-compact-support-restriction-data). -/
structure ProperComparison {B C : Etale.SystemProjection.Coefficients.{u} l}
    {a : B.rings ⟶ C.rings} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : GeometricSquare a f) where
  iso : derivedRestriction X a ⋙ VaryingRing.P (levels B) (steps B) f ≅
    VaryingRing.P (levels C) (steps C) f ⋙ derivedRestriction Y a
  normalized : ∀ (H : CochainComplex (VaryingRing.Modules (levels C) (steps C) X) ℤ)
    [H.IsKInjective]
    (I : CochainComplex (VaryingRing.Modules (levels B) (steps B) X) ℤ)
    [I.IsKInjective]
    (v : ((restriction X a).mapHomologicalComplex (.up ℤ)).obj H ⟶ I) [QuasiIso v],
    QuasiIso (((VaryingRing.push (levels B) (steps B) f).mapHomologicalComplex (.up ℤ)).map v) ∧
      iso.hom.app (DerivedCategory.Q.obj H) ≫
        (derivedRestriction Y a).map
          ((VaryingRing.push (levels C) (steps C) f).rightDerivedFunctorObjQIso H).hom ≫
        (restriction Y a).mapDerivedCategoryFactors.hom.app
          (((VaryingRing.push (levels C) (steps C) f).mapHomologicalComplex (.up ℤ)).obj H) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex g.push (.up ℤ)).inv.app H) ≫
        DerivedCategory.Q.map
          (((VaryingRing.push (levels B) (steps B) f).mapHomologicalComplex (.up ℤ)).map v) =
      (VaryingRing.P (levels B) (steps B) f).map
          ((restriction X a).mapDerivedCategoryFactors.hom.app H) ≫
        (VaryingRing.P (levels B) (steps B) f).map (DerivedCategory.Q.map v) ≫
        ((VaryingRing.push (levels B) (steps B) f).rightDerivedFunctorObjQIso I).hom

/-- The open comparison is normalized by the original open-adjunction units.
This determines the identity on the open and the unique map between zero objects
outside it, including the coefficient transition maps.
Source: Stacks 03DI and 03DJ
(blueprint: def-sp-system-compact-support-restriction-data). -/
structure OpenComparison {B C : Etale.SystemProjection.Coefficients.{u} l}
    {a : B.rings ⟶ C.rings} {X Z : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    (g : GeometricSquare a j) where
  iso : restriction X a ⋙ VaryingRing.extension (levels B) (steps B) j ≅
    VaryingRing.extension (levels C) (steps C) j ⋙ restriction Z a
  normalized : ∀ M : VaryingRing.Modules (levels C) (steps C) X,
    (VaryingRing.moduleJAdj (levels B) (steps B) j).unit.app ((restriction X a).obj M) ≫
      (VaryingRing.pull (levels B) (steps B) j).map (iso.hom.app M) ≫
      g.pull.inv.app ((VaryingRing.extension (levels C) (steps C) j).obj M) =
    (restriction X a).map ((VaryingRing.moduleJAdj (levels C) (steps C) j).unit.app M)

/-- Localization of the ordinary section-normalized open comparison.
Source: Stacks 05RU (blueprint: def-sp-system-compact-support-restriction-data). -/
def OpenComparison.derived {B C : Etale.SystemProjection.Coefficients.{u} l}
    {a : B.rings ⟶ C.rings} {X Z : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {g : GeometricSquare a j} (o : OpenComparison g) :=
  Functor.mapDerivedCategorySquareIso o.iso

/-- The two specified normalized factors of compact-support restriction.
Source: Stacks 03DI and 0D6E
(blueprint: def-sp-system-compact-support-restriction-data). -/
structure Comparison {B C : Etale.SystemProjection.Coefficients.{u} l}
    (a : B.rings ⟶ C.rings) {X Z Y : Scheme.{u}}
    (j : X ⟶ Z) [IsOpenImmersion j] (p : Z ⟶ Y) where
  openSquare : GeometricSquare a j
  properSquare : GeometricSquare a p
  openPart : OpenComparison openSquare
  properPart : ProperComparison properSquare

/-- The comparison d is the specified open/proper paste, before finite evaluation.
Source: the coefficient-composition assertion, proof step 5
(blueprint: def-sp-system-compact-support-restriction-data). -/
def Comparison.iso {B C : Etale.SystemProjection.Coefficients.{u} l}
    {a : B.rings ⟶ C.rings} {X Z Y : Scheme.{u}}
    {j : X ⟶ Z} [IsOpenImmersion j] {p : Z ⟶ Y} (d : Comparison a j p) :
    derivedRestriction X a ⋙ support B j p ≅ support C j p ⋙ derivedRestriction Y a :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight d.openPart.derived (VaryingRing.P (levels B) (steps B) p) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (VaryingRing.J (levels C) (steps C) j) d.properPart.iso ≪≫
    (Functor.associator _ _ _).symm

end AlgebraicGeometry.ProEtale.SystemCompactSupportRestriction
