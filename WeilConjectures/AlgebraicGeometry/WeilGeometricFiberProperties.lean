/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory
public import WeilConjectures.AlgebraicGeometry.SfCommonStageWeilCohomology
import Mathlib.Algebra.CharP.CharAndCard

/-! # Geometric-fibre properties for the normalized Weil operations

Source: geometric base change in the blueprint composition argument; Stacks Tags
01T6, 01K0, 01L4, 01W4 and 01JU.
(blueprint: def-zl-weil-geometric-fiber-properties).

These elementary instances let realization comparisons use geometric base change
without importing the higher compact-support construction. They give the canonical
structure maps already used there; the two presentations are definitionally equal.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- The base-changed map respects the specified geometric structure maps.
Source: blueprint geometric-fibre convention
(blueprint: def-zl-weil-geometric-fiber-properties).
Proof: this is the Over.w equation of the image of f₀ under Over.pullback. -/
@[instance]
theorem zlRealizationFiberMap_isOver {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    (zlFiberMap D f₀).IsOver (Spec (.of D.k)) := by
  exact ⟨((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f₀).w⟩

/-- Separatedness survives geometric base change.
Source: Stacks 01L4; blueprint compact-support geometric fibre
(blueprint: def-zl-weil-geometric-fiber-properties).
Proof: the square of f₀ with its geometric-fibre map is Cartesian. Base change
preserves closed diagonals, which characterize separatedness. -/
@[instance]
theorem zlRealizationFiberMap_separated {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] : IsSeparated (zlFiberMap D f₀) := by
  exact MorphismProperty.overPullbackMap (P := @IsSeparated)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

/-- Local finite type survives geometric base change.
Source: Stacks 01T6; blueprint compact-support geometric fibre
(blueprint: def-zl-weil-geometric-fiber-properties).
Proof: f₀.left and zlFiberMap D f₀ form the base-change square of the two
structure-map pullbacks. Apply locally finite type stability under base change. -/
@[instance]
theorem zlRealizationFiberMap_finiteType {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left] :
    LocallyOfFiniteType (zlFiberMap D f₀) := by
  exact MorphismProperty.overPullbackMap (P := @LocallyOfFiniteType)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

/-- Quasi-compactness survives geometric base change.
Source: Stacks 01K0; blueprint compact-support geometric fibre
(blueprint: def-zl-weil-geometric-fiber-properties).
Proof: use the same Cartesian square and quasi-compact base-change stability. -/
@[instance]
theorem zlRealizationFiberMap_quasiCompact {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) [QuasiCompact f₀.left] : QuasiCompact (zlFiberMap D f₀) := by
  exact MorphismProperty.overPullbackMap (P := @QuasiCompact)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

include hl in
/-- The coefficient prime is a unit in the closure field itself.
Source: blueprint finite-field coefficient convention
(blueprint: def-zl-weil-geometric-fiber-properties).
Proof: D.card_base and D.cardinality_eq give characteristic D.p in D.k₀ and
hence D.k. The prime l differs from D.p, so its image in that field is nonzero,
and therefore invertible. -/
theorem zlRealizationPrimeUnit : IsUnit (l : D.k) := by
  let := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
  have : CharP D.k D.p :=
    charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
  exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
    (fun h ↦ hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)

/-- Properness survives the same geometric base change.
Source: Stacks 01W4
(blueprint: def-zl-weil-geometric-fiber-properties).
Proof: apply stability of properness to the Over pullback map. -/
@[instance]
theorem zlRealizationFiberMap_isProper {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) [IsProper f₀.left] : IsProper (zlFiberMap D f₀) := by
  exact MorphismProperty.overPullbackMap (P := @IsProper)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

/-- Open immersions survive the same geometric base change.
Source: Stacks 01JU
(blueprint: def-zl-weil-geometric-fiber-properties).
Proof: apply stability of open immersions to the Over pullback map. -/
@[instance]
theorem zlRealizationFiberMap_isOpenImmersion {X₀ Y₀ : Over (Spec (.of D.k₀))}
    (f₀ : X₀ ⟶ Y₀) [IsOpenImmersion f₀.left] :
    IsOpenImmersion (zlFiberMap D f₀) := by
  exact MorphismProperty.overPullbackMap (P := @IsOpenImmersion)
    (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) f₀ inferInstance

end WeilConjectures
