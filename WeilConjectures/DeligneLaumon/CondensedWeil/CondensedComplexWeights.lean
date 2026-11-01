/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CondensedWeil.ConstantExtensionPunctualWeights
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationOpenComparison.CondensedCompactificationData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Native.NativeConstructibleExceptionalInverseImage

/-! # Cohomological weights of condensed Weil complexes

Source: latest blueprint, def-weil-complex-weights, all three weight displays.
(blueprint: def-weil-complex-weights).

The cohomology Weil structure is induced by exact pullback and the given derived
Weil structure. In particular it retains the Frobenius datum after forgetting a
native derived Weil module.

The remaining definitions characterize the chosen dualizing object by its exceptional
counit, normalize its Frobenius by that counit, and define the contragredient dual,
lower bound and purity.

## Main definitions

- `condensedWeilCohomology`: cohomology with Frobenius.
- `condensedComplexIsMixedOfWeightsAtMost`: shifted upper bound.
- `CondensedWeightDualizingDatum`: the chosen canonical dualizing Weil object.
- `condensedWeightVerdierDual`: its internal-Hom dual.
- `condensedComplexIsMixedOfWeightsAtLeast`, `condensedComplexIsPureOfWeight`: lower and pure.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
-- Condensed coefficient type conversions require the declaration-scoped budgets below.
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.CondensedRing.CompactificationOpenComparison
namespace WeilConjectures.CondensedWeil

set_option maxHeartbeats 1600000 in
-- Condensed coefficient type normalization can exceed the default budget.
set_option maxHeartbeats 1600000 in
-- Condensed coefficient type normalization can exceed the default budget.
set_option maxHeartbeats 1600000 in
-- Condensed coefficient type normalization can exceed the default budget.
end WeilConjectures.CondensedWeil

namespace WeilConjectures.CondensedWeil

set_option maxHeartbeats 1600000 in
-- Condensed coefficient type normalization can exceed the default budget.
/-- The finite-field structure morphism, bundled in the existing compactification interface.
Source: latest blueprint, def-weil-complex-weights, the structure morphism a_Y.
(blueprint: def-weil-complex-weights). -/
abbrev condensedWeightStructureModel (D : FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] : Model D where
  X₀ := X₀
  Y₀ := Over.mk (𝟙 (Spec (.of D.k₀)))
  f₀ := Over.homMk X₀.hom (Category.comp_id _)
  finiteX := inferInstance
  compactX := inferInstance
  qsX := quasiSeparatedSpace_of_quasiSeparated X₀.hom
  finiteY := inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of D.k₀))))
  compactY := inferInstanceAs (QuasiCompact (𝟙 (Spec (.of D.k₀))))
  qsY := inferInstanceAs (QuasiSeparatedSpace (Spec (.of D.k₀)))
  separated := inferInstanceAs (IsSeparated X₀.hom)
  finite := inferInstanceAs (LocallyOfFiniteType X₀.hom)
  compact := inferInstanceAs (QuasiCompact X₀.hom)

set_option maxHeartbeats 1600000 in
-- Condensed coefficient type normalization can exceed the default budget.
/-- The algebraic closure inherits the prime characteristic of the finite base.
Source: finite-field coefficient convention (blueprint: def-weil-complex-weights). -/
instance condensedWeightClosureCharP (D : FiniteFieldDatum.{u}) : CharP D.k D.p := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  exact charP_of_injective_algebraMap' D.k₀ D.p

/-- Locally finite type is inherited by geometric base change.
Source: the structure morphism in def-weil-complex-weights
(blueprint: def-weil-complex-weights). -/
instance condensedWeightGeometricLft (D : FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType T₀.hom] :
    LocallyOfFiniteType ((geometric D).obj T₀).hom :=
  MorphismProperty.baseChange_obj (P := @LocallyOfFiniteType) _ T₀ inferInstance

/-- Quasi-compactness is inherited by geometric base change.
Source: the structure morphism in def-weil-complex-weights
(blueprint: def-weil-complex-weights). -/
instance condensedWeightGeometricQc (D : FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀))) [QuasiCompact T₀.hom] :
    QuasiCompact ((geometric D).obj T₀).hom :=
  MorphismProperty.baseChange_obj (P := @QuasiCompact) _ T₀ inferInstance

/-- Separatedness is inherited by geometric base change.
Source: the separated structure morphism in def-weil-complex-weights
(blueprint: def-weil-complex-weights). -/
instance condensedWeightGeometricSep (D : FiniteFieldDatum.{u})
    (T₀ : Over (Spec (.of D.k₀))) [IsSeparated T₀.hom] :
    IsSeparated ((geometric D).obj T₀).hom :=
  MorphismProperty.baseChange_obj (P := @IsSeparated) _ T₀ inferInstance

/-- The actual constructible exceptional inverse image for the structure morphism.
Source: the dualizing-object equality, using def-weil-exceptional-inverse-image
(blueprint: def-weil-complex-weights). -/
def condensedWeightExceptionalInverseImage (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] :=
  let M := condensedWeightStructureModel D X₀
  letI : LocallyOfFiniteType ((geometric D).obj M.X₀).hom :=
    @condensedWeightGeometricLft D M.X₀ M.finiteX
  letI : LocallyOfFiniteType ((geometric D).obj M.Y₀).hom :=
    @condensedWeightGeometricLft D M.Y₀ M.finiteY
  letI : QuasiCompact ((geometric D).obj M.X₀).hom :=
    @condensedWeightGeometricQc D M.X₀ M.compactX
  letI : QuasiCompact ((geometric D).obj M.Y₀).hom :=
    @condensedWeightGeometricQc D M.Y₀ M.compactY
  letI : IsSeparated ((geometric D).obj M.X₀).hom :=
    @condensedWeightGeometricSep D M.X₀ (inferInstanceAs (IsSeparated X₀.hom))
  letI : IsSeparated ((geometric D).obj M.Y₀).hom :=
    @condensedWeightGeometricSep D M.Y₀
      (inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k₀)))))
  letI : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  letI : Fact (ringChar D.k ≠ l) := ⟨by rw [ringChar.eq D.k D.p]; exact hl.symm⟩
  constructibleExceptionalInverseImage (Profinite.padicAlgClRingObj l) l D.k
    ((geometric D).map M.f₀)
    (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))

/-- The recorded adjunction for the actual exceptional functor, with its fixed counit.
Source: canonical dualizing Weil lift, adjunction normalization
(blueprint: def-weil-complex-weights). -/
def condensedWeightExceptionalAdjunction (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated X₀.hom] :=
  let M := condensedWeightStructureModel D X₀
  letI : LocallyOfFiniteType ((geometric D).obj M.X₀).hom :=
    @condensedWeightGeometricLft D M.X₀ M.finiteX
  letI : LocallyOfFiniteType ((geometric D).obj M.Y₀).hom :=
    @condensedWeightGeometricLft D M.Y₀ M.finiteY
  letI : QuasiCompact ((geometric D).obj M.X₀).hom :=
    @condensedWeightGeometricQc D M.X₀ M.compactX
  letI : QuasiCompact ((geometric D).obj M.Y₀).hom :=
    @condensedWeightGeometricQc D M.Y₀ M.compactY
  letI : IsSeparated ((geometric D).obj M.X₀).hom :=
    @condensedWeightGeometricSep D M.X₀ (inferInstanceAs (IsSeparated X₀.hom))
  letI : IsSeparated ((geometric D).obj M.Y₀).hom :=
    @condensedWeightGeometricSep D M.Y₀
      (inferInstanceAs (IsSeparated (𝟙 (Spec (.of D.k₀)))))
  letI : Fact (ringChar D.k).Prime := ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
  letI : Fact (ringChar D.k ≠ l) := ⟨by rw [ringChar.eq D.k D.p]; exact hl.symm⟩
  constructibleExceptionalAdjunction (Profinite.padicAlgClRingObj l) l D.k
    ((geometric D).map M.f₀)
    (Or.inr (Or.inr (Or.inr ⟨Iso.refl _⟩)))

set_option maxHeartbeats 1600000 in
-- Normalize the actual exceptional functor and its recorded counit endpoints.
set_option maxHeartbeats 1600000 in
-- Condensed coefficient type normalization can exceed the default budget.
set_option maxHeartbeats 1600000 in
-- Condensed coefficient type normalization can exceed the default budget.
set_option maxHeartbeats 1600000 in
-- Condensed coefficient type normalization can exceed the default budget.
end WeilConjectures.CondensedWeil
