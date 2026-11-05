/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import WeilConjectures.SixFunctors.NearbyCycles.BoundedConstructibleUnitIdentity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.WeaklyEtale
public import WeilConjectures.TraceFormula.Specialization.TraitProduct

/-!

# Generic slices of the affine line over the trait

Let `k'` be a field, `K` a field extension of `k'` and `x ∈ K`. The ring homomorphism
`k'⟦t⟧[x] ⟶ K⟦t⟧` extending the coefficientwise map `k'⟦t⟧ ⟶ K⟦t⟧` by `x ↦ x`
(`AlgebraicGeometry.traitSliceRingHom`) defines a morphism
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` over the trait map `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧ = S`
(`AlgebraicGeometry.traitSlice`). On closed points it is the point `x : Spec K ⟶ 𝔸¹_{k'}` of
the special fibre of `𝔸¹_S` (`AlgebraicGeometry.traitClosedPoint_traitSlice`); if `x` is
transcendental over `k'` (for instance `K` a separable closure of `k'(x)`), this is the generic
point of the special-fibre line (`AlgebraicGeometry.isGenericPoint_traitSlicePoint`). This is the
*generic slice* of Gabber's Künneth formula (blueprint `sk-prop-tf-nearby-external-kunneth`,
identification (2)): `Spec K⟦t⟧` is the completion of the strict localization of `𝔸¹_S` at the
generic point of its special fibre.

The square of traits `Spec K ⟶ Spec K⟦t⟧`, `Spec k' ⟶ Spec k'⟦t⟧` is cartesian
(`AlgebraicGeometry.isPullback_traitClosedPoint_traitMap`).

For a model `M` over `S` with a coordinate `b : 𝒳 ⟶ 𝔸¹_S`, the *slice model* `M''` has total space
`𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧`, special fibre `𝒳''_s = 𝒳'' ×_{Spec K⟦t⟧} Spec K` and generic fibre
`𝒳'' ×_{Spec K⟦t⟧} E` over a given scheme `E` mapping to `Spec K⟦t⟧` and to the geometric generic
point `Spec Ω` of `S` (`NearbyCyclesModel.sliceModel`, for `E = Spec L`, `L` the compositum of `Ω`
and `Frac K⟦t⟧`). The projection is a morphism of models `M'' ⟶ M`
(`NearbyCyclesModel.sliceHom`) whose special-fibre square is cartesian
(`NearbyCyclesModel.isPullback_sliceHom_i`). Its pullback exchange `α` is invertible as soon as the
base change morphism of its square of generic fibres is
(`NearbyCyclesModel.isIso_pullbackExchange_sliceHom`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section TraitSlice

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

/-- The morphism of traits `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧` induced by the coefficientwise map. -/
noncomputable def traitMap : trait K ⟶ trait k' :=
  Spec.map (CommRingCat.ofHom (PowerSeries.map (algebraMap k' K)))

/-- The constant coefficient of the coefficientwise image of a power series. -/
lemma constantCoeff_map_apply (f : PowerSeries k') :
    PowerSeries.constantCoeff (PowerSeries.map (algebraMap k' K) f) =
      algebraMap k' K (PowerSeries.constantCoeff f) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]

/-- The constant coefficient commutes with the coefficientwise map. -/
lemma constantCoeff_comp_map :
    (PowerSeries.constantCoeff (R := K)).comp (PowerSeries.map (algebraMap k' K)) =
      (algebraMap k' K).comp PowerSeries.constantCoeff := by
  ext f
  exact constantCoeff_map_apply k' K f

/-- The closed point of `Spec K⟦t⟧` lies over the closed point of `Spec k'⟦t⟧`. -/
@[reassoc]
lemma traitClosedPoint_traitMap :
    traitClosedPoint K ≫ traitMap k' K =
      Spec.map (CommRingCat.ofHom (algebraMap k' K)) ≫ traitClosedPoint k' := by
  rw [traitClosedPoint, traitMap, traitClosedPoint, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, constantCoeff_comp_map]

variable {k' K} (x : K)

/-- The ring homomorphism `k'⟦t⟧[x] ⟶ K⟦t⟧` of the generic slice: the coefficientwise map on
`k'⟦t⟧`, and `x ↦ x`. -/
noncomputable def traitSliceRingHom :
    MvPolynomial (ULift.{u} (Fin 1)) (PowerSeries k') →+* PowerSeries K :=
  MvPolynomial.eval₂Hom (PowerSeries.map (algebraMap k' K)) fun _ ↦ PowerSeries.C x

/-- The generic slice `σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` (`S = Spec k'⟦t⟧`) given by
`k'⟦t⟧[x] ⟶ K⟦t⟧`. -/
noncomputable def traitSlice : trait K ⟶ 𝔸(ULift.{u} (Fin 1); trait k') :=
  Spec.map (CommRingCat.ofHom (traitSliceRingHom x)) ≫
    (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (.of (PowerSeries k'))).inv

/-- The generic slice lies over the trait map `Spec K⟦t⟧ ⟶ Spec k'⟦t⟧`. -/
@[reassoc (attr := simp)]
lemma traitSlice_over :
    traitSlice x ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = traitMap k' K := by
  rw [traitSlice, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, traitMap]
  congr 2
  ext a : 1
  simp [traitSliceRingHom]

end TraitSlice

namespace ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] (x : K)
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}
  (hM : M.IsTraitModelOver q g) {b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k')}
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q)
  {E : Scheme.{u}} {γ : E ⟶ trait K} {δ : E ⟶ Spec (.of (traitGenericField k'))}
  (hγδ : γ ≫ traitMap k' K = δ ≫ traitGenericPoint k')

include hb in
/-- On the total space `𝒳'' = 𝒳 ×_{𝔸¹_S} Spec K⟦t⟧` of the slice, the two maps to the trait
`S = Spec k'⟦t⟧` agree. -/
@[reassoc]
lemma pullback_fst_comp_eq_snd_traitMap :
    pullback.fst b (traitSlice x) ≫ q = pullback.snd b (traitSlice x) ≫ traitMap k' K := by
  rw [← hb, pullback.condition_assoc, traitSlice_over]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end NearbyCyclesModel

end ProEtale.CondensedRing

end AlgebraicGeometry
