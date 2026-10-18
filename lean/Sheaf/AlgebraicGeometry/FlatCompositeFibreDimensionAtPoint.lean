/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.CompositeFibreLocalModels
import Sheaf.AlgebraicGeometry.FiniteTypeDimensionFormula
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import WeilConjectures.PointCount

/-!
# Pointwise fibre dimension is additive for a flat first morphism

Source: literature/stacks-project/morphisms.tex, Tag 02JS
(blueprint: lem-sbc-flat-composite-fibre-dimension-at-point)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The local case of the flat height formula (Stacks 00ON). -/
private theorem local_flat_dimension {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [IsLocalRing A] [IsLocalRing B]
    [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing C]
    (φ : A →+* B) [IsLocalHom φ] (hf : φ.Flat)
    (e : (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) ≃+* C) :
    ringKrullDim B = ringKrullDim A + ringKrullDim C := by
  let : Algebra A B := φ.toAlgebra
  have : Module.Flat A B := hf
  have : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap φ).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
  have : IsLocalRing (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) :=
    e.symm.isLocalRing
  change (IsLocalRing.maximalIdeal B).height =
    (IsLocalRing.maximalIdeal A).height +
      ((IsLocalRing.maximalIdeal B).map
        (Ideal.Quotient.mk (Ideal.map φ (IsLocalRing.maximalIdeal A)))).height at h
  have hm : (IsLocalRing.maximalIdeal B).map
      (Ideal.Quotient.mk (Ideal.map φ (IsLocalRing.maximalIdeal A))) =
      IsLocalRing.maximalIdeal (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal A)) := by
    have : IsLocalHom (Ideal.Quotient.mk
        (Ideal.map φ (IsLocalRing.maximalIdeal A))) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    rw [← IsLocalRing.maximalIdeal_comap
      (Ideal.Quotient.mk (Ideal.map φ (IsLocalRing.maximalIdeal A)))]
    exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  rw [hm] at h
  have h' := congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) h
  simpa only [WithBot.coe_add, IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ringKrullDim_eq_of_ringEquiv e] using h'

/-- Transport the finite-type dimension formula along an open inclusion (Stacks 02FX). -/
private theorem open_dimension_formula {K : Type u} [Field K]
    {Y : Scheme.{u}} (g : Y ⟶ Spec (.of K)) (V : Y.Opens)
    [LocallyOfFiniteType (V.ι ≫ g)] [QuasiCompact (V.ι ≫ g)] (v : V) :
    topologicalKrullDimAt (V.ι v) = ringKrullDim (Y.presheaf.stalk (V.ι v)) +
      (Cardinal.toENat (@Algebra.trdeg K (Y.residueField (V.ι v)) _ _
        (g.residueFieldAlgebraMap (V.ι v)).toAlgebra) : WithBot ℕ∞) := by
  let : V.toScheme.Over (Spec (.of K)) := ⟨V.ι ≫ g⟩
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (.of K)) :=
    show LocallyOfFiniteType (V.ι ≫ g) from inferInstance
  have : QuasiCompact (V.toScheme ↘ Spec (.of K)) :=
    show QuasiCompact (V.ι ≫ g) from inferInstance
  have hd := topologicalKrullDimAt_eq_stalk_dimension_add_residue_trdeg (K := K) V v
  let : Algebra K (Y.residueField (V.ι v)) :=
    (g.residueFieldAlgebraMap (V.ι v)).toAlgebra
  let : Algebra K (V.toScheme.residueField v) :=
    ((V.ι ≫ g).residueFieldAlgebraMap v).toAlgebra
  let e : Y.residueField (V.ι v) ≃ₐ[K] V.toScheme.residueField v :=
    { (asIso (V.ι.residueFieldMap v)).commRingCatIsoToRingEquiv with
      commutes' c := by
        change _ = (V.ι ≫ g).residueFieldAlgebraMap v c
        rw [Scheme.Hom.residueFieldAlgebraMap_comp]
        rfl }
  rw [← e.trdeg_eq] at hd
  rw [← ringKrullDim_eq_of_ringEquiv
    (asIso (V.ι.stalkMap v)).commRingCatIsoToRingEquiv] at hd
  exact (V.isOpen.topologicalKrullDimAt_eq v.2).symm.trans hd

/-- Identify the fibre scalar map through the canonical fibre square (Stacks 02FX). -/
private theorem fibre_scalar {Y T : Scheme.{u}} (g : Y ⟶ T) (y : Y) :
    CommRingCat.ofHom
        ((g.fiberToSpecResidueField (g y)).residueFieldAlgebraMap (g.asFiber y)) =
      g.residueFieldMap y ≫ (Y.residueFieldCongr (g.fiberι_asFiber y)).inv ≫
        (g.fiberι (g y)).residueFieldMap (g.asFiber y) := by
  apply Spec.map_injective
  rw [Scheme.Hom.specMap_residueFieldAlgebraMap]
  apply (cancel_mono (T.fromSpecResidueField (g y))).mp
  simp only [Spec.map_comp, Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    Scheme.residueFieldCongr_inv, Scheme.residueFieldCongr_fromSpecResidueField_assoc]
  rw [← g.fiber_fac]
  simp only [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc]

/-- Express fibre dimension using the original residue fields (Stacks 02FX). -/
private theorem fibre_dimension_formula {Y T : Scheme.{u}} (g : Y ⟶ T)
    (y : Y) (V : (g.fiber (g y)).Opens)
    [LocallyOfFiniteType (V.ι ≫ g.fiberToSpecResidueField (g y))]
    [QuasiCompact (V.ι ≫ g.fiberToSpecResidueField (g y))]
    (v : V) (hv : V.ι v = g.asFiber y)
    [IsIso ((g.fiberι (g y)).residueFieldMap (V.ι v))] :
    topologicalKrullDimAt (g.asFiber y) =
      ringKrullDim ((g.fiber (g y)).presheaf.stalk (g.asFiber y)) +
      (Cardinal.toENat (@Algebra.trdeg (T.residueField (g y)) (Y.residueField y) _ _
        (g.residueFieldMap y).hom.toAlgebra) : WithBot ℕ∞) := by
  have hd := open_dimension_formula (g.fiberToSpecResidueField (g y)) V v
  rw [hv] at hd
  have : IsIso ((g.fiberι (g y)).residueFieldMap (g.asFiber y)) := hv ▸ inferInstance
  let : Algebra (T.residueField (g y)) (Y.residueField y) :=
    (g.residueFieldMap y).hom.toAlgebra
  let : Algebra (T.residueField (g y))
      ((g.fiber (g y)).residueField (g.asFiber y)) :=
    ((g.fiberToSpecResidueField (g y)).residueFieldAlgebraMap (g.asFiber y)).toAlgebra
  let e : Y.residueField y ≃ₐ[T.residueField (g y)]
      (g.fiber (g y)).residueField (g.asFiber y) :=
    { ((Y.residueFieldCongr (g.fiberι_asFiber y)).symm ≪≫
        asIso ((g.fiberι (g y)).residueFieldMap (g.asFiber y))).commRingCatIsoToRingEquiv
      with
      commutes' c := by
        exact (ConcreteCategory.congr_hom (fibre_scalar g y) c).symm }
  exact hd.trans (congrArg
    (fun c : Cardinal =>
      ringKrullDim ((g.fiber (g y)).presheaf.stalk (g.asFiber y)) +
        (Cardinal.toENat c : WithBot ℕ∞)) e.trdeg_eq.symm)

/-- Source: Stacks Project, Tag 02JS (blueprint: lem-sbc-flat-composite-fibre-dimension-at-point).

Proof:
1. Put x = a(u) and s = f(x). By `lem-sbc-composite-fibre-local-models`, set
   A = O_{X_s,x}, B = O_{U_s,u}, and C = O_{U_x,u}. These are Noetherian local
   rings, A → B is local and flat by flatness of a at u, and B / m_A B ≅ C.
   The same lemma gives finite-type affine neighbourhoods in the three fibres
   with the required stalk and residue-field identifications. This uses no
   Noetherian hypothesis on S.
2. Apply `lem-weil-pbc-flat-height-formula` (Stacks 00ON) at the maximal ideal
   of B. Its contraction is m_A, and localizing either local ring at its
   maximal ideal changes nothing. Thus dim B = dim A + dim C.
3. Apply `lem-kun-dimension-formula` to the three affine neighbourhoods and
   `lem-weil-pbc-dimension-at-point-open-subspace` to pass to the whole fibres.
   This gives dim_u U_s = dim B + trdeg_{κ(s)} κ(u),
   dim_u U_x = dim C + trdeg_{κ(x)} κ(u), and
   dim_x X_s = dim A + trdeg_{κ(s)} κ(x). These equalities take values
   in extended dimensions. No separate
   finiteness bound is needed because the final calculation only adds terms.
4. Apply `lem-sbc-transcendence-degree-tower` to κ(s) → κ(x) → κ(u).
   Substitute trdeg_{κ(s)} κ(u) = trdeg_{κ(x)} κ(u) + trdeg_{κ(s)} κ(x)
   and the equality from step 2 into step 3. Rearranging the sums gives
   dim_u U_s = (dim C + trdeg_{κ(x)} κ(u)) +
   (dim A + trdeg_{κ(s)} κ(x)) = dim_u U_x + dim_x X_s.
-/
theorem flat_composite_fibre_dimension_at_point
    {U X S : Scheme.{u}} (a : U ⟶ X) (f : X ⟶ S) (u : U)
    [LocallyOfFiniteType a] [LocallyOfFiniteType f]
    (hflat : (a.stalkMap u).hom.Flat) :
    topologicalKrullDimAt ((a ≫ f).asFiber u) =
      topologicalKrullDimAt (a.asFiber u) + topologicalKrullDimAt (f.asFiber (a u)) := by
  obtain ⟨hA, hB, hC, ⟨b, hb₁, hb₂, hb, φ, hφ, hlocal, ⟨e, he⟩, hr, hf⟩,
    ⟨V, hV, hVft, hVqc, v, hv, hvs, hvr, hvi, hvir⟩,
    ⟨W, hW, hWft, hWqc, w, hw, hws, hwr, hwi, hwir⟩,
    ⟨T, hT, hTft, hTqc, t, ht, hts, htr, hti, htir⟩, htower⟩ :=
    composite_fibre_local_models a f u
  have hd := local_flat_dimension φ (hf hflat) e
  have hX := fibre_dimension_formula f (a u) V v hv
  have hU := @fibre_dimension_formula U S (a ≫ f) u W hWft hWqc w hw hwi
  have hF := fibre_dimension_formula a u T t ht
  let : Algebra (S.residueField (f (a u))) (X.residueField (a u)) :=
    (f.residueFieldMap (a u)).hom.toAlgebra
  let : Algebra (X.residueField (a u)) (U.residueField u) :=
    (a.residueFieldMap u).hom.toAlgebra
  let : Algebra (S.residueField (f (a u))) (U.residueField u) :=
    ((a ≫ f).residueFieldMap u).hom.toAlgebra
  have : IsScalarTower (S.residueField (f (a u))) (X.residueField (a u))
      (U.residueField u) :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom htower).symm
  have htrdeg := congrArg Cardinal.toENat
    (trdeg_add_eq (S.residueField (f (a u))) (X.residueField (a u))
      (A := U.residueField u))
  rw [map_add] at htrdeg
  rw [hU, hF, hX]
  erw [hd, ← htrdeg, WithBot.coe_add]
  ac_rfl

end AlgebraicGeometry
