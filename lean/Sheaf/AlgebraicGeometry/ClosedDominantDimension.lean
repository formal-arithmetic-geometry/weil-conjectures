/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.SetTheory.Cardinal.ENat
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.Topology.KrullDimension
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Sheaf.TraceFormula.GenericFibreClosedChain
import Sheaf.TraceFormula.LocalDimensionFormula
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Dimension formula for a closed dominant morphism

Source: Stacks Project, Morphisms, Tag 02JX, lemma-alteration-dimension
(blueprint: lem-trf-closed-dominant-dimension).

The induced map of function fields `k(U) → k(V)` is the existing
`AlgebraicGeometry.Scheme.Hom.functionFieldMap` (the stalk map at the generic point), applied
to the identification `f (genericPoint V) = genericPoint U` given by
`AlgebraicGeometry.Scheme.Hom.apply_genericPoint_of_isDominant`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

private theorem flat_preimmersion_stalk_iso {X Y : Scheme.{u}} (j : X ⟶ Y)
    [Flat j] [IsPreimmersion j] (x : X) : IsIso (j.stalkMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨?_, j.stalkMap_surjective x⟩
  algebraize [(j.stalkMap x).hom]
  have : Module.FaithfullyFlat (Y.presheaf.stalk (j x)) (X.presheaf.stalk x) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap j x) (j.toLRSHom.prop x)
  exact ‹RingHom.FaithfullyFlat _›.injective

private theorem generic_field_pullback_integral
    {U V : Scheme.{u}} [IsIntegral U] [IsIntegral V]
    (f : V ⟶ U) [IsDominant f] :
    IsIntegral (Limits.pullback f (U.fromSpecStalk (genericPoint U))) := by
  let X := Limits.pullback f (U.fromSpecStalk (genericPoint U))
  let j : X ⟶ V := Limits.pullback.fst _ _
  have : IsPreimmersion j := by dsimp [j]; infer_instance
  have : Flat j := by dsimp [j]; infer_instance
  have hi (x : X) : IsIso (j.stalkMap x) := flat_preimmersion_stalk_iso j x
  have : IsReduced X := by
    have (x : X) : _root_.IsReduced (X.presheaf.stalk x) :=
      isReduced_of_injective (inv (j.stalkMap x)).hom
        (ConcreteCategory.bijective_of_isIso (inv (j.stalkMap x))).injective
    exact isReduced_of_isReduced_stalk X
  obtain ⟨a, ha⟩ : ∃ a : X, j a = genericPoint V := by
    have hx : genericPoint V ∈ Set.range j := by
      rw [show Set.range j = f ⁻¹' Set.range (U.fromSpecStalk (genericPoint U)) from
        Scheme.Pullback.range_fst _ _]
      exact ⟨IsLocalRing.closedPoint _, by simp [f.apply_genericPoint_of_isDominant]⟩
    exact hx
  have hgen : IsGenericPoint a (Set.univ : Set X) := by
    rw [isGenericPoint_def]
    apply Set.eq_univ_of_forall
    intro x
    exact specializes_iff_mem_closure.mp
      (j.isEmbedding.isInducing.specializes_iff.mp (ha ▸ genericPoint_specializes (j x)))
  have : PreirreducibleSpace X := ⟨hgen.isIrreducible.2⟩
  have : IrreducibleSpace X := ⟨⟨a⟩⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced X

private theorem functionFieldBaseRingHom_spec
    {K : Type u} [Field K] {X : Scheme.{u}}
    [X.Over (Spec (.of K))] [IsIntegral X] :
    Spec.map (CommRingCat.ofHom (functionFieldBaseRingHom (K := K) (X := X))) =
      X.fromSpecStalk (genericPoint X) ≫ (X ↘ Spec (.of K)) := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (.of K)).inv,
    ← Scheme.ΓSpecIso_inv_naturality]
  simp [functionFieldBaseRingHom,
    Scheme.fromSpecStalk_appTop, Scheme.germToFunctionField, Category.assoc]

private theorem functionFieldMap_spec {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (h : f (genericPoint X) = genericPoint Y) :
    Spec.map (f.functionFieldMap h) ≫ Y.fromSpecStalk (genericPoint Y) =
      X.fromSpecStalk (genericPoint X) ≫ f := by
  simp [Scheme.Hom.functionFieldMap, Spec.map_comp, Category.assoc]

private theorem base_dimension_le_height
    {U V : Scheme.{u}} [IsIntegral U] (f : V ⟶ U) (hf : IsClosedMap f)
    (x : V) (hx : f x = genericPoint U) :
    topologicalKrullDim U ≤ (Order.height x : WithBot ℕ∞) := by
  let Z := closure ({x} : Set V)
  have : QuasiSober Z := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  let g : Z → U := fun z ↦ f z.1
  have hg : IsClosedMap g := hf.comp isClosed_closure.isClosedMap_subtype_val
  have hη : genericPoint U ∈ Set.range g :=
    ⟨⟨x, subset_closure (Set.mem_singleton x)⟩, hx⟩
  have hsurj : Function.Surjective g := fun y ↦
    (genericPoint_specializes y).mem_closed hg.isClosed_range hη
  have hdim := topologicalKrullDim_le_of_specializingMap hg.specializingMap hsurj
  exact hdim.trans_eq (topologicalKrullDim_closure_singleton x)

/--
Source: Stacks Project, Morphisms, Tag 02JX, lemma-alteration-dimension
(blueprint: lem-trf-closed-dominant-dimension).

Let `f : V ⟶ U` be a dominant morphism locally of finite type between integral schemes with
`U` locally Noetherian, and let `r = trdeg_{k(U)} k(V)` for the injection of function fields
induced by `f` (the stalk map at the generic point). Then `dim V ≤ dim U + r`; if the
underlying map of `f` is closed, `dim V = dim U + r`; and if `f` is proper and `k(V)` is
finite over `k(U)`, then `dim V = dim U`. Dimensions are topological Krull dimensions in
`WithBot ℕ∞`, so infinite values are allowed.

Proof (Tag 02JX):
1. Let `ξ₀ ⤳ ⋯ ⤳ ξₑ` be a chain of specializations in `V`, `x = ξₑ`, `y = f x`. By
   lem-sc-scheme-stalk-dimension-generalization-chains the chain lies in the local scheme at
   `x`, so `e ≤ dim 𝒪_{V,x}`. By lem-trf-local-dimension-formula,
   `dim 𝒪_{V,x} ≤ dim 𝒪_{U,y} + r - trdeg_{κ(y)} κ(x)`; drop the last term and use
   `dim 𝒪_{U,y} ≤ dim U`. Taking the supremum gives `dim V ≤ dim U + r`.
2. Assume `f` closed. Take a chain `η = ξ̄₀ ⤳ ⋯ ⤳ ξ̄_d` in `U` from the generic point. The
   generic fibre `V_η = V ×_U Spec k(U)` is nonempty, integral, locally of finite type over
   `k(U)`. Its projection to `V` is a flat preimmersion, hence induces isomorphisms
   on stalks. Its image contains the generic point of `V`, which is generic also in the
   fibre. Thus the fibre is integral and has function field `k(V)`. Compatibility of the
   two function-field maps with the structure map gives an isomorphism over `k(U)`. By
   lem-trf-generic-fibre-closed-chain there is a closed point `ξ₀` of `V_η` and a chain of
   `r` specializations ending at `ξ₀`, with finite residue extension over `k(U)`.
3. The closed subset `closure {ξ₀}` maps onto `U`: its closed image contains the
   generic point. By lem-trf-closed-map-specializing, this restricted map is specializing.
   The dimension comparison for specializing surjections gives
   `dim U ≤ dim (closure {ξ₀}) = height ξ₀`.
4. The generic-fibre chain gives `r ≤ coheight ξ₀`. The chain-concatenation bound
   `height ξ₀ + coheight ξ₀ ≤ dim V` now gives `dim U + r ≤ dim V`, hence equality.
   These order-theoretic bounds allow infinite dimensions. Integrality excludes emptiness.
5. A proper `f` is closed by pqf-lem-proper-closed-map, and a finite extension
   `k(U) ⊆ k(V)` has transcendence degree zero, so the equality gives `dim V = dim U`.
-/
theorem closed_dominant_dimension
    (U V : Scheme.{u}) [IsIntegral U] [IsIntegral V]
    (f : V ⟶ U) [IsDominant f] [LocallyOfFiniteType f] [IsLocallyNoetherian U] :
    letI := (f.functionFieldMap f.apply_genericPoint_of_isDominant).hom.toAlgebra
    Function.Injective (algebraMap U.functionField V.functionField) ∧
      topologicalKrullDim V ≤ topologicalKrullDim U +
          (Cardinal.toENat (Algebra.trdeg U.functionField V.functionField) : WithBot ℕ∞) ∧
      (IsClosedMap f →
        topologicalKrullDim V = topologicalKrullDim U +
          (Cardinal.toENat (Algebra.trdeg U.functionField V.functionField) : WithBot ℕ∞)) ∧
      (IsProper f → Module.Finite U.functionField V.functionField →
        topologicalKrullDim V = topologicalKrullDim U) := by
  let := (f.functionFieldMap f.apply_genericPoint_of_isDominant).hom.toAlgebra
  have hle : topologicalKrullDim V ≤ topologicalKrullDim U +
      (Cardinal.toENat (Algebra.trdeg U.functionField V.functionField) : WithBot ℕ∞) := by
    rw [topologicalKrullDim_eq_krullDim_specializationOrder, Order.krullDim_eq_iSup_coheight]
    refine iSup_le fun x ↦ ?_
    rw [← ringKrullDim_stalk_eq_coheight]
    have hlocal := local_dimension_formula f x
    have hnonneg : (0 : WithBot ℕ∞) ≤
        (Cardinal.toENat
          (@Algebra.trdeg (U.residueField (f x)) (V.residueField x) _ _
            (f.residueFieldMap x).hom.toAlgebra) : WithBot ℕ∞) := by
      exact WithBot.coe_le_coe.mpr (by positivity)
    have hdrop := (le_add_of_nonneg_right hnonneg).trans hlocal
    have hstalk : ringKrullDim (U.presheaf.stalk (f x)) ≤ topologicalKrullDim U := by
      rw [ringKrullDim_stalk_eq_coheight]
      exact coheight_le_topologicalKrullDim (f x)
    exact hdrop.trans (add_le_add hstalk le_rfl)
  have heq : IsClosedMap f → topologicalKrullDim V = topologicalKrullDim U +
      (Cardinal.toENat (Algebra.trdeg U.functionField V.functionField) : WithBot ℕ∞) := by
    intro hf
    apply le_antisymm hle
    let X := Limits.pullback f (U.fromSpecStalk (genericPoint U))
    let j : X ⟶ V := Limits.pullback.fst _ _
    let q : X ⟶ Spec U.functionField := Limits.pullback.snd _ _
    have : IsIntegral X := generic_field_pullback_integral f
    have : Flat j := by dsimp [j]; infer_instance
    have : IsPreimmersion j := by dsimp [j]; infer_instance
    have hj := j.apply_genericPoint_of_flat
    have hi (x : X) : IsIso (j.stalkMap x) := flat_preimmersion_stalk_iso j x
    let φ := j.functionFieldMap hj
    have : IsIso φ := by
      have hiso : IsIso (V.presheaf.stalkSpecializes (specializes_of_eq hj)) := by
        have he : V.presheaf.stalkSpecializes (specializes_of_eq hj) =
            (V.presheaf.stalkCongr (Inseparable.of_eq hj.symm)).hom := by
          rw [TopCat.Presheaf.stalkCongr_hom]
        rw [he]
        infer_instance
      dsimp [φ, Scheme.Hom.functionFieldMap]
      infer_instance
    let : X.Over (Spec U.functionField) := ⟨q⟩
    have : LocallyOfFiniteType (X ↘ Spec U.functionField) := by
      change LocallyOfFiniteType q
      dsimp [q]
      infer_instance
    let := (functionFieldBaseRingHom (K := U.functionField) (X := X)).toAlgebra
    have hcompat :
        f.functionFieldMap f.apply_genericPoint_of_isDominant ≫ φ =
          CommRingCat.ofHom (functionFieldBaseRingHom (K := U.functionField) (X := X)) := by
      apply Spec.map_injective
      apply (cancel_mono (U.fromSpecStalk (genericPoint U))).mp
      rw [Spec.map_comp, Category.assoc, functionFieldMap_spec,
        ← Category.assoc, functionFieldMap_spec, Category.assoc,
        show j ≫ f = q ≫ U.fromSpecStalk (genericPoint U) from Limits.pullback.condition,
        ← Category.assoc, functionFieldBaseRingHom_spec]
      rfl
    let e : V.functionField ≃ₐ[U.functionField] X.functionField :=
      { (asIso φ).commRingCatIsoToRingEquiv with
        commutes' := fun a ↦ congr($(hcompat) a) }
    obtain ⟨r, hr, x, ξ, hxclosed, hξfirst, hξlast, hξstep, hxfin⟩ :=
      exists_generic_fibre_closed_chain (K := U.functionField) (X := X)
    have hr' : Algebra.trdeg U.functionField V.functionField = (r : Cardinal) :=
      e.trdeg_eq.trans hr
    rw [hr']
    simp only [map_natCast]
    have hxη : f (j x) = genericPoint U := by
      rw [← Scheme.Hom.comp_apply,
        show j ≫ f = q ≫ U.fromSpecStalk (genericPoint U) from Limits.pullback.condition,
        Scheme.Hom.comp_apply]
      have he : q x = IsLocalRing.closedPoint U.functionField :=
        Subsingleton.elim (α := PrimeSpectrum U.functionField) _ _
      rw [he, Scheme.fromSpecStalk_closedPoint]
    have hbase := base_dimension_le_height f hf (j x) hxη
    let p : LTSeries Vᵒᵈ :=
      { length := r
        toFun := fun i ↦ j (ξ i)
        step := fun i ↦
          ⟨(hξstep i).1.map j.continuous, fun hrev ↦
            (hξstep i).2 (j.isEmbedding.injective
              (((hξstep i).1.map j.continuous).antisymm hrev).eq)⟩ }
    have hco : (r : ℕ∞) ≤ Order.coheight (j x) := by
      have hhead : j x ≤ p.reverse.head := by
        simp only [RelSeries.head_reverse]
        change j x ≤ j (ξ (Fin.last r))
        rw [hξlast]
      exact Order.length_le_coheight hhead
    have hsum : ((Order.height (j x) + Order.coheight (j x) : ℕ∞) : WithBot ℕ∞) ≤
        topologicalKrullDim V := by
      rw [topologicalKrullDim_eq_krullDim_specializationOrder,
        Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
      exact WithBot.coe_le_coe.mpr
        (le_iSup (fun a : V ↦ Order.height a + Order.coheight a) (j x))
    calc
      topologicalKrullDim U + ((r : ℕ∞) : WithBot ℕ∞) ≤
          (Order.height (j x) : WithBot ℕ∞) +
            (Order.coheight (j x) : WithBot ℕ∞) :=
        add_le_add hbase (WithBot.coe_le_coe.mpr hco)
      _ = ((Order.height (j x) + Order.coheight (j x) : ℕ∞) : WithBot ℕ∞) :=
        (WithBot.coe_add _ _).symm
      _ ≤ topologicalKrullDim V := hsum
  refine ⟨(algebraMap U.functionField V.functionField).injective, hle, heq, ?_⟩
  intro hp hfin
  have h := heq (IsProper.isClosedMap f)
  simpa only [trdeg_eq_zero, map_zero, WithBot.coe_zero, add_zero] using h

end AlgebraicGeometry
