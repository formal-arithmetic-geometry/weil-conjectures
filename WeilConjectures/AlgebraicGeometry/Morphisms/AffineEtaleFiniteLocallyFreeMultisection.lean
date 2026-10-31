/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree

import WeilConjectures.AlgebraicGeometry.FibreCohenMacaulayLocus
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteAtPoint
import WeilConjectures.AlgebraicGeometry.FinitePiecePersistence
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Morphisms.CohenMacaulayClosedPointSlice
import WeilConjectures.TraceFormula.FlatLFPCMLocusFibreDense

/-!
# An affine elementary étale finite locally free multisection

Source: Stacks Project, More on Morphisms, Tag 055W,
`lemma-fibre-geometrically-connected-reduced`, second paragraph.
(blueprint: lem-trf-affine-etale-finite-free-multisection)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

private theorem fibre_cm_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (y : X) (s : S) (x : f.fiber s) (hs : f y = s) (hx : f.fiberι s x = y) :
    ((IsLocalRing.depth (R := (f.fiber (f y)).presheaf.stalk (f.asFiber y))
        ((f.fiber (f y)).presheaf.stalk (f.asFiber y)) : WithBot ℕ∞) =
      ringKrullDim ((f.fiber (f y)).presheaf.stalk (f.asFiber y))) ↔
    ((IsLocalRing.depth (R := (f.fiber s).presheaf.stalk x)
        ((f.fiber s).presheaf.stalk x) : WithBot ℕ∞) =
      ringKrullDim ((f.fiber s).presheaf.stalk x)) := by
  subst s
  have he : f.asFiber y = x := (f.fiberι _).isEmbedding.injective (by simpa using hx.symm)
  rw [he]

private theorem exists_closed_cm_fibre_point {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] (s : S) (hs : Nonempty (f.fiber s)) :
    ∃ x : f.fiber s, x ∈ closedPoints (f.fiber s) ∧
      IsNoetherianRing ((f.fiber s).presheaf.stalk x) ∧
      (IsLocalRing.depth (R := (f.fiber s).presheaf.stalk x)
        ((f.fiber s).presheaf.stalk x) : WithBot ℕ∞) =
        ringKrullDim ((f.fiber s).presheaf.stalk x) := by
  let C : Set (f.fiber s) := {x |
    (IsLocalRing.depth (R := (f.fiber s).presheaf.stalk x)
      ((f.fiber s).presheaf.stalk x) : WithBot ℕ∞) =
      ringKrullDim ((f.fiber s).presheaf.stalk x)}
  have hbase (x : f.fiber s) : f (f.fiberι s x) = s :=
    (f.range_fiberι s).le ⟨x, rfl⟩
  have hC : IsOpen C := by
    convert (isOpen_fibre_depth_eq_ringKrullDim f).preimage (f.fiberι s).continuous using 1
    ext x
    exact (fibre_cm_iff f _ s x (hbase x) rfl).symm
  obtain ⟨x, _, _, hx⟩ := flat_lfp_cm_locus_fibre_dense f s Set.univ isOpen_univ
    ⟨hs.some, Set.mem_univ _⟩
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints ⟨x, hx⟩ hC.isLocallyClosed
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsLocallyNoetherian (f.fiber s) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField s)
  exact ⟨y, hyclosed, inferInstance, hy⟩

private theorem baseChange_fibre_iso {Y S U : Scheme.{u}} (h : Y ⟶ S)
    (a : U ⟶ S) (u : U) (s : S) (hu : a u = s) :
    ∃ e : (pullback.snd h a).fiber u ≅
        pullback (h.fiberToSpecResidueField s)
          (Spec.map ((S.residueFieldCongr hu).inv ≫ a.residueFieldMap u)),
      e.hom ≫ pullback.fst (h.fiberToSpecResidueField s)
          (Spec.map ((S.residueFieldCongr hu).inv ≫ a.residueFieldMap u)) ≫
          h.fiberι s = (pullback.snd h a).fiberι u ≫ pullback.fst h a ∧
      e.hom ≫ pullback.snd (h.fiberToSpecResidueField s)
          (Spec.map ((S.residueFieldCongr hu).inv ≫ a.residueFieldMap u)) =
          (pullback.snd h a).fiberToSpecResidueField u := by
  subst s
  change ∃ e : (pullback.snd h a).fiber u ≅
      pullback (h.fiberToSpecResidueField (a u)) (Spec.map (a.residueFieldMap u)),
    e.hom ≫ pullback.fst _ _ ≫ h.fiberι (a u) =
        (pullback.snd h a).fiberι u ≫ pullback.fst h a ∧
      e.hom ≫ pullback.snd _ _ = (pullback.snd h a).fiberToSpecResidueField u
  let H := isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback h a) u
  refine ⟨H.isoPullback, ?_, ?_⟩
  · simpa only [Scheme.residueFieldCongr_refl, Iso.refl_inv, Category.id_comp,
      Category.assoc, Scheme.Hom.fiberι, pullback.map, pullback.lift_fst] using
      congrArg (fun k ↦ k ≫ h.fiberι (a u)) H.isoPullback_hom_fst
  · exact H.isoPullback_hom_snd

/-- A nonempty fibre of a flat finitely presented family with geometrically reduced fibres
admits a finite locally free multisection with singleton fibre after an affine elementary
étale base change. The fibre isomorphism is canonical: it respects the projections to `Y`
and to the spectrum of the new residue field.

Source: Stacks Project, More on Morphisms, Tag 055W,
`lemma-fibre-geometrically-connected-reduced`, second paragraph.
Proof:
1. The fibre over `s` is locally of finite type over its residue field and locally Noetherian
   (`lem-weil-pbc-qcqs-morphism-permanence`, `def-weil-finite-type-morphism`,
   `lem-sbc-restricted-fibre-locally-noetherian`). Its stalks are Noetherian localizations
   of affine chart rings (`pqf-def-locnoeth`, `lem-weil-pbc-affine-open-stalk-localization`,
   `lem-weil-pbc-localization-noetherian`). No Noetherian hypothesis on the base is needed.
2. The relative Cohen--Macaulay locus is open and its intersection with this fibre is dense
   (`lem-sbc-fibre-cohen-macaulay-locus-open`, `lem-trf-flat-lfp-cm-locus-fibre-dense`).
   The fibre is Jacobson (`lem-sc-lft-over-field-jacobson-space`), so this nonempty open
   contains a closed Cohen--Macaulay point.
3. Use `lem-trf-cm-closed-point-flat-quasifinite-slice` to obtain a flat locally finitely
   presented locally quasi-finite slice with singleton special fibre. Its affine charts
   are finitely presented and hence finitely generated (`lem-weil-pbc-affine-opens-basis`,
   `lem-weil-pbc-lfp-affine-opens-finite-presentation`). Apply
   `lem-weil-pbc-etale-local-finite-at-point-elementary` at its isolated fibre point to
   get a finite open piece after an elementary étale base change.
4. Refine to an affine open neighbourhood of the distinguished base point
   (`lem-weil-pbc-affine-opens-basis`, `lem-weil-pbc-etale-composition-cancellation`).
   Residue fields are unchanged by this restriction. Pull back the finite open piece;
   `lem-weil-pbc-elementary-etale-finite-piece-persistence` preserves its singleton fibre.
5. Flatness and local finite presentation persist under base change and open restriction
   (`lem-weil-pbc-flat-morphism-base-change`, `lem-weil-pbc-qcqs-morphism-permanence`,
   `def-weil-open-immersion`, `def-sbc-locally-finite-presentation`). Thus the finite piece
   is finite locally free (`def-pc-finite-locally-free`). Compose its inclusion with the
   base change of the slice map to define the multisection, compatibly with projections
   (`def-pc-base-change`, `def-pc-fibre-product`).
6. Flatness and finite presentation of the family persist under base change. The fibre
   universal property canonically identifies each new fibre with the old fibre extended
   along the induced residue-field map. Further field extensions give the same base
   changes, preserving geometric reducedness and, at the distinguished point, geometric
   connectedness (`def-pc-fibre-product`, `def-pc-base-change`,
   `def-pc-geometrically-irreducible`).
(blueprint: lem-trf-affine-etale-finite-free-multisection) -/
theorem exists_affine_etale_finiteLocallyFree_multisection
    {Y S : Scheme.{u}} [IsAffine S] (h : Y ⟶ S) [Flat h]
    [LocallyOfFinitePresentation h] [QuasiCompact h] [QuasiSeparated h]
    (hred : ∀ t : S, GeometricallyReduced (h.fiberToSpecResidueField t))
    (s : S) (hs : Nonempty (h.fiber s)) :
    ∃ (U : Scheme.{u}) (a : U ⟶ S) (u : U) (hu : a u = s),
      IsAffine U ∧ Etale a ∧ IsIso (a.residueFieldMap u) ∧
      ∃ (E : Scheme.{u}) (p : E ⟶ U) (σ : E ⟶ pullback h a),
        Scheme.Hom.IsFiniteLocallyFree p ∧ σ ≫ pullback.snd h a = p ∧
        Nonempty (p.fiber u) ∧ Subsingleton (p.fiber u) ∧
        Flat (pullback.snd h a) ∧ LocallyOfFinitePresentation (pullback.snd h a) ∧
        QuasiCompact (pullback.snd h a) ∧ QuasiSeparated (pullback.snd h a) ∧
        (∀ v : U, GeometricallyReduced ((pullback.snd h a).fiberToSpecResidueField v)) ∧
        (∃ e : (pullback.snd h a).fiber u ≅
            pullback (h.fiberToSpecResidueField s)
              (Spec.map ((S.residueFieldCongr hu).inv ≫ a.residueFieldMap u)),
          e.hom ≫ pullback.fst (h.fiberToSpecResidueField s)
              (Spec.map ((S.residueFieldCongr hu).inv ≫ a.residueFieldMap u)) ≫
              h.fiberι s = (pullback.snd h a).fiberι u ≫ pullback.fst h a ∧
          e.hom ≫ pullback.snd (h.fiberToSpecResidueField s)
              (Spec.map ((S.residueFieldCongr hu).inv ≫ a.residueFieldMap u)) =
              (pullback.snd h a).fiberToSpecResidueField u) ∧
        (GeometricallyConnected (h.fiberToSpecResidueField s) →
          GeometricallyConnected ((pullback.snd h a).fiberToSpecResidueField u)) := by
  classical
  obtain ⟨y, hy, hnoeth, hdepth⟩ := exists_closed_cm_fibre_point h s hs
  have := hnoeth
  obtain ⟨Z, i, z, _, hf, hfp, hsingle, _⟩ :=
    exists_flat_locallyQuasiFinite_slice_of_closed_fibre_depth_eq_ringKrullDim
      h s y hy hdepth
  let f := i ≫ h
  have : Flat f := hf
  have : LocallyOfFinitePresentation f := hfp
  let x : Z := f.fiberι s z
  have hxs : f x = s := (f.range_fiberι s).le ⟨z, rfl⟩
  have hsub : Subsingleton (f.fiber s) :=
    ⟨fun z₁ z₂ ↦ (hsingle z₁).trans (hsingle z₂).symm⟩
  have hisolated : IsOpen ({f.asFiber x} : Set (f.fiber (f x))) := by
    have : Subsingleton (f.fiber (f x)) := by rw [hxs]; exact hsub
    exact isOpen_discrete _
  obtain ⟨U₀, a₀, u₀, ha₀, hu₀, hres₀, V, hfin, v, hv, hvuniq, hvx, hvres⟩ :=
    exists_etale_finite_open_of_isolated_fiber_point f x hisolated
  have := ha₀
  have := hres₀
  let j := U₀.affineCover.f (U₀.affineCover.idx u₀)
  obtain ⟨u, hu⟩ := U₀.affineCover.covers u₀
  change j u = u₀ at hu
  let a := j ≫ a₀
  let π : pullback f a ⟶ pullback f a₀ :=
    pullback.map f a f a₀ (𝟙 Z) j (𝟙 S) (by simp) (by simp [a])
  have hπp : π ≫ pullback.fst f a₀ = pullback.fst f a := by simp [π]
  have hπq : π ≫ pullback.snd f a₀ = pullback.snd f a ≫ j := by simp [π]
  obtain ⟨hfin', v', hv', hvuniq', _, _, _⟩ :=
    finitePiece_persistence_of_isIso_residueFieldMap f a₀ u₀ x hu₀.symm V v
      hfin hv hvuniq hvx hvres j u hu inferInstance π hπp hπq
  let E := π ⁻¹ᵁ V
  let p : E.toScheme ⟶ _ := E.ι ≫ pullback.snd f a
  let σ : E.toScheme ⟶ pullback h a := E.ι ≫
    pullback.map f a h a i (𝟙 _) (𝟙 _) (by simp [f]) (by simp)
  have : IsFinite p := hfin'
  have hpflat : Flat p := inferInstance
  have hplfp : LocallyOfFinitePresentation p := inferInstance
  have hpff : p.IsFiniteLocallyFree := ⟨⟩
  have hpsub : Subsingleton (p.fiber u) := by
    refine ⟨fun e₁ e₂ ↦ (p.fiberι u).isEmbedding.injective ?_⟩
    have he (e : p.fiber u) : p.fiberι u e = v' :=
      hvuniq' _ ((p.range_fiberι u).le ⟨e, rfl⟩)
    exact (he e₁).trans (he e₂).symm
  have hpnonempty : Nonempty (p.fiber u) :=
    ⟨(p.fiberHomeo u).symm ⟨v', hv'⟩⟩
  have hau : a u = s := by
    change a₀ (j u) = s
    rw [hu, hu₀, hxs]
  have : IsIso (a₀.residueFieldMap (j u)) :=
    (congrArg (fun w : U₀ ↦ IsIso (a₀.residueFieldMap w)) hu).mpr hres₀
  have : IsIso (a.residueFieldMap u) := by
    dsimp [a]
    rw [Scheme.residueFieldMap_comp]
    infer_instance
  refine ⟨_, a, u, hau, inferInstance, inferInstance, inferInstance,
    E.toScheme, p, σ, hpff, ?_, hpnonempty, hpsub, inferInstance, inferInstance,
    inferInstance, inferInstance, ?_, baseChange_fibre_iso h a u s hau, ?_⟩
  · simp [σ, p]
  · intro v
    have : GeometricallyReduced (h.fiberToSpecResidueField (a v)) := hred (a v)
    exact MorphismProperty.of_isPullback
      (isPullback_fiberToSpecResidueField_of_isPullback
        (IsPullback.of_hasPullback h a) v) inferInstance
  · intro hc
    have hc' : GeometricallyConnected (h.fiberToSpecResidueField (a u)) := by
      rw [hau]
      exact hc
    have := hc'
    exact MorphismProperty.of_isPullback
      (isPullback_fiberToSpecResidueField_of_isPullback
        (IsPullback.of_hasPullback h a) u) inferInstance

end AlgebraicGeometry
