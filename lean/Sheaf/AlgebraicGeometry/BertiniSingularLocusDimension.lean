/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import Sheaf.AlgebraicGeometry.BertiniUniversalFamily
public import Mathlib.Topology.KrullDimension
public import Mathlib.LinearAlgebra.Basis.Defs
import Sheaf.AlgebraicGeometry.BertiniSingularFibreCharts
import Sheaf.AlgebraicGeometry.FiniteTypeFibreImageDimensionBounds
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.Topology.KrullDimension

/-!
# Dimension bound for the singular locus in a Bertini family

Source: Stacks Project, Varieties, Situation 0FD3 and Lemma 0FD6, universal-family proof
(blueprint: lem-zl-bertini-singular-locus-dimension).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

/-- The non-smooth locus of the universal Bertini family has dimension less than `r`,
and its image lies in a proper closed subset of coefficient affine space. The additive map
`ψ` and its scalar equation express exactly linearity for the canonical action through `f`.
The basis indexed by `ULift (Fin r)` expresses finite dimensionality and dimension `r`.

Source: Stacks Project, Tag 0FD6, universal-family proof
(blueprint: lem-zl-bertini-singular-locus-dimension).

Proof:
1. If `Y` is empty, the singular locus is empty and take `B` empty. If `r = 0`, generation
   forces the invertible sheaf's stalks to vanish, so `Y` is empty as well
   (`def-sc-invertible-module`, `def-weil-pbc-generating-sections`).
2. The projective immersion places `Y` in a Noetherian space, so it is quasi-compact;
   smoothness then makes it finite type. Affine trivializations show that the universal
   zero scheme is finite type. Its non-smooth locus is closed by openness of smoothness,
   hence its reduced induced scheme is finite type too. Use
   `lem-wf-affine-noetherian-components`, `lem-kun-finite-union-noetherian`,
   `lem-sfb-noetherian-space-compact-subsets`, `def-weil-closed-immersion`,
   `def-sbc-smooth-morphisms`, `def-weil-finite-type-morphism`, `def-pc-zero-scheme`.
3. On finitely many affine charts trivializing a generating section and the differential
   sheaf of rank `d`, the immersion and conormal sequence imply that the differentials of
   the section ratios span the cotangent fibres. Thus the value-and-differential matrix
   sends the `r` coordinates onto a vector space of dimension `d + 1`. Use
   `lem-weil-pbc-smooth-differentials-free-rank-fibre-dimension`,
   `lem-pur-conormal-sequence-smooth-immersion`, `def-sc-relative-differential-sheaf`,
   and `def-weil-pbc-morphism-to-projective-space-by-sections`.
4. Write `F = ∑ xⱼ fⱼ` locally. The ambient projection is smooth by smooth base change.
   The hypersurface nonzero-relative-differential criterion puts the non-smooth locus
   inside the closed locus `F = dF = 0`. This uses only containment, including at the zero
   parameter; it makes no false flatness inference there. Use
   `lem-pc-proper-base-change` (smoothness clause),
   `lem-zl-hypersurface-nonzero-relative-differential`,
   `def-sc-relative-differential-sheaf`, and `def-pc-zero-scheme`.
5. Each residue-field fibre of this linear kernel is affine space of dimension `r-d-1`,
   by the rank computation. The polynomial dimension formula and the finite-type fibre
   bound give dimension at most `r-1` on each chart, hence on its closed singular subspace.
   Use `lem-sf-noetherian-polynomial-dimension`,
   `lem-weil-pbc-spec-topological-krull-dimension-ring`, and
   `lem-zl-finite-type-fibre-image-dimension-bounds`.
6. Every chain of irreducible closed subsets can be restricted to a chart meeting its
   smallest member without losing strictness. Thus the singular locus has dimension
   at most `r-1 < r`. The finite-type image-dimension bound shows that the closure of its
   image has dimension less than `r`; affine coefficient space has dimension `r`, so
   that closure is the required proper closed subset. Use
   `lem-zl-finite-type-fibre-image-dimension-bounds`,
   `lem-sf-noetherian-polynomial-dimension`, and
   `lem-weil-pbc-spec-topological-krull-dimension-ring`. -/
theorem bertini_singularLocus_dimension_lt
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (L : Y.Modules) [L.IsInvertible]
    {V : Type v} [AddCommGroup V] [Module k V]
    (r : ℕ) (b : Module.Basis (ULift.{u} (Fin r)) k V)
    (ψ : V →+ Γ(L, ⊤))
    (_hlinear : ∀ (c : k) (v : V),
      ψ (c • v) = f.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) • ψ v)
    (hgen : Epi (L.freeHomEquiv.symm (fun i : ULift.{u} (Fin r) ↦
      (SheafOfModules.unitHomEquiv L) (Scheme.Modules.homOfGlobalSection L (ψ (b i))))))
    [IsImmersion (ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin r)) f L
      (fun i ↦ (SheafOfModules.unitHomEquiv L)
        (Scheme.Modules.homOfGlobalSection L (ψ (b i)))) hgen)] :
    topologicalKrullDim (bertiniUniversalSingularLocus f L (fun i ↦ ψ (b i))) <
        (r : WithBot ℕ∞) ∧
      ∃ B : Set (Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin r)) k))),
        IsClosed B ∧ B ≠ Set.univ ∧
          (bertiniUniversalProjection f L (fun i ↦ ψ (b i))) ''
            bertiniUniversalSingularLocus f L (fun i ↦ ψ (b i)) ⊆ B := by
  classical
  let s : ULift.{u} (Fin r) → Γ(L, ⊤) := fun i ↦ ψ (b i)
  let φ := ProjectiveSpace.homOfGeneratingSections (ULift.{u} (Fin r)) f L
    (fun i ↦ (SheafOfModules.unitHomEquiv L)
      (Scheme.Modules.homOfGlobalSection L (s i))) hgen
  let A := Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin r)) k))
  let a : A ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial _ k))
  let Z := (bertiniSingularIdeal f L s).subscheme
  let p : Z ⟶ Y := bertiniSingularToSource f L s
  let q : Z ⟶ A :=
    (bertiniSingularIdeal f L s).subschemeι ≫ bertiniUniversalProjection f L s
  have ha : LocallyOfFiniteType a := bertiniCoefficient_locallyOfFiniteType
  let : Y.Over (Spec (CommRingCat.of k)) := ⟨f⟩
  let : A.Over (Spec (CommRingCat.of k)) := ⟨a⟩
  have : LocallyOfFiniteType (A ↘ Spec (CommRingCat.of k)) := ha
  let : Z.Over (Spec (CommRingCat.of k)) := ⟨p ≫ f⟩
  have hq : q ≫ a = p ≫ f := by
    dsimp [q, p, bertiniSingularToSource, bertiniUniversalProjection, a]
    simp only [Category.assoc, pullback.condition]
  have : q.IsOver (Spec (CommRingCat.of k)) := ⟨hq⟩
  have hp : LocallyOfFiniteType p := by
    dsimp [p, bertiniSingularToSource]
    infer_instance
  have : LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k)) := by
    change LocallyOfFiniteType (p ≫ f)
    infer_instance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian (ProjectiveSpace (ULift.{u} (Fin r))
      (Spec (CommRingCat.of k))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (ProjectiveSpace (ULift.{u} (Fin r)) (Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k))
  have : QuasiCompact φ := by
    rw [← φ.liftCoborder_ι]
    infer_instance
  have : CompactSpace (ProjectiveSpace (ULift.{u} (Fin r))
      (Spec (CommRingCat.of k))) :=
    QuasiCompact.compactSpace_of_compactSpace
      (ProjectiveSpace (ULift.{u} (Fin r)) (Spec (CommRingCat.of k)) ↘
        Spec (CommRingCat.of k))
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace φ
  have : IsNoetherian Y := {}
  have : QuasiCompact p := by
    dsimp [p, bertiniSingularToSource]
    infer_instance
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace p
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian Z := {}
  have hdim : topologicalKrullDim Z < (r : WithBot ℕ∞) := by
    cases r with
    | zero =>
      have : IsEmpty Y := Function.isEmpty φ
      have : IsEmpty Z := Function.isEmpty p
      have : IsEmpty (IrreducibleCloseds Z) := ⟨fun C ↦ by
        obtain ⟨z, _⟩ := C.isIrreducible.nonempty
        exact isEmptyElim z⟩
      simp [topologicalKrullDim, Order.krullDim_eq_bot]
    | succ t =>
      choose U hyU hU d n hsum hbase hfib using
        bertini_singular_affine_fibre_charts f L t s hgen
      have hcover : ⨆ y, p ⁻¹ᵁ U y = ⊤ := by
        apply eq_top_iff.mpr
        intro z _
        exact Opens.mem_iSup.mpr ⟨p z, hyU (p z)⟩
      have hbound : topologicalKrullDim Z ≤ (t : WithBot ℕ∞) := by
        apply topologicalKrullDim_le_of_iSup_eq_top (fun y ↦ p ⁻¹ᵁ U y) hcover
        intro y
        let g := p ∣_ U y
        let : (U y : Scheme).Over (Spec (CommRingCat.of k)) := ⟨(U y).ι ≫ f⟩
        let : (p ⁻¹ᵁ U y : Scheme).Over (Spec (CommRingCat.of k)) :=
          ⟨(p ⁻¹ᵁ U y).ι ≫ p ≫ f⟩
        have : g.IsOver (Spec (CommRingCat.of k)) := by
          constructor
          change g ≫ (U y).ι ≫ f = (p ⁻¹ᵁ U y).ι ≫ p ≫ f
          rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
        have : LocallyOfFiniteType ((U y : Scheme) ↘ Spec (CommRingCat.of k)) := by
          change LocallyOfFiniteType ((U y).ι ≫ f)
          infer_instance
        have : LocallyOfFiniteType ((p ⁻¹ᵁ U y : Scheme) ↘ Spec (.of k)) := by
          change LocallyOfFiniteType ((p ⁻¹ᵁ U y).ι ≫ p ≫ f)
          infer_instance
        have : QuasiCompact ((U y : Scheme) ↘ Spec (.of k)) := by
          change QuasiCompact ((U y).ι ≫ f)
          infer_instance
        have : QuasiCompact ((p ⁻¹ᵁ U y : Scheme) ↘ Spec (.of k)) := by
          change QuasiCompact ((p ⁻¹ᵁ U y).ι ≫ p ≫ f)
          infer_instance
        have hb := (g.finiteType_fibre_image_dimension_bounds (k := k)).2
          (d y) (n y) (hbase y) (hfib y)
        exact hb.trans (by exact_mod_cast hsum y)
      exact hbound.trans_lt (by exact_mod_cast Nat.lt_succ_self t)
  have hdimS : topologicalKrullDim (bertiniUniversalSingularLocus f L s) =
      topologicalKrullDim Z :=
    ((bertiniSingularHomeomorph f L s).isHomeomorph.topologicalKrullDim_eq _).symm
  refine ⟨hdimS.trans_lt hdim, closure (Set.range q), isClosed_closure, ?_, ?_⟩
  · intro hB
    have hBdim := (q.finiteType_fibre_image_dimension_bounds (k := k)).1
    have hAdim : topologicalKrullDim A = (r : WithBot ℕ∞) := by
      change topologicalKrullDim (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin r)) k)) = _
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
        MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      simp
    have hlt := hBdim.trans_lt hdim
    rw [hB] at hlt
    have he := (Homeomorph.Set.univ A).isHomeomorph.topologicalKrullDim_eq _
    rw [he, hAdim] at hlt
    exact (lt_irrefl _ hlt)
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨z, hz⟩ := (bertiniSingularHomeomorph f L s).surjective ⟨h, hh⟩
    apply subset_closure
    refine ⟨z, ?_⟩
    exact congrArg (bertiniUniversalProjection f L s) (congrArg Subtype.val hz)

end

end AlgebraicGeometry
