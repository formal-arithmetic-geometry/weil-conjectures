/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedDescent
import WeilConjectures.AlgebraicGeometry.UnramifiedFieldFibreDecomposition
import WeilConjectures.AlgebraicGeometry.UnramifiedOrdinaryFibreCriterion

/-!
# Unramifiedness tested on geometric fibres

Source: Stacks Project, Morphisms, Tags 02G7 and 02G8; Descent, Tag 02VM
(blueprint: lem-trf-geometric-fibre-unramified-criterion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A locally finite type morphism is unramified if and only if its geometric fibres are
unramified. The algebraic closure chosen at each point is Mathlib's `AlgebraicClosure`.
Empty geometric fibres are permitted, and the base scheme is arbitrary.
Source: Stacks Project, Morphisms, Tags 02G7 and 02G8; Descent, Tag 02VM
(blueprint: lem-trf-geometric-fibre-unramified-criterion).

Proof:
1. Apply `lem-weil-pbc-unramified-base-change-open` to the canonical geometric point
   defining each geometric fibre (`def-weil-geometric-fibre`).
2. Conversely, form the ordinary fibre (`def-pc-scheme-fibre`). Its base change along
   the algebraic-closure extension is the given geometric fibre. This extension is an
   fpqc singleton cover by `lem-pc-field-extension-fpqc-cover`. Descend unramifiedness
   using `lem-galois-fpqc-descend-unramified`.
3. By `lem-trf-unramified-field-fibre-decomposition` (Tag 02G7), every ordinary fibre is
   a disjoint union of spectra of finite separable extensions of the residue field.
4. Apply `lem-trf-unramified-ordinary-fibre-criterion` (Tag 02G8(2)), using the given
   local finite type hypothesis (`def-weil-finite-type-morphism`). -/
theorem unramified_iff_unramified_geometric_fibres
    {Z B : Scheme.{u}} (h : Z ⟶ B) [LocallyOfFiniteType h] :
    (LocallyOfFiniteType h ∧ IsOpenImmersion (pullback.diagonal h)) ↔
      ∀ s : B,
        LocallyOfFiniteType
          (pullback.snd h
            (Spec.map (CommRingCat.ofHom
              (algebraMap (B.residueField s) (AlgebraicClosure (B.residueField s)))) ≫
                B.fromSpecResidueField s)) ∧
          IsOpenImmersion
            (pullback.diagonal
              (pullback.snd h
                (Spec.map (CommRingCat.ofHom
                  (algebraMap (B.residueField s) (AlgebraicClosure (B.residueField s)))) ≫
                    B.fromSpecResidueField s))) := by
  constructor
  · intro hh s
    obtain ⟨hlft, hopen, _⟩ := unramified_baseChange_restrict_open h hh
      (Spec.map (CommRingCat.ofHom
        (algebraMap (B.residueField s) (AlgebraicClosure (B.residueField s)))) ≫
          B.fromSpecResidueField s)
    exact ⟨hlft, hopen⟩
  · intro hgeom
    apply unramified_of_ordinary_fibre_coproduct_finite_separable h
    intro s
    let g := Spec.map (CommRingCat.ofHom
      (algebraMap (B.residueField s) (AlgebraicClosure (B.residueField s))))
    have hfibre : LocallyOfFiniteType (h.fiberToSpecResidueField s) ∧
        IsOpenImmersion (pullback.diagonal (h.fiberToSpecResidueField s)) := by
      apply locallyOfFiniteType_and_openDiagonal_of_fpqcCover
        (h.fiberToSpecResidueField s) (fun _ : PUnit.{1} ↦ g)
      · simpa only [Presieve.ofArrows_pUnit, g] using!
          (fpqcCover_specMap_algebraMap_of_field
            (k := B.residueField s) (K := AlgebraicClosure (B.residueField s))).2.2.2
      · intro _
        let e := pullbackLeftPullbackSndIso h (B.fromSpecResidueField s) g
        have hlft := (hgeom s).1
        have hopen := (hgeom s).2
        have hformal : FormallyUnramified
            (pullback.snd h (g ≫ B.fromSpecResidueField s)) := inferInstance
        have hlft' : LocallyOfFiniteType
            (e.hom ≫ pullback.snd h (g ≫ B.fromSpecResidueField s)) := inferInstance
        have hformal' : FormallyUnramified
            (e.hom ≫ pullback.snd h (g ≫ B.fromSpecResidueField s)) :=
          MorphismProperty.comp_mem _ _ _ inferInstance hformal
        rw [pullbackLeftPullbackSndIso_hom_snd] at hlft' hformal'
        exact ⟨hlft', by
          change IsOpenImmersion (pullback.diagonal
            (pullback.snd (pullback.snd h (B.fromSpecResidueField s)) g))
          infer_instance⟩
    obtain ⟨I, L, hfield, halg, hsep, e, he⟩ :=
      (unramified_iff_exists_iso_coproduct_spec_finite_separable
        (B.residueField s) (h.fiber s) (h.fiberToSpecResidueField s)).mp hfibre
    refine ⟨I, L, hfield, halg, fun i ↦ (hsep i).1, fun i ↦ (hsep i).2,
      e.symm, ?_⟩
    apply (Iso.inv_comp_eq e).2
    apply Sigma.hom_ext
    intro i
    simpa using (he i).symm

end AlgebraicGeometry
