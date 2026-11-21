/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.DirectedColimitHomology

/-!
# Filtered-colimit comparison on finite spectral-sequence pages

Source: Stacks Project, Tags 0EZM and 00DB.
-/

@[expose] public section

universe u

namespace CategoryTheory

open Limits

/-- Page-one comparison propagates to each finite page, without convergence hypotheses.

Source: Stacks Project, Tags 0EZM and 00DB. -/
theorem spectral_sequence_finite_page_comparison
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (E : I ⥤ SpectralSequence AddCommGrpCat.{u}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (E' : SpectralSequence AddCommGrpCat.{u}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1)
    (v : ∀ i : I, E.obj i ⟶ E')
    (hv : ∀ {i j : I} (f : i ⟶ j), E.map f ≫ v j = v i)
    (hpage : ∀ (p q : ℤ)
      (φ : colimit (E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 1 ⋙
        HomologicalComplex.eval _ _ ⟨p, q⟩) ⟶ (E'.page 1).X ⟨p, q⟩),
      (∀ i : I, colimit.ι _ i ≫ φ = ((v i).hom 1).f ⟨p, q⟩) → IsIso φ) :
    ∀ (r : ℤ) (hr : 1 ≤ r) (p q : ℤ)
      (φ : colimit (E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 r hr ⋙
        HomologicalComplex.eval _ _ ⟨p, q⟩) ⟶ (E'.page r hr).X ⟨p, q⟩),
      (∀ i : I, colimit.ι _ i ≫ φ = ((v i).hom r hr).f ⟨p, q⟩) → IsIso φ := by
  classical
  intro r hr
  induction r, hr using Int.leInduction with
  | base => exact hpage
  | succ r hr ih =>
    let P := SpectralSequence.pageFunctor AddCommGrpCat.{u}
      (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 r hr
    let s : Cocone (E ⋙ P) :=
      { pt := E'.page r hr
        ι :=
          { app := fun i ↦ (v i).hom r hr
            naturality := fun i j f ↦ by
              simpa [P] using congrArg (fun w ↦ w.hom r hr) (hv f) } }
    have hs : IsColimit s := by
      apply HomologicalComplex.isColimitOfEval
      intro pq
      have h : IsIso (colimit.desc _ ((HomologicalComplex.eval _ _ pq).mapCocone s)) :=
        ih pq.1 pq.2 _ (fun i ↦ colimit.ι_desc _ i)
      change IsIso ((colimit.isColimit _).desc
        ((HomologicalComplex.eval _ _ pq).mapCocone s)) at h
      exact (colimit.isColimit _).ofPointIso
    intro p q φ hφ
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
      (ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) (p, q)
    have : PreservesColimitsOfShape I H := directed_colimit_homology _ _
    have hH := isColimitOfPreserves H hs
    let e := Functor.isoWhiskerLeft E
      (SpectralSequence.pageHomologyNatIso AddCommGrpCat.{u}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 r (r + 1) (p, q))
    let t := (H.mapCocone s).extend (E'.iso r (r + 1) (p, q)).hom
    have ht : IsColimit t := hH.extendIso _
    let u : Cocone (E ⋙ SpectralSequence.pageFunctor AddCommGrpCat.{u}
        (fun r ↦ ComplexShape.up' (⟨1 - r, r⟩ : ℤ × ℤ)) 1 (r + 1) ⋙
        HomologicalComplex.eval _ _ (p, q)) :=
      { pt := (E'.page (r + 1)).X (p, q)
        ι :=
          { app := fun i ↦ ((v i).hom (r + 1)).f (p, q)
            naturality := fun i j f ↦ by
              have h := congrArg (fun w ↦ (w.hom (r + 1)).f (p, q)) (hv f)
              change ((E.map f).hom (r + 1)).f (p, q) ≫
                ((v j).hom (r + 1)).f (p, q) = ((v i).hom (r + 1)).f (p, q) at h
              exact h } }
    have he : (Cocone.precompose e.hom).obj u ≅ t := by
      refine Cocone.ext (Iso.refl _) ?_
      intro i
      simpa [e, u, t, H, s, P] using ((v i).comm r (r + 1) (p, q)).symm
    have hu : IsColimit u :=
      (IsColimit.precomposeHomEquiv e u).1 (ht.ofIsoColimit he.symm)
    let a := (colimit.isColimit _).coconePointUniqueUpToIso hu
    have hEq : φ = a.hom := by
      apply colimit.hom_ext
      intro i
      rw [hφ i]
      exact ((colimit.isColimit _).comp_coconePointUniqueUpToIso_hom hu i).symm
    rw [hEq]
    infer_instance

end CategoryTheory
