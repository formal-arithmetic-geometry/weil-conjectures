/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Sheaf.AlgebraicGeometry.PicardNormalizedFpqc
import WeilConjectures.AlgebraicGeometry.DensePoints
import WeilConjectures.AlgebraicGeometry.Picard.RationalPoint

/-! # Fpqc descent for the relative Picard sheaf of a curve -/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

private theorem isSheaf_fpqc_of_fppf_of_baseChange {B B' : Scheme.{u}}
    (g : B' ⟶ B) [Flat g] [Surjective g] [LocallyOfFinitePresentation g]
    (F : (Over B)ᵒᵖ ⥤ Type (u + 1))
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over B) F)
    (hFG : Presheaf.IsSheaf (Scheme.fpqcTopology.over B') ((Over.map g).op ⋙ F)) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over B) F := by
  rw [isSheaf_iff_isSheaf_of_type] at hF hFG ⊢
  intro T R hR
  let T' : Over B := Over.mk (pullback.snd g T.hom ≫ T.hom)
  let a : T' ⟶ T := Over.homMk (pullback.snd g T.hom)
  let Q : Sieve T := Sieve.ofArrows (fun _ : PUnit.{1} ↦ T') (fun _ ↦ a)
  have hQ : Q ∈ (Scheme.fppfTopology.over B) T := by
    rw [GrothendieckTopology.mem_over_iff]
    change Sieve.overEquiv T (Sieve.ofArrows (fun _ : PUnit.{1} ↦ T') (fun _ ↦ a)) ∈ _
    rw [Sieve.overEquiv_ofArrows]
    change Sieve.generate (Presieve.ofArrows (fun _ : PUnit.{1} ↦ pullback g T.hom)
      (fun _ ↦ pullback.snd g T.hom)) ∈ _
    rw [Presieve.ofArrows_pUnit]
    exact Precoverage.generate_mem_toGrothendieck
      (Scheme.Hom.singleton_mem_fppfPrecoverage _)
  refine Presieve.isSheafFor_trans F Q R (hF _ hQ) ?_ ?_
  · intro Y b _
    exact (hF _ ((Scheme.fppfTopology.over B).pullback_stable b hQ)).isSeparatedFor
  · intro Y b hb
    obtain ⟨i, c, hc⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hb
    let q : Y.left ⟶ B' := c.left ≫ pullback.fst g T.hom
    have hq : q ≫ g = Y.hom := by
      dsimp [q]
      rw [Category.assoc, pullback.condition]
      exact Over.w c
    let Y' : Over B' := Over.mk q
    let e : (Over.map g).obj Y' ≅ Y := Over.isoMk (Iso.refl Y.left) (by
      change (𝟙 Y.left) ≫ Y.hom = q ≫ g
      simpa using hq.symm)
    let R' : Sieve Y' := (Sieve.overEquiv Y').symm (Sieve.overEquiv Y (R.pullback b))
    have hR' : R' ∈ (Scheme.fpqcTopology.over B') Y' := by
      rw [GrothendieckTopology.mem_over_iff]
      change Sieve.overEquiv Y' ((Sieve.overEquiv Y').symm _) ∈ _
      rw [OrderIso.apply_symm_apply]
      exact (GrothendieckTopology.mem_over_iff _ _).1
        ((Scheme.fpqcTopology.over B).pullback_stable b hR)
    have h := (Presieve.isSheafFor_over_map_op_comp_iff g F R' e).1 (hFG _ hR')
    convert h using 1
    apply congrArg Sieve.arrows
    rw [Sieve.functorPushforward_over_map]
    apply (Sieve.overEquiv Y).injective
    rw [Sieve.overEquiv_pullback, Sieve.overEquiv_pullback, OrderIso.apply_symm_apply]
    simp only [e, Over.isoMk_inv_left, Iso.refl_inv]
    ext Z a
    simp only [Sieve.pullback_apply, Category.comp_id]


private theorem isSheaf_fpqc_picardFunctor_of_section {X B : Scheme.{u}}
    (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B)
    (hf : ∀ T : Over B, IsIso (pushforwardUnitMap (pullback.snd f T.hom))) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over B) (picardFunctor f).obj := by
  let η := (picardFunctorNormalized f σ hσ).ι ≫ toPicardFunctor f
  have : IsIso η := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    rw [isIso_iff_bijective]
    exact bijective_toPicardFunctor_picardFunctorNormalized f σ hσ hf T.unop
  exact (Presheaf.isSheaf_of_iso_iff (asIso η)).1
    (isSheaf_fpqc_picardFunctorNormalized f σ hσ hf)

/-- The relative Picard sheaf of a smooth proper geometrically integral curve is an fpqc
sheaf. Choose a closed point with finite separable residue field. After extension to this
field the curve has a section; its universally trivial structure pushforward identifies
the Picard sheaf with normalized Picard classes. Normalized classes satisfy fpqc descent.
For a test scheme, pull back the finite field cover. The fppf sheaf property and the fpqc
sheaf property over this cover imply the fpqc sheaf property on the test scheme by the
transitivity lemma for sheaf conditions. Source: Stacks Project, Tags 0D28, 0D2B, 023T, 056U.
(blueprint: lem-pd-picard-sheaf-fpqc) -/
theorem isSheaf_fpqc_picardFunctor {k : Type u} [Field k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] [IsProper f]
    [GeometricallyIntegral f] :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over (Spec (.of k))) (picardFunctor f).obj := by
  have : Smooth f := SmoothOfRelativeDimension.smooth (n := 1) f
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton f
  obtain ⟨p, hp⟩ := f.dense_setOf_isClosed_finite_isSeparable.nonempty
  let K := C.residueField p
  let : Algebra k K := (f.residueFieldAlgebraMap p).toAlgebra
  have : Module.Finite k K := hp.2.1
  let g : Spec (.of K) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : Flat g := inferInstance
  have : Surjective g := inferInstance
  have : LocallyOfFinitePresentation g := by
    rw [LocallyOfFinitePresentation.SpecMap_iff]
    change (algebraMap k K).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]
    exact (Algebra.FinitePresentation.of_finiteType (R := k) (A := K)).mp inferInstance
  let C' := pullback f g
  let f' : C' ⟶ Spec (.of K) := pullback.snd f g
  let σ : Spec (.of K) ⟶ C' :=
    pullback.lift (C.fromSpecResidueField p) (𝟙 _) (by
      rw [Category.id_comp]
      exact (f.specMap_residueFieldAlgebraMap p).symm)
  have hσ : σ ≫ f' = 𝟙 _ := pullback.lift_snd _ _ _
  have : SmoothOfRelativeDimension 1 f' :=
    smoothOfRelativeDimension_pullback_snd 1 f g
  let : C'.Over (Spec (.of K)) := ⟨f'⟩
  have : SmoothOfRelativeDimension 1 (C' ↘ Spec (.of K)) := by
    change SmoothOfRelativeDimension 1 f'
    infer_instance
  have : IsProper (C' ↘ Spec (.of K)) := by
    change IsProper f'
    infer_instance
  have : GeometricallyIntegral (C' ↘ Spec (.of K)) := by
    change GeometricallyIntegral f'
    infer_instance
  have hf' (T : Over (Spec (.of K))) :
      IsIso (pushforwardUnitMap (pullback.snd f' T.hom)) :=
    isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral T
  have hF := isSheaf_fpqc_picardFunctor_of_section f' σ hσ hf'
  obtain ⟨e⟩ := nonempty_picardFunctor_iso_of_isPullback (IsPullback.of_hasPullback f g)
  exact isSheaf_fpqc_of_fppf_of_baseChange g (picardFunctor f).obj
    (picardFunctor f).property ((Presheaf.isSheaf_of_iso_iff e).2 hF)

end AlgebraicGeometry
