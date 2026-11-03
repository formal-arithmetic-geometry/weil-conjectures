/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.GenericPoint
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.KummerCover
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.Basic

import WeilConjectures.AlgebraicGeometry.Sites.GaloisModule
import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Stalk

/-! # Finite generic multiplication fibres and the Galois action -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
namespace AlgebraicGeometry


private theorem generic_fibre_one_point
    (k : Type u) [Field k] (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]
    (n : ℕ) [IsFinite (𝟙 E ^ n).left] [Etale (𝟙 E ^ n).left] :
    Subsingleton (pullback (𝟙 E ^ n).left
      (E.left.fromSpecStalk (genericPoint E.left)) : Scheme.{u}) := by
  let f := (𝟙 E ^ n).left
  let K : Type u := E.left.functionField
  let b : Spec (.of K) ⟶ E.left := E.left.fromSpecStalk (genericPoint E.left)
  let Y := pullback f b
  let j := pullback.fst f b
  let q := pullback.snd f b
  have : IsPreimmersion j := inferInstance
  have : Etale q := inferInstance
  have : DiscreteTopology Y := by
    have hd := q.isDiscrete_preimage_singleton (default : Spec (.of K))
    have heq : q ⁻¹' {default} = Set.univ := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      exact Subsingleton.elim _ _
    rw [heq] at hd
    exact isDiscrete_univ_iff.mp hd
  have hη : genericPoint E.left ∈ Set.range j := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint E.left.functionField, ?_⟩
    change (E.left.fromSpecStalk (genericPoint E.left))
      (IsLocalRing.closedPoint E.left.functionField) = f (genericPoint E.left)
    rw [Scheme.fromSpecStalk_closedPoint]
    symm
    obtain ⟨w, hw, hfw⟩ := Flat.generalizingMap f
      (genericPoint_specializes (f (genericPoint E.left)))
    obtain rfl : w = genericPoint E.left :=
      (hw.antisymm (genericPoint_specializes w)).eq
    exact hfw
  obtain ⟨z, hz⟩ := hη
  have heq (w : Y) : z = w := by
    apply Specializes.eq
    apply j.isEmbedding.isInducing.specializes_iff.mp
    rw [hz]
    exact genericPoint_specializes _
  exact ⟨fun w v ↦ (heq w).symm.trans (heq v)⟩

private theorem field_points_transitive
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (Y : Scheme.{u}) [Subsingleton Y]
    (q : Y ⟶ Spec (.of K)) [IsFinite q] [Etale q]
    (x y : Over.mk (Scheme.specAlgebraMap K Ω) ⟶ Over.mk q) :
    ∃ σ : Gal(Ω/K), Scheme.galoisOverHom σ ≫ x = y := by
  have : Nonempty Y := ⟨x.left (IsLocalRing.closedPoint Ω)⟩
  have : IsAffine Y := isAffine_of_isAffineHom q
  have : IsReduced Y := isReduced_of_etale q
  have : IrreducibleSpace Y := ⟨inferInstance⟩
  have : IsIntegral Y := isIntegral_of_irreducibleSpace_of_isReduced Y
  let : Algebra K Γ(Y, ⊤) := q.ΓAlgebra
  let : Field Γ(Y, ⊤) := (isField_of_isIntegral_of_subsingleton Y).toField
  let a := q.overHomEquivAlgHom Ω x
  let b := q.overHomEquivAlgHom Ω y
  let e := a.equivFieldRange.symm.trans b.equivFieldRange
  let σ := e.liftNormal Ω
  refine ⟨σ, (q.overHomEquivAlgHom Ω).injective ?_⟩
  have hσ : σ.toAlgHom.comp a = b := by
    ext z
    have h := e.liftNormal_commutes Ω (a.equivFieldRange z)
    simpa [e, σ] using h
  change _ = b
  rw [← hσ]
  ext z
  change (((Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left).appTop ≫
    (Scheme.ΓSpecIso (.of Ω)).hom).hom z) = _
  rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
  rfl

/-- The absolute Galois group of the function field acts transitively on the
geometric generic fibre of a finite etale surjective multiplication map.

Pull back [n] to the generic field. The projection to E is a topological
embedding, being the base change of the generic stalk preimmersion. Flatness
makes its image contain the generic point of E. The finite etale fibre is
discrete; specialization from that generic point to every point, reflected
by the embedding, makes the fibre a one-point scheme. It is also affine and
reduced, so its global-section ring is a field. The two geometric points are
embeddings of that field into the separable closure. The isomorphism of
their ranges extends by normality to an automorphism of the separable closure.
Naturality of the affine-point equivalence gives precomposition by Spec sigma;
projecting from the pullback gives the displayed identity over k.
Source: step 2 of the multiplication tower in the scope counterexample.
(blueprint: lem-sf-elliptic-division-orbit-transitive) -/
theorem ellipticDivisionOrbitTransitive
    (k : Type u) [Field k] [IsAlgClosed k]
    (E : Over (Spec (.of k))) [GrpObj E] [IsAbelianVariety E]
    (n : ℕ) [IsFinite (𝟙 E ^ n).left] [Etale (𝟙 E ^ n).left]
    [Surjective (𝟙 E ^ n).left]
    (x y : ((Over.map E.hom).obj
      ((Scheme.ProEt.forget E.left).obj (Scheme.ProEt.genericPointSep E.left)) ⟶ E))
    (hx : x ≫ (𝟙 E ^ n) = Over.homMk (Scheme.ProEt.genericPointSep E.left).hom rfl)
    (hy : y ≫ (𝟙 E ^ n) = Over.homMk (Scheme.ProEt.genericPointSep E.left).hom rfl) :
    ∃ σ : SeparableClosure E.left.functionField ≃ₐ[E.left.functionField]
      SeparableClosure E.left.functionField,
      (Over.map E.hom).map ((Scheme.ProEt.forget E.left).map
        (Scheme.ProEt.genericPointSepAut E.left σ)) ≫ x = y := by
  classical
  let K : Type u := E.left.functionField
  let Ω := SeparableClosure K
  let f := (𝟙 E ^ n).left
  let b : Spec (.of K) ⟶ E.left := E.left.fromSpecStalk (genericPoint E.left)
  let g := Scheme.specAlgebraMap K Ω
  let Y := pullback f b
  let q := pullback.snd f b
  let j := pullback.fst f b
  have : IsFinite q := inferInstance
  have : Etale q := inferInstance
  have : Subsingleton Y := generic_fibre_one_point k E n
  have hx' : x.left ≫ f = g ≫ b := congrArg Over.Hom.left hx
  have hy' : y.left ≫ f = g ≫ b := congrArg Over.Hom.left hy
  let x' : Over.mk g ⟶ Over.mk q :=
    Over.homMk (pullback.lift x.left g hx') (by simp [q])
  let y' : Over.mk g ⟶ Over.mk q :=
    Over.homMk (pullback.lift y.left g hy') (by simp [q])
  obtain ⟨σ, hσ⟩ := field_points_transitive K Ω Y q x' y'
  refine ⟨σ, Over.OverMorphism.ext ?_⟩
  have h := congrArg (fun w ↦ w.left ≫ j) hσ
  change (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫
    pullback.lift x.left g hx') ≫ j = pullback.lift y.left g hy' ≫ j at h
  dsimp only [j] at h
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.left = y.left
  simpa only [Category.assoc, pullback.lift_fst] using h

end AlgebraicGeometry
