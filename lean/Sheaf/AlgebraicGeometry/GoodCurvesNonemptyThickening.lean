/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q5
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Sheaf.AlgebraicGeometry.Thickening
import Sheaf.AlgebraicGeometry.GoodCurvesAffineNonemptyThickening

/-!
# Good curve diagrams with a fibrewise nonempty thickening locus

Source: Stacks Project, More on Morphisms, Tag 0GK7, proof through the shrinking
which makes every W_i → T_i surjective.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Construct the curve presentation and a thickening locus which meets every fibre
of each smooth curve. Density is not asserted here.

Source: Stacks Project, More on Morphisms, Tag 0GK7, proof through the sentence
"Shrinking S once more we can assume W_i → T_i is surjective for all i".
(blueprint: lem-weil-pbc-good-curves-nonempty-thickening)

Proof: Choose an affine open A containing η. Its inverse-image component and the
specialization characterization of generic points show that η is generic in A.
The restricted morphism has the same fibre at η, by its explicit fibre homeomorphism.
Apply the affine-base presentation. For its open B in A, take the open image U in S.
Compose the cover with the isomorphism B ≅ U. Pasting the cartesian restriction squares
identifies the two pullbacks of X. Compose ν with this isomorphism and take the image of
W. The corresponding square of inverse-image opens is cartesian, so its projection is
isomorphic to the old thickening projection. This transports the thickening properties,
all commuting equations, and the point witnessing nonemptiness in each curve fibre. -/
theorem exists_good_curves_nonempty_thickening
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (η : S) (hη : ∃ Z ∈ irreducibleComponents S, IsGenericPoint η Z)
    (hdim : topologicalKrullDim (f.fiber η) ≤ 1) :
    ∃ (U : S.Opens) (_ : η ∈ U) (V : Scheme.{u}) (g : V ⟶ U.toScheme),
      IsFinite g ∧ Surjective g ∧ UniversallyInjective g ∧
      ∃ (n : ℕ) (T Y Ybar : Fin n → Scheme.{u})
        (t : ∀ i, T i ⟶ V) (j : ∀ i, Y i ⟶ Ybar i)
        (p : ∀ i, Ybar i ⟶ T i)
        (ν : (∐ Y) ⟶ pullback f (g ≫ U.ι)),
        IsFinite ν ∧ Surjective ν ∧
        (∀ i, Sigma.ι Y i ≫ ν ≫ pullback.snd f (g ≫ U.ι) = j i ≫ p i ≫ t i) ∧
        (∀ i, IsFinite (t i) ∧ Etale (t i)) ∧
        (∀ i, IsOpenImmersion (j i)) ∧
        (∀ i, Smooth (j i ≫ p i) ∧ Surjective (j i ≫ p i)) ∧
        (∀ i, Smooth (p i) ∧ IsProper (p i) ∧
          ∀ s : T i, GeometricallyConnected ((p i).fiberToSpecResidueField s) ∧
            topologicalKrullDim ((p i).fiber s) ≤ 1) ∧
        ∃ W : (pullback f (g ≫ U.ι)).Opens,
          (∀ (i : Fin n) (s : T i),
            ∃ y : (j i ≫ p i).fiber s,
              ((j i ≫ p i).fiberι s ≫ Sigma.ι Y i ≫ ν) y ∈ W) ∧
          IsThickening (pullback.snd ν W.ι) := by
  obtain ⟨A, hA, hηA, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := S) (x := η) (U := ⊤) (by trivial)
  let ηA : A.toScheme := ⟨η, hηA⟩
  have : IsAffine A.toScheme := hA
  obtain ⟨Z, hZ, hηZ⟩ := hη
  have hηA' : ∃ Z' ∈ irreducibleComponents A.toScheme, IsGenericPoint ηA Z' := by
    refine ⟨A.ι ⁻¹' Z, preimage_mem_irreducibleComponents hZ A.ι.isOpenEmbedding
      ⟨η, hηZ.mem, ⟨ηA, rfl⟩⟩, ?_⟩
    rw [isGenericPoint_iff_specializes]
    intro x
    change ηA ⤳ x ↔ A.ι x ∈ Z
    exact (A.ι.isOpenEmbedding.isInducing.specializes_iff (x := ηA) (y := x)).symm.trans
      hηZ.specializes_iff_mem
  let fA := f ∣_ A
  have hdimA : topologicalKrullDim (fA.fiber ηA) ≤ 1 := by
    let e : (fA ⁻¹' {ηA}) ≃ₜ (f ⁻¹' {η}) :=
      { toEquiv :=
          { toFun := fun x ↦ ⟨(f ⁻¹ᵁ A).ι x.1, by
              have hx := congrArg (fun z : A.toScheme ↦ A.ι z) x.2
              change f ((f ⁻¹ᵁ A).ι x.1) = η
              exact (morphismRestrict_base_coe f A x.1).symm.trans hx⟩
            invFun := fun x ↦ ⟨⟨x.1, by
              change f x.1 ∈ A
              rw [x.2]
              exact hηA⟩, by
              apply Subtype.ext
              exact (morphismRestrict_base_coe f A _).trans x.2⟩
            left_inv := fun x ↦ rfl
            right_inv := fun x ↦ rfl }
        continuous_toFun := by
          apply Continuous.subtype_mk
          exact (f ⁻¹ᵁ A).ι.continuous.comp continuous_subtype_val
        continuous_invFun := by
          apply Continuous.subtype_mk
          apply (f ⁻¹ᵁ A).ι.isOpenEmbedding.isInducing.continuous_iff.mpr
          exact continuous_subtype_val }
    let E := (fA.fiberHomeo ηA).trans (e.trans (f.fiberHomeo η).symm)
    rw [E.isHomeomorph.topologicalKrullDim_eq]
    exact hdim
  obtain ⟨B, hηB, V, g, hgfin, hgsurj, hginj, n, T, Y, Ybar, t, j, p, ν,
    hνfin, hνsurj, hcomm, ht, hj, hq, hp, W, hWmeet, hWthick⟩ :=
    exists_good_curves_affine_nonempty_thickening fA ηA hηA' hdimA
  let U : S.Opens := A.ι ''ᵁ B
  let g' : V ⟶ U.toScheme := g ≫ (A.ι.isoImage B).hom
  have hg' : g' ≫ U.ι = g ≫ B.ι ≫ A.ι := by simp [g', U]
  let e : pullback fA (g ≫ B.ι) ≅ pullback f (g' ≫ U.ι) :=
    (((IsPullback.of_hasPullback fA (g ≫ B.ι)).flip.paste_vert
      (isPullback_morphismRestrict f A)).flip.isoPullback) ≪≫
      pullback.congrHom rfl (by simpa only [Category.assoc] using hg'.symm)
  have hesnd : e.hom ≫ pullback.snd f (g' ≫ U.ι) = pullback.snd fA (g ≫ B.ι) := by
    simp [e]
  let ν' := ν ≫ e.hom
  let W' := e.hom ''ᵁ W
  have hνfin' : IsFinite ν' := by have := hνfin; infer_instance
  have hνsurj' : Surjective ν' := by have := hνsurj; infer_instance
  have hWthick' : IsThickening (pullback.snd ν' W'.ι) := by
    have : IsClosedImmersion (ν ∣_ W) := by
      have := hWthick.1
      change IsClosedImmersion ((pullbackRestrictIsoRestrict ν W).inv ≫ pullback.snd ν W.ι)
      infer_instance
    have : Surjective (ν ∣_ W) := by
      have := hWthick.2
      change Surjective ((pullbackRestrictIsoRestrict ν W).inv ≫ pullback.snd ν W.ι)
      infer_instance
    let k := (ν ∣_ W) ≫ (e.hom.isoImage W).hom
    have hk : IsClosedImmersion k := inferInstance
    have hks : Surjective k := inferInstance
    have hpb : IsPullback k (ν ⁻¹ᵁ W).ι W'.ι ν' := by
      apply IsOpenImmersion.isPullback
      · simp [k, W', ν', Category.assoc]
      · simp [ν', W']
    have he : hpb.isoPullback.inv ≫ k = pullback.fst W'.ι ν' :=
      hpb.isoPullback_inv_fst
    have hk' : IsClosedImmersion (pullback.fst W'.ι ν') := by
      rw [← he]
      infer_instance
    have hks' : Surjective (pullback.fst W'.ι ν') := by
      rw [← he]
      infer_instance
    constructor
    · have heq : (pullbackSymmetry ν' W'.ι).hom ≫ pullback.fst W'.ι ν' =
          pullback.snd ν' W'.ι := by simp
      rw [← heq]
      infer_instance
    · have heq : (pullbackSymmetry ν' W'.ι).hom ≫ pullback.fst W'.ι ν' =
          pullback.snd ν' W'.ι := by simp
      rw [← heq]
      infer_instance
  refine ⟨U, ⟨ηA, hηB, rfl⟩, V, g', ?_, ?_, ?_, n, T, Y, Ybar, t, j, p, ν',
    hνfin', hνsurj', ?_, ht, hj, hq, hp, W', ?_, hWthick'⟩
  · have := hgfin
    infer_instance
  · have := hgsurj
    infer_instance
  · have := hginj
    change UniversallyInjective (g ≫ (A.ι.isoImage B).hom)
    exact (MorphismProperty.cancel_right_of_respectsIso
      (@UniversallyInjective) g (A.ι.isoImage B).hom).mpr hginj
  · intro i
    simpa only [ν', Category.assoc, hesnd] using hcomm i
  · intro i s
    obtain ⟨y, hy⟩ := hWmeet i s
    refine ⟨y, ?_⟩
    exact ⟨((j i ≫ p i).fiberι s ≫ Sigma.ι Y i ≫ ν) y, hy, rfl⟩

end AlgebraicGeometry
