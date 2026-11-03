/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopDegree.TopDegreeTraceDefs
import WeilConjectures.AlgebraicGeometry.AffineSpace.AffineSpaceIteratedCoordinates
import WeilConjectures.AlgebraicGeometry.SmoothSectionCentredCoordinates.SmoothSectionAffineCoordinates

/-! # Centred coordinates for the point class

Source: sk-cor-trace, proof step 9, using lem-sc-smooth-section-affine-coordinates.
(blueprint: lem-pd-top-degree-point-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
namespace AlgebraicGeometry.ProEtale.CondensedRing.TopDegree

/-- A rational section of a smooth scheme has the two Cartesian coordinate
squares required by the local point-product normalization.
Source: sk-cor-trace, complement (ii), proof step 9
(blueprint: lem-pd-top-degree-point-coordinates).
Proof: take a centred affine smooth-section chart. Its base open contains the
unique point of Spec k, hence is the entire base. Transport that chart along
this base isomorphism and the coordinate-preserving comparison from affine
space to the ordered affine-line tower. Both preserve the zero section. The
chart's zero-fibre pullback gives the second square; restriction to its source
open gives the first square. Both maps are etale, and the empty tower is covered. -/
theorem exists_affinePointCoordinates {k : Type u} [Field k]
    (X : Over (Spec (.of k))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : Spec (.of k) ⟶ X.left) [IsClosedImmersion x]
    (hx : x ≫ X.hom = 𝟙 _) : ∃ q : PointCoordinates X d x, IsAffine q.U.left := by
  classical
  let S := Spec (.of k)
  obtain ⟨q, hq⟩ := SmoothSectionCentredCoordinates.exists_affineChart d X.hom x hx
    (Classical.arbitrary S)
  have hT : q.T.1 = ⊤ := by
    apply top_unique
    intro t _
    exact (Subsingleton.elim (Classical.arbitrary S) t) ▸ hq
  have : IsIso q.T.1.ι :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simpa using hT)
  let b : q.T.1.toScheme ≅ S := asIso q.T.1.ι
  let σ := x.resLE q.U.1 q.T.1 q.sectionInto
  let z := b.inv ≫ σ
  let m := asIso (AffineSpace.map (ULift.{u} (Fin d)) b.hom) ≪≫
    AffineSpace.iteratedIso S d
  let t := q.e ≫ m.hom
  let U : Over S := Over.mk (q.U.1.ι ≫ X.hom)
  have hz : z ≫ q.U.1.ι = x := by
    simp only [z, Category.assoc, σ, Scheme.Hom.resLE_comp_ι]
    change b.inv ≫ b.hom ≫ x = x
    simp
  have hzero : AffineSpace.zeroSection (ULift.{u} (Fin d)) q.T.1.toScheme ≫ m.hom =
      b.hom ≫ AffineZeroPurity.zero S d := by
    dsimp only [m, Iso.trans_hom, asIso_hom]
    rw [← Category.assoc, AffineSpace.zeroSection_comp_map, Category.assoc,
      AffineSpace.zeroSection_iteratedIso]
    rfl
  have hsq : IsPullback z (𝟙 S) t (AffineZeroPurity.zero S d) := by
    apply q.zeroFiber.of_iso b (Iso.refl _) b m
    · simp [z, σ]
    · simp
    · simp [t]
    · simpa only [Category.id_comp, AffineSpace.zeroSection, Pi.zero_def] using hzero
  have : Etale q.e := q.etale
  refine ⟨⟨U, q.U.1.ι, t, z, inferInstance, inferInstance, rfl, ?_, ?_, hsq⟩, ?_⟩
  · dsimp only [t, m, Iso.trans_hom, asIso_hom, U, Over.mk_hom]
    rw [Category.assoc, Category.assoc, AffineSpace.iteratedIso_hom_proj,
      AffineSpace.map_over, ← Category.assoc, q.over]
    change X.hom.resLE q.T.1 q.U.1 q.mapsInto ≫ q.T.1.ι = _
    exact Scheme.Hom.resLE_comp_ι _ _
  · apply IsOpenImmersion.isPullback z (𝟙 S) q.U.1.ι x
    · simpa using hz.symm
    · simpa only [Scheme.Opens.opensRange_ι, Scheme.Hom.opensRange_of_isIso,
        q.sectionPreimage] using hT
  · exact q.U.2

end AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
