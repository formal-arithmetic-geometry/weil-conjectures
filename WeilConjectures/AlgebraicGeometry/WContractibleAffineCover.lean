/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
public import WeilConjectures.RingTheory.ProEtale.WContractible

/-! # Coverings by w-contractible affines
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.ProEt

/-- Every small pro-etale object has a pro-etale covering by spectra of w-contractible
rings, with each covering map factoring through an affine open by a faithfully flat
ind-etale ring map. The isomorphism `e` identifies the covering object with `Spec D`;
`j` identifies `Spec B` with an affine open of the target.
-/
theorem exists_wContractible_affine_cover (X : Scheme.{u}) (U : X.ProEt) :
    ∃ (I : Type u) (W : I → X.ProEt) (f : ∀ i : I, W i ⟶ U),
      Presieve.ofArrows W f ∈ precoverage X U ∧
      ∀ i : I, ∃ (D : CommRingCat.{u}), IsWContractibleRing D ∧
        ∃ (e : Spec D ≅ (W i).left) (B : CommRingCat.{u})
          (φ : B ⟶ D) (j : Spec B ⟶ U.left),
          IsOpenImmersion j ∧ φ.hom.FaithfullyFlat ∧ φ.hom.IndEtale ∧
          e.hom ≫ (f i).left = Spec.map φ ≫ j := by
  classical
  let A := U.left.affineOpenCover
  choose D hD hAlg hind hff hw using fun j : A.I₀ ↦ exists_isWContractibleRing (A.X j)
  let (j : A.I₀) : CommRing (D j) := hD j
  let (j : A.I₀) : Algebra (A.X j) (D j) := hAlg j
  let φ (j : A.I₀) : A.X j ⟶ CommRingCat.of (D j) :=
    CommRingCat.ofHom (algebraMap (A.X j) (D j))
  have hwp (j : A.I₀) : WeaklyEtale (Spec.map (φ j)) := by
    rw [WeaklyEtale.Spec_iff]
    exact RingHom.IndEtale.weaklyEtale ((RingHom.IndEtale.algebraMap_iff _ _).mpr (hind j))
  have hsp (j : A.I₀) : Surjective (Spec.map (φ j)) :=
    ((flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr (hff j))).2
  let C := A.openCover.weaken
    (zariskiPrecoverage_le_propQCPrecoverage (P := @WeaklyEtale))
  let E (j : A.I₀) : Scheme.Cover.{0} proetalePrecoverage (Spec (A.X j)) :=
    .singleton (Spec.map (φ j))
      (Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) (hwp j))
  let B := C.bind E
  have hB (i : B.I₀) : WeaklyEtale (B.f i) :=
    Scheme.Cover.map_prop (Scheme.Cover.forgetQc B) i
  let W (i : B.I₀) : X.ProEt := ProEt.mk (B.f i ≫ U.hom)
  let f (i : B.I₀) : W i ⟶ U := MorphismProperty.Over.homMk (B.f i)
  refine ⟨B.I₀, W, f, ?_, ?_⟩
  · change (Presieve.ofArrows W f).map (ProEt.forget X ⋙ Over.forget X) ∈
      proetalePrecoverage U.left
    rw [Presieve.map_ofArrows]
    exact B.mem₀
  · rintro ⟨j, i⟩
    refine ⟨CommRingCat.of (D j), hw j, Iso.refl _, A.X j, φ j, A.f j,
      inferInstance, ?_, ?_, ?_⟩
    · exact RingHom.faithfullyFlat_algebraMap_iff.mpr (hff j)
    · exact (RingHom.IndEtale.algebraMap_iff _ _).mpr (hind j)
    · exact Category.id_comp _

end AlgebraicGeometry.Scheme.ProEt
