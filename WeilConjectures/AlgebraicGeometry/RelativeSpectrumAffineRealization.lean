/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebraAffineInclusion
import Mathlib.AlgebraicGeometry.RelativeGluing
import WeilConjectures.AlgebraicGeometry.RelativeSpectrumStructureAlgebra

/-! # Existence of an affine realization of a quasi-coherent algebra

## References

* [Stacks Project, Tag 01LP](https://stacks.math.columbia.edu/tag/01LP)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

set_option hygiene false in
local notation "𝒪⁎" f:max => Under.mk (⟨(f).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (f).base).obj (Scheme.sheaf _))

/-- Every quasi-coherent algebra is the direct image of the structure algebra of an
 affine scheme over the base. -/
theorem exists_affine_structure_algebra (S : Scheme.{u}) (A : S.CommAlgebraSheaf)
    (hA : A.toModule.IsQuasicoherent) :
    ∃ (X : Scheme.{u}) (f : X ⟶ S), IsAffineHom f ∧ Nonempty (A ≅ 𝒪⁎ f) := by
  obtain ⟨hsquares, hcomp, hid⟩ := quasi_coherent_algebra_affine_inclusion S A hA
  let F : S.affineOpens ⥤ Scheme.{u} :=
    { obj := fun U ↦ Spec (A.right.obj.obj (op U.1))
      map := fun {U V} h ↦ Spec.map (A.right.obj.map (homOfLE h.le).op)
      map_id := fun U ↦ hid U
      map_comp := fun {U V W} h k ↦ (hcomp U V W h.le k.le).symm }
  let t : F ⟶ S.directedAffineCover.functorOfLocallyDirected :=
    { app := fun U ↦ Spec.map (A.hom.hom.app (op U.1)) ≫ U.2.isoSpec.inv
      naturality := fun {U V} h ↦ (hsquares U V h.le).2.1.w }
  let d : S.directedAffineCover.RelativeGluingData :=
    { functor := F
      natTrans := t
      equifibered := fun {U V} h ↦ (hsquares U V h.le).2.1 }
  have : (d.functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin d
  have : ∀ {U V : S.affineOpens} (h : U ⟶ V),
      IsOpenImmersion (d.functor.map h) := fun h ↦
    Scheme.Cover.RelativeGluingData.instIsOpenImmersionMapI₀Functor d h
  refine ⟨d.glued, d.toBase, ?_, ?_⟩
  · constructor
    intro U hU
    let i : S.affineOpens := ⟨U, hU⟩
    have he : d.toBase ⁻¹ᵁ U = (Limits.colimit.ι d.functor i).opensRange := by
      simpa using d.toBase_preimage_eq_opensRange_ι i
    rw [he]
    exact isAffineOpen_opensRange (Limits.colimit.ι d.functor i)
  · apply structure_algebra_iso_of_affine_spectral_charts S A d.glued d.toBase
      (fun U ↦ Limits.colimit.ι d.functor U)
    · intro U
      exact d.isPullback_natTrans_ι_toBase U
    · intro U V hUV
      exact Limits.colimit.w d.functor (homOfLE hUV)

end AlgebraicGeometry
