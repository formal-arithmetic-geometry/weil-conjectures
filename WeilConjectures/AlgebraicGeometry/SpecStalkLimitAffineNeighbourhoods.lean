/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Filtered.Final

/-!
# The spectrum of a stalk as a limit of affine neighbourhoods

The inverse system is written with its objects and inclusion maps. Its limit property
is the unique-factorization property for every compatible family, in the category of schemes.

## References

* [Stacks Project, Tag 0GWT](https://stacks.math.columbia.edu/tag/0GWT)
* [Stacks Project, Tag 01YW](https://stacks.math.columbia.edu/tag/01YW)
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

set_option linter.unusedVariables false in
/-- Affine neighbourhoods are cofinal and directed, their inclusion maps form an inverse
system with affine transitions and qcqs objects, and `Spec O_{X,x}` is its limit. -/
theorem fromSpecStalk_limit_affine_neighbourhoods (X : Scheme.{u}) (x : X) :
    (∀ (U : X.Opens), x ∈ U →
      ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ U) ∧
    Nonempty {W : X.Opens // IsAffineOpen W ∧ x ∈ W} ∧
    (∀ (W V : {W : X.Opens // IsAffineOpen W ∧ x ∈ W}),
      ∃ Z : {W : X.Opens // IsAffineOpen W ∧ x ∈ W}, Z.1 ≤ W.1 ⊓ V.1) ∧
    (∀ W : {W : X.Opens // IsAffineOpen W ∧ x ∈ W},
      X.homOfLE (le_refl W.1) = 𝟙 W.1.toScheme) ∧
    (∀ (W V Z : {W : X.Opens // IsAffineOpen W ∧ x ∈ W})
      (hZV : Z.1 ≤ V.1) (hVW : V.1 ≤ W.1),
      X.homOfLE hZV ≫ X.homOfLE hVW = X.homOfLE (hZV.trans hVW)) ∧
    (∀ W : {W : X.Opens // IsAffineOpen W ∧ x ∈ W},
      CompactSpace W.1.toScheme ∧ QuasiSeparatedSpace W.1.toScheme) ∧
    (∀ (W V : {W : X.Opens // IsAffineOpen W ∧ x ∈ W}) (hVW : V.1 ≤ W.1),
      IsOpenImmersion (X.homOfLE hVW) ∧ IsAffineHom (X.homOfLE hVW)) ∧
    (∀ (U : X.Opens) (hxU : x ∈ U),
      ∃! g : Spec (X.presheaf.stalk x) ⟶ U.toScheme, g ≫ U.ι = X.fromSpecStalk x) ∧
    (∀ (W V : {W : X.Opens // IsAffineOpen W ∧ x ∈ W}) (hVW : V.1 ≤ W.1),
      V.1.fromSpecStalkOfMem x V.2.2 ≫ X.homOfLE hVW =
        W.1.fromSpecStalkOfMem x W.2.2) ∧
    (∀ (T : Scheme.{u})
      (tW : ∀ W : {W : X.Opens // IsAffineOpen W ∧ x ∈ W}, T ⟶ W.1.toScheme),
      (∀ (W V : {W : X.Opens // IsAffineOpen W ∧ x ∈ W}) (hVW : V.1 ≤ W.1),
        tW V ≫ X.homOfLE hVW = tW W) →
      ∃! t : T ⟶ Spec (X.presheaf.stalk x),
        ∀ W : {W : X.Opens // IsAffineOpen W ∧ x ∈ W},
          t ≫ W.1.fromSpecStalkOfMem x W.2.2 = tW W) := by
  classical
  have basis : ∀ (U : X.Opens), x ∈ U →
      ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ U := by
    intro U hxU
    exact exists_isAffineOpen_mem_and_subset hxU
  let N := {W : X.Opens // IsAffineOpen W ∧ x ∈ W}
  have nonempty : Nonempty N := by
    obtain ⟨W, hW, hxW, _⟩ := basis ⊤ trivial
    exact ⟨⟨W, hW, hxW⟩⟩
  have directed : ∀ W V : N, ∃ Z : N, Z.1 ≤ W.1 ⊓ V.1 := by
    intro W V
    obtain ⟨Z, hZ, hxZ, hZWV⟩ := basis (W.1 ⊓ V.1) ⟨W.2.2, V.2.2⟩
    exact ⟨⟨Z, hZ, hxZ⟩, hZWV⟩
  refine ⟨basis, nonempty, directed, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W
    exact X.homOfLE_rfl W.1
  · intro W V Z hZV hVW
    exact X.homOfLE_homOfLE hZV hVW
  · intro W
    let : IsAffine W.1.toScheme := W.2.1
    exact ⟨inferInstance, inferInstance⟩
  · intro W V hVW
    let : IsAffine W.1.toScheme := W.2.1
    let : IsAffine V.1.toScheme := V.2.1
    exact ⟨inferInstance, inferInstance⟩
  · intro U hxU
    refine ⟨U.fromSpecStalkOfMem x hxU, U.fromSpecStalkOfMem_ι x hxU, ?_⟩
    intro g hg
    apply (cancel_mono U.ι).mp
    exact hg.trans (U.fromSpecStalkOfMem_ι x hxU).symm
  · intro W V hVW
    apply (cancel_mono W.1.ι).mp
    simp only [Category.assoc, homOfLE_ι, Opens.fromSpecStalkOfMem_ι]
  · intro T tW htW
    let : Nonempty N := nonempty
    let : IsDirected N (· ≥ ·) := ⟨fun W V ↦ by
      obtain ⟨Z, hZ⟩ := directed W V
      exact ⟨Z, hZ.trans inf_le_left, hZ.trans inf_le_right⟩⟩
    let i : N ⥤ OpenNhds x :=
      (show Monotone (fun W : N ↦ (⟨W.1, W.2.2⟩ : OpenNhds x)) from
        fun _ _ h ↦ h).functor
    have : i.op.Final := Functor.final_of_exists_of_isFiltered _
      (fun V ↦ by
        obtain ⟨W, hW, hxW, hWV⟩ := basis V.unop.1 V.unop.2
        exact ⟨op (⟨W, hW, hxW⟩ : N), ⟨(homOfLE hWV).op⟩⟩)
      (fun s s' ↦ ⟨_, 𝟙 _, Subsingleton.elim _ _⟩)
    let R : Nᵒᵖ ⥤ CommRingCat.{u} :=
      i.op ⋙ (OpenNhds.inclusion x).op ⋙ X.presheaf
    let c : Cocone R :=
      (colimit.cocone ((OpenNhds.inclusion x).op ⋙ X.presheaf)).whisker i.op
    have hc : IsColimit c :=
      (Functor.Final.isColimitWhiskerEquiv i.op _).symm (colimit.isColimit _)
    let D : N ⥤ Scheme.{u} := R.rightOp ⋙ Scheme.Spec
    let s : Cone D := Scheme.Spec.mapCone (coneRightOpOfCocone c)
    have hs : IsLimit s :=
      isLimitOfPreserves Scheme.Spec (isLimitConeRightOpOfCocone _ hc)
    let t : Cone D :=
      { pt := T
        π :=
          { app := fun W ↦ tW W ≫ W.1.toSpecΓ
            naturality := by
              intro W V f
              change tW V ≫ V.1.toSpecΓ = (tW W ≫ W.1.toSpecΓ) ≫
                Spec.map (X.presheaf.map (homOfLE (leOfHom f) : W.1 ⟶ V.1).op)
              rw [Category.assoc]
              symm
              rw [Opens.toSpecΓ_SpecMap_presheaf_map, ← Category.assoc,
                htW V W (leOfHom f)] } }
    have proj (W : N) : s.π.app W =
        W.1.fromSpecStalkOfMem x W.2.2 ≫ W.1.toSpecΓ := by
      exact (W.1.fromSpecStalkOfMem_toSpecΓ x W.2.2).symm
    refine ⟨hs.lift t, ?_, ?_⟩
    · intro W
      have : IsIso W.1.toSpecΓ := by
        change IsIso W.2.1.isoSpec.hom
        infer_instance
      apply (cancel_mono W.1.toSpecΓ).mp
      rw [Category.assoc, ← proj]
      exact hs.fac t W
    · intro f hf
      apply hs.uniq t f
      intro W
      rw [proj, ← Category.assoc, hf W]

end AlgebraicGeometry.Scheme
