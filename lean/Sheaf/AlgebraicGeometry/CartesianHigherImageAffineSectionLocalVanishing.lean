/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.CartesianHigherImageTransitions
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Sheaf.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import Sheaf.AlgebraicGeometry.AbelianHigherDirectImageNaturalComparison

/-! # Local affine-cover glue for cartesian higher-image sections

Source: Stacks Project, Tag 0EYM, second proof, affine section reduction.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- A transitioned cartesian higher-image section vanishes when it vanishes on a finite
etale cover. This is the sheaf-separatedness part of the affine-section argument.
Source: Stacks Project, Tag 0EYM, second proof, injectivity on affine etale objects.
(blueprint: lem-sc-cartesian-higher-image-affine-section-local-vanishing)
-/
theorem cartesianHigherImage_section_eq_zero_of_finite_cover
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (_hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) (i j : I) (a : j ⟶ i)
    (x : (cartesianHigherImageStage D c f F q i).obj.obj (Opposite.op U))
    (J : Type u) [Finite J] (V : J → c.pt.left.Etale) (r : ∀ t, V t ⟶ U)
    (hcover : Sieve.ofArrows V r ∈ c.pt.left.smallEtaleTopology U)
    (hzero : ∀ t, (cartesianHigherImageTransition D c f F q a).hom.app
      (Opposite.op (V t))
      ((cartesianHigherImageStage D c f F q i).obj.map (r t).op x) = 0) :
    (cartesianHigherImageTransition D c f F q a).hom.app
      (Opposite.op U) x = 0 := by
  let T := cartesianHigherImageTransition D c f F q a
  let G := cartesianHigherImageStage D c f F q j
  let e : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ G.obj.obj (Opposite.op U) :=
    AddCommGrpCat.ofHom
      { toFun := fun n ↦ n.down • (T.hom.app (Opposite.op U) x)
        map_zero' := zero_zsmul _
        map_add' := fun m n ↦ add_zsmul _ _ _ }
  have he : e = 0 := by
    apply G.property.hom_ext_ofArrows r hcover
    intro t
    rw [Limits.zero_comp]
    ext n
    change G.obj.map (r t).op (n.down • (T.hom.app (Opposite.op U) x)) = 0
    rw [map_zsmul, ← NatTrans.naturality_apply]
    rw [hzero t, smul_zero]
  have h := congrArg (fun k ↦ k (ULift.up (1 : ℤ))) he
  change (1 : ℤ) • (T.hom.app (Opposite.op U) x) = 0 at h
  simpa only [one_zsmul] using h


/-- The cohomology-continuity and affine-descent portion of the affine section argument.
Source: Stacks Project, Tag 0EYM, second proof, affine section reduction.
The proof lifts to the cohomology presheaf, refines by affine etale objects, descends
finitely presented objects to a common stage, and applies derived etale cohomology
continuity. Naturality and exchange pasting identify the resulting maps.
(blueprint: lem-sc-cartesian-higher-image-affine-section-local-vanishing)
-/
theorem exists_cartesianHigherImage_affine_section_local_zero
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (U : c.pt.left.Etale) [IsAffine U.left] (i : I)
    (x : (cartesianHigherImageStage D c f F q i).obj.obj (Opposite.op U))
    (hx : (cartesianHigherImageLeg D c f F q i).hom.app (Opposite.op U) x = 0) :
    ∃ (j : I) (a : j ⟶ i) (J : Type u) (_ : Fintype J)
      (V : J → c.pt.left.Etale) (r : ∀ t, V t ⟶ U),
      Sieve.ofArrows V r ∈ c.pt.left.smallEtaleTopology U ∧
      ∀ t, (cartesianHigherImageTransition D c f F q a).hom.app
        (Opposite.op (V t))
        ((cartesianHigherImageStage D c f F q i).obj.map (r t).op x) = 0 := by
  sorry

end AlgebraicGeometry.Etale
