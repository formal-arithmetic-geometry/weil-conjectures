/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Filtered.Final

/-! # Descent of a map to a finitely presented scheme at a fixed stage

Source: Stacks Project, Tag 01ZM.
(blueprint: lem-sbc-pointed-section-stage-descent)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- A map to a finitely presented scheme over one stage descends after refining that stage.

Source: Stacks Project, Tag 01ZM, morphism descent.
(blueprint: lem-sbc-pointed-section-stage-descent)

Proof:
Restrict the diagram to the cofiltered category `Over i`. The forgetful functor is
initial, so the original limit cone induces a limit cone on this restriction.
Its maps to `K.obj i` are the transition maps. The given map is over `K.obj i` by
`ha`. Apply finite-presentation factorization of maps from an affine-transition
limit to obtain an object of `Over i`, hence a stage `j`, a map `f : j ⟶ i`,
and a map `a₀` with the two asserted equalities. Quasi-compactness,
quasi-separatedness, and affine transitions are inherited by the restriction. -/
theorem exists_map_at_refinement_of_affine_limit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (K : I ⥤ Scheme.{u})
    (hKqc : ∀ i, CompactSpace (K.obj i)) (hKqs : ∀ i, QuasiSeparatedSpace (K.obj i))
    (hKa : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (K.map f))
    {T : Scheme.{u}} (b : (Functor.const I).obj T ⟶ K)
    (hb : IsLimit (Cone.mk T b)) (i : I)
    {P : Scheme.{u}} (p : P ⟶ K.obj i) [LocallyOfFinitePresentation p]
    (a : T ⟶ P) (ha : a ≫ p = b.app i) :
    ∃ (j : I) (f : j ⟶ i) (a₀ : K.obj j ⟶ P),
      b.app j ≫ a₀ = a ∧ a₀ ≫ p = K.map f := by
  let L := Over.forget i ⋙ K
  let c := (Cone.mk T b).whisker (Over.forget i)
  have hc : IsLimit c :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) (Cone.mk T b)).symm hb
  let t : L ⟶ (Functor.const (Over i)).obj (K.obj i) :=
    { app := fun j ↦ K.map j.hom
      naturality := fun j k f ↦ by
        change K.map f.left ≫ K.map k.hom = K.map j.hom ≫ 𝟙 _
        rw [Category.comp_id, ← K.map_comp, Over.w f] }
  have hqc : ∀ j, CompactSpace (L.obj j) := fun j ↦ hKqc j.left
  have hqs : ∀ j, QuasiSeparatedSpace (L.obj j) := fun j ↦ hKqs j.left
  have haf : ∀ {j k} (f : j ⟶ k), IsAffineHom (L.map f) := fun f ↦ hKa f.left
  have hcompat : c.π ≫ t = (Functor.const (Over i)).map (a ≫ p) := by
    ext j
    simpa [c, t, ha] using (b.naturality j.hom).symm
  obtain ⟨j, a₀, heq, hp⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation L t p c hc a hcompat
  exact ⟨j.left, j.hom, a₀, heq, hp⟩

end AlgebraicGeometry.Scheme
