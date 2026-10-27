/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.PureDimension
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import Sheaf.AlgebraicGeometry.FibreDimensionAfterBaseChange

/-! # Pure relative dimension is preserved by base change

Source: Stacks Project, Morphisms, Tag 02NK (lemma-base-change-relative-dimension-d),
using Tag 02FY (lemma-fibre-dimension-after-base-change).
(blueprint: lem-trf-relative-dimension-base-change)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

-- Transfer component dimensions along the homeomorphism with the top open.
private theorem component_dimensions_homeomorph
    {A B : Type u} [TopologicalSpace A] [TopologicalSpace B] (e : A ≃ₜ B) (d : ℕ)
    (h : ∀ C ∈ irreducibleComponents A, topologicalKrullDim C = (d : WithBot ℕ∞)) :
    ∀ C ∈ irreducibleComponents B, topologicalKrullDim C = (d : WithBot ℕ∞) := by
  intro C hC
  have hpre : e ⁻¹' C ∈ irreducibleComponents A :=
    preimage_mem_irreducibleComponents hC e.isOpenEmbedding
      (by simpa only [e.surjective.range_eq, Set.inter_univ] using hC.1.nonempty)
  have hd := h (e ⁻¹' C) hpre
  have he := (e.symm.image C).isHomeomorph.topologicalKrullDim_eq (e.symm.image C)
  rw [e.symm.image_eq_preimage_symm] at he
  exact he.trans hd

private theorem local_dimension_fiber_point {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (y : f.fiber s) (x : X) (hy : f.fiberι s y = x) :
    topologicalKrullDimAt y = topologicalKrullDimAt (f.asFiber x) := by
  have hx : f x = s := by
    rw [← hy, ← Scheme.Hom.comp_apply, f.fiber_fac, Scheme.Hom.comp_apply]
    simp
  subst s
  congr 1
  apply (f.fiberι (f x)).isEmbedding.injective
  simpa using hy

/-- A locally finite type morphism whose nonempty fibres are pure of dimension `d`
remains so after arbitrary base change.  For a base-change morphism `g : S' ⟶ S`,
the base-changed morphism is the second pullback projection
`pullback.snd f g : pullback f g ⟶ S'`.

Source: Stacks Project, Morphisms, Tag 02NK (lemma-base-change-relative-dimension-d),
using Tag 02FY (lemma-fibre-dimension-after-base-change).

Proof: Let `s' : S'` and assume the fibre of `pullback.snd f g` at `s'` is
nonempty.  The locally-finite-type base-change lemma makes this morphism locally
of finite type.  The fibre-dimension-after-base-change identification compares
its local dimensions with those of the fibre of `f` at the image of `s'`.
The pure-dimension hypothesis, together with the locally algebraic local-dimension
criterion and the locally Noetherian component criterion, therefore makes every
irreducible component of this base-changed fibre have dimension `d`.  Empty fibres
are covered by the explicit nonempty premise.

(blueprint: lem-trf-relative-dimension-base-change)
-/
theorem pure_relative_dimension_base_change
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (d : ℕ)
    (hpure : ∀ s : S, Nonempty (f.fiber s) → (f.fiber s).IsPureDimension d)
    (g : S' ⟶ S) :
    ∀ s' : S', Nonempty ((pullback.snd f g).fiber s') →
      ((pullback.snd f g).fiber s').IsPureDimension d := by
  have hlocal (s : S) (x : f.fiber s) :
      topologicalKrullDimAt x = (d : WithBot ℕ∞) := by
    have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have htop := component_dimensions_homeomorph
      (Homeomorph.Set.univ (f.fiber s)).symm d (hpure s ⟨x⟩)
    exact topologicalKrullDimAt_eq_of_equidimensional_open
      (f.fiberToSpecResidueField s) ⊤ d htop x trivial
  let f' : pullback f g ⟶ S' := pullback.snd f g
  have : LocallyOfFiniteType f' := MorphismProperty.pullback_snd _ _ inferInstance
  intro s' _
  have : LocallyOfFiniteType (f'.fiberToSpecResidueField s') :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsLocallyNoetherian (f'.fiber s') :=
    LocallyOfFiniteType.isLocallyNoetherian (f'.fiberToSpecResidueField s')
  have hlocal' (y : f'.fiber s') : topologicalKrullDimAt y = (d : WithBot ℕ∞) := by
    let p : ↥(pullback f g) := f'.fiberι s' y
    have hd := (fibre_dimension_after_base_change f g p).2.2
    exact (local_dimension_fiber_point f' s' y p rfl).trans
      (hd.trans (hlocal _ _))
  have htop := topologicalKrullDim_component_eq_of_constant_local_dimension
    (Y := f'.fiber s') ⊤ d (fun x _ ↦ hlocal' x)
  exact component_dimensions_homeomorph (Homeomorph.Set.univ (f'.fiber s')) d htop

end AlgebraicGeometry
