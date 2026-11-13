/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Category.Grp.Limits
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalBaseChangePointsGeometry
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalSingletonNeighbourhoods
import WeilConjectures.AlgebraicGeometry.AbelianStrictlyHenselianOpenGerm
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover

/-!
# Sections on a zero-dimensional scheme and geometric stalks

## References

* [Stacks Project, Tag 03QO](https://stacks.math.columbia.edu/tag/03QO)
* [Stacks Project, Tag 00KH](https://stacks.math.columbia.edu/tag/00KH)
* [Stacks Project, Tag 06RS](https://stacks.math.columbia.edu/tag/06RS)
* [Stacks Project, Tag 040R](https://stacks.math.columbia.edu/tag/040R)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Sections are naturally the product of the geometric stalks on a zero-dimensional
separated finite-type scheme over an algebraically closed field.
-/
theorem zeroDimensional_sections_stalks (k : Type u) [Field k] [IsAlgClosed k]
    (C : Scheme.{u}) [C.Over (Spec (.of k))]
    [IsSeparated (C ↘ Spec (.of k))] [LocallyOfFiniteType (C ↘ Spec (.of k))]
    [QuasiCompact (C ↘ Spec (.of k))] (hdim : topologicalKrullDim C ≤ 0)
    (Ω : C → Type u) [∀ c, Field (Ω c)] [∀ c, IsAlgClosed (Ω c)]
    (s : ∀ c, Spec (.of (Ω c)) ⟶ C) (hs : ∀ c, s c default = c) :
    Finite C ∧
      (∀ F : Sheaf C.smallEtaleTopology AddCommGrpCat.{(max u v) + 1},
        IsIso (Limits.Pi.lift (fun c : C =>
          (pointSmallEtale (s c)).toPresheafFiber (Etale.mk (𝟙 C))
            (Over.homMk (s c) (Category.comp_id (s c))) F.obj))) ∧
      (∀ (F G : Sheaf C.smallEtaleTopology AddCommGrpCat.{(max u v) + 1}) (φ : F ⟶ G),
        φ.hom.app (op (Etale.mk (𝟙 C))) ≫
          Limits.Pi.lift (fun c : C =>
            (pointSmallEtale (s c)).toPresheafFiber (Etale.mk (𝟙 C))
              (Over.homMk (s c) (Category.comp_id (s c))) G.obj) =
        Limits.Pi.lift (fun c : C =>
          (pointSmallEtale (s c)).toPresheafFiber (Etale.mk (𝟙 C))
            (Over.homMk (s c) (Category.comp_id (s c))) F.obj) ≫
          Limits.Pi.map (fun c : C => (pointSmallEtale (s c)).sheafFiber.map φ)) := by
  classical
  refine ⟨(AlgebraicGeometry.zeroDimensional_baseChange_geometry k C hdim).1, ?_, ?_⟩
  · obtain ⟨U, t, hU⟩ := zeroDimensional_singleton_neighbourhoods k C hdim Ω s hs
    let W : C → C.Etale := fun c ↦ Etale.mk (U c).ι
    let π : ∀ c, W c ⟶ Etale.mk (𝟙 C) := fun c ↦
      MorphismProperty.Over.homMk (W c).hom (Category.comp_id _)
    let (c : C) : IsOpenImmersion (W c).hom := inferInstanceAs (IsOpenImmersion (U c).ι)
    let (c : C) : Mono (π c) := by
      constructor
      intro Z a b hab
      apply MorphismProperty.Over.Hom.ext
      apply (cancel_mono (W c).hom).mp
      exact congrArg (fun f ↦ f.left) hab
    have hcov : Sieve.ofArrows W π ∈ C.smallEtaleTopology (Etale.mk (𝟙 C)) := by
      rw [ofArrows_mem_smallEtaleTopology_iff]
      ext c
      simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
      refine ⟨c, ?_⟩
      change c ∈ Set.range (U c).ι
      rw [Scheme.Opens.range_ι, (hU c).2.1]
      exact Set.mem_singleton c
    have hdisj : ∀ c d, c ≠ d →
        Disjoint (Set.range (π c).left.base) (Set.range (π d).left.base) := by
      intro c d hcd
      change Disjoint (Set.range (U c).ι) (Set.range (U d).ι)
      rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι, (hU c).2.1, (hU d).2.1]
      exact Set.disjoint_singleton.mpr hcd
    intro F
    let g := fun c ↦ (pointSmallEtale (s c)).toPresheafFiber (W c) (Over.homMk (t c) (hU c).1) F.obj
    have hg (c : C) : IsIso (g c) := by
      obtain ⟨R, hring, hlocal, hstrict, e, he⟩ := (hU c).2.2
      let := hring
      let := hlocal
      exact strictlyHenselianOpen_abelian_germ_isIso (U c) hstrict e (s c) (t c) (hU c).1 he F
    let (c : C) : IsIso (g c) := hg c
    have hr : IsIso (Limits.Pi.lift (fun c ↦ F.obj.map (π c).op)) :=
      Etale.isIso_piLift_of_disjoint F W π hcov hdisj
    have hfactor : Limits.Pi.lift (fun c ↦ F.obj.map (π c).op) ≫ Limits.Pi.map g =
        Limits.Pi.lift (fun c : C ↦
          (pointSmallEtale (s c)).toPresheafFiber (Etale.mk (𝟙 C))
            (Over.homMk (s c) (Category.comp_id (s c))) F.obj) := by
      apply Limits.Pi.hom_ext
      intro c
      simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_comp_π_assoc,
        Limits.Pi.lift_comp_π]
      dsimp [g]
      rw [(pointSmallEtale (s c)).toPresheafFiber_w]
      congr 1
      apply Over.OverMorphism.ext
      exact (hU c).1
    rw [← hfactor]
    infer_instance
  · intro F G φ
    dsimp [GrothendieckTopology.Point.sheafFiber]
    apply Limits.Pi.hom_ext
    intro c
    simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.lift_comp_π_assoc,
      Limits.Pi.lift_comp_π]
    exact ((pointSmallEtale (s c)).toPresheafFiber_naturality φ.hom
      (Etale.mk (𝟙 C)) (Over.homMk (s c) (Category.comp_id (s c)))).symm

end AlgebraicGeometry.Scheme
