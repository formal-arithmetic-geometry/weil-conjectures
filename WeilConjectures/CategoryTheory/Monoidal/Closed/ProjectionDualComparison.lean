/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Dual comparison from an adjoint triple and the projection formula

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/\
lem-weil-delta-proper-pushforward.proof.md`, first and third paragraphs (blueprint:
`lem-pur-projection-dual-comparison`).

## Main statements

* `CategoryTheory.Adjunction.projectionDualComparison` is the canonical comparison obtained
  from the adjoint lax monoidal structure on the right adjoint.
* `CategoryTheory.Adjunction.isIso_projectionDualComparison` states its invertibility and the
  specified Hom-set description under the projection formula.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace CategoryTheory.Adjunction

universe u₁ u₂ v₁ v₂

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [SymmetricCategory C] [SymmetricCategory D]
  [MonoidalClosed C] [MonoidalClosed D]
  {F : C ⥤ D} {G : D ⥤ C} [F.Braided]

/-- The projection map `G M ⊗ T ⟶ G (M ⊗ F T)` attached to an adjunction and its
canonical adjoint lax monoidal structure. Source: the projection map in the first paragraph of
`lem-weil-delta-proper-pushforward.proof.md` (blueprint: lem-pur-projection-dual-comparison). -/
noncomputable def projectionDualProjection (adj : F ⊣ G) (M : D) (T : C) :
    G.obj M ⊗ T ⟶ G.obj (M ⊗ F.obj T) := by
  exact ((adj.rightAdjointProjectionMap
    (Functor.OplaxMonoidal.δNatTrans F)).app M).app T

/-- The canonical dual comparison `G [M,W] ⟶ [G M,W']` obtained by first applying the
internal-hom comparison and then the counit of `G ⊣ Q` after the chosen isomorphism
`W ≅ Q W'`. Source: the internal ambient adjunction in the first and third paragraphs of
`lem-weil-delta-proper-pushforward.proof.md` (blueprint: lem-pur-projection-dual-comparison). -/
noncomputable def projectionDualComparison
    (adj : F ⊣ G) {Q : C ⥤ D} (q : G ⊣ Q)
    {W : D} {W' : C} (e : W ≅ Q.obj W') (M : D) :
    G.obj ((ihom M).obj W) ⟶ (ihom (G.obj M)).obj W' := by
  letI := adj.rightAdjointLaxMonoidal
  letI := adj.rightAdjointLaxBraided
  exact MonoidalClosed.dualComparison G (G.map e.hom ≫ q.counit.app W') M

/-- The Hom-set bijection appearing in the proof of the dual comparison theorem. Its successive
factors are the adjunction `F ⊣ G`, the closed adjunction for `M`, the chosen isomorphism `e`, the
adjunction `G ⊣ Q`, precomposition by the projection map, and the closed adjunction for `G M`.
Source: the displayed Hom chain in the first paragraph of
`lem-weil-delta-proper-pushforward.proof.md` (blueprint: lem-pur-projection-dual-comparison). -/
noncomputable def projectionHomEquiv
    (adj : F ⊣ G) {Q : C ⥤ D} (q : G ⊣ Q)
    {W : D} {W' : C} (e : W ≅ Q.obj W') (M : D) (T : C)
    (hπ : IsIso (projectionDualProjection adj M T)) :
    (T ⟶ G.obj ((ihom M).obj W)) ≃ (T ⟶ (ihom (G.obj M)).obj W') := by
  letI := hπ
  exact (adj.homEquiv _ _).symm.trans <|
    ((ihom.adjunction M).homEquiv _ _).symm.trans <|
      ((Iso.refl _).homCongr e).trans <|
        (q.homEquiv _ _).symm.trans <|
          ((asIso (projectionDualProjection adj M T)).homCongr (Iso.refl _)).symm.trans
            ((ihom.adjunction (G.obj M)).homEquiv _ _)

/-- Let `C,D` be locally small symmetric monoidal closed categories, and let `F` be a strong
symmetric monoidal functor with adjoint triple `F ⊣ G ⊣ Q`. For `W ≅ Q W'`, the canonical dual
comparison from `G [M,W]` to `[G M,W']` is an isomorphism whenever every projection map
`G M ⊗ T ⟶ G (M ⊗ F T)` is an isomorphism. More precisely, for every `T`, postcomposition
with this comparison is exactly the displayed Hom-set bijection induced by the two adjunctions,
the closed structure, symmetry, the chosen isomorphism, and the projection map. No biduality
assumption is made.

Source: first and third paragraphs of `lem-weil-delta-proper-pushforward.proof.md`
(blueprint: lem-pur-projection-dual-comparison).

Proof: (1) Transpose the braiding compatibility of the strong symmetric monoidal `F`
through `adj.homEquiv`; injectivity gives braiding compatibility of the canonical lax
monoidal tensorator on `G` (lem-sfb-monoidal-adjunction-mates).
(2) For each `T`, compose the two adjunction Hom bijections, the two closed bijections,
postcomposition with `e`, and precomposition with the invertible projection map to get
`projectionHomEquiv adj q e M T (hπ T)` (lem-weil-pbc-adjunction-of-natural-bijection).
(3) For a map `φ : T ⟶ G [M,W]`, its transpose `a : F T ⟶ [M,W]` satisfies
`η_T ≫ G(a) = φ` by unit naturality and the right triangle identity.
(4) Uncurry the Hom-chain image of `φ`. Expanding the projection map and using the
braiding compatibility from (1), tensorator naturality and the cancellation in (3),
this is the pushed-forward evaluation pairing precomposed with `φ` in its Hom slot.
Hence currying identifies the Hom-chain image with `φ ≫ projectionDualComparison adj q e M`.
(5) Each Hom chain is a bijection, so postcomposition with the specified comparison is
bijective for every `T`. The Yoneda criterion lem-coef-joyal-homset-iso-detection gives
its invertibility. The calculation uses only projections for the fixed `M` and no biduality. -/
theorem isIso_projectionDualComparison
    (adj : F ⊣ G)
    {Q : C ⥤ D} (q : G ⊣ Q) {W : D} {W' : C}
    (e : W ≅ Q.obj W') (M : D)
    (hπ : ∀ T : C, IsIso (projectionDualProjection adj M T)) :
    IsIso (projectionDualComparison adj q e M) ∧
      ∀ T : C,
        Function.Bijective
            (fun φ : T ⟶ G.obj ((ihom M).obj W) ↦
              φ ≫ projectionDualComparison adj q e M) ∧
          (fun φ : T ⟶ G.obj ((ihom M).obj W) ↦
              φ ≫ projectionDualComparison adj q e M) =
            ⇑(projectionHomEquiv adj q e M T (hπ T)) := by
  sorry

end CategoryTheory.Adjunction
