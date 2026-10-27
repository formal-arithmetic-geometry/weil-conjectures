/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q09
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.DescendSurjective

/-! # Eventual surjectivity for inverse systems of algebraic spaces

Source: Stacks Project, Spaces and Morphisms of Spaces, Situation 084W and Tag 07SN
(blueprint: lem-sfb-space-eventually-surjective-map).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical base change of a morphism, formed on its underlying presheaves.
Source: Stacks Project, Situation 084W
(blueprint: lem-sfb-space-eventually-surjective-map). -/
def spaceBaseChangeMap {S : Scheme.{u}} {X Y B T : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (p : Y ⟶ B) (g : T ⟶ B) :
    Limits.pullback (f ≫ p) g ⟶ Limits.pullback p g :=
  ((Over.pullback g).map
    (Over.homMk (U := Over.mk (f ≫ p)) (V := Over.mk p) f rfl)).left

/-- A locally finitely presented map which is surjective over the limit is surjective
at every sufficiently late stage. No transition morphism need be surjective.
Source: Stacks Project, Situation 084W, Tag 07SN, and persistence under base change
(blueprint: lem-sfb-space-eventually-surjective-map).

Proof:
1. Choose affine surjective étale charts V₀ → Y₀ and U₀ → X₀ ×_{Y₀} V₀ using
   [lem-sfb-qc-space-affine-etale-atlas]. Their qcqs properties follow from
   [lem-weil-pbc-affine-scheme-qcqs] and [lem-sfb-qcqs-space-fibre-product]. The map
   U₀ → V₀ is locally finitely presented by [lem-sfb-space-local-properties-chart-test].
2. Base change these charts to every stage and to the limit. Affine transitions and
   [lem-sfb-space-affine-limits-schematic-stages], [lem-sfb-space-affine-locality]
   make all chart sources affine schemes and identify their limits. Pullback pasting
   identifies Uᵢ = U₀ ×_{V₀} Vᵢ. The charts remain surjective étale by
   [lem-trf-space-fibre-products-etale-covers].
3. The point-image formula [lem-a1-space-point-open-calculus] makes U → V surjective.
   Apply [lem-weil-pbc-descend-surjective] to the affine scheme base system Vᵢ and
   U₀ → V₀, obtaining a surjective Uⱼ → Vⱼ for some j ≥ i₀.
4. Lift each point of Yⱼ first to Vⱼ and then to Uⱼ to obtain surjectivity of fⱼ.
   Every fᵢ for i ≥ j is its base change; [lem-a1-space-point-open-calculus] gives
   surjectivity at all those stages. No transition surjectivity is used. -/
theorem eventually_surjective_of_isLimit
    {S : Scheme.{u}} {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I] (D : Iᵒᵖ ⥤ AlgebraicSpace S)
    (hqc : ∀ i : Iᵒᵖ, CompactSpace (Point (D.obj i).obj.obj))
    (hqs : ∀ i : Iᵒᵖ, IsAbsolutelyQuasiSeparated (D.obj i))
    (haff : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      IsRepresentableWith (fun _ _ p ↦ IsAffineHom p.left) (D.map a).hom.hom)
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    (hXqc : CompactSpace (Point X₀.left.obj.obj))
    (hXqs : IsAbsolutelyQuasiSeparated X₀.left)
    (hYqc : CompactSpace (Point Y₀.left.obj.obj))
    (hYqs : IsAbsolutelyQuasiSeparated Y₀.left)
    (hlfp : MapIsLocallyOfFinitePresentation f₀.left)
    (hf : Function.Surjective (mapPoint
      (spaceBaseChangeMap f₀.left.hom.hom Y₀.hom.hom.hom (c.π.app (op i₀)).hom.hom))) :
    ∃ (j : I) (hj : i₀ ≤ j), ∀ (i : I) (hi : j ≤ i),
      Function.Surjective (mapPoint (spaceBaseChangeMap f₀.left.hom.hom Y₀.hom.hom.hom
        (D.map (homOfLE (le_trans hj hi)).op).hom.hom)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
