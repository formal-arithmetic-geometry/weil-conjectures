/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic
import Sheaf.AlgebraicGeometry.LimitAffineTransition

/-!
# Affine charts for flatness descent

Source: Stacks Project, Limits, proof of Tag 04AI, first paragraph.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The ring data of one affine triple in the proof of Stacks Tag 04AI.
(blueprint: def-weil-pbc-flat-descent-chart). -/
structure FlatDescentChart (J : Type u) [Preorder J] (j₀ : J) where
  rings : J ⥤ CommRingCat.{u}
  source : CommRingCat.{u}
  target : CommRingCat.{u}
  sourceAlgebra : Algebra (rings.obj j₀) source
  targetAlgebra : Algebra (rings.obj j₀) target
  map : letI := sourceAlgebra; letI := targetAlgebra; source →ₐ[rings.obj j₀] target
  finitePresentation : map.toRingHom.FinitePresentation

namespace FlatDescentChart

/-- Flatness of the chart's tensor-product map after an arbitrary base-ring map. -/
def baseFlat {J : Type u} [Preorder J] {j₀ : J} (a : FlatDescentChart J j₀)
    {R : CommRingCat.{u}} (q : a.rings.obj j₀ ⟶ R) : Prop :=
  letI := a.sourceAlgebra
  letI := a.targetAlgebra
  letI := q.hom.toAlgebra
  (Algebra.TensorProduct.map (Algebra.ofId R R) a.map).toRingHom.Flat

/-- Flatness of a chart at a stage above its initial stage. -/
def stageFlat {J : Type u} [Preorder J] {j₀ : J} (a : FlatDescentChart J j₀)
    (j : J) (h : j₀ ≤ j) : Prop :=
  a.baseFlat (a.rings.map (homOfLE h))

/-- Flatness of the chart over the colimit of its base rings. -/
def limitFlat {J : Type u} [Preorder J] {j₀ : J} (a : FlatDescentChart J j₀) : Prop :=
  a.baseFlat (colimit.ι a.rings j₀)

end FlatDescentChart

/-- A finite family of affine triples translates flatness over the limit to flatness of
colimit tensor-product maps, and translates flatness of all stage maps back to scheme
flatness. This is only the affine reduction, with no eventual flatness assertion.

Source: Stacks Project, Limits, proof of Tag 04AI, first paragraph, and the affine
identification in Situation 081D.
(blueprint: lem-weil-pbc-flat-descent-affine-charts).

Proof: At each point of X₀ choose nested affine opens U ⊆ X₀, V ⊆ Y₀, W ⊆ S₀
with f₀(U) ⊆ V and Y₀.hom(V) ⊆ W. Quasi-compactness of X₀ supplies finitely many
such U covering X₀. Put B₀ = Γ(V) and C₀ = Γ(U); local finite presentation gives
finite presentation of B₀ → C₀. On the upper tail the inverse images of W are affine,
so their sections define a directed diagram Aᵢ. The inverse image of W in the limit
is the spectrum of colim Aᵢ, compatibly with the projection to W, by the limit theorem
for affine transitions and the spectrum-colimit comparison. Open base change and the
spectrum tensor-product pullback identify the inverse images of U and V with spectra
of Aᵢ ⊗ C₀ and Aᵢ ⊗ B₀, and similarly at the limit. The induced morphism is Spec
of id ⊗ (B₀ → C₀), by the pullback universal property. Restricting a flat limit morphism
to these opens and using the affine flatness criterion gives limitFlat for every chart.
Conversely, stageFlat for every chart gives flatness on a covering of the stage source;
the local rings of open subschemes are the ambient local rings, hence the stage map is
flat. If X₀ is empty the family has size zero, and all base-changed sources are empty,
so the last assertion is vacuous stalkwise. No flatness descent is used here. -/
theorem exists_flat_descent_affine_charts
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀))) (f₀ : X₀ ⟶ Y₀)
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    [LocallyOfFinitePresentation f₀.left] :
    ∃ n : ℕ, ∃ charts : Fin n →
      FlatDescentChart {i : I // i₀ ≤ i} ⟨i₀, le_rfl⟩,
      (Flat (((Over.pullback (c.π.app (op i₀))).map f₀).left) →
        ∀ b, (charts b).limitFlat) ∧
      (∀ j : {i : I // i₀ ≤ i},
        (∀ b, (charts b).stageFlat j j.property) →
        Flat (((Over.pullback (D.map (homOfLE j.property).op)).map f₀).left)) := by
  sorry

end AlgebraicGeometry
