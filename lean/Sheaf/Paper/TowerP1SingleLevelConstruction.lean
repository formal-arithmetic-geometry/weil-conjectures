/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.Paper.TowerP1SingleLevelData

/-! # Exact single-level projective-line comparisons

Source: the Levels argument of det-sp-tower-p1-adjunction, steps 1--3 of
lem-sp-tower-p1-single-level-triangles.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) [Finite (SpTowerShriek.R l E n)]


omit [Finite (SpTowerShriek.R l E n)] in
/-- Exact singleton realizations and their normalized operation comparisons.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels;
lem-sp-tower-p1-single-level-triangles, steps 1--3.
(blueprint: lem-sp-tower-p1-single-level-construction).

Proof: On the product site put the given module sheaf at level n and the zero
module sheaf at each other level. Use its restriction maps on the n-slice and
zero maps between distinct slices. A composite with distinct endpoints is zero;
if a composite has equal level endpoints, monotonicity forces its intermediate
level to be the same. This proves functoriality and scalar compatibility.
Componentwise kernels and cokernels make the singleton additive and exact.
Compose it with exact comparison inverse image and localize termwise. Exactness
preserves lower cohomological bounds. At n retain the input etale complex and
its exact-localization coordinate; at all other levels retain the zero complex.
These witnesses establish the range condition. Take the coordinates and four
formula-comparison fields from h.levels n. Their canonical direct-image,
pullback, tensor and shift comparisons applied to the singleton origin give
push and pull. The canonical site mate is invertible on bounded-below inputs;
the line tensor and exact pullback comparisons are invertible as well.
Naturality of these maps and of the exact-localization coordinate gives the
natural isomorphisms. Their component definitions are exactly push_eq and
pull_eq. This construction makes no use of a tower triangle identity. -/
theorem singleLevelConstruction (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤)))
    (p : Presentation l E S hS) (d : Maps l E p) (h : EtaleOriginComparisons l E p d) :
    letI : Finite (SpTowerShriek.R l E n) := p.classes.base.finite n
    Nonempty (SingleLevelComparisons l E n d h) := by sorry

end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
