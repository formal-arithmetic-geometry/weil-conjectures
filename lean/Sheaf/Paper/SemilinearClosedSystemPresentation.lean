/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.SemilinearOpenClosedData

/-! # Closed operations on strict coefficient systems
Source: Stacks 09A5 and 09BM
(blueprint: lem-sp-semilinear-closed-system-presentation). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.SemilinearSections.OpenClosed

/-- The closed system operations have exact, normalized level presentations.
Source: Stacks 09A5 and 09BM; parent proof steps 1, 2, 4 and 5
(blueprint: lem-sp-semilinear-closed-system-presentation).

Proof: direct image on the sequence site is restriction to base-change objects,
with the coefficient adjunction unit. At level n this is ordinary module direct
image: both modules have the same sections and restrictions, and their actions
agree by naturality of the ring unit. These identity section maps give the
push-evaluation isomorphism. Transpose this comparison along the module
adjunctions. Since inverse image is computed using vertical covers at the fixed
index, the transpose is invertible; its unit equation is the defining mate
equation. The same uniqueness of left adjoints identifies the level pullback
with the small-model inverse image. The identity section maps and the adjunctions
are additive. Kernels and cokernels of strict systems are computed at each level:
restriction of scalars preserves the underlying additive sheaves, so the maps
on kernels/cokernels commute with transitions by their universal properties.
Apply immersion inverse-image exactness at every level. Apply closed direct-image
exactness at every level, using the quasi-compact complementary open (Tag 09BM).
The level comparisons then imply exactness of both system functors. The empty
closed subscheme and zero coefficient ring give the same constructions. -/
theorem semilinearClosedSystemPresentation
    {T Z : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (U : T.ProEt) [IsOpenImmersion U.hom] [QuasiCompact U.hom]
    (hU : Set.range U.hom = (Set.range i)ᶜ)
    (B : ℕ → Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) : Nonempty (ClosedData i B τ) := by sorry

end WeilConjectures.SemilinearSections.OpenClosed
