/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap

/-! # Single-module transposes for the pinned derived adjunction

Source: Stacks Project, Tags 079W and 0FP1.
(blueprint: lem-pc-canonical-single-adjunction-transpose).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The pinned derived adjunction transposes the ordinary single-module comparison.
Source: Stacks Project, Tags 079W and 0FP1; the factorization defining
`exists_schemeDerivedAdjunction`.
(blueprint: lem-pc-canonical-single-adjunction-transpose).

Proof: Let ε be the selected left-derived counit and t the unique isomorphism
from tensor pullback to ordinary pullback preserving their common right adjoint.
Represent a by the homotopy-category single map after the single-map comparison
for tensor pullback and t. Apply the factorization in
`Classical.choose_spec (exists_schemeDerivedAdjunction ...)` to this morphism.
Naturality of the single-map comparison identifies its underived transpose with
the single map of the tensor adjunction transpose. The counit law for
`leftAdjointUniq` identifies this transpose with the ordinary adjunction transpose.
The inverse single-map comparison for direct image followed by the specified
right-derived unit is exactly `canonicalSingleDirectImageMap`. Reassociate the
result to obtain the equality. No invertibility of a pullback comparison is used;
zero modules and empty schemes satisfy the same naturality and counit identities. -/
theorem canonicalSingleAdjunctionTranspose {X S : Scheme.{u}} (f : X ⟶ S)
    (N : S.Modules) (M : X.Modules) (a : (pullback f).obj N ⟶ M) :
    (Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f)
    ((Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) f)
    ((Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) f))).homEquiv _ _
      (canonicalSinglePullbackMap f N ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).map a) =
    (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
        ((pullbackPushforwardAdjunction f).homEquiv _ _ a) ≫
      canonicalSingleDirectImageMap f M := by sorry

end AlgebraicGeometry.Scheme.Modules
