/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.SfStrictDirectImageScalar.SfStrictDirectImageScalarData

/-! # Normalized strict integral direct-image models

Source: the strict direct-image scalar-comparison proof, Steps 1, 2 and 6;
Stacks 0D6E and 0A07.
(blueprint: lem-sf-strict-direct-image-integral-models)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.SfStrictDirectImageScalar
variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

/-- The functorial strict reduction model and its scalar-linear, shift-compatible
reconstruction, before any coefficient change or rationalization.

Source: the proof of `lem-sf-strict-direct-image-scalar-comparison`, Steps 1, 2 and 6;
Stacks 0D6E and 0A07.
(blueprint: lem-sf-strict-direct-image-integral-models)

Proof:
Use the completed coefficient pushforward comparison with its structure map fixed by
all finite projections. Uniqueness of that map identifies it with the published
completed coefficient map. The universal right-derived comparison identifies its
completed image with the published derived image, respecting the universal units.
Curry the strict reduction sequence degree by degree to obtain the strict functor and
its identification. Its actual tensor-unit augmentation is natural in the good
representatives. Apply derived direct image and then the normalized direct-image/limit
comparison. Completeness makes the augmentation invertible, so this descends along
the representative localization. Integral direct-image constructibility places its
values in the full constructible subcategory and supplies the image functor.
The resulting composite is precisely the displayed reconstruction normalization,
since the augmentation is unique from its sectionwise quotient projections.
Transfer addition and constant-scalar linearity from the ambient direct image through
this reconstruction; its naturality on scalar identities gives the scalar equation.
The augmentation has the quotient map in its first Roos coordinate and zero in the
second. Reindexing the first coordinate and preserving zero commutes with native
signed shifts. For each derived compositor, use shifted K-injective resolutions:
the representing map is the shifted direct image of the same resolution map.
Thus realization and reconstruction have the required coherent shift structures. -/
theorem strictDirectImageIntegralModel
    (k : Type u) [Field k] (hl : IsUnit (l : k))
    {Z X : Scheme.{u}} [Z.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (f : Z ⟶ X) [f.IsOver (Spec (.of k))] :
    Nonempty (IntegralModel l E f) := by sorry

end WeilConjectures.SfStrictDirectImageScalar
