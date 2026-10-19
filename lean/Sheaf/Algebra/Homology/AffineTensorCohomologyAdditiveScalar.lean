/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R3
-/
module

public import WeilConjectures.Algebra.Homology.RingTensorCohomology
import Sheaf.Algebra.Homology.AffineTensorCohomologyAdditiveScalarParts
import Sheaf.Algebra.Homology.AffineTensorCohomologyScalarParts

/-! # Additivity and base scalars on affine tensor cohomology

Source: Stacks Project, More on Algebra, Tag 06Y6 and perfect.tex, Tag 0DJ8.
(blueprint: lem-pc-affine-tensor-cohomology-additive-scalar). -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory

namespace RingTensorCohomology

/-- Additivity and compatibility of the original-base scalar actions.
Source: Stacks Project, More on Algebra, Tag 06Y6, derived tensor functor,
and perfect.tex, Tag 0DJ8, affine coefficient actions.
(blueprint: lem-pc-affine-tensor-cohomology-additive-scalar)

Proof: K-flat quasi-isomorphism invariance identifies source cohomology naturally
with the cohomology of derived extension from R to B after restriction from A.
The derived extension is additive and R-linear, as obtained by computing on K-flat
models (exists_baseDerivedExtension_linear). Restriction, localization Q, and
homology are additive, so this identification transports additivity and the scalar
identity to source. The target is naturally identified with cohomology of derived
extension from A to A tensor_R B, restricted to B, using the ordinary tensor
associativity isomorphism on the functorial A-K-flat resolution. That derived
extension is A-linear, hence R-linear. Restriction to B identifies multiplication
by the image of r in the tensor algebra with multiplication by algebraMap R B r.
These identifications commute with the resolution augmentations, so the asserted
identities concern the existing functors and maps, even if the chosen resolution
functor itself is not additive. No ring map is assumed flat. Zero rings, complexes,
and identity maps satisfy the same transported equations. -/
theorem affineTensorCohomology_additive_scalar
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (i : ℤ) :
    (source R A B i).Additive ∧ (target R A B i).Additive ∧
    (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (r : R),
      (source R A B i).map (algebraMap R A r • 𝟙 M) =
        algebraMap R B r • 𝟙 ((source R A B i).obj M)) ∧
    (∀ (M : CochainComplex (ModuleCat.{u} A) ℤ) (r : R),
      (target R A B i).map (algebraMap R A r • 𝟙 M) =
        algebraMap R B r • 𝟙 ((target R A B i).obj M)) := by
  obtain ⟨haddS, haddT⟩ := affineTensorCohomology_additive_parts R A B i
  obtain ⟨hscalarS, hscalarT⟩ := affineTensorCohomology_scalar_parts R A B i
  exact ⟨haddS, haddT, hscalarS, hscalarT⟩

end RingTensorCohomology
