/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.SixFunctors.ScalarSixCtfGenerators
public import Sheaf.Paper.LocalizingAdmissibleCoefficients

/-! # Locally perfect models have constructible finite-Tor locally closed extensions.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (2), local models.
(blueprint: lem-sfb-scalar-six-perfect-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

/-- Locally perfect models have constructible finite-Tor locally closed extensions.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (2), local models.
(blueprint: lem-sfb-scalar-six-perfect-extension).

Proof in words: reduce the coefficient presentation using the displayed admissibility
isomorphism. Choose the cover and bounded projective scalar complexes witnessing Q.
Apply stratum_perfect_uniform_bounds to that cover. Strict support is equivalent to
termwise vanishing outside the bounds, so its hypotheses are precisely those of the
specified models; the finite affine refinement makes the bounds uniform on S.
The theorem supplies bounded constant-model constructibility, finite Tor amplitude,
and separated finite-type geometry for S and its immersion into X. Its scalar
cohomology assertions use admissible_scalar_model_cohomology, and apply to arbitrary
projective complexes, including torsion cohomology. Factor i through its
scheme-theoretic image as i.toImage followed by i.imageι. The image is closed in the
standing Noetherian scheme; it too is standing, and i.toImage is quasi-compact.
Apply clause (2) of constructibleFiniteTor_stability_direct_images to this actual
factorization and the Ctf object Q. The resulting functor is definitionally the
composite in the conclusion. Coefficient-isomorphism transport preserves constant
models and Tor bounds. Empty S uses the empty refinement and interval [0,0]. -/
theorem sfbPerfectLocallyClosedExtension (ell : ℕ) [Fact ell.Prime]
    (Λ : ScalarSixRing.{u}) (hΛ : IsLocalizingAdmissibleCoefficient ell Λ.X)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (S : Scheme.{u}) (i : S ⟶ X.left) (hi : IsImmersion i)
    (Q : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S))
    (hQ : IsLocallyPerfectScalarModel Λ.X S Q) :
    constantModelBoundedConstructible Λ.X X.left
        ((sfbLocallyClosedDerivedExtension Λ i hi).obj Q) ∧
      DerivedCategory.finiteTorAmplitude _
        ((sfbLocallyClosedDerivedExtension Λ i hi).obj Q) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
