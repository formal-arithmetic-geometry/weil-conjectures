/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D5
-/
module

public import Sheaf.SixFunctors.ScalarSixCtfGenerators

/-! # Finite-coefficient generation in the scalar-perfect presentation.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (1), generators.
(blueprint: lem-sfb-scalar-six-finite-generation).
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

/-- Finite-coefficient generation in the scalar-perfect presentation.

Source: blueprint latest, sec-six-functors-basics/sk-prop-scalar-six,
det-prop-scalar-six-ctf.proof.md, (1), generators.
(blueprint: lem-sfb-scalar-six-finite-generation).

Proof in words: finite discrete condensed and scheme ring comparisons identify the
coefficient sheaf with the constant ring sheaf. Apply the normalized exact equivalence
of module categories and its derived equivalence to K. Finite constant models become
finite locally constant ordinary modules on the same strata, and Tor amplitude is
unchanged because the equivalence is monoidal. Apply proEtale_flatConstructible_thickGeneration.
Its generators are locally constant finite-projective modules in degree zero. On a
trivializing cover the corresponding scalar module is a retract of a finite free
module, so its single complex is a locally perfect scalar model. The comparison of
ordinary and internal open extension and closed direct image identifies their locally
closed extensions with sfbLocallyClosedDerivedExtension. Rotate each cone to an
extension and use the finite extension-product identities to collect summands at the
end. Finite sums are split extensions, so no infinite closure is introduced. Finally
transport along e; coefficient isomorphisms preserve the splittings, local scalar
models, and the normalized extension functors. The zero ring, empty stratum and rank
zero use the same splittings. -/
theorem sfbFiniteScalarGeneration {Λ : ScalarSixRing.{u}}
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [Finite A]
    (e : Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj A))
    {k : Type u} [Field k] (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left) :
    ∃ n : ℕ, (((sfbPerfectScalarGenerator Λ X).shiftClosure ℤ).extensionProductIter n
      ).retractClosure K.obj := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
