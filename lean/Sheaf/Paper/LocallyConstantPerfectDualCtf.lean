/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A6
-/
module

public import Sheaf.Paper.LocallyConstantPerfectComplex

/-! # Duality for locally constant scalar-perfect complexes

Source: current blueprint, internal-Hom stability proof, Step 6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- A locally constant scalar-perfect complex has a bounded constructible dual,
and its derived internal Hom into any ambient object is tensor with that dual.
Source: internal-Hom stability proof, Step 6
(blueprint: lem-sfb-locally-constant-perfect-dual-ctf).

Proof: Compare internal module objects with modules on the ringed site, preserving the
relative derived tensor, unit, internal Hom and slice restrictions. Pull the given
bounded finite-projective scalar complexes to the local charts. Finite projective
splittings give finite free retracts, so their duals are finite projective and the
canonical tensor--Hom evaluation is an isomorphism, also against an unbounded complex:
in every degree only finitely many source terms occur. Perfect duality and exact
slice restriction descend this canonical evaluation to the whole scheme. Scalar
cohomology models give bounded constructibility for the dual, including the completed
integral models and finite-subextension-valued algebraic closure. A finite affine
refinement of the cover exists since X is Noetherian and quasi-compact. The finitely
many bounded models have common cohomological bounds; descend their vanishing and
finite constant cohomology presentations by the cover criterion.
For empty X the cohomology is zero and has the empty stratification; evaluation is
then the unique isomorphism of zero objects. Finite Tor amplitude is a separate
assertion supplied by the existing dual Tor-amplitude theorem. -/
theorem locallyConstantPerfect_dual_constructible
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (P : (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))))
    (hP : IsLocallyConstantPerfectComplex Λ X P) :
    constantModelBoundedConstructible Λ X (relativeInternalHomDual (Mon.mk Λ) X P) ∧
    ∀ N : (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      Nonempty (((derivedHom Λ X).obj (op P)).obj N ≅
      ((derivedTensor Λ X).obj (relativeInternalHomDual (Mon.mk Λ) X P)).obj N) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
