/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper base change on the admissible constant-model generators

Source: blueprint sec-six-functors-basics/sk-thm-sfb-proper-base-change and
sk-thm-sf-comp-composition, proper base change in proof (2), with the recorded
coefficient convention of sk-def-localizing-closure.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  condensedAmbientExchange

/-- The specified proper exchange is invertible on Dctf for every recorded admissible
coefficient, including coefficients isomorphic to the listed representatives.
The square may use any chosen Cartesian realization of the pullback.

Source: blueprint sk-thm-sfb-proper-base-change, finite (2), integral (3), rational (3),
and det-sf-comp-composition-base-change, proof step 3.
(blueprint: lem-sfb-proper-base-change-admissible-generators).

Proof: for a finite ell-primary coefficient apply finite proper base change. For O_E,
apply integral proper base change to the bounded constructible input; the Tor hypothesis
is additional information. For E and the finite-subextension-valued algebraic closure,
apply rational proper base change; Z_ell and Q_ell are the degree-one cases. For the full
continuous-map algebraic closure, stratify a constant-model constructible complex, use
its finite Postnikov filtration, and descend each finite-rank lisse piece and its
monodromy to a finite coefficient extension. Proper finiteness supplies finite cochain
models on an adapted target stratification. Scalar extension commutes with those finite
models, so the proper exchange is the scalar extension of the finite-extension exchange.
Exactness and the connecting square propagate invertibility through the finite
filtrations. This concerns the actual continuous-map ring, without identifying it with
the finite-subextension-valued ring. Finally restriction along a ring-object isomorphism
is an exact equivalence on modules and derived categories. It transports constant local
models and Tor amplitude. Transpose the scalar/pullback comparison cube under the two
proper adjunctions; the counit equations identify the transported exchange with the
specified ambient mate. Reflection of isomorphisms gives the result for every coefficient
isomorphism class. Empty schemes and the zero input are covered by the same argument. -/
theorem properBaseChange_admissible_generators
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A Z Y Y' : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : Z ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    {a : A ⟶ Z} {q' : A ⟶ Y'} (sq : ChosenCartesianSquare a q' q v)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)))
    (hK : constantModelBoundedConstructible Λ Z K ∧ DerivedCategory.finiteTorAmplitude _ K) :
    IsIso ((condensedAmbientExchange Λ sq).app K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
