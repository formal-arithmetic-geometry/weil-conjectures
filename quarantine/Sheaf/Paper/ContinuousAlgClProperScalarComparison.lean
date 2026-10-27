/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.Paper.AllContinuousScalarMate
public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import Sheaf.Paper.ModuleRingedToposDerivedComparison
import Sheaf.Paper.RingedCoefficientProjectionCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import Sheaf.Paper.ProperBaseChangeRational
import Sheaf.Paper.ConstructibleAlgClTopologyComparison
import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.Paper.ContinuousAlgClConstructibleTor
import Sheaf.Paper.ProperLocalizingContinuousAlgCl
import Sheaf.Paper.KFlatScalarComparisonNormalization

/-!
# Proper direct image and all-continuous algebraic-closure scalar extension

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md,
paragraph (3), separate proper coefficient-change input
(blueprint: lem-sfb-continuous-algcl-proper-scalar-comparison).

The arrow is the existing K-flat-normalized counit mate. Its coefficient ring is
C(-, PadicAlgCl ell) with the extended ell-adic norm topology. Both endpoints are in
the ordinary unbounded derived category of internal modules.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Proper direct image commutes with the specified all-continuous scalar extension
on bounded constructible inputs over a finite extension of Q_ell with finite constant models.
Source: blueprint main-20261015, direct-image stability proof paragraph (3),
proper coefficient-change obligation
(blueprint: lem-sfb-continuous-algcl-proper-scalar-comparison).

Proof, following the six DAG steps:
1. Let C be the finite-subextension-valued algebraic-closure coefficient, distinct
from B = C(-, PadicAlgCl ell). Factor A_E to B through C. Write S for extension
A_E to C and J for extension C to B. The balanced associator identifies JS with T.
Use lem-sfb-alpha-iso and lem-pd-module-ringed-topos-derived-comparison to identify
inverse-image coefficients and internal/section modules. The normalized scalar
push comparisons and associators are those of
lem-pur-ringed-coefficient-projection-cocycle, without a flatness hypothesis.
2. For L = S_Z K, lem-sfb-extend-to-qlbar-constructible gives bounded constructibility.
The finite-subextension clause of det-thm-sfb-proper-base-change-rational gives
P = Rf_{*,C} L bounded constructible and makes the A_E-to-C push comparison invertible.
It applies because K is bounded, hence bounded below. This step concerns C only.
3. The equivalence of lem-sfb-constructible-algcl-topology-comparison makes J_Z L
and J_T P bounded constructible. Finite type over a field makes the schemes
Noetherian by lem-weil-pbc-finite-type-over-noetherian. Then
det-sf-comp-continuous-algcl-constructible-tor gives finite Tor amplitude for J_Z L,
and det-sf-comp-proper-continuous-algcl gives Q = Rf_{*,B} J_Z L bounded constructible.
Thus both endpoints of the C-to-B push comparison lie in the full constructible category.
4. For bounded constructible M on T, lem-sfb-dc-upper-star-preserves gives the same
property for f_C^* M. Full faithfulness of J_T and J_Z and the geometric adjunctions
give Hom_B(J_T M,J_T P) = Hom_C(M,P) = Hom_C(f_C^* M,L)
= Hom_B(J_Z f_C^* M,J_Z L) = Hom_B(J_T M,Q).
Naturality of the pullback comparison, normalized by
lem-sfb-kflat-scalar-comparison-normalization, identifies this composite with
postcomposition by the actual C-to-B counit mate: J_T u maps to the adjunct of
J_Z(counit) composed with the pullback comparison and f_B^*(J_T u).
5. Essential surjectivity of J_T extends these Hom bijections to every bounded
constructible test object. Testing with Q gives a right inverse v; testing with
J_T P and injectivity gives the left-inverse identity. The C-to-B mate is invertible
in the ambient derived category because the constructible subcategory is full.
6. The coefficient cocycle identifies the A_E-to-B mate, after the balanced
associator, with J_T of the A_E-to-C mate followed by the C-to-B mate and the
pushforward of the source associator. All factors are invertible by steps 2 and 5.
The cocycle normalization identifies this composite with the original coefficient
inclusion and precisely the pullback-comparison/counit adjunct defining beta.
Hence the specified beta is invertible. No constructibility hypothesis on T_Z K
or either direct image, and no flatness of the coefficient map, is required. -/
theorem continuousAlgClProperScalarComparison_isIso
    (ℓ p : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [CharP k p]
    (_hp : 0 < p) (_hpℓ : p ≠ ℓ) (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {Z T : Scheme.{u}} [Z.Over (Spec (.of k))] [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    (f : Z ⟶ T) [f.IsOver (Spec (.of k))] [IsProper f]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E.1) Z)))
    (_hK : constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) Z K) :
    IsIso (tameBoundaryScalarComparison ℓ E f K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
