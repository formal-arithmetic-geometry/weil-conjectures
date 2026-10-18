/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q89
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.CategoryTheory.Triangulated.LocalizingFunctor
import Sheaf.Paper.CartesianCoefficients
import Sheaf.Paper.LocalizingClosureExistence
import Sheaf.Paper.OpenExtensionConstantModelConstructible
import Sheaf.SixFunctors.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-!
# Open extension by zero on localizing categories

Source: blueprint main-20261015, sec-six-functors/sk-lem-sf-open-ctf,
sk-prop-proper-image-localizing-open.md
(blueprint: det-proper-image-localizing-open).

The ambient categories are ordinary unbounded derived categories of module objects.
Constructibility uses finite constant models. The restricted functor is the canonical
full-subcategory lift of the existing termwise derived extension by zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- Open extension by zero preserves bounded constructible finite-Tor complexes and
all small direct sums, and restricts to an exact, sum-preserving functor on their
localizing closures. The existential triangulated structures below are the closure
properties needed for the inherited full-subcategory triangulations; the functor is
explicitly the canonical lift of `D(j_!)`, not an arbitrary functor.

Source: blueprint main-20261015, sk-prop-proper-image-localizing-open.md and its proof
(blueprint: det-proper-image-localizing-open).

Proof plan, following the node:
1. By sk-def-sfb-module-lower-shriek, the sheaf functor is exact and left adjoint to
pullback. Apply lem-sf-exact-functor-derived-triangulated. Termwise exactness identifies
`H^r(D(j_!) K)` with `j_! H^r(K)`, preserving any vanishing interval, even for unbounded K.
2. By det-def-localizing-closure-existence (1), ambient sums are termwise sums of
complexes. The sheaf adjunction and lem-weil-pbc-left-adjoint-preserves-colimits give
the degreewise sum comparisons. Their compatibility with differentials follows on
each coprojection, so they identify the derived coproduct cocones. This includes the
empty family, whose termwise sum is zero.
3. For bounded constant-model constructible K, use the cohomology identity and
lem-sf-open-extension-zero-constant-model-constructible: keep the strata of U and add
the reduced closed complement, where the extended module is zero. Constant models
transfer across the cohomology isomorphisms, giving the same boundedness interval.
4. For a Tor interval [a,b] and any module M on X, sk-prop-sfb-cartesian-coefficients
makes pullback exact. Apply det-lem-int-tensor-projection with open part j and closed
part the identity of X. It identifies `(D(j_!) K) ⊗ᴸ M` with
`D(j_!)(K ⊗ᴸ j^* M)`. Step 1 gives vanishing outside [a,b], uniformly for all the
admissible coefficients, proving finite Tor amplitude without an integral Dctf=Dbc claim.
5. Apply det-proper-image-localizing-principle to D(j_!), using steps 1--4 and the
inclusion of the generators in their localizing closure. This gives the objectwise
restriction. Both closures have the inherited ambient triangles and sums, so the
canonical lift is triangulated and preserves their sums. -/
theorem openImmersionLowerShriek_localizing
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [CharP k p] (_hp : 0 < p) (_hpℓ : p ≠ ℓ)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {U X : Scheme.{u}} [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (.of k))] :
    (∀ K : ConstantModelConstructibleFiniteTor Λ U,
      (constantModelBoundedConstructible Λ X ⊓ fun L ↦
        DerivedCategory.finiteTorAmplitude _ L)
          ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj)) ∧
    (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
      (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory) ∧
    ∃ (_ : (localizingClosureProEtale Λ U).IsTriangulated)
      (_ : (localizingClosureProEtale Λ X).IsTriangulated),
      ∃ h : ∀ K : (localizingClosureProEtale Λ U).FullSubcategory,
        localizingClosureProEtale Λ X
          ((CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory.obj K.obj),
        ((localizingClosureProEtale Λ X).lift
          ((localizingClosureProEtale Λ U).ι ⋙
            (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory) h).IsTriangulated ∧
        ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I)
          ((localizingClosureProEtale Λ X).lift
            ((localizingClosureProEtale Λ U).ι ⋙
              (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory) h) := by
  sorry

end AlgebraicGeometry.ProEtale
