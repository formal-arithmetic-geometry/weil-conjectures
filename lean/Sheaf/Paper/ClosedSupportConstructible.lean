/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q40
-/
module

public import Sheaf.Paper.FormalClosedSupport
public import Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible
public import Sheaf.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Triangulated.Triangulated

import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Sheaf.CategoryTheory.OrthogonalTriangleCounitNormalization
import Sheaf.Paper.CoefficientHeartTriangulated
import Sheaf.Paper.CondensedModuleDerivedPushpull
import Sheaf.Paper.FormalClosedSupportDerived
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!
# Constructibility of sections with closed support

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-closed-adjoint-constructible/sk-prop-closed-adjoint-constructible-support.md
(blueprint: det-prop-closed-adjoint-constructible-support).

The support functor, exact closed direct image, and exact inverse image are the existing
module-object constructions. The adjunction is specified by its kernel-inclusion counit,
so the first arrow cannot be replaced by an arbitrarily rescaled counit.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The closed-support localization assertion for a given coefficient ring.
The existential adjunction is normalized by the existing support-kernel inclusion, exactly
as in `FormalClosedSupportAssertions`. Its derived counit and the canonical open unit are
the first two arrows. The only unspecified triangle arrow is the connecting morphism.
The middle vertex is bounded constructible by its type; the other three displayed terms
and the closed-support object are explicitly required to be bounded constructible.

Source: blueprint main-20261015, closed-adjoint-constructible, support detail statement
(blueprint: det-prop-closed-adjoint-constructible-support). -/
def ClosedSupportConstructibleAssertions
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j] : Prop :=
  ∃ a : lowerStar Λ i ⊣ formalClosedSupport Λ i j,
    (∀ M : FormalSupportModules Λ X,
      (formalSupportKernelComparison Λ i j).app M ≫ a.counit.app M =
        (formalSupportKernelInclusion Λ j).app M) ∧
    ∀ K : BoundedConstructible (condensedRingObj Λ X),
      ∃ δ : (lowerStar Λ j).rightDerivedFunctor.obj
          ((formalSupportPullback Λ j).mapDerivedCategory.obj K.obj) ⟶
          ((lowerStar Λ i).mapDerivedCategory.obj
            ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)) ⟦(1 : ℤ)⟧,
        Triangle.mk
            (a.mapDerivedCategoryRightDerivedAdjunction.counit.app K.obj)
            ((formalSupportPullbackAdjunction Λ j).mapDerivedCategoryRightDerivedAdjunction.unit.app
              K.obj) δ ∈ distTriang _ ∧
        boundedConstructible (condensedRingObj Λ X)
          ((lowerStar Λ i).mapDerivedCategory.obj
            ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)) ∧
        boundedConstructible (condensedRingObj Λ X)
          ((lowerStar Λ j).rightDerivedFunctor.obj
            ((formalSupportPullback Λ j).mapDerivedCategory.obj K.obj)) ∧
        boundedConstructible (condensedRingObj Λ X)
          (((lowerStar Λ i).mapDerivedCategory.obj
            ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)) ⟦(1 : ℤ)⟧) ∧
        boundedConstructible (condensedRingObj Λ Z)
          ((formalClosedSupport Λ i j).rightDerivedFunctor.obj K.obj)

/-- Sections with closed support preserve bounded constructibility for both field
coefficients, and the counit-unit localization triangle has bounded constructible terms.
Finite intermediate fields use their induced norm topology. The algebraic-closure ring
uses finite-subextension-valued continuous functions, not all continuous functions.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-closed-adjoint-constructible-support.md and its proof
(blueprint: det-prop-closed-adjoint-constructible-support).

Proof plan (the seven steps of the DAG node):
1. Finite type over the Noetherian field makes X and Z Noetherian by
   lem-weil-pbc-finite-type-over-noetherian. By
   lem-weil-pbc-noetherian-open-subscheme-noetherian, U is Noetherian and quasi-compact.
   lem-weil-pbc-locally-noetherian-quasi-separated and
   lem-weil-pbc-qcqs-morphism-permanence make j quasi-compact.
2. sk-def-sfb-coefficient-morphisms gives the coefficient isomorphisms. The module
   pullback of sk-def-sfb-module-pushforward-pullback is exact by
   lem-weil-pbc-proetale-immersion-limit-preservation; sk-def-sfb-derived-categories
   therefore identifies the derived inverse images with their termwise functors.
3. det-lem-formal-closed-support-derived gives the normalized support adjunction,
   the localization triangle with open unit, and its closed-pullback fiber formula.
4. lem-weil-pbc-proetale-ringed-open-closed gives exact i_* and j^*i_* = 0.
   lem-weil-pbc-proetale-ringed-closed-counit and
   lem-sc-derived-adjunction-from-underived make the actual derived counit invertible;
   lem-weil-pbc-adjunction-counit-iso-right-fully-faithful gives fully faithful i_*.
   Adjunction kills Hom(i_*A,B) and Hom(i_*A,B[-1]) for B = Rj_*j^*K. Apply
   lem-sfb-orthogonal-triangle-counit-normalization: the first arrow is the actual
   support counit and the second stays the open unit.
5. lem-sfb-dc-upper-star-preserves gives constructible j^*K, and
   lem-sfb-dc-lower-star-preserves gives constructible Rj_*j^*K, for either coefficient.
6. det-cor-coefficient-heart-ii-triangulated gives the remaining vertex and its shift
   from K and Rj_*j^*K by two-out-of-three and shift closure.
7. Apply lem-sfb-dc-upper-star-preserves to i and this vertex. The fiber formula of
   det-lem-formal-closed-support-derived identifies its pullback with RΓ_Z K.
   Isomorphism closure from det-cor-coefficient-heart-ii-triangulated on the Noetherian
   Z completes the assertion. All constructions are for the pulled-back ring objects.
-/
theorem closedSupport_constructible
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    (p : ℕ) [Fact p.Prime] [CharP k p] (hpℓ : p ≠ ℓ)
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : U ⟶ X) [i.IsOver (Spec (.of k))] [j.IsOver (Spec (.of k))]
    [IsClosedImmersion i] [IsOpenImmersion j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      ClosedSupportConstructibleAssertions (Profinite.continuousMapRingObj.{u} E) i j) ∧
    ClosedSupportConstructibleAssertions (Profinite.padicAlgClRingObj.{u} ℓ) i j := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
