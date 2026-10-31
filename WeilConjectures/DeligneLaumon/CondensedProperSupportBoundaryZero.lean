/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleConeCounterexample
public import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact

import WeilConjectures.SixFunctors.CondensedProperBoundaryVanishing

/-!
# Proper condensed direct image has no contribution on a disjoint closed boundary

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-sf-comp-coherence/
 det-sf-comp-coherence-refinement.proof.md`, clause (2)
(blueprint: lem-zl-condensed-proper-support-boundary-zero).

The theorem states the affine-local closed-boundary vanishing for ordinary unbounded derived
categories of condensed module objects.  It is the finite-subextension algebraic-closure
case of `isZero_closedBoundary_pullback_properPushforward_openExtension`
(blueprint: lem-fix-condensed-proper-boundary-vanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Proper direct image of an open extension by zero restricts to zero on a disjoint closed
boundary, for bounded constructible finite-subextension-valued algebraic-closure coefficients.

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-sf-comp-coherence/
 det-sf-comp-coherence-refinement.proof.md`, clause (2)
(blueprint: lem-zl-condensed-proper-support-boundary-zero).

Proof: this is the case `Λ = Qbar_ℓ` (finite-subextension condensed structure) of the
closed-boundary vanishing theorem
`isZero_closedBoundary_pullback_properPushforward_openExtension`
(`lem-fix-condensed-proper-boundary-vanishing`), applied to the same `h`, `a`, `i`, `c`, `K`.
That theorem needs neither quasi-separatedness nor `char k` prime; it needs `V` of finite type
and quasi-compact over `k`, which follows because `V → Spec k` is `i ≫ (Z → Spec k)`, a
composite of a quasi-compact open immersion (locally of finite type) with a quasi-compact,
locally finite type morphism. Its factorization hypothesis `a ≫ h = q ≫ i` is the given one
read in the other direction. Its proof: the image of `W ×_Z C → W` is disjoint from `a(U)`,
so the pullback of the open extension by zero vanishes degreewise; compact-support base change
for the compactification `U → W → Z` of `a ≫ h` transports this zero to `c^* Rh_* D(a_!) K`.
-/
theorem proper_support_boundary_zero
    (ℓ : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (W Z U V C : Over (Spec (.of k)))
    [QuasiSeparated W.hom] [LocallyOfFiniteType W.hom] [QuasiCompact W.hom]
    [QuasiSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    [QuasiSeparated U.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    (h : W ⟶ Z) [IsProper h.left]
    (a : U ⟶ W) [IsOpenImmersion a.left] [QuasiCompact a.left]
    (i : V ⟶ Z) [IsOpenImmersion i.left] [QuasiCompact i.left]
    (ha : ∃ q : U ⟶ V, q ≫ i = a ≫ h)
    (c : C ⟶ Z) [IsClosedImmersion c.left]
    (hc : Set.range c.left.base = (Set.range i.left.base)ᶜ)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U.left) Ab.{u + 1})
        (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left)))
    (hK : boundedConstructible
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) U.left) K) :
    IsZero
      ((moduleObjectDerivedPullback (Profinite.padicAlgClRingObj ℓ) c.left).obj
        ((moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj ℓ) h.left).obj
          ((openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) a.left).mapDerivedCategory.obj
            K))) := by
  have : LocallyOfFiniteType V.hom := by
    have hV : LocallyOfFiniteType (i.left ≫ Z.hom) := inferInstance
    simpa only [Over.w i] using hV
  have : QuasiCompact V.hom := by
    have hV : QuasiCompact (i.left ≫ Z.hom) := inferInstance
    simpa only [Over.w i] using hV
  exact isZero_closedBoundary_pullback_properPushforward_openExtension
    ℓ ⟨⊥, inferInstance⟩
    ⟨Profinite.padicAlgClRingObj ℓ⟩ (Or.inr rfl) h a i
    (by obtain ⟨q, hq⟩ := ha; exact ⟨q, hq.symm⟩) c hc K hK

end AlgebraicGeometry.ProEtale.CondensedRing
