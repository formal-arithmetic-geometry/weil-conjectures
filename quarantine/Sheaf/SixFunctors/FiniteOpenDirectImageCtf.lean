/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.Topology.ContinuousMapCondensedRing
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients
import Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
import Sheaf.AlgebraicGeometry.OpenDirectImageClassicalAmplitude
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Sheaf.Paper.ModuleRingedToposDerivedComparison
import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
import Sheaf.Paper.OpenTorBoundArbitraryField
import Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison

/-!
# Finite-coefficient open direct image with a uniform Tor interval

Source: blueprint main-20261015, sec-six-functors-basics/sk-thm-sf-ctf-stability,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), finite-coefficient open case
(blueprint: lem-sfb-finite-open-direct-image-ctf).

The coefficients are the continuous-map condensed ring of a finite discrete ring, pulled
back from the point. Both categories are the ordinary unbounded derived categories of
internal modules; the direct image is the total right derived module direct image.
-/

@[expose] public section

set_option autoImplicit false

universe u

attribute [instance] Profinite.continuousMapRingObjOfUniverseMonObj
  Profinite.isCommMonObj_continuousMapRingObjOfUniverse

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A quasi-compact open immersion over an arbitrary field of positive characteristic
prime to `ℓ` preserves constant-model bounded constructibility for finite `ℓ`-primary
coefficients and enlarges every Tor interval `[a,b]` to `[a,b+d]` for one fixed `d ≥ 0`.
Tor amplitude tests all degree-zero internal module objects. Zero coefficients and the
zero complex are allowed, and the field need not be separably closed.

Source: blueprint main-20261015, sk-thm-sf-ctf-stability-direct-images.proof.md,
paragraph (3), finite-coefficient open case
(blueprint: lem-sfb-finite-open-direct-image-ctf).

Proof plan:
1. If A is nonzero, finiteness makes A Noetherian and every finite A-module finitely
presented. The scalar ℓ is invertible over k. The separated finite-type schemes U,X are
qcqs (lem-weil-pbc-qcqs-over-affine), and j is qcqs by
lem-weil-pbc-qcqs-morphism-permanence.
2. Apply lem-sf-module-object-ordinary-coefficient-equivalence to the actual internal
coefficient ring. Descend the bounded constructible ordinary pro-etale complex to an
etale complex L using sk-thm-pe-constructible-comparison; the exact interval [a,b] is
reflected by det-pe-finite-tor-comparison-noetherian. Thus L is bounded above and below.
3. By det-geo-open-finiteness-ii-amplitude choose d = cd(j), the nonnegative finite
relative cohomological dimension (def-kun-cd). It bounds every higher module direct
image and depends only on j and the fixed coefficients, not on K,a,b or cd(k).
4. The Noetherian coefficient ring, bounded-above L, and the uniform cohomological bound
allow lem-sf-projection-finite-constant for every finite A-module. Then
lem-sf-open-tor-bound-arbitrary-field gives Tor interval [a,b+d] against every etale
module sheaf, using bounded-below L and these projection isomorphisms.
5. By cor-fin-deligne-open-finite-coefficients the same ordinary etale Rj_*L is bounded
constructible: the schemes have finite type over k and ℓ is invertible there.
6. Use lem-sfb-ordinary-proetale-direct-image-plus-comparison on the bounded-below input.
Use sk-thm-pe-constructible-comparison and det-pe-finite-tor-comparison-noetherian on X
for constructibility and the full Tor interval. The compatibility from
lem-pd-module-ringed-topos-derived-comparison and the finite-discrete equivalence
identify this with the specified total derived internal module direct image and reflect
both conclusions back to it.
7. If A is the zero ring all unital modules vanish; take d=0. The zero complex and an
empty source have zero direct image and every Tor interval. The single d from step 3
works for every K,a,b, and none of these steps assumes a separably closed field.
-/
theorem finiteOpenDirectImage_constantModel_torAmplitude
    (ℓ p : ℕ) [Fact ℓ.Prime]
    (k : Type u) [Field k] [CharP k p] (_hp : 0 < p) (_hne : p ≠ ℓ)
    (A : Type u) [CommRing A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
    (_hA : ∃ n : ℕ, 1 ≤ n ∧ (ℓ : A) ^ n = 0)
    {U X : Scheme.{u}}
    [U.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [QuasiCompact (U ↘ Spec (.of k))] [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
    (j : U ⟶ X) [j.IsOver (Spec (.of k))] [IsOpenImmersion j] [QuasiCompact j] :
    ∃ d : ℤ, 0 ≤ d ∧ ∀ (a b : ℤ), a ≤ b →
      ∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObjOfUniverse.{u, u} A) U)),
      constantModelBoundedConstructible
        (Profinite.continuousMapRingObjOfUniverse.{u, u} A) U K →
      DerivedCategory.torAmplitudeIn _ a b K →
      constantModelBoundedConstructible (Profinite.continuousMapRingObjOfUniverse.{u, u} A) X
        ((moduleObjectDerivedPushforward
          (Profinite.continuousMapRingObjOfUniverse.{u, u} A) j).obj K) ∧
      DerivedCategory.torAmplitudeIn _ a (b + d)
        ((moduleObjectDerivedPushforward
          (Profinite.continuousMapRingObjOfUniverse.{u, u} A) j).obj K) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
