/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q64
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
import Sheaf.AlgebraicGeometry.ModuleObjectPostnikovRoos

/-!
# Uniform lower-tail bounds on the constructible finite-Tor localizing hull

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md, (2), first paragraph
(blueprint: lem-sfb-qcqs-proper-hull-tail-bound).

The categories, truncation, and total direct image are the ordinary ambient module-object
constructions. Membership in the localizing hull is required only of the original object.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Proper direct image has a uniform upper bound on every lower truncation tail of an
object in the constructible finite-Tor localizing hull, over a qcqs base.

Source: blueprint main-20261015, sec-six-functors-basics,
sk-prop-sf-comp-coherence/det-sf-comp-coherence-refinement.proof.md, (2), first paragraph,
relative cohomological estimate (blueprint: lem-sfb-qcqs-proper-hull-tail-bound).

Proof plan:
1. The sheaf tensor theorem (lem-weil-pbc-sheaf-tensor-closed) and the module-object
   Grothendieck theorem (lem-sfb-modobj-grothendieck) make the source and target module
   categories Grothendieck abelian (def-sp-grothendieck-abelian). Exact coproducts and
   lem-kun-grothendieck-derived-coproducts identify cohomology of a sum with the sum of
   cohomologies, by applying the sum to kernel, image, and cokernel sequences.
2. Use the weak Serre coproduct class P of lem-sfb-qcqs-proper-serre-heart-bound.
   Complexes whose cohomology lies in P are replete and shift stable. The long exact
   cohomology sequence (lem-sf-derived-homology-long-exact) expresses a triangle's middle
   cohomology as an extension of a cokernel by a kernel, so this class is triangulated.
   Step 1 makes it closed under sums. It contains the finite constant-model constructible
   finite-Tor generators (sk-def-sfb-constructible), hence their intersection-defined
   localizing hull (sk-def-localizing-closure). Good truncations (def-kun-truncations)
   retain cohomology in P, since the other cohomology objects are zero.
3. Choose d in N from the heart bound. The underived full module pushforward is additive
   and left exact (sk-def-sfb-module-pushforward-pullback); K-injective resolutions exist
   by lem-sfb-grothendieck-k-injective, and its total right derived functor is triangulated
   by lem-pc-right-derived-functor-triangulated. For L = tau_(le a-1) K, each bounded
   truncation L_n = tau_(ge -n) L has cohomology in P and no cohomology above a-1.
   Lemma lem-sfb-bounded-heart-amplitude-devissage gives vanishing of Rf_* L_n above
   a-1+d, uniformly in n. When -n > a-1 this truncation is zero.
4. Lemma lem-module-object-postnikov-roos gives the triangle Rf_* L -> P -> P ->
   (Rf_* L)[1], where P is the product of the Rf_* L_n and the middle arrow is 1-shift.
   Its product-cohomology assertion makes H^j(P) zero for j > a-1+d. For r > a+d,
   both H^(r-1)(P) and H^r(P) vanish, so the exact segment from
   lem-sf-derived-homology-long-exact gives H^r(Rf_* L) = 0. This applies to the ordinary
   unbounded L without membership in the hull or derived completeness.
5. Set c = d+1. Then r >= a+c implies r > a+d. This choice depends only on the fixed
   morphisms and coefficients. The zero object, empty schemes, and empty fibres are
   covered by the same argument.
-/
theorem exists_uniform_lowerTail_bound_of_isProper
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    {S Y X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (q : Y ⟶ S) [IsProper q] (f : X ⟶ Y) [IsProper f] :
    ∃ c : ℕ, ∀ (a : ℤ)
      (K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))),
      localizingClosureProEtale Λ X K → ∀ r : ℤ, a + (c : ℤ) ≤ r →
        IsZero ((DerivedCategory.homologyFunctor _ r).obj
          ((moduleObjectDerivedPushforward Λ f).obj
            ((DerivedCategory.TStructure.t.truncLE (a - 1)).obj K))) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
