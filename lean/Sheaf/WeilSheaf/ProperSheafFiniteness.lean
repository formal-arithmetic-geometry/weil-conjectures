/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import WeilConjectures.WeilSheaf.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Sheaf.CategoryTheory.FixedPairDerivedForgetComparison
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Proper direct image finiteness for native Weil sheaves

Source: `WeilConjectures/WeilSheaf/LowerStar.lean`, the additive and finite-limit
instances and `WeilComplex.objectProperty_rightDerivedLowerStar_singleFunctor`,
specialized to a proper morphism
(blueprint: lem-sf-native-weil-proper-sheaf-finiteness).

The ambient derived category is that of all native pro-etale Weil sheaves. The
object property combines boundedness and constructibility of every cohomology sheaf.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Proper pushforward on native pro-etale Weil sheaves is additive and left exact,
and its actual total right derived functor takes each constructible sheaf in degree
zero to an object with bounded constructible cohomology.

Source: `WeilConjectures/WeilSheaf/LowerStar.lean`, lines 79-141, proper specialization
(blueprint: lem-sf-native-weil-proper-sheaf-finiteness).

Proof:
1. Base change p to the algebraic closure of k₀. Properness is preserved by
   lem-pc-proper-base-change; it implies quasi-compactness and local finite type,
   and lem-pc-separated-quasi-separated gives quasi-separatedness. Apply
   lem-pc-quasi-compact-base-change and lem-weil-pbc-lft-base-change to the target
   structure map. The injective field inclusion preserves characteristic.
2. Direct image evaluates a sheaf on the base-changed test object, with scalars
   restricted along the framework coefficient map. It therefore preserves addition
   and kernels. Frobenius pullback is an additive equivalence by
   lem-weil-proetale-isomorphism-inverse-image. The coefficient comparison is
   precomposition of the same locally finite functions. Kernels and finite sums
   inherit the invertible Frobenius structure, proving both functor properties.
3. Apply lem-sf-adic-affine-direct-image-finiteness to the affine hypotheses of
   lem-sf-adic-affine-finiteness-descent. Locally finite-dimensional spans are
   equivalent to locally having values in a finite coefficient extension: finitely
   many basis elements generate a finite compositum, and conversely a finite
   extension is finite-dimensional. The constructibility conventions agree. Descent
   gives bounded constructible underlying derived direct image of the single sheaf.
4. The module categories are Grothendieck by lem-weil-pbc-ring-sheaves-grothendieck.
   Apply lem-sf-fixed-pair-derived-forget-comparison to their Frobenius equivalences
   and the direct image. Its lift is precisely the framework equivariant direct
   image. Thus forgetting its actual derived direct image is canonically isomorphic
   to the underlying derived direct image, in the ordinary derived category.
5. Exact forgetting commutes with cohomology and conservativity reflects its
   vanishing outside the finite interval of step 3. The same cohomology isomorphisms
   transport constructibility in every integer degree. -/
theorem WeilComplex.proper_sheaf_finiteness
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] {Z T : Scheme.{u}}
    [Z.Over (Spec (CommRingCat.of k₀))] [T.Over (Spec (CommRingCat.of k₀))]
    (p : Z ⟶ T) [p.IsOver (Spec (CommRingCat.of k₀))] [IsProper p]
    [QuasiCompact (T ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (T ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (T ↘ Spec (CommRingCat.of k₀))] :
    (ProEtaleWeilSheaf.lowerStar k₀ l p).Additive ∧
      PreservesFiniteLimits (ProEtaleWeilSheaf.lowerStar k₀ l p) ∧
      ∀ (F : ProEtaleWeilSheaf k₀ l Z), WeilSheaf.objectProperty k₀ l Z F →
        WeilComplex.objectProperty k₀ l T
          ((ProEtaleWeilSheaf.lowerStar k₀ l p).rightDerivedFunctor.obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) := by
  sorry

end AlgebraicGeometry
