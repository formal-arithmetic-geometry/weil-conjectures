/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Paper.IntegralCriterionReductions
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
public import Sheaf.Paper.AdicStratifiedPerfectData

import Sheaf.Paper.ModuleObjectRingedSiteDerivedComparison
import Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

/-! # Completeness of internal Hom under the integral presentation equivalence

Source: Stacks Tag 099A, with the section-action and coefficient comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})


/-- The integral presentation of ambient internal Hom is locally derived complete whenever
its second argument is complete. The first argument is unrestricted.

Source: Stacks Project, algebraization.tex, Tag 099A, Definition 0999, and the
module-object/ringed-site comparison on slices
(blueprint: lem-sfb-integral-adic-hom-completeness).

Proof: apply moduleObject_ringedSite_derived_comparison to the spectral integral ring.
Its evaluation and slice comparisons identify ambient internal Hom with the K-injective
ringed-site Hom under the section-action equivalence. Restriction along each of the two
coefficient isomorphisms is exact and is an equivalence; tensor-Hom adjunction identifies
its transported Hom with Hom of the transported objects. The maps fix all quotient
projections, so they also identify the kernel ideal of the first residue projection.
Transport to the equivalent small site used in IsSfbAdicComplete. The same comparisons
hold on every slice. Apply isLocallyDerivedRingedIdealComplete_derivedInternalHom to the
kernel ideal and the transported second argument. Equivalently, for each local ideal
section f, symmetry and currying identify Hom(O[1/f],Hom(K,L)) with
Hom(K,Hom(O[1/f],L)); the inner Hom is zero by the hypothesis. Transport this vanishing
back to the displayed presentation, for every slice and f. No boundedness or
constructibility of the first argument is used. -/
theorem integralAdicHom_complete
    (K L : DerivedCategory (AdicCompletion.Modules l E X))
    (hL : Scheme.IsSfbAdicComplete X (Scheme.pbcIntegralDatum l E).ideal
      (((integralSectionDerivedEquivalence l E X).functor ⋙
        Scheme.integralDetailedTransport X l E ⋙
        Scheme.pbcDerivedRestrict (Scheme.pbcCompletedComparison X
          (Scheme.pbcIntegralDatum l E)).hom).obj L)) :
    Scheme.IsSfbAdicComplete X (Scheme.pbcIntegralDatum l E).ideal
      (((integralSectionDerivedEquivalence l E X).functor ⋙
        Scheme.integralDetailedTransport X l E ⋙
        Scheme.pbcDerivedRestrict (Scheme.pbcCompletedComparison X
          (Scheme.pbcIntegralDatum l E)).hom).obj
        (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj
        (op K)).obj L)) := by sorry

end AlgebraicGeometry.ProEtale
