/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic

import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyContractibleEvaluationColimits
import Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
import Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections
import Sheaf.AlgebraicGeometry.ProEtaleVanishingDetection
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
import Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction

/-!
# Proper acyclicity after extension by zero on a Cartesian open

Source: blueprint `prop-exc-base-change-proper`, Steps 2--4; Stacks Project,
Tag 0F7B (the etale analogue), and proetale Tags 09AE and 09BN
(blueprint: lem-exc-proetale-cartesian-open-injective-acyclic).
-/

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

universe u

set_option autoImplicit false

@[expose] public section

/--
For a proper morphism and an arbitrary open of the target, extension by zero of an
injective module sheaf on the Cartesian inverse image is acyclic for proper direct
image.  The finite cohomological-dimension assumption is retained exactly as in the
node, although the reduction through quasi-compact principal opens does not use it.

Source: blueprint `prop-exc-base-change-proper`, Steps 2--4; Stacks Project,
Tag 0F7B, case (b), with the pro-etale open functors of Tags 09AE and 09BN
(blueprint: lem-exc-proetale-cartesian-open-injective-acyclic).

Proof plan, following the six steps of the node.
1. Choose a bounded-below injective resolution using
   `prop-pur-kinjective-resolutions-exist` and `lem-weil-pbc-dplus-injective-representative`.
   The derived-computation lemma `lem-weil-pbc-right-derived-plus-injective`, exact
   evaluation (`lem-weil-pbc-proetale-wcontractible-affine-evaluation-colimits`), and
   `lem-weil-pbc-proetale-restriction-injectives` identify the value of the higher
   direct image on an affine weakly contractible object Q with cohomology on
   P = V times_T Q. The same calculation applies at the terminal object of Q's site.
2. Exhaust W times_T Q by finite unions W_E of principal opens of the affine Q.
   Their inverse images U_E in P are quasi-compact opens. Properness survives base
   change. Restriction of J to U_E is injective by the restriction lemma. The
   weakly-etale localization and normalized open-base-change lemmas identify the
   restriction of k_!J to P with extension by zero of J restricted to U times_T Q.
3. Apply `lem-sp-proetale-open-injective-proper-acyclic` to each finite stage.
   Step 1 identifies its positive cohomology on P with zero.
4. The adjunction `lem-weil-extension-by-zero-adjunction` gives transition maps
   between the finite-stage extensions. Its Hom bijection and sheaf gluing on
   the open cover exhibit their filtered colimit as the restriction of k_!J to P.
   Composition of open extensions follows from their composite right adjoints.
5. Properness over the affine Q makes P qcqs. Apply
   `det-pe-bounded-continuity-sections` to the finite-stage complexes concentrated
   in degree zero, with common lower bound zero. Their positive cohomology and
   hence that of their colimit vanish by Step 3.
6. `lem-sf-proetale-vanishing-detection` detects zero sheaves on affine weakly
   contractible objects, so Step 1 gives vanishing of each positive higher image.
The empty open, whole open, zero ring, and identity proper morphism are included.
-/
theorem isZero_higherDirectImage_cartesianOpen_injective
    (A : Type u) [CommRing A] [Finite A]
    {V T W : Scheme.{u}} (p : V ⟶ T) (i : W ⟶ T)
    [IsProper p] [IsOpenImmersion i]
    (hcd : ∃ d : ℕ, ∀ (F : proEtaleRingModules V (proEtaleConstantRing V A))
      (q : ℕ), d < q →
        IsZero ((DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T A)) (q : ℤ)).obj
          ((proEtaleConstantDerivedDirectImage p A).obj
            ((DerivedCategory.singleFunctor
              (proEtaleRingModules V (proEtaleConstantRing V A)) 0).obj F))))
    (J : proEtaleRingModules (pullback p i)
      (proEtaleConstantRing (pullback p i) A)) [Injective J] :
    ∀ q : ℕ, 0 < q →
      IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules T (proEtaleConstantRing T A)) (q : ℤ)).obj
        ((proEtaleConstantDerivedDirectImage p A).obj
          ((DerivedCategory.singleFunctor
            (proEtaleRingModules V (proEtaleConstantRing V A)) 0).obj
            ((sfIntrinsicExtensionByZero (pullback.fst p i) A).obj J)))) := by
  sorry

end

end AlgebraicGeometry.Scheme
