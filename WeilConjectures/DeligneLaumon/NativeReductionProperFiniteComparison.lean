/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralDirectImageTowerData
public import WeilConjectures.SixFunctors.ModCondensedCachedInstances
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Finite evaluation of the specified proper-reduction mate

This is the finite scalar comparison needed to prove invertibility of the
whole-system natural transformation. No whole-system isomorphism is assumed here.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Every positive finite evaluation of the specified proper-reduction mate is invertible.
Source: current blueprint integral-adjunction direct-image proof, paragraphs (1)--(2),
the finite scalar cone and restriction-of-scalars argument.
(blueprint: lem-dla1-native-reduction-proper-finite-comparison).

Proof: put r = s.base.ramification and m = r(n+1). The normalized coefficient comparison
identifies reduction modulo ell^(n+1) with reduction modulo the uniformizer to power m.
Use equality of the principal ideals and the corresponding unit rescaling of their
two-term resolutions; this fixes quotient classes and the reduction coaugmentation.
Represent the integral complex by a flat-term K-flat complex. After restriction to the
integral coefficient ring, finite derived reduction is its principal scalar cone. Compute
native direct image by K-injective resolutions. It is triangulated and commutes with the
scalar endomorphism, so it carries this cone to the scalar cone on the native direct image.
Restriction from finite coefficients to integral coefficients is exact. Derived direct-image
composition for the scalar restriction and geometric direct image identifies the restricted
finite direct image with the integral direct image of the restricted finite complex.
To identify the actual map, transpose through the scalar and geometric adjunctions.
On tensor generators the normalization of q.pullback is the scalar/pullback comparison;
on flat-term K-flat representatives its representatives equation gives the derived version.
The normalized pushEvaluation comparison has the same geometric unit and counit. Therefore
the restriction of the displayed composite is the cone comparison just constructed,
not merely an unspecified isomorphism between its endpoints. The cone comparison is
invertible. Scalar restriction is exact and faithful, hence detects invertibility on every
cohomology sheaf; the displayed finite-coefficient morphism is consequently invertible.
All comparisons use the actual positive quotient n+1, including n=0; zero complexes and
empty schemes give the same formulas. No choice of a system morphism from its levels is used. -/
theorem nativeReductionProperFiniteComparison (s : Presentation l E)
    (q : ReductionGeometry l E s) :
    ∀ (k : Type u) [Field k] [PerfectField k] (_hl : IsUnit (l : k))
      (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))]
      (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p],
      ∀ (K : Constructible l E X) (n : ℕ),
        IsIso
          ((SpTowerShriek.Ev l E Y n).map (properReduction l E s q p K.obj) ≫
            ((s.operations.geometry p).pushEvaluation n).hom.app
              ((derivedReduction l E s X).obj K.obj)) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower
