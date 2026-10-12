/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine
import Sheaf.AlgebraicGeometry.Coherent
import Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine

/-! # An ideal power kills a coherent module exactly when its support lies in the zero set

Source: Stacks Project, Cohomology of Schemes, Lemma 30.10.2 (Tag 01Y9),
using Algebra, Lemma 10.62.4 (Tag 00L6)
(blueprint: lem-weil-pbc-coherent-support-power-ideal-kills).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- On a Noetherian scheme, a coherent module is annihilated by some nonnegative power of
an ideal exactly when its nonzero-stalk locus lies in the locus where the stalk ideal is
proper. The latter condition is failure of surjectivity of the stalk inclusion, as in
`quasi_coherent_ideal_zero_set_affine`. The shared `idealSheafPower` has the structure sheaf
with identity inclusion at exponent zero, so its product with `F` is canonically `F`.

Source: Stacks Project, Cohomology of Schemes, Lemma 30.10.2 (Tag 01Y9), with Algebra,
Lemma 10.62.4 (Tag 00L6) (blueprint: lem-weil-pbc-coherent-support-power-ideal-kills).

Proof:
1. Choose a finite affine cover with Noetherian section rings, using pqf-def-locnoeth
   and quasi-compactness (def-weil-pbc-noetherian-ring, def-pc-scheme,
   def-weil-affine-spectrum).
2. Coherence gives finite presentation locally and hence quasi-coherence and finite type.
   By lem-weil-pbc-quasi-coherent-finite-type-affine the sections on each affine in the
   cover form a finite module (pqf-def-coherent, def-weil-finitely-generated-module).
3. By lem-weil-pbc-ideal-times-quasi-coherent-affine-sections, the sections of each ideal
   power times F are the corresponding ideal power times its affine section module.
   At exponent zero this is F itself (def-weil-pbc-coherent-formal-module).
4. Vanishing is equivalent to vanishing of these modules on every member of the cover:
   use lem-weil-pbc-module-restriction-open-immersion-colimits and the counit and
   zero preservation of lem-weil-pbc-affine-tilde-gamma-adjunction, then the sheaf
   property (def-weil-sheaf-of-modules-category).
5. On each affine, support is V(Ann M), by lem-weil-pbc-finite-type-module-support-closed
   and lem-weil-pbc-finite-module-support-annihilator. The ideal zero set is V(I), by
   lem-weil-pbc-quasi-coherent-ideal-zero-set-affine. Thus the global containment is
   equivalent to these containments on the cover.
6. Algebra 00L6: I^n M = 0 iff I^n is contained in Ann M. Such containment implies
   V(Ann M) is contained in V(I). Conversely the zero-locus containment gives
   I contained in the radical of Ann M (lem-weil-pbc-zero-locus-eq-iff-radical-eq).
   Noetherianity makes I finitely generated, so lem-weil-pbc-fg-ideal-radical-power
   gives a power contained in Ann M; all higher powers also kill M.
7. A global killing power therefore implies the support containment. Conversely take
   the maximum of the finitely many affine killing exponents and apply step 4.
   For an empty cover (the empty scheme) take exponent zero. -/
theorem coherent_support_power_ideal_kills (X : Scheme.{u}) [IsNoetherian X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F)
    (K : X.IdealSheafData) :
    (∃ t : ℕ, IsZero (idealModuleProduct (idealSheafPower K.toModulesι t).2 F)) ↔
      {x : X | ¬ Subsingleton (F.presheaf.stalk x)} ⊆
        {x : X | ¬ Function.Surjective
          ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map K.toModulesι).hom} := by
  sorry

end AlgebraicGeometry.Scheme
