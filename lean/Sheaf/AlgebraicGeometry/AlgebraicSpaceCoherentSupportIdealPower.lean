/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q84
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedIdealFiltration
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.CoherentSupportPowerIdealKills
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Coherent ideal powers and support on a Noetherian algebraic space

Source: Stacks Project, Spaces Cohomology, Tags 07UK and 07UD
(blueprint: lem-sfb-space-coherent-support-ideal-power).

Coherence is site quasi-coherence and coherence of every Zariski chart restriction,
as in the node. Support containment is written on every etale scheme chart: a nonzero
ordinary stalk maps into the closed subspace. For quasi-coherent modules ordinary
and geometric stalks have identical vanishing, since strict henselization is faithfully
flat. Every space point lifts to a chart, so this is exactly the geometric-support
condition, with no chosen atlas or additional hypothesis.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- All ideal powers and their quotients are coherent, and support in a closed subspace
is equivalent to annihilation by some ideal power. Reducedness is not assumed.
Source: Stacks, Spaces Cohomology, Tags 07UK and 07UD
(blueprint: lem-sfb-space-coherent-support-ideal-power).

Proof:
1. Restrict to an etale scheme chart. The Zariski/etale equivalence
   (lem-trf-scheme-zariski-etale-quasi-coherent-equivalence) and the ideal correspondence
   (lem-sfb-space-ideal-closed-subspace-correspondence) identify the defining ideal with
   the ideal of the closed base change. Local products restrict to the same products.
   By induction the restricted power is the scheme ideal power times the restricted
   module. Quotients agree by exactness of etale association
   (lem-sfb-scheme-etale-module-exact-finiteness-comparison). The scheme section formulas
   (lem-weil-pbc-ideal-times-quasi-coherent-affine-sections) identify both conventions
   for powers and show that products and quotients are quasi-coherent.
2. Apply lem-sfb-space-noetherian-coherent-support to the resulting quasi-coherent
   submodule of the coherent F. Both it and its quotient are coherent, also for n = 0.
3. Choose an affine surjective etale atlas (lem-sfb-qc-space-affine-etale-atlas).
   It is locally Noetherian by hypothesis and quasi-compact because it is affine
   (lem-weil-pbc-affine-scheme-qcqs). Its closed base change has the pulled-back ideal.
4. Support pulls back on this atlas (lem-sfb-space-etale-chart-support); surjectivity
   detects containment in the closed subspace. Apply the scheme criterion
   lem-weil-pbc-coherent-support-power-ideal-kills to obtain one exponent on this atlas.
   The affine section formulas in step 1 identify its powers with the iterated products.
5. Restriction to the atlas detects zero: on any chart T its pullback cover is an etale
   scheme cover (lem-trf-space-fibre-products-etale-covers). A section zero on that cover
   is zero by the separatedness axiom of def-weil-sheaf-of-modules-category. Combine
   with step 4 for the equivalence. None of these steps uses reducedness of Z. -/
theorem coherent_support_ideal_power
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (F : X.Modules) (hFqc : F.IsQuasicoherent)
    (hFcoh : ∀ T : X.EtaleSite,
      RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj F))
    {Z : AlgebraicSpace S} (i : Z ⟶ X)
    (hi : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom) :
    (∀ n : ℕ,
      ((closedIdealPowerModule i F n).IsQuasicoherent ∧
        ∀ T : X.EtaleSite,
          RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
            ((X.schemeRestriction T).obj (closedIdealPowerModule i F n))) ∧
      ((closedIdealPowerQuotient i F n).IsQuasicoherent ∧
        ∀ T : X.EtaleSite,
          RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
            ((X.schemeRestriction T).obj (closedIdealPowerQuotient i F n)))) ∧
    ((∀ (T : X.EtaleSite) (x : X.etaleForget.obj T),
        ¬ Subsingleton (((X.schemeRestriction T).obj F).presheaf.stalk x) →
          schemePointMap T.obj.hom x ∈ pointImage i.hom.hom) ↔
      ∃ n : ℕ, IsZero (closedIdealPowerModule i F n)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
