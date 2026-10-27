/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportClosed
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleChartSupport

/-!
# Coherent subquotients and their support on a locally Noetherian algebraic space

Source: Stacks Project, Spaces Cohomology, Tags 07UB and 07UD
(lemma-coherent-Noetherian and lemma-coherent-Noetherian-quasi-coherent-sub-quotient);
Morphisms of Spaces, Tag 07TZ (lemma-support-finite-type)
(blueprint: lem-sfb-space-noetherian-coherent-support).

Coherence means site quasi-coherence and coherence on every étale scheme chart.
A submodule is a monomorphism in all module sheaves. Quotients are specified by
cokernel coforks and their universal property, so every choice of quotient is covered.
Support is the existing geometric-germ support in the atlas topology.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure module is coherent; quasi-coherent submodules and their quotients
in a coherent module are coherent and have closed support. In particular this holds
for the quotient by any quasi-coherent ideal of the structure module.
Source: Stacks Project, Spaces Cohomology, Tags 07UB and 07UD; Morphisms of Spaces,
Tag 07TZ(1) (blueprint: lem-sfb-space-noetherian-coherent-support).

Proof:
1. Restrict to an arbitrary étale scheme chart T. The hypothesis makes T locally
   Noetherian. Restriction is exact by lem-weil-pbc-site-restriction-exact and the
   sectionwise kernels and sheafified cokernels of def-weil-sheaf-of-modules-category.
   It preserves quasi-coherence by local free presentations. The inverse comparison
   in lem-trf-scheme-zariski-etale-quasi-coherent-equivalence is restriction to opens,
   hence preserves the monomorphism N to F on every open of T.
2. The structure module has its rank-one free presentation, so is quasi-coherent.
   Its chart restriction is O_T, quasi-coherent of finite type with generator 1.
   Apply pqf-lem-coherent-ft-locnoeth to obtain its coherence on each chart.
3. Apply lem-weil-pbc-coherent-kernel-cokernel-locnoeth, clause (2), to N_T inside
   F_T. Both N_T and F_T/N_T are coherent. The exact comparison of
   lem-sfb-scheme-etale-module-exact-finiteness-comparison identifies this quotient
   with restriction of any cokernel cofork with its colimit universal property.
   Its local presentations also give site quasi-coherence of that quotient on X.
   Every chart therefore has the required coherent restriction for N and F/N.
4. For either module, pqf-lem-coherent-ft-locnoeth gives finite type on each chart.
   Apply lem-weil-pbc-finite-type-module-support-closed there. By
   lem-sfb-space-etale-chart-support the closed chart support is the inverse image
   of moduleSupport. The final topology of def-a1-space-point-topology, applied to
   complements, gives closedness of both supports on X.
5. Specialize step 3 and step 4 to F = O_X, coherent by step 2, and N = I. This gives
   coherence and closed support of every quotient O_X/I. -/
theorem noetherian_coherent_subquotients_closed_support
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T)) :
    (SheafOfModules.IsQuasicoherent (SheafOfModules.unit X.structureSheaf) ∧
      ∀ T : X.EtaleSite,
        RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj (SheafOfModules.unit X.structureSheaf))) ∧
    (∀ (F N : X.Modules) (i : N ⟶ F), Mono i → F.IsQuasicoherent →
      (∀ T : X.EtaleSite,
        RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj F)) → N.IsQuasicoherent →
      (∀ T : X.EtaleSite,
        RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj N)) ∧
      IsClosed (moduleSupport N) ∧
      ∀ c : CokernelCofork i, IsColimit c →
        c.pt.IsQuasicoherent ∧
        (∀ T : X.EtaleSite,
          RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
            ((X.schemeRestriction T).obj c.pt)) ∧
        IsClosed (moduleSupport c.pt)) ∧
    (∀ (I : X.Modules) (i : I ⟶ SheafOfModules.unit X.structureSheaf),
      Mono i → I.IsQuasicoherent →
      ∀ c : CokernelCofork i, IsColimit c →
        c.pt.IsQuasicoherent ∧
        (∀ T : X.EtaleSite,
          RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
            ((X.schemeRestriction T).obj c.pt)) ∧
        IsClosed (moduleSupport c.pt)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
