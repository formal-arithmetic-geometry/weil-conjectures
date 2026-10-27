/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport
import Sheaf.AlgebraicGeometry.AlgebraicSpaceIdealClosedSubspaceCorrespondence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentSupportIdealPower
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import Sheaf.CategoryTheory.RingedSiteModules

/-! # Separating two closed supports of a coherent module on an algebraic space

Source: Stacks Project, Spaces Cohomology, Tag 07UP, lemma-prepare-filter-support,
with Zprime = T₁ and Z = T₂
(blueprint: lem-sfb-space-coherent-support-union-sequence).

Coherence is site quasi-coherence together with coherence on every etale scheme chart.
Support is the existing geometric-germ locus `moduleSupport`. The quotient is specified
by its cokernel universal property in the original category of module sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A coherent module supported on the union of two closed sets is an extension of
coherent modules supported on those sets, with the submodule on the first set.
Source: Stacks Project, Spaces Cohomology, Tag 07UP, lemma-prepare-filter-support,
with Zprime = T₁ and Z = T₂
(blueprint: lem-sfb-space-coherent-support-union-sequence).

Proof:
1. Give T₂ its reduced closed subspace Z using lem-sfb-space-reduced-closed-support.
   Its defining ideal I is quasi-coherent and restricts to the defining ideal on charts
   by lem-sfb-space-ideal-closed-subspace-correspondence. Set A_n = I^n F and B_n = F/A_n.
   Both are coherent for every n, including zero, by lem-sfb-space-coherent-support-ideal-power.
2. The open U = X minus T₁ exists by lem-a1-space-etale-open-image. It is Noetherian:
   lem-sfb-noetherian-space-topology makes its point space quasi-compact, local
   Noetherianity is inherited on charts, and lem-sfb-space-integral-qcqs-permanence
   gives quasi-separatedness of this quasi-compact open subspace.
3. Restriction to U preserves coherence and geometric stalks. The support of F|U lies
   in Z times_X U. The ideal correspondence identifies its defining ideal with I|U.
   Apply lem-sfb-space-coherent-support-ideal-power on U to find n with (I|U)^n F|U = 0.
   Locally generated products commute with restriction, so A_n|U = 0. Thus Supp(A_n)
   is contained in T₁.
4. On W = X minus T₂ the base change of Z is empty, by the reduced-closed-support
   theorem. The ideal correspondence gives I|W = O_W. Hence A_n|W = F|W, also for n = 0,
   and B_n|W = 0. Cokernels are sheafified sectionwise quotients, and restriction to
   the localized site computes the same local quotients (def-weil-sheaf-of-modules-category).
   Thus Supp(B_n) is contained in T₂, including at points outside both closed sets.
5. Choose the n from step 3, take A = A_n as a subobject of F and B = B_n. The inclusion
   is monic and its cokernel has kernel A, giving the asserted short exact sequence
   in module sheaves. Step 1 gives coherence; steps 3 and 4 give the two inclusions. -/
theorem exists_coherent_subobject_of_support_union
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    (hln : ∀ T : X.EtaleSite, IsLocallyNoetherian (X.etaleForget.obj T))
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (F : X.Modules) (hFqc : F.IsQuasicoherent)
    (hFcoh : ∀ T : X.EtaleSite,
      RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
        ((X.schemeRestriction T).obj F))
    (T₁ T₂ : Set (Point X.obj.obj)) (hT₁ : IsClosed T₁) (hT₂ : IsClosed T₂)
    (hSupp : moduleSupport F = T₁ ∪ T₂) :
    ∃ (A : Subobject F) (B : X.Modules) (q : F ⟶ B) (w : A.arrow ≫ q = 0),
      SheafOfModules.IsQuasicoherent (A : X.Modules) ∧
      (∀ T : X.EtaleSite,
        RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj (A : X.Modules))) ∧
      B.IsQuasicoherent ∧
      (∀ T : X.EtaleSite,
        RingedSpace.IsCoherent (X.etaleForget.obj T).toRingedSpace
          ((X.schemeRestriction T).obj B)) ∧
      Nonempty (IsColimit (CokernelCofork.ofπ q w)) ∧
      (ShortComplex.mk A.arrow q w).ShortExact ∧
      moduleSupport (A : X.Modules) ⊆ T₁ ∧ moduleSupport B ⊆ T₂ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
