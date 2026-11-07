/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.EtaleRestrictedSectionsFactors
import Submission.WeilConjectures.AlgebraicGeometry.EtaleRestrictedSectionsComponentIso

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Properties of the restricted augmented CE total

Source: Stacks Project, Tags 015J and 0133.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The unique lift through the monic filtered-step inclusion, a genuine universal
property construction rather than a choice of an arbitrary isomorphism.
Source: Stacks, Tag 015J, column filtration.
(blueprint: def-weil-pbc-etale-restricted-sections-lift). -/
noncomputable def etaleRestrictedSectionsLift
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :=
  (T.L.step q).factorThru (etaleRestrictedSectionsInclusion X K T q)
    (etaleRestrictedSections_factors X K T q)

/-- The lift has the prescribed composite with the filtered-step inclusion.
Source: Stacks, Tag 015J. Proof: the defining universal property of factorThru.
(blueprint: def-weil-pbc-etale-restricted-sections-lift). -/
theorem etaleRestrictedSectionsLift_arrow
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :
    etaleRestrictedSectionsLift X K T q ≫ (T.L.step q).arrow =
      etaleRestrictedSectionsInclusion X K T q := by
  exact Subobject.factorThru_arrow _ _ _


/-- The canonical sections lift is an isomorphism of complexes.
Source: Stacks, Tag 015J, proof remark (3); finite diagonal sums.

Proof: In degree n, Γ commutes with the finite sum of terms having r ≥ 0,
s ≥ q, r+s=n, as implemented by etaleCEMappedTotalIso. The restricted mapped
total inclusion identifies this sum with the second-filtration subobject.
By T.filtration_formula, this is precisely the degree-n filtered step.
Consequently the degree-n lift is the canonical isomorphism onto that subobject.
It is the lift in the definition by cancellation of the monic step inclusion.
All its components are isomorphisms, hence the chain map is an isomorphism.
The empty sum gives the zero-object isomorphism; the same calculation works
for arbitrary integer bounds and for zero terms.
(blueprint: lem-weil-pbc-etale-restricted-sections-lift-isIso). -/
theorem etaleRestrictedSectionsLift_isIso
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q : ℤ) :
    IsIso (etaleRestrictedSectionsLift X K T q) := by
  have h (n : ℤ) : IsIso ((etaleRestrictedSectionsLift X K T q).f n) :=
    etaleRestrictedSectionsLift_component_isIso X K T q n
  exact HomologicalComplex.Hom.isIso_of_components _

end AlgebraicGeometry.Etale
