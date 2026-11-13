/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleRestrictedSectionsFactors
import WeilConjectures.AlgebraicGeometry.EtaleRestrictedSectionsComponentEpi
import WeilConjectures.AlgebraicGeometry.EtaleRestrictedSectionsInclusionMono

/-! # Degreewise restricted sections comparison

Source: Stacks Project, Tag 015J, proof remark (3), column filtration.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The degree-n factorization of the restricted sections inclusion is invertible.
Source: Stacks Project, Tag 015J, proof remark (3), column filtration. -/
theorem etaleRestrictedSectionsLift_component_isIso
    (X : Scheme.{u})
    (K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (T : EtaleTermwiseHypercohomology X K) (q n : ℤ) :
    IsIso (((T.L.step q).factorThru (etaleRestrictedSectionsInclusion X K T q)
      (etaleRestrictedSections_factors X K T q)).f n) := by
  let f := ((T.L.step q).factorThru (etaleRestrictedSectionsInclusion X K T q)
    (etaleRestrictedSections_factors X K T q)).f n
  have hfac : f ≫ (T.L.step q).arrow.f n =
      (etaleRestrictedSectionsInclusion X K T q).f n := by
    exact HomologicalComplex.congr_hom (Subobject.factorThru_arrow _ _ _) n
  have : Mono ((etaleRestrictedSectionsInclusion X K T q).f n) :=
    etaleRestrictedSectionsInclusion_mono_component X K T q n
  have hmono : Mono f := mono_of_mono_fac hfac
  have hepi : Epi f := etaleRestrictedSectionsLift_component_epi X K T q n
  exact isIso_of_mono_of_epi f

end AlgebraicGeometry.Etale
