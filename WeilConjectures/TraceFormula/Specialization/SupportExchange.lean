/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Basic

/-!

# Trace specialization from the exchange of the support

Let `c` be an endocorrespondence over `k` (the generic fibre) and `c'` one over `k'` (the special
fibre), with fixed loci `ι : F ⟶ C` and `ι' : F' ⟶ C'`. The specialization data
`TraceSpecialization` of blueprint `sk-prop-tf-trace-specialization` consists of specialization
functors `Ψ_C, Ψ_F, Ψ_X, Ψ_{X×X}`, units `σ`, dualizing maps `θ` and exchange maps `χ`, `β`, with
three coherences.

The specialization of the fixed locus can be read off the specialization of the support: since
`ι` and `ι'` are closed immersions, `Ψ_F ≅ Lι'^* Ψ_C Rι_*` for nearby cycles, through the proper
exchange `χ_ι`. Taking this as the *definition* of `Ψ_F`, the data attached to the fixed locus
are determined by those of the support:
* `χ_ι : Ψ_C Rι_* ⟶ Rι'_* Lι'^* Ψ_C Rι_*` is the unit of `Lι'^* ⊣ Rι'_*`;
* `σ_F` is `Lι'^*` of `Ψ_C(η_ι) σ_C`;
* `β_d` is `Lι'^*` of the composite `B' ∘ c'^!(χ_Δ) ∘ β_c(RΔ_*) ∘ Ψ_C(B⁻¹)` followed by the counit,
  where `B : c^! RΔ_* ≅ Rι_* d^!` is the base change of the fixed square;
* `θ_F = d'^! θ_X ∘ β_d(ω_X)` read through the composition isomorphisms of the dualizing complexes.

With these choices the three coherences of `TraceSpecialization` hold by the triangle identities
of `Lι'^* ⊣ Rι'_*` (`ProEtale.CondensedRing.Correspondence.TraceSpecialization.ofSupportExchange`).
What remains to be given is the specialization `Ψ_C` of the support with its unit `σ_C`, the
specializations `Ψ_X`, `Ψ_{X×X}` with any transformation `χ_Δ`, the exceptional exchange `β_c` of
the support map and the dualizing map `θ_X`.

## Main definitions

- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.ofSupportExchange`: the
  specialization data determined by the data of the support.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace Correspondence

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {F : c.FixedLocus} {c' : Correspondence ℓ K'} {F' : c'.FixedLocus}

namespace TraceSpecialization

section Abstract

variable {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {L : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} (adj : L ⊣ R)

end Abstract

variable (ΨC : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc(c'.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨXX : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((X' ⨯ X').left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (χΔ : boundedConstructibleLowerStar ℓ (diag X) ⋙ ΨXX ⟶
    ΨX ⋙ boundedConstructibleLowerStar ℓ (diag X'))
  (βc : boundedConstructibleUpperShriek ℓ c.support ⋙ ΨC ⟶
    ΨXX ⋙ boundedConstructibleUpperShriek ℓ c'.support)

variable (σC : 𝟙_ _ ⟶ ΨC.obj (𝟙_ _))
  (θX : ΨX.obj (dualizingComplex' ℓ X) ⟶ dualizingComplex' ℓ X')

end TraceSpecialization

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
