/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.CompactSupportExchange
public import WeilConjectures.TraceFormula.Specialization.SupportExchange

/-!

# The integral of a specialized section

Let `T` be specialization data from a correspondence `c` over `k` with fixed locus `F` to a
correspondence `c'` over `k'` with fixed locus `F'` (`TraceSpecialization`), whose dualizing map
`θ_F` is the dualizing map of a compact-support exchange `ν_F : Ra_{F'!} Ψ_F ⟶ Ψ_s Ra_{F!}` of
the structure maps (`ProEtale.CondensedRing.dualizingExchange`). If `F'` is proper, the integral of
the specialization `sp_F(z) = θ_F Ψ_F(z) σ_F` of a Borel–Moore section `z` is
```
∫_{F'} sp_F(z) = σ_s⁻¹ ∘ Ψ_s(z^♭) ∘ S,     S = ν_F(ℚ̄_ℓ) ∘ Ra_{F'!}(σ_F) ∘ [F'],
```
where `z^♭ : Ra_{F!} ℚ̄_ℓ ⟶ ℚ̄_ℓ` is the adjoint of `z` and `[F'] : ℚ̄_ℓ ⟶ Ra_{F'!} ℚ̄_ℓ` the unit
class of the proper scheme `F'`
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.integral_sp_eq`). The morphism `S`
does not depend on `z`: it is the specialization of the unit class of `F`.

For the specialization data determined by the support
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.ofSupportExchange`), whose exceptional
exchange `β_c` and dualizing map `θ_X` come from compact-support exchanges `ν_c`, `ν_X`, the
dualizing map `θ_F` is the dualizing map of the composite of `ν_X` with the compact-support exchange
`ν_d` whose mate is `β_d`
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.θF_ofSupportExchange`;

blueprint `det-nearby-exceptional-tensor` (3)).

## Main definitions

- `ProEtale.CondensedRing.BorelMooreSection.unitClass`: the unit class `ℚ̄_ℓ ⟶ Ra_! ℚ̄_ℓ` of a
  proper scheme.
- `ProEtale.CondensedRing.compExchange`: the composite of two exchange transformations through
  composition isomorphisms.

## Main statements

- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.integral_sp_eq`: the integral of a
  specialized section.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Abstract

variable {𝒜 𝒜' ℬ ℬ' 𝒮 𝒮' : Type*} [Category 𝒜] [Category 𝒜'] [Category ℬ] [Category ℬ']
  [Category 𝒮] [Category 𝒮']

variable {L : 𝒜 ⥤ 𝒮} {R : 𝒮 ⥤ 𝒜} {L' : 𝒜' ⥤ 𝒮'} {R' : 𝒮' ⥤ 𝒜'} (adj : L ⊣ R) (adj' : L' ⊣ R')
  {G : 𝒜 ⥤ 𝒜'} {H : 𝒮 ⥤ 𝒮'}

end Abstract

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

section Composition

variable (ℓ) {F X : Over (Spec (.of k))} [LocallyOfFiniteType F.hom] [QuasiCompact F.hom]
  [IsSeparated F.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  {F' X' : Over (Spec (.of k'))} [LocallyOfFiniteType F'.hom] [QuasiCompact F'.hom]
  [IsSeparated F'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  {ΨF : Dᵇc(F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(F'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  (σpt : 𝟙_ _ ⟶ Ψpt.obj (𝟙_ _)) [IsIso σpt]

end Composition

namespace BorelMooreSection

variable (ℓ) (X : Over (Spec (.of k))) [QuasiCompact X.hom] [IsProper X.hom]

variable {ℓ X}

end BorelMooreSection

namespace Correspondence

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {F : c.FixedLocus} {c' : Correspondence ℓ K'} {F' : c'.FixedLocus}

namespace TraceSpecialization

variable (T : c.TraceSpecialization F c' F')
  {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  (σpt : 𝟙_ _ ⟶ Ψpt.obj (𝟙_ _)) [IsIso σpt]

section OfSupportExchange

variable (ΨC : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc(c'.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (ΨXX : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((X' ⨯ X').left)⟦Profinite.padicAlgClRingObj ℓ⟧)
  (χΔ : boundedConstructibleLowerStar ℓ (diag X) ⋙ ΨXX ⟶
    ΨX ⋙ boundedConstructibleLowerStar ℓ (diag X'))
  (βc : boundedConstructibleUpperShriek ℓ c.support ⋙ ΨC ⟶
    ΨXX ⋙ boundedConstructibleUpperShriek ℓ c'.support)
  (σC : 𝟙_ _ ⟶ ΨC.obj (𝟙_ _))
  (νX : ΨX ⋙ boundedConstructibleLowerShriek ℓ (toPoint X') ⟶
    boundedConstructibleLowerShriek ℓ (toPoint X) ⋙ Ψpt)

end OfSupportExchange

end TraceSpecialization

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
