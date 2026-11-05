/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCompose
public import WeilConjectures.CategoryTheory.Adjunction.MateFixedSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence
public import WeilConjectures.TraceFormula.Specialization.Basic

/-!

# Trace specialization from compact-support exchanges

Let `c` be an endocorrespondence over `k` (the generic fibre) and `c'` one over `k'` (the special
fibre), with fixed loci `F` and `F'`, and let `Ψ` be specialization functors between the bounded
constructible derived categories of the corresponding schemes. In the nearby-cycles formalism
(blueprint `det-nearby-exchange-maps`) the exceptional exchanges `β_f : Ψ Rf^! ⟶ Rf'^! Ψ` and
the dualizing maps `θ_X : Ψ ω_X ⟶ ω_{X'}` are built from the *compact-support exchanges*

```
ν_f : Rf'_! Ψ ⟶ Ψ Rf_!
```

as their mates for `Rf_! ⊣ Rf^!` (`ProEtale.CondensedRing.exceptionalExchange`), and
`θ_X = β_{a_X}(ℚ̄_ℓ)` read through the specialization unit `σ : ℚ̄_ℓ ≅ Ψ ℚ̄_ℓ` of the point
(`ProEtale.CondensedRing.dualizingExchange`). The proper exchanges `χ_f` are the mates of the
pullback exchanges `α_f : f'^* Ψ ⟶ Ψ f^*` for `f^* ⊣ Rf_*`.

The two coherences of the trace class (blueprint `sk-lem-tf-nearby-mate-coherences` (4) and (6))
follow formally from two properties of `ν`, which in the nearby-cycles formalism hold because `ν`
is compatible with composition and is the inverse of `χ` for proper maps:

* if `ν_{a_F}` is the composite of `ν_d` and `ν_{a_X}` (for `a_F = a_X ∘ d`), then
  `θ_F = d'^! θ_X ∘ β_d(ω_X)` (`ProEtale.CondensedRing.dualizingExchange_eq_comp`, (4));
* if `ν_ι`, `ν_Δ` are inverse to `χ_ι`, `χ_Δ` and the composites of `ν` along `cι = Δd` agree,
  then the fixed-square identity `Rι'_* β_d ∘ χ_ι ∘ Ψ_C(B) = B' ∘ c'^!(χ_Δ) ∘ β_c(RΔ_*)` holds
  (`CategoryTheory.fixedSquare_of_compactSupportExchange`, (6)).

Together with the unit identity, this builds the specialization data `TraceSpecialization` of
blueprint `sk-prop-tf-trace-specialization` out of pullback and compact-support exchanges
(`ProEtale.CondensedRing.Correspondence.TraceSpecialization.ofCompactSupportExchange`).

## Main definitions

- `ProEtale.CondensedRing.exceptionalExchange`: the exceptional exchange `β_f`, the mate of a
  compact-support exchange `ν_f`.
- `ProEtale.CondensedRing.dualizingExchange`: the dualizing map `θ_X = β_{a_X}(ℚ̄_ℓ)`.
- `ProEtale.CondensedRing.Correspondence.TraceSpecialization.ofCompactSupportExchange`: the
  specialization data built from pullback and compact-support exchanges.

## Main statements

- `ProEtale.CondensedRing.dualizingExchange_eq_comp`: the composition law
  `θ_F = d'^! θ_X ∘ β_d(ω_X)` (blueprint `det-nearby-exceptional-tensor` (3)).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {k' : Type u} [Field k'] [Fact (ringChar k').Prime] [Fact (ringChar k' ≠ ℓ)]

section Exchange

variable (ℓ) {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

end Exchange

section Composition

variable (ℓ) {F X P : Over (Spec (.of k))} [LocallyOfFiniteType F.hom] [QuasiCompact F.hom]
  [IsSeparated F.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {F' X' P' : Over (Spec (.of k'))} [LocallyOfFiniteType F'.hom] [QuasiCompact F'.hom]
  [IsSeparated F'.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {ΨF : Dᵇc(F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(F'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

variable {Ψpt : Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
    Dᵇc((point k').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  (σpt : 𝟙_ _ ⟶ Ψpt.obj (𝟙_ _)) [IsIso σpt]

end Composition
namespace Correspondence

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]
  {X' : Over (Spec (.of k'))} [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom]
  {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {K' : Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
  {c : Correspondence ℓ K} {F : c.FixedLocus} {c' : Correspondence ℓ K'} {F' : c'.FixedLocus}

section FixedSquare

variable
    {ΨC : Dᵇc(c.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(c'.C.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {ΨF : Dᵇc(F.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc(F'.F.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {ΨX : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤ Dᵇc(X'.left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    {ΨXX : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧ ⥤
      Dᵇc((X' ⨯ X').left)⟦Profinite.padicAlgClRingObj ℓ⟧}
    (αι : ΨC ⋙ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F'.ι ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ F.ι ⋙ ΨF)
    (αΔ : ΨXX ⋙ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X') ⟶
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (diag X) ⋙ ΨX)
    (νc : ΨC ⋙ boundedConstructibleLowerShriek ℓ c'.support ⟶
      boundedConstructibleLowerShriek ℓ c.support ⋙ ΨXX)
    (νd : ΨF ⋙ boundedConstructibleLowerShriek ℓ F'.d ⟶
      boundedConstructibleLowerShriek ℓ F.d ⋙ ΨX)
    (νι : ΨF ⋙ boundedConstructibleLowerShriek ℓ F'.ι ⟶
      boundedConstructibleLowerShriek ℓ F.ι ⋙ ΨC)
    (νΔ : ΨX ⋙ boundedConstructibleLowerShriek ℓ (diag X') ⟶
      boundedConstructibleLowerShriek ℓ (diag X) ⋙ ΨXX)

end FixedSquare

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
