/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing

/-!
# Inputs from other subsections for the projection formula on `Loc(Dbc)`

The projection formula and proper base change on the localizing categories `Loc(Dbc(-, Λ))`
for the `ℓ`-adic coefficient rings `Λ = 𝒪̲_E, E̲, ℚ̲̄_ℓ` (blueprint `sk-thm-sf-pf-adic`,
`sk-thm-sf-pf-field`) rest on the following statements of other subsections of the blueprint,
stated here for the module objects over `Λ_X` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject` (each theorem carries the blueprint id of the
node it formalises; they are not proved here):

* `lem-sfb-dc-tensor-preserves`: `⊗ᴸ` preserves bounded constructible complexes;
* `det-thm-sfb-proper-base-change-integral`, `det-thm-sfb-proper-base-change-rational`: proper
  base change and the projection formula on `Dbc(-, Λ)`;
* `det-prop-int-compactness-direct-sums`, `sk-prop-proper-image-localizing`: the proper direct
  image maps `Loc(Dbc(X, Λ))` into `Loc(Dbc(Y, Λ))` and preserves direct sums there;
* `sk-prop-proper-base-change-unbounded`, `det-proper-base-change-unbounded-extension`: proper
  base change on the localizing categories;
* `sk-prop-open-coefficients`: the direct image along a quasi-compact open immersion preserves
  `Dbc(-, Λ)`.

## The setting

As for the bounded constructible six functors
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`), all schemes
are separated and of finite type over a field `k` of characteristic `p > 0` with `p ≠ ℓ`
(blueprint `sk-def-sfb-dc-setting`), and the functors are those of the underlying morphisms of
schemes. The coefficient rings are the condensed rings `𝒪̲_E = Profinite.padicIntegersRingObj ℓ E`
(for a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`), `E̲ = Profinite.continuousMapRingObj E` (for a finite
extension `E` of `ℚ_ℓ`, as in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper`) and
`ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ) = D(Mod_{Λ_X})` of module objects over `Λ_X`. -/
local notation "𝔻[" Λ "](" X ")" =>
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

include ℓ k

/-! ### The integral coefficient ring `𝒪̲_E` -/

section Integers

variable (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]

/-- Blueprint `lem-sfb-dc-tensor-preserves`: `⊗ᴸ` preserves bounded constructible complexes
(`ℓ`-adic `Λ`); the case `Λ = 𝒪̲_E`. If `K, L ∈ D(Mod_{𝒪_{E,X}})` are bounded constructible, then
so is `K ⊗ᴸ_{𝒪_{E,X}} L`. -/
theorem boundedConstructible_tensor_padicIntegersRingObj
    {K L : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left)}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) K)
    (hL : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) L) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)
      (K ⊗ L) :=
  sorry

/-- Blueprint `det-thm-sfb-proper-base-change-integral`: Proper direct image, base change and
projection formula for `𝒪_E`; part (3), the projection formula: for `p : X ⟶ Y` proper,
`K ∈ Dbc(X, 𝒪_E)` and `M ∈ Dbc(Y, 𝒪_E)`, the projection formula map
`Rp_*K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ p^*M)` is an isomorphism. -/
theorem isIso_projectionMap_padicIntegersRingObj (p : X ⟶ Y) [IsProper p.left]
    {K : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left)}
    {M : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](Y.left)}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) K)
    (hM : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left) M) :
    IsIso (((projectionMap (Profinite.padicIntegersRingObj ℓ E) p.left).app K).app M) :=
  sorry

/-- Blueprint `det-thm-sfb-proper-base-change-integral`: Proper direct image, base change and
projection formula for `𝒪_E`; part (3), proper base change: for a cartesian square
`g' ≫ p = p' ≫ g` with `p` proper and `K ∈ Dbc(X, 𝒪_E)`, the base change map
`g^*Rp_*K ⟶ Rp'_*g'^*K` is an isomorphism. -/
theorem isIso_baseChangeMap_padicIntegersRingObj {p : X ⟶ Y} {g : Y' ⟶ Y} {p' : X' ⟶ Y'}
    {g' : X' ⟶ X} [IsProper p.left] (sq : IsPullback g' p' p g)
    {K : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left)}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) K) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E)
      ((Over.forget _).map_commSq sq.toCommSq)).app K) :=
  sorry

/-- Blueprint `det-prop-int-compactness-direct-sums`: Integral proper direct image on the
localizing categories; part (3): for `p : X ⟶ Y` proper, `Rp_*` maps `Loc(Dbc(X, 𝒪_E))` into
`Loc(Dbc(Y, 𝒪_E))` and preserves direct sums there. -/
theorem localizingBoundedConstructible_rightDerivedLowerStar_padicIntegersRingObj (p : X ⟶ Y)
    [IsProper p.left] :
    (∀ M, localizingBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X.left M →
      localizingBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) Y.left
        ((R((p.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj M)) ∧
    (R((p.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).PreservesCoproductsOn.{u + 1}
      (localizingBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X.left) :=
  sorry

/-- Blueprint `det-proper-base-change-unbounded-extension`: Extending proper base change from
`Dctf` to the localizing closure; the case `Λ = 𝒪̲_E` (for which `Dctf = Dbc`): for a cartesian
square `g' ≫ p = p' ≫ g` with `p` proper, if the base change map `g^*Rp_*K ⟶ Rp'_*g'^*K` is an
isomorphism for every `K ∈ Dbc(X, 𝒪_E)`, then it is an isomorphism for every
`K ∈ Loc(Dbc(X, 𝒪_E))`. -/
theorem isIso_baseChangeMap_of_localizing_padicIntegersRingObj {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper p.left] (sq : IsPullback g' p' p g)
    (h : ∀ K, boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left)
      K → IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E)
        ((Over.forget _).map_commSq sq.toCommSq)).app K))
    {K : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left)}
    (hK : localizingBoundedConstructible (Profinite.padicIntegersRingObj ℓ E) X.left K) :
    IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E)
      ((Over.forget _).map_commSq sq.toCommSq)).app K) :=
  sorry

/-- Blueprint `sk-prop-open-coefficients`: Direct image along an open immersion; the case
`Λ = 𝒪̲_E`: for a quasi-compact open immersion `j : U ⟶ X`, `Rj_*` maps `Dbc(U, 𝒪_E)` into
`Dbc(X, 𝒪_E)`. -/
theorem boundedConstructible_rightDerivedLowerStar_openImmersion_padicIntegersRingObj
    (j : X ⟶ Y) [IsOpenImmersion j.left] [QuasiCompact j.left]
    {K : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left)}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) K) :
    boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left)
      ((R((j.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K) :=
  sorry

end Integers


/-! ### The coefficient ring E̲ -/

section Field

variable (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]

/-- Blueprint `lem-sfb-dc-tensor-preserves`: `⊗ᴸ` preserves bounded constructible complexes
(`ℓ`-adic `Λ`); the case `Λ = E̲`. If `K, L ∈ D(Mod_{Λ_X})` are bounded constructible, then
so is `K ⊗ᴸ_{Λ_X} L`. -/
theorem boundedConstructible_tensor_continuousMapRingObj
    {K L : 𝔻[Profinite.continuousMapRingObj.{u} E](X.left)}
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X.left) K)
    (hL : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X.left) L) :
    boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X.left) (K ⊗ L) :=
  sorry

/-- Blueprint `det-thm-sfb-proper-base-change-rational`: Proper direct image, base change and
projection formula for `E` and `ℚ̄_ℓ`; part (3), the projection formula, for `Λ = E̲`: for
`p : X ⟶ Y` proper, `K ∈ Dbc(X, Λ)` and `M ∈ Dbc(Y, Λ)`, the projection formula map
`Rp_*K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ p^*M)` is an isomorphism. -/
theorem isIso_projectionMap_continuousMapRingObj (p : X ⟶ Y) [IsProper p.left]
    {K : 𝔻[Profinite.continuousMapRingObj.{u} E](X.left)} {M : 𝔻[Profinite.continuousMapRingObj.{u} E](Y.left)}
    (hK : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} E) X.left) K)
    (hM : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj.{u} E) Y.left) M) :
    IsIso (((projectionMap (Profinite.continuousMapRingObj.{u} E) p.left).app K).app M) :=
  sorry

/-- Blueprint `sk-prop-proper-image-localizing`: Proper direct image and extension by zero;
the proper direct image, for `Λ = E̲` (for which `Dctf = Dbc`): for `p : X ⟶ Y` proper,
`Rp_*` restricts to an exact functor `Loc(Dbc(X, Λ)) ⥤ Loc(Dbc(Y, Λ))` that preserves direct
sums. -/
theorem localizingBoundedConstructible_rightDerivedLowerStar_continuousMapRingObj (p : X ⟶ Y)
    [IsProper p.left] :
    (∀ M, localizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X.left M →
      localizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) Y.left ((R((p.left)_*⟦Profinite.continuousMapRingObj.{u} E⟧)).obj M)) ∧
    (R((p.left)_*⟦Profinite.continuousMapRingObj.{u} E⟧)).PreservesCoproductsOn.{u + 1}
      (localizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X.left) :=
  sorry

/-- Blueprint `sk-prop-proper-base-change-unbounded`: Proper base change on the localizing
categories, for `Λ = E̲` (for which `Dctf = Dbc`): for a cartesian square
`g' ≫ p = p' ≫ g` with `p` proper, the base change map `g^*Rp_*K ⟶ Rp'_*g'^*K` is an
isomorphism for every `K ∈ Loc(Dbc(X, Λ))`. -/
theorem isIso_baseChangeMap_of_localizing_continuousMapRingObj {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper p.left] (sq : IsPullback g' p' p g)
    {K : 𝔻[Profinite.continuousMapRingObj.{u} E](X.left)} (hK : localizingBoundedConstructible (Profinite.continuousMapRingObj.{u} E) X.left K) :
    IsIso ((baseChangeMap (Profinite.continuousMapRingObj.{u} E) ((Over.forget _).map_commSq sq.toCommSq)).app K) :=
  sorry

end Field

/-! ### The coefficient ring ℚ̲̄_ℓ -/

section AlgCl


/-- Blueprint `lem-sfb-dc-tensor-preserves`: `⊗ᴸ` preserves bounded constructible complexes
(`ℓ`-adic `Λ`); the case `Λ = ℚ̲̄_ℓ`. If `K, L ∈ D(Mod_{Λ_X})` are bounded constructible, then
so is `K ⊗ᴸ_{Λ_X} L`. -/
theorem boundedConstructible_tensor_padicAlgClRingObj
    {K L : 𝔻[Profinite.padicAlgClRingObj.{u} ℓ](X.left)}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X.left) K)
    (hL : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X.left) L) :
    boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X.left) (K ⊗ L) :=
  sorry

/-- Blueprint `det-thm-sfb-proper-base-change-rational`: Proper direct image, base change and
projection formula for `E` and `ℚ̄_ℓ`; part (3), the projection formula, for `Λ = ℚ̲̄_ℓ`: for
`p : X ⟶ Y` proper, `K ∈ Dbc(X, Λ)` and `M ∈ Dbc(Y, Λ)`, the projection formula map
`Rp_*K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ p^*M)` is an isomorphism. -/
theorem isIso_projectionMap_padicAlgClRingObj (p : X ⟶ Y) [IsProper p.left]
    {K : 𝔻[Profinite.padicAlgClRingObj.{u} ℓ](X.left)} {M : 𝔻[Profinite.padicAlgClRingObj.{u} ℓ](Y.left)}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) X.left) K)
    (hM : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Y.left) M) :
    IsIso (((projectionMap (Profinite.padicAlgClRingObj.{u} ℓ) p.left).app K).app M) :=
  sorry

/-- Blueprint `sk-prop-proper-image-localizing`: Proper direct image and extension by zero;
the proper direct image, for `Λ = ℚ̲̄_ℓ` (for which `Dctf = Dbc`): for `p : X ⟶ Y` proper,
`Rp_*` restricts to an exact functor `Loc(Dbc(X, Λ)) ⥤ Loc(Dbc(Y, Λ))` that preserves direct
sums. -/
theorem localizingBoundedConstructible_rightDerivedLowerStar_padicAlgClRingObj (p : X ⟶ Y)
    [IsProper p.left] :
    (∀ M, localizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X.left M →
      localizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) Y.left ((R((p.left)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧)).obj M)) ∧
    (R((p.left)_*⟦Profinite.padicAlgClRingObj.{u} ℓ⟧)).PreservesCoproductsOn.{u + 1}
      (localizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X.left) :=
  sorry

/-- Blueprint `sk-prop-proper-base-change-unbounded`: Proper base change on the localizing
categories, for `Λ = ℚ̲̄_ℓ` (for which `Dctf = Dbc`): for a cartesian square
`g' ≫ p = p' ≫ g` with `p` proper, the base change map `g^*Rp_*K ⟶ Rp'_*g'^*K` is an
isomorphism for every `K ∈ Loc(Dbc(X, Λ))`. -/
theorem isIso_baseChangeMap_of_localizing_padicAlgClRingObj {p : X ⟶ Y} {g : Y' ⟶ Y}
    {p' : X' ⟶ Y'} {g' : X' ⟶ X} [IsProper p.left] (sq : IsPullback g' p' p g)
    {K : 𝔻[Profinite.padicAlgClRingObj.{u} ℓ](X.left)} (hK : localizingBoundedConstructible (Profinite.padicAlgClRingObj.{u} ℓ) X.left K) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj.{u} ℓ) ((Over.forget _).map_commSq sq.toCommSq)).app K) :=
  sorry

end AlgCl

end AlgebraicGeometry.ProEtale.CondensedRing
