/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenLowerShriekLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperNoetherianBase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicAlgCl
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionFormulaPadicIntegers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperPadicSubfield
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperAmbientIntegral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriekLocalizingEllAdic
import WeilConjectures.Tactic.ExactModProofs

/-!
# Inputs from other subsections for the projection formula on `Loc(Dbc)`

The projection formula and proper base change on the localizing categories `Loc(Dbc(-, Λ))`
for the `ℓ`-adic coefficient rings `Λ = 𝒪̲_E, E̲, ℚ̲̄_ℓ` (blueprint `sk-thm-sf-pf-adic`,
`sk-thm-sf-pf-field`) rest on the following statements of other subsections of the blueprint,
stated here for the module objects over `Λ_X` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject`. Each theorem carries the blueprint id of the
node it formalises and states that node for one coefficient ring; the docstring lists the
clauses of the node which are not stated, for lack of the relevant notions for module objects.
They are not proved here, except that `lem-sfb-dc-tensor-preserves` and
`sk-prop-open-coefficients` are deduced from the general statements
`AlgebraicGeometry.ProEtale.CondensedRing.isMonoidal_boundedConstructible` and
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_rightDerivedLowerStar_obj`, and
that the proper direct image maps `Loc(Dbc)` into `Loc(Dbc)` and preserves direct sums there is
deduced from `properLowerStarHypotheses_padicIntegersRingObj`,
`properLowerStarHypotheses_continuousMapRingObj` and `properLowerStarHypotheses_padicAlgClRingObj`
(`localizingBoundedConstructible_rightDerivedLowerStar_of_properLowerStarHypotheses`).

* `lem-sfb-dc-tensor-preserves`: `⊗ᴸ` preserves bounded constructible complexes;
* `det-thm-sfb-proper-base-change-integral`, `det-thm-sfb-proper-base-change-rational`: proper
  direct image, proper base change and the projection formula on `Dbc(-, Λ)`;
* `det-prop-int-compactness-direct-sums`, `sk-prop-proper-image-localizing`: the proper direct
  image maps `Loc(Dbc(X, Λ))` into `Loc(Dbc(Y, Λ))` and preserves direct sums there (and so does
  the extension by zero along an open immersion);
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
subextension `E` of `ℚ̄_ℓ / ℚ_ℓ`, `E : PadicAlgCl.FiniteIntermediateField ℓ`) and
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

/-- Blueprint `det-thm-sfb-proper-base-change-integral`: Proper direct image, base change and
projection formula for `𝒪_E`. Let `p : X ⟶ Y` be proper.

1. For `K ∈ Dbc(X, 𝒪_E)`, `Rp_*K` is derived `π_E`-complete, and
   `(Rp_*K) ⊗ᴸ 𝒪_{E,Y}/π_E ≃ Rp_*(K ⊗ᴸ 𝒪_{E,X}/π_E)`; hence `Rp_*K ∈ Dbc(Y, 𝒪_E)`.
2. (Derived Nakayama.) A derived `π_E`-complete `C` with `C ⊗ᴸ 𝒪_E/π_E = 0` is zero.
3. The proper base change map `g^*Rp_*K ⟶ Rp'_*g'^*K` (for a cartesian square
   `g' ≫ p = p' ≫ g`) and the projection formula map `Rp_*K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ p^*M)` are
   isomorphisms for `K ∈ Dbc(X, 𝒪_E)` and `M ∈ Dbc(Y, 𝒪_E)`.

Stated here: the conclusion `Rp_*K ∈ Dbc(Y, 𝒪_E)` of (1), and (3). Not stated: the derived
completeness and the reduction formula of (1), and (2): derived completeness and reduction
modulo `π_E` (`sk-def-pe-derived-completion`) are not available for module objects over
`𝒪_{E,X}`. -/
theorem properDirectImage_baseChange_projectionFormula_padicIntegersRingObj (p : X ⟶ Y)
    [IsProper p.left] :
    (∀ K : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) K →
        boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left)
          ((R((p.left)_*⟦Profinite.padicIntegersRingObj ℓ E⟧)).obj K)) ∧
    (∀ {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' p' p g)
      (K : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left)),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) K →
        IsIso ((baseChangeMap (Profinite.padicIntegersRingObj ℓ E)
          ((Over.forget _).map_commSq sq.toCommSq)).app K)) ∧
    (∀ (K : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](X.left))
      (M : 𝔻[Profinite.padicIntegersRingObj.{u} ℓ E](Y.left)),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) X.left) K →
        boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E) Y.left) M →
          IsIso (((projectionMap (Profinite.padicIntegersRingObj ℓ E) p.left).app K).app M)) :=
  ⟨fun K hK ↦ PadicIntegersRingObj.boundedConstructible_rightDerivedLowerStar_obj ℓ E p ⟨K, hK⟩,
    fun sq K hK ↦ isIso_baseChangeMap_app_padicIntegers_of_isProper ℓ E sq
      ((Over.forget _).map_commSq sq.toCommSq) rfl rfl rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl K hK,
    fun K M hK hM ↦
      isIso_projectionMap_padicIntegersRingObj_of_boundedConstructible ℓ E p K M hK hM⟩

end Integers

/-! ### The coefficient ring E̲ -/

section Field

variable (E : PadicAlgCl.FiniteIntermediateField ℓ)

set_option hygiene false in
/-- The condensed field `E̲`. -/
local notation "𝐄" => Profinite.continuousMapRingObj.{u} E

end Field

/-! ### The coefficient ring ℚ̲̄_ℓ -/

section AlgCl

set_option hygiene false in
/-- The condensed field `ℚ̲̄_ℓ`. -/
local notation "𝐐" => Profinite.padicAlgClRingObj.{u} ℓ

omit [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [IsSeparated Y'.hom] in
/-- Blueprint `det-thm-sfb-proper-base-change-rational`: Proper direct image, base change and
projection formula for `E` and `ℚ̄_ℓ`; the case `Λ = ℚ̲̄_ℓ`. Let `p : X ⟶ Y` be proper.

1. For `K ∈ D(X_proét, 𝒪_E)` bounded below, `Rp_*(K[1/ℓ]) ≃ (Rp_*K)[1/ℓ]`; for
   `K ∈ D(X_proét, E)` bounded below and `F/E` finite, `Rp_*(K_F) ≃ (Rp_*K)_F` and
   `Rp_*(K_{ℚ̄_ℓ}) ≃ (Rp_*K)_{ℚ̄_ℓ}`, via the canonical maps.
2. `Rp_*` maps `Dbc(X, Λ)` into `Dbc(Y, Λ)`.
3. The proper base change map `g^*Rp_*K ⟶ Rp'_*g'^*K` (for a cartesian square
   `g' ≫ p = p' ≫ g`) and the projection formula map `Rp_*K ⊗ᴸ M ⟶ Rp_*(K ⊗ᴸ p^*M)` are
   isomorphisms for `K ∈ Dbc(X, Λ)` and `M ∈ Dbc(Y, Λ)`.

Stated here: (2) and (3), for `Λ = ℚ̲̄_ℓ`. Not stated: the comparisons (1) of the direct image
with the changes of coefficients `𝒪_E → E`, `E → F`, `E → ℚ̄_ℓ` on bounded below complexes;
the comparison maps `AlgebraicGeometry.ProEtale.CondensedRing.derivedPushHom` are defined only
for an exact extension of scalars; exactness is not available for `𝒪_{E,X} ⟶ E_X`, and for
`E_X ⟶ F_X`, `E_X ⟶ ℚ̄_ℓ,X` it is only an unproved input of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility` (where the
comparisons for these two changes are also asserted, on all unbounded objects), which formalises
no blueprint node. The morphisms of condensed rings involved are constructed only for finite
subextensions of `ℚ̄_ℓ` (`PadicAlgCl.FiniteIntermediateField`). -/
theorem properDirectImage_baseChange_projectionFormula_padicAlgClRingObj (p : X ⟶ Y)
    [IsProper p.left] :
    (∀ K : 𝔻[𝐐](X.left), boundedConstructible (condensedRingObj 𝐐 X.left) K →
      boundedConstructible (condensedRingObj 𝐐 Y.left) ((R((p.left)_*⟦𝐐⟧)).obj K)) ∧
    (∀ {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' p' p g)
      (K : 𝔻[𝐐](X.left)), boundedConstructible (condensedRingObj 𝐐 X.left) K →
        IsIso ((baseChangeMap 𝐐 ((Over.forget _).map_commSq sq.toCommSq)).app K)) ∧
    (∀ (K : 𝔻[𝐐](X.left)) (M : 𝔻[𝐐](Y.left)), boundedConstructible (condensedRingObj 𝐐 X.left) K →
      boundedConstructible (condensedRingObj 𝐐 Y.left) M →
        IsIso (((projectionMap 𝐐 p.left).app K).app M)) :=
  ⟨fun K hK ↦ boundedConstructible_rightDerivedLowerStar_obj ℓ p ⟨K, hK⟩,
    fun sq K hK ↦ by
      have : IsNoetherian ((Over.forget (Spec (.of k))).obj Y) := isNoetherian_left Y
      have : IsNoetherian ((Over.forget (Spec (.of k))).obj Y') := isNoetherian_left Y'
      have : IsProper ((Over.forget (Spec (.of k))).map p) := ‹IsProper p.left›
      exact isIso_baseChangeMap_app_padicAlgCl_of_isProper ℓ (Y := (Over.forget _).obj Y)
        (Y' := (Over.forget _).obj Y') Y.hom Y'.hom ((Over.forget _).map_commSq sq.toCommSq)
        (sq.map (Over.forget _)) K hK,
    fun K M hK hM ↦ isIso_projectionMap_padicAlgClRingObj_of_integral ℓ p
      (fun E K M hK hM ↦ by
        exact_mod_proofs (properDirectImage_baseChange_projectionFormula_padicIntegersRingObj ℓ
          (X' := X) (Y' := Y) E.1 p).2.2 K M hK hM) K M hK hM⟩

end AlgCl

end AlgebraicGeometry.ProEtale.CondensedRing
