/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-!
# The basic operations and reduction of the coefficients

Let `Λ` be a commutative ring and `ϖ` a nonzerodivisor of `Λ`, the intended case being
`Λ = 𝒪_E` with a uniformizer `ϖ`, so that `Λ ⧸ (ϖ)ⁿ = A_{E,n}`. The reduction of a complex `K`
of sheaves of `Λ`-modules is its derived base change `K_n = K ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ`, characterised by
its universal property (`CategoryTheory.Sheaf.IsDerivedBaseChange`) and read in `D(Λ)` through
restriction of scalars. Blueprint `lem-fix-operation-reduction` states that this reduction
commutes with the basic operations, compatibly with the units and counits out of which the
projection and exchange transformations are built.

The compatibilities are recorded, for the étale and for the pro-étale model of the coefficient
categories, as the propositions `AlgebraicGeometry.Etale.ReductionCompatibility` and
`AlgebraicGeometry.ProEtale.ReductionCompatibility`, and the node itself is
`AlgebraicGeometry.reductionCompatibility_span_singleton`.

## Main definitions

- `AlgebraicGeometry.Etale.projectionMapApp`: the component `PF_{f, K, L}` of the étale
  projection map over a coefficient ring `Λ'`.
- `AlgebraicGeometry.Etale.ReductionCompatibility`,
  `AlgebraicGeometry.ProEtale.ReductionCompatibility`: reduction modulo `Iⁿ` commutes with the
  basic operations, the projection map and the compact-support exchange map.

## Main statements

- `AlgebraicGeometry.reductionCompatibility_span_singleton` (`lem-fix-operation-reduction`).
- `AlgebraicGeometry.Etale.exists_isDerivedBaseChange_arrowIso_reductionModIdeal_projectionMap`:
  the reduction of `PF_{f, K, L}` modulo `(ϖ)ⁿ` is isomorphic, as an arrow, to the restriction
  of scalars of `PF_{f, K_n, L_n}`.
- `nonempty_arrowIso_reductionModIdeal_rightDerivedLowerShriekOfCompactificationBaseChangeMap`
  (in the namespace `AlgebraicGeometry.ProEtale`): the reduction of the pro-étale exchange map
  `Ex_!(c)` at `K` is isomorphic, as an arrow, to the restriction of scalars of `Ex_!(c)` at
  `K_n`.

## Implementation notes

The two clauses are proved in this file, from the node, rather than in the files using them:
restating a statement involving the monoidal structure of the derived categories over a
quotient ring in another module and closing it with the node makes the kernel compare
independently elaborated instances, which does not terminate in practice.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

/-- The component `PF_{f, K, L}` of the projection map over a coefficient ring `Λ'`.

Stating results at a quotient ring `Λ ⧸ (ϖ)ⁿ` through this constant keeps the monoidal structure
of the derived categories out of their statements: comparing a freshly elaborated projection map
over `Λ ⧸ (ϖ)ⁿ` with an instance of a generic one makes the kernel compare the nested proofs of
the two elaborated monoidal instances, which does not terminate in practice. -/
noncomputable def projectionMapApp (Λ' : Type (u + 1)) [CommRing Λ'] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (K : 𝐃(X, Λ')) (L : 𝐃(Y, Λ')) :=
  ((projectionMap (ModuleCat.{u + 1} Λ') f).app K).app L

/-- Restriction of scalars `D(X_ét, Λ ⧸ Iⁿ) ⥤ D(X_ét, Λ)` along the quotient map. -/
local notation "𝐑𝐞𝐬[" X ", " I ", " n "]" =>
  derivedRestrictScalars (Ideal.Quotient.mk (I ^ n)) X

/-- The compatibility of the reduction `Λ → Λ ⧸ Iⁿ` with the basic operations of the étale
derived categories (the étale part of blueprint `lem-fix-operation-reduction`): every object
has a reduction (a derived base change along `Λ → Λ ⧸ Iⁿ`); the derived pullback, the derived
tensor product, the derived direct image and the compact-support direct image of reductions are
reductions of the corresponding operations; and the reduction of the projection map
`PF_{f, K, L}` (its image under `- ⊗ᴸ (Λ ⧸ Iⁿ)_Y`) is isomorphic as an arrow to the
restriction of scalars of the projection map `PF_{f, K_n, L_n}` over `Λ ⧸ Iⁿ`, which expresses
that the comparisons preserve the units, counits and associativity maps out of which the
projection map is built. -/
structure ReductionCompatibility (Λ : Type (u + 1)) [CommRing Λ] (I : Ideal Λ) (n : ℕ) :
    Prop where
  /-- Every object has a reduction modulo `Iⁿ`. -/
  exists_isDerivedBaseChange (X : Scheme.{u}) (K : 𝐃(X, Λ)) :
    ∃ (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn), IsDerivedBaseChange η
  /-- The derived pullback commutes with reduction modulo `Iⁿ`. -/
  leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) (L : 𝐃(Y, Λ))
    (Ln : 𝐃(Y, Λ ⧸ I ^ n)) (η : L ⟶ 𝐑𝐞𝐬[Y, I, n].obj Ln) (hη : IsDerivedBaseChange η) :
    ∃ θ : L((f)^*[ModuleCat.{u + 1} Λ]).obj L ⟶
      𝐑𝐞𝐬[X, I, n].obj (L((f)^*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Ln),
      IsDerivedBaseChange θ
  /-- The derived tensor product commutes with reduction modulo `Iⁿ`. -/
  derivedTensor {X : Scheme.{u}} (K L : 𝐃(X, Λ)) (Kn Ln : 𝐃(X, Λ ⧸ I ^ n))
    (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn) (η' : L ⟶ 𝐑𝐞𝐬[X, I, n].obj Ln)
    (hη : IsDerivedBaseChange η) (hη' : IsDerivedBaseChange η') :
    ∃ θ : ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj L ⟶
      𝐑𝐞𝐬[X, I, n].obj (((-⊗ᴸ-(X)[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Kn).obj Ln),
      IsDerivedBaseChange θ
  /-- The derived direct image commutes with reduction modulo `Iⁿ`. -/
  rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) (K : 𝐃(X, Λ))
    (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn) (hη : IsDerivedBaseChange η) :
    ∃ θ : R((f)_*[ModuleCat.{u + 1} Λ]).obj K ⟶
      𝐑𝐞𝐬[Y, I, n].obj (R((f)_*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Kn),
      IsDerivedBaseChange θ
  /-- The compact-support direct image commutes with reduction modulo `Iⁿ`. -/
  rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : 𝐃(X, Λ)) (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn)
    (hη : IsDerivedBaseChange η) :
    ∃ θ : (R(f)_![ModuleCat.{u + 1} Λ]).obj K ⟶
      𝐑𝐞𝐬[Y, I, n].obj ((R(f)_![ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Kn),
      IsDerivedBaseChange θ
  /-- The reduction of the projection map is the projection map of the reductions. -/
  projectionMap {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (K : 𝐃(X, Λ))
    (L : 𝐃(Y, Λ)) (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn)
    (Ln : 𝐃(Y, Λ ⧸ I ^ n)) (η' : L ⟶ 𝐑𝐞𝐬[Y, I, n].obj Ln) (hη : IsDerivedBaseChange η)
    (hη' : IsDerivedBaseChange η') :
    Nonempty (Arrow.mk ((reductionModIdeal Λ Y (I ^ n)).map (projectionMapApp Λ f K L)) ≅
      Arrow.mk (𝐑𝐞𝐬[Y, I, n].map (projectionMapApp (Λ ⧸ I ^ n) f Kn Ln)))

end Etale

namespace ProEtale

set_option hygiene false in
/-- The derived category `D(X_proét, Λ)` of pro-étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))

/-- Restriction of scalars `D(X_proét, Λ ⧸ Iⁿ) ⥤ D(X_proét, Λ)` along the quotient map. -/
local notation "𝐑𝐞𝐬[" X ", " I ", " n "]" =>
  Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (Ideal.Quotient.mk (I ^ n))

/-- The compatibility of the reduction `Λ → Λ ⧸ Iⁿ` with the basic operations of the pro-étale
derived categories (the pro-étale part of blueprint `lem-fix-operation-reduction`): every
object has a reduction (a derived base change along `Λ → Λ ⧸ Iⁿ`); the derived pullback and the
compact-support direct image of reductions are reductions of the corresponding operations; and
the reduction of the compact-support exchange map `Ex_!(c) : Lg^* Rf_!(c) ⟶ Rf'_!(c') Lg'^*`
at `K` (its image under `- ⊗ᴸ (Λ ⧸ Iⁿ)_{Y'}`) is isomorphic as an arrow to the restriction of
scalars of the exchange map over `Λ ⧸ Iⁿ` at `K_n`, which expresses that the comparisons
preserve the units and counits out of which the exchange map is built. -/
structure ReductionCompatibility (Λ : Type (u + 1)) [CommRing Λ] (I : Ideal Λ) (n : ℕ) :
    Prop where
  /-- Every object has a reduction modulo `Iⁿ`. -/
  exists_isDerivedBaseChange (X : Scheme.{u}) (K : 𝐃(X, Λ)) :
    ∃ (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn), Sheaf.IsDerivedBaseChange η
  /-- The derived pullback commutes with reduction modulo `Iⁿ`. -/
  leftDerivedUpperStar {X Y : Scheme.{u}} (f : X ⟶ Y) (L : 𝐃(Y, Λ))
    (Ln : 𝐃(Y, Λ ⧸ I ^ n)) (η : L ⟶ 𝐑𝐞𝐬[Y, I, n].obj Ln) (hη : Sheaf.IsDerivedBaseChange η) :
    ∃ θ : L((f)^*[ModuleCat.{u + 1} Λ]).obj L ⟶
      𝐑𝐞𝐬[X, I, n].obj (L((f)^*[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Ln),
      Sheaf.IsDerivedBaseChange θ
  /-- The compact-support direct image commutes with reduction modulo `Iⁿ`. -/
  rightDerivedLowerShriekOfCompactification {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : 𝐃(X, Λ)) (Kn : 𝐃(X, Λ ⧸ I ^ n))
    (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn) (hη : Sheaf.IsDerivedBaseChange η) :
    ∃ θ : (Rf_!(c)[ModuleCat.{u + 1} Λ]).obj K ⟶
      𝐑𝐞𝐬[Y, I, n].obj ((Rf_!(c)[ModuleCat.{u + 1} (Λ ⧸ I ^ n)]).obj Kn),
      Sheaf.IsDerivedBaseChange θ
  /-- The reduction of the compact-support exchange map is the exchange map of the
  reduction. -/
  exchange {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback g' f' f g) (c : Compactification f) (K : 𝐃(X, Λ))
    (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, I, n].obj Kn) (hη : Sheaf.IsDerivedBaseChange η) :
    Nonempty (Arrow.mk
        ((_root_.DerivedCategory.reductionModIdeal (Scheme.ProEt.topology Y') (I ^ n)).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
          c).app K)) ≅
      Arrow.mk (𝐑𝐞𝐬[Y', I, n].map ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) sq c).app Kn)))

end ProEtale

/-- Blueprint `lem-fix-operation-reduction`: Basic operations and coefficient reduction.

Let `ϖ` be a nonzerodivisor of `Λ` (for `Λ = 𝒪_E` a uniformizer, so that the reduction
`Λ → Λ ⧸ (ϖ)ⁿ` is `𝒪_E → A_{E,n}`). Reduction modulo `(ϖ)ⁿ` commutes with derived pullback,
derived tensor product, ordinary derived direct image and compact-support direct image, for the
étale and for the pro-étale coefficient categories, and the comparisons preserve the units,
counits and associativity maps used to construct the projection and exchange transformations:
the reductions of the projection map and of the compact-support exchange map are, as arrows,
the projection map and the exchange map of the reductions
(`AlgebraicGeometry.Etale.ReductionCompatibility`,
`AlgebraicGeometry.ProEtale.ReductionCompatibility`).

The remaining assertions of the node are formalised separately: the reduction of internal Hom
for arbitrary first variable is `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_derivedHom`
and, between finite quotients for site-perfect first
variable, `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_derivedHom_of_isSitePerfect`;
the reduction as an endofunctor of `D(X_ét, Λ)` commutes with `Lf^*`, `Rf_*` and `Rf_!`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarReductionModIdealIso`,
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarReductionModIdealMap_span_pow`,
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerShriekReductionModIdealMap_span_pow`); the
statement for admissible exceptional adjoints is their admissibility hypothesis. The
comparisons between two finite quotients `A_{E,n} → A_{E,m}` on finite-Tor domains and the
transport of the comparisons to rationalization and common-stage scalar extension are not part
of this statement. -/
theorem reductionCompatibility_span_singleton {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) :
    Etale.ReductionCompatibility.{u} Λ (Ideal.span {ϖ}) n ∧
      ProEtale.ReductionCompatibility.{u} Λ (Ideal.span {ϖ}) n :=
  sorry

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ : Type (u + 1)} [CommRing Λ] {ϖ : Λ} {X Y : Scheme.{u}}

/-- Blueprint `lem-fix-operation-reduction`: Basic operations and coefficient reduction; the
compatibility of the reduction `Λ → Λ ⧸ (ϖ)ⁿ` (for `Λ = 𝒪_E`, the reduction `𝒪_E → A_{E,n}`) with
the projection transformation.

For a nonzerodivisor `ϖ` of `Λ`, `f : X ⟶ Y` admitting a compactification, `K ∈ D(X_ét, Λ)` and
`L ∈ D(Y_ét, Λ)`, there are reductions `K_n = K ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ` and `L_n = L ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ`
(derived base changes, `AlgebraicGeometry.Etale.IsDerivedBaseChange`) such that the reduction
`ρ(PF_{f, K, L})` of the projection map, its image under `- ⊗ᴸ (Λ ⧸ (ϖ)ⁿ)_Y`, is isomorphic as an
arrow to the restriction of scalars of the projection map `PF_{f, K_n, L_n}` over `Λ ⧸ (ϖ)ⁿ`.
It is the reduction square that Step 1 of `sk-thm-sf-pf-adic` cites from
`sk-prop-sf-pf-reduction`, a consequence of
`AlgebraicGeometry.reductionCompatibility_span_singleton`. -/
theorem exists_isDerivedBaseChange_arrowIso_reductionModIdeal_projectionMap
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) (f : X ⟶ Y) [HasCompactification f]
    (K : 𝐃(X, Λ)) (L : 𝐃(Y, Λ)) :
    ∃ (Kn : 𝐃(X, Λ ⧸ Ideal.span {ϖ} ^ n))
      (η : K ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) X).obj Kn)
      (Ln : 𝐃(Y, Λ ⧸ Ideal.span {ϖ} ^ n))
      (η' : L ⟶ (derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) Y).obj Ln),
      IsDerivedBaseChange η ∧ IsDerivedBaseChange η' ∧
        Nonempty (Arrow.mk ((reductionModIdeal Λ Y (Ideal.span {ϖ} ^ n)).map
            (projectionMapApp Λ f K L)) ≅
          Arrow.mk ((derivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) Y).map
            (projectionMapApp (Λ ⧸ Ideal.span {ϖ} ^ n) f Kn Ln))) := by
  have h := (reductionCompatibility_span_singleton hϖ n).1
  obtain ⟨Kn, η, hη⟩ := h.exists_isDerivedBaseChange X K
  obtain ⟨Ln, η', hη'⟩ := h.exists_isDerivedBaseChange Y L
  exact ⟨Kn, η, Ln, η', hη, hη', h.projectionMap f K L Kn η Ln η' hη hη'⟩

end Etale

namespace ProEtale

set_option hygiene false in
/-- The derived category `D(X_proét, Λ)` of pro-étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ}
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Restriction of scalars `D(X_proét, Λ/Iⁿ) ⥤ D(X_proét, Λ)` along the quotient map. -/
local notation "𝐑𝐞𝐬[" X ", " n "]" =>
  Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (Ideal.Quotient.mk (I ^ n))

/-- Blueprint `lem-fix-operation-reduction`: Basic operations and coefficient reduction; the
compatibility of the reduction `Λ → Λ/Iⁿ` (for `Λ = 𝒪_E` and `I = 𝔪_E`, the reduction
`𝒪_E → A_{E,n}`) with the compact-support exchange transformation.

For an ideal `I` of `Λ` generated by a nonzerodivisor, a cartesian square `g' ≫ f = f' ≫ g`, a
compactification `c` of `f` and `K ∈ D(X_proét, Λ)` with a reduction `K_n = K ⊗ᴸ_Λ Λ/Iⁿ` (a
derived base change `η : K ⟶ Res K_n`, `CategoryTheory.Sheaf.IsDerivedBaseChange`), the
reduction modulo `Iⁿ` of the compact-support exchange map `Ex_!(c) : Lg^* Rf_!(c) K ⟶
Rf'_!(c') Lg'^* K` over `Λ` is isomorphic, as an arrow, to the restriction of scalars of the
exchange map `Ex_!(c)` over `Λ/Iⁿ` at `K_n`. It is a consequence of
`AlgebraicGeometry.reductionCompatibility_span_singleton`. -/
theorem nonempty_arrowIso_reductionModIdeal_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (hI : ∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})
    (n : ℕ) (sq : IsPullback g' f' f g) (c : Compactification f) (K : 𝐃(X, Λ))
    (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, n].obj Kn) (hη : Sheaf.IsDerivedBaseChange η) :
    Nonempty (Arrow.mk
        ((_root_.DerivedCategory.reductionModIdeal (Scheme.ProEt.topology Y') (I ^ n)).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
          c).app K)) ≅
      Arrow.mk (𝐑𝐞𝐬[Y', n].map ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) sq c).app Kn))) := by
  obtain ⟨ϖ, hϖ, rfl⟩ := hI
  exact (reductionCompatibility_span_singleton hϖ n).2.exchange sq c K Kn η hη

end ProEtale

end AlgebraicGeometry
