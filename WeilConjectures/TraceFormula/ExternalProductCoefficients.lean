/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.KunnethVerdier

/-!

# External products and Verdier duals with general `ℓ`-adic coefficients

The external product `M ⊠ N = Lp_X^* M ⊗ Lp_Y^* N` (`ProEtale.CondensedRing.externalProduct`) and
the Verdier dual `𝔻_X K = RHom(K, Ra^! ℚ̄_ℓ)` (`ProEtale.CondensedRing.verdierDual`) of the trace
formula are defined with coefficients `ℚ̄_ℓ`. The passage from integral to `ℚ̄_ℓ`-coefficients
(blueprint `sk-lem-tf-curve-restriction-zero`, through the integral models of
`sk-lem-tf-rational-model`) needs them for the other `ℓ`-adic coefficient rings `Λ` as well, in
particular for `𝒪_E`. This file defines them for every `ℓ`-adic coefficient ring `Λ`:

* `ProEtale.CondensedRing.boundedConstructibleExternalProduct Λ ℓ M N = Lp_X^* M ⊗ Lp_Y^* N`;
* `ProEtale.CondensedRing.boundedConstructibleDualizingComplex Λ ℓ a = Ra^! Λ`;
* `ProEtale.CondensedRing.boundedConstructibleVerdierDual Λ ℓ a K = RHom(K, Ra^! Λ)`,

and checks that for `Λ = ℚ̲̄_ℓ` they are the constructions of the trace formula
(`ProEtale.CondensedRing.externalProduct_eq_boundedConstructibleExternalProduct`,
`ProEtale.CondensedRing.verdierDual_eq_boundedConstructibleVerdierDual`).

As for `ProEtale.CondensedRing.boundedConstructibleUpperShriek`, the dualizing complex of a
general `Λ` assumes that `Rg_*` along the proper part `g` of the compactification is a left
adjoint. For `Λ = 𝒪_E`, `E` and `ℚ̲̄_ℓ` this is an instance
(`ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj` and its
siblings), so it need not be supplied there.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] [IsEllAdicFinitenessCoefficient ℓ Λ] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section ExternalProduct

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The *external product* `M ⊠ N = Lp_X^* M ⊗ Lp_Y^* N` on `X ⨯ Y` of bounded constructible
complexes over an `ℓ`-adic coefficient ring `Λ` (blueprint `def-trf-external-product`), with the
projections `p_X = prod.fst` and `p_Y = prod.snd`. -/
noncomputable def boundedConstructibleExternalProduct (M : Dᵇc(X.left)⟦Λ⟧) (N : Dᵇc(Y.left)⟦Λ⟧) :
    Dᵇc((X ⨯ Y).left)⟦Λ⟧ :=
  (boundedConstructibleUpperStar Λ ℓ (prod.fst : X ⨯ Y ⟶ X)).obj M ⊗
    (boundedConstructibleUpperStar Λ ℓ (prod.snd : X ⨯ Y ⟶ Y)).obj N

/-- For `Λ = ℚ̲̄_ℓ`, the external product is the one of the trace formula. -/
lemma externalProduct_eq_boundedConstructibleExternalProduct
    (M : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    externalProduct ℓ M N = boundedConstructibleExternalProduct _ ℓ M N :=
  rfl

end ExternalProduct

section Dualizing

variable {X S : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType S.hom]
  [QuasiCompact S.hom] [IsSeparated S.hom]
  (a : X ⟶ S)
  [(boundedConstructibleLowerStar Λ ℓ (compactificationOverField a).overG).IsLeftAdjoint]

/-- The *dualizing complex* `ω_X = Ra^! Λ_S` relative to `a : X ⟶ S`, with coefficients in an
`ℓ`-adic coefficient ring `Λ`. -/
noncomputable def boundedConstructibleDualizingComplex : Dᵇc(X.left)⟦Λ⟧ :=
  (boundedConstructibleUpperShriek Λ ℓ a).obj (𝟙_ _)

/-- The *Verdier dual* `𝔻_X K = RHom(K, ω_X)` relative to `a : X ⟶ S`, with coefficients in an
`ℓ`-adic coefficient ring `Λ`. -/
noncomputable def boundedConstructibleVerdierDual (K : Dᵇc(X.left)⟦Λ⟧) : Dᵇc(X.left)⟦Λ⟧ :=
  (ihom K).obj (boundedConstructibleDualizingComplex Λ ℓ a)

/-- For `Λ = ℚ̲̄_ℓ`, the dualizing complex is the one of Verdier duality. -/
lemma dualizingComplex_eq_boundedConstructibleDualizingComplex :
    dualizingComplex ℓ a = boundedConstructibleDualizingComplex _ ℓ a :=
  rfl

/-- For `Λ = ℚ̲̄_ℓ`, the Verdier dual is the one of Verdier duality. -/
lemma verdierDual_eq_boundedConstructibleVerdierDual
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    verdierDual ℓ a K = boundedConstructibleVerdierDual _ ℓ a K :=
  rfl

end Dualizing

end AlgebraicGeometry.ProEtale.CondensedRing
