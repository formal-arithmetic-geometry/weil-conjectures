/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormula
public import WeilConjectures.PoincareDuality.VerdierBiduality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleMonoidalComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ShriekComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual

/-!

# Verdier duality on bounded constructible complexes on the pro-étale site

Let `k` be a field of characteristic `≠ ℓ` and `f : X ⟶ Y` a morphism of separated `k`-schemes
of finite type, a morphism of `Over (Spec (.of k))`. This file specializes the abstract
constructions of `WeilConjectures.PoincareDuality.Abstract` to the six functors on the bounded
constructible derived categories `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` with coefficients in the condensed ring `ℚ̲̄_ℓ`
(`Profinite.padicAlgClRingObj ℓ`): the adjunctions `Lf^* ⊣ Rf_*` and `Rf_! ⊣ Rf^!`, the internal
hom `RHom` and the derived exceptional projection morphism `PF^!` of
`WeilConjectures.PoincareDuality.ProjectionFormula`.

The exceptional inverse image `Rf^!` only exists on `Dᵇc`
(`ProEtale.CondensedRing.boundedConstructibleUpperShriek`), and requires `Rg_*` along the proper
half of the chosen compactification to be a left adjoint. This is why the coefficients are
`ℚ̲̄_ℓ` rather than a general condensed ring: for `ℚ̲̄_ℓ` it is the instance
`ProEtale.CondensedRing.isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj`. The
monoidal closed structure on `Dᵇc` is that of
`ProEtale.CondensedRing.isMonoidal_boundedConstructible` and
`ProEtale.CondensedRing.isMonoidalClosed_boundedConstructible`, and its braiding, used in the
double-dual morphism, is the Koszul braiding `ProEtale.CondensedRing.boundedConstructibleBraiding`,
made a local instance.

## Main definitions

- `ProEtale.CondensedRing.verdierExchange`: the Verdier exchange morphism
  `Φ_{f,K,L} : Rf_* RHom(K, Rf^! L) ⟶ RHom(Rf_! K, L)`.
- `ProEtale.CondensedRing.dualizingComplex`: the absolute dualizing complex
  `ω_X = Ra_X^! ℚ̄_ℓ` of `X`, for its structure morphism `a_X : X ⟶ Spec k`, and
  `ProEtale.CondensedRing.verdierDual`: the Verdier dual `𝔻_X K = RHom(K, ω_X)`.
- `ProEtale.CondensedRing.verdierBiduality`: the double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K`.
- `ProEtale.CondensedRing.upperShriekDualizingComplexIso`: for `f : X ⟶ Y`, the identification
  `γ : Rf^! ω_Y ≅ ω_X`, from `f ≫ a_Y = a_X` and the composition isomorphism
  `R(f ≫ a_Y)^! ≅ Ra_Y^! ⋙ Rf^!`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicAlgCl`) at the unit.
- `ProEtale.CondensedRing.absoluteVerdierExchange` and
  `ProEtale.CondensedRing.dualVerdierExchange`: the absolute exchange
  `Rf_* 𝔻_X K ⟶ 𝔻_Y Rf_! K` and the opposite exchange `Θ_K : Rf_! 𝔻_X K ⟶ 𝔻_Y Rf_* K`, built
  with `γ`.

The isomorphism `γ` is the conjugate of the composition isomorphism of lower shrieks
`R(f ≫ a_Y)_! ≅ Rf_! ⋙ Ra_Y_!`
(`ProEtale.CondensedRing.boundedConstructibleLowerShriekComp_padicAlgCl`).

## Main results

- `ProEtale.CondensedRing.isIso_verdierExchange`: **Verdier duality**, the exchange morphism
  is an isomorphism, deduced from the derived projection formula
  (`isIso_boundedConstructibleExceptionalProjectionMorphism`) by the Yoneda argument.
- `ProEtale.CondensedRing.isIso_verdierBiduality_of_isDualizable` and
  `ProEtale.CondensedRing.isIso_verdierBiduality_of_isCompl`: the lisse and open–closed steps of
  biduality.
- `ProEtale.CondensedRing.dualizingComplexIsoUpperStar`: `Lj^* ω_X ≅ ω_U` for an open immersion
  `j`, and `ProEtale.CondensedRing.isIso_map_verdierBiduality_iff_of_isOpenImmersion`:
  `Lj^* δ_K` is an isomorphism iff `δ_{Lj^* K}` is.

**Constructible biduality**, `δ_K` an isomorphism for every bounded constructible `K`
(`ProEtale.CondensedRing.isIso_verdierBiduality`), is proved in
`WeilConjectures.PoincareDuality.Biduality.Constructible`, by reduction to finite coefficients.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The Verdier exchange morphism -/

section Exchange

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The **Verdier exchange morphism** `Φ_{f,K,L} : Rf_* RHom(K, Rf^! L) ⟶ RHom(Rf_! K, L)` on
bounded constructible complexes (`ℚ̄_ℓ`-coefficient): the transpose of the pairing
```
Rf_! K ⊗ᴸ Rf_* RHom(K, Rf^! L) ⟶ Rf_! (K ⊗ᴸ Lf^* Rf_* RHom(K, Rf^! L))
  ⟶ Rf_! (K ⊗ᴸ RHom(K, Rf^! L)) ⟶ Rf_! Rf^! L ⟶ L,
```
see `CategoryTheory.Verdier.exchange`. -/
noncomputable def verdierExchange
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar ℓ f).obj
        ((ihom K).obj ((boundedConstructibleUpperShriek ℓ f).obj L)) ⟶
      (ihom ((boundedConstructibleLowerShriek ℓ f).obj K)).obj L :=
  Verdier.exchange (boundedConstructibleUpperStarLowerStarAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleExceptionalProjection ℓ f) K L

/-- **Verdier duality** (`ℚ̄_ℓ`-coefficient): the exchange morphism `Φ_{f,K,L}` is an isomorphism,
by the derived projection formula and the Yoneda lemma. -/
theorem isIso_verdierExchange (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (L : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso (verdierExchange ℓ f K L) := by
  have := isIso_boundedConstructibleExceptionalProjection_app_app ℓ f K
  exact Verdier.isIso_exchange_of_isIso _ _ _ K L

end Exchange

/-! ### The absolute dualizing complex and the double-dual morphism -/

section Dualizing

instance : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 _))

instance : QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 _))

instance : IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 _))

variable (X : Over (Spec (.of k)))
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The **dualizing complex** `ω_X = Ra_X^! ℚ̄_ℓ` of a separated `k`-scheme of finite type `X`, for
its structure morphism `a_X : X ⟶ Spec k`, the morphism `Over.mkIdTerminal.from X` to the
terminal object `Over.mk (𝟙 (Spec k))` of `Over (Spec k)`. -/
noncomputable def dualizingComplex : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (boundedConstructibleUpperShriek ℓ (Over.mkIdTerminal.from X)).obj (𝟙_ _)

variable {X}

/-- The **Verdier dual** `𝔻_X K = RHom(K, ω_X)`. -/
noncomputable def verdierDual (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  (ihom K).obj (dualizingComplex ℓ X)

/-- The **double-dual morphism** `δ_K : K ⟶ 𝔻_X 𝔻_X K`: the transpose of the evaluation pairing
`𝔻_X K ⊗ᴸ K ⟶ K ⊗ᴸ 𝔻_X K ⟶ ω_X`. -/
noncomputable def verdierBiduality (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    K ⟶ verdierDual ℓ (verdierDual ℓ K) :=
  Verdier.bidualityMap (dualizingComplex ℓ X) K

end Dualizing

/-! ### The absolute and opposite exchange morphisms -/

section Absolute

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The identification `γ : Rf^! ω_Y ≅ ω_X` of the dualizing complexes (`ℚ̄_ℓ`-coefficient): the
composition isomorphism `R(f ≫ a_Y)^! ≅ Ra_Y^! ⋙ Rf^!` of
`ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicAlgCl` at the unit, followed by
the equality `f ≫ a_Y = a_X` of morphisms to the terminal object. -/
noncomputable def upperShriekDualizingComplexIso :
    (boundedConstructibleUpperShriek ℓ f).obj (dualizingComplex ℓ Y) ≅ dualizingComplex ℓ X :=
  ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f (Over.mkIdTerminal.from Y)).app
      (𝟙_ _)).symm ≪≫
    eqToIso (by rw [Over.mkIdTerminal.comp_from]; rfl)

end Absolute

/-! ### Restriction of the dualizing complex to an open subscheme -/

section OpenImmersion

variable {U X : Over (Spec (.of k))}
  [LocallyOfFiniteType U.hom] [QuasiCompact U.hom] [IsSeparated U.hom] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]
  (j : U ⟶ X) [IsOpenImmersion j.left]

/-- For an open immersion `j`, the lower shriek `Rj_!` on bounded constructible `ℚ̄_ℓ`-complexes
is the extension by zero `j_!`: the independence of the compactification, comparing the chosen
compactification of `j` with the compactification `X ⟶ X` by the identity, along which the
derived pushforward is the identity. -/
noncomputable def boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek :
    boundedConstructibleLowerShriek ℓ j ≅
      boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  boundedConstructibleLowerShriekOfCompactificationIso_padicAlgCl ℓ (compactificationOverField j)
      (Compactification.ofIsOpenImmersion j.left) ≪≫
    (Iso.refl _ : _ ≅ boundedConstructibleOpenImmersionLowerShriek _ ℓ j ⋙
      boundedConstructibleLowerStar ℓ (𝟙 X)) ≪≫
    Functor.isoWhiskerLeft _ (boundedConstructibleLowerStarId ℓ X) ≪≫ Functor.rightUnitor _

/-- For an open immersion `j`, the exceptional inverse image `Rj^!` on bounded constructible
`ℚ̄_ℓ`-complexes is the pullback `Lj^*`: the conjugate of
`boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek`. -/
noncomputable def boundedConstructibleUpperShriekIsoUpperStar :
    boundedConstructibleUpperShriek ℓ j ≅
      boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j :=
  conjugateIsoEquiv (boundedConstructibleUpperShriekAdjunction ℓ j)
    (boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ ℓ j)
    (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek ℓ j).symm

/-- **The dualizing complex restricts to open subschemes**: for an open immersion `j : U ⟶ X`,
the dualizing complex of `U` is the restriction `Lj^* ω_X` of the dualizing complex of `X`. -/
noncomputable def dualizingComplexIsoUpperStar :
    dualizingComplex ℓ U ≅
      (boundedConstructibleUpperStar _ ℓ j).obj (dualizingComplex ℓ X) :=
  (upperShriekDualizingComplexIso ℓ j).symm ≪≫
    (boundedConstructibleUpperShriekIsoUpperStar ℓ j).app _

end OpenImmersion

end AlgebraicGeometry.ProEtale.CondensedRing
