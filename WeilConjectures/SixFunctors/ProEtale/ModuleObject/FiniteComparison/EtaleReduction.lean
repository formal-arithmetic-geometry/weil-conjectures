/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.IntegralReductionConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Derived

/-!

# Reduction modulo `ℓⁿ` read on the small étale site

For a finite extension `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` and `n : ℕ`, the coefficient change
`𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` sends a bounded constructible `𝒪_E`-complex `K` on the pro-étale site of `X`
to `K ⊗ᴸ 𝒪_E ⧸ ℓⁿ`. For the finite ring `𝒪_E ⧸ ℓⁿ` the blueprint reads the target on the small
étale site (`sk-def-sf-categories`: "for finite `Λ = A_{E,n}`, and only there, the same
definitions may be read on the small étale site; the comparison `ν_T^*` identifies them with the
pro-étale categories"). This file defines this étale reading of the reduction,
```
Dᵇc(X)⟦𝒪_E⟧ ⥤ D(X_ét, 𝒪_E ⧸ ℓⁿ),   K ↦ Rν_* (K ⊗ᴸ 𝒪_E ⧸ ℓⁿ),
```
(`AlgebraicGeometry.ProEtale.CondensedRing.etaleReduction`): the reduction of condensed
coefficients (`AlgebraicGeometry.ProEtale.boundedConstructibleIntegersModPowReduction`), the
identification of condensed `𝒪_E ⧸ ℓⁿ`-module objects with pro-étale sheaves of modules
(`AlgebraicGeometry.ProEtale.finiteCoefficientDerivedEquivalence`) and the comparison
`Rν_* : D(X_proét) ⥤ D(X_ét)`.

It states the coefficient comparisons of blueprint `sk-prop-scalar-six` for the coefficient map
`𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale site, that the trace formula uses to pass from integral to
finite coefficients (blueprint `sk-lem-tf-curve-restriction-zero`, last step). They are
compatibilities required from section `sec-six-functors-basics`, each exactly one blueprint node:

* `nonempty_etaleReductionUpperStarIso`: pullback (`det-prop-scalar-six-pullback`, (1));
* compactly supported direct image and exceptional inverse image, for closed immersions
  (`det-prop-scalar-six-exceptional`, with the comparison `γ^!` of
  `det-prop-scalar-six-compact-support`): proved as `exists_etaleReductionLowerShriekIso` in
  the file `FiniteComparison/EtaleReductionLowerShriekMate.lean`;
* `nonempty_etaleReductionTensorIso`: tensor product (`det-prop-scalar-six-tensor-hom`, (1));
* `boundedConstructibleFiniteTor_etaleReduction`: preservation of `Dctf`
  (`det-prop-scalar-six-ctf`, (3)).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

/-- The finite coefficient ring `𝒪_E ⧸ ℓⁿ`, lifted to the universe of étale sheaves of
modules. -/
abbrev integersModPowCoeff : Type (u + 1) :=
  ULift.{u + 1} (PadicAlgCl.integersModPow ℓ E n)

/-- **The reduction modulo `ℓⁿ`, read on the small étale site**: `K ↦ Rν_* (K ⊗ᴸ 𝒪_E ⧸ ℓⁿ)`,
from bounded constructible `𝒪_E`-complexes on `X_proét` to the derived category of étale sheaves
of `𝒪_E ⧸ ℓⁿ`-modules on `X`. -/
noncomputable def etaleReduction (Y : Over (Spec (.of k))) [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] [IsSeparated Y.hom] :
    Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤
      DerivedCategory (Sheaf Y.left.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))) :=
  boundedConstructibleIntegersModPowReduction Y.left ℓ E n ⋙ (boundedConstructible _).ι ⋙
    (finiteCoefficientDerivedEquivalence Y.left (PadicAlgCl.integersModPow ℓ E n)).functor ⋙
      R(ν_*(Y.left)[ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)])

/-! ### The coefficient comparisons for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` -/

variable {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- Compatibility required from `sec-six-functors-basics` (to be proved there): blueprint
`det-prop-scalar-six-pullback`, (1), for the coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the
étale site (`sk-def-sf-categories`). **Reduction modulo `ℓⁿ` commutes with pullback**:
`(f^* K)_{𝒪_E ⧸ ℓⁿ} ≅ f^* (K_{𝒪_E ⧸ ℓⁿ})`. -/
theorem nonempty_etaleReductionUpperStarIso (f : Z ⟶ Y) :
    Nonempty (boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f ⋙
        etaleReduction ℓ E n Z ≅
      etaleReduction ℓ E n Y ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left)) :=
  sorry

/-- Reduction modulo `ℓⁿ` commutes with pullback (`nonempty_etaleReductionUpperStarIso`). -/
noncomputable def etaleReductionUpperStarIso (f : Z ⟶ Y) :
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f ⋙
        etaleReduction ℓ E n Z ≅
      etaleReduction ℓ E n Y ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) f.left) :=
  (nonempty_etaleReductionUpperStarIso ℓ E n f).some

/-- Compatibility required from `sec-six-functors-basics` (to be proved there): blueprint
`det-prop-scalar-six-tensor-hom`, (1), for the coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the
étale site (`sk-def-sf-categories`). **Reduction modulo `ℓⁿ` commutes with the tensor
product**: `(K ⊗ᴸ M)_{𝒪_E ⧸ ℓⁿ} ≅ K_{𝒪_E ⧸ ℓⁿ} ⊗ᴸ M_{𝒪_E ⧸ ℓⁿ}`. -/
theorem nonempty_etaleReductionTensorIso (K M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    Nonempty ((etaleReduction ℓ E n Y).obj (K ⊗ M) ≅
      ((Etale.derivedTensor (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Y.left).obj
        ((etaleReduction ℓ E n Y).obj K)).obj ((etaleReduction ℓ E n Y).obj M)) :=
  sorry

/-- Compatibility required from `sec-six-functors-basics` (to be proved there): blueprint
`det-prop-scalar-six-ctf`, (3), for the coefficient map `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ`, read on the étale
site (`sk-def-sf-categories`). **Reduction modulo `ℓⁿ` preserves `Dctf`**: for a bounded
constructible `𝒪_E`-complex `K` (for which `Dᵇc = Dctf`, `lem-integral-ctf-equals-bc`), the
reduction `K_{𝒪_E ⧸ ℓⁿ}` is bounded constructible of finite Tor amplitude. -/
theorem boundedConstructibleFiniteTor_etaleReduction
    (K : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    Etale.DerivedCategory.boundedConstructibleFiniteTor (integersModPowCoeff.{u} ℓ E n) Y.left
      ((etaleReduction ℓ E n Y).obj K) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
