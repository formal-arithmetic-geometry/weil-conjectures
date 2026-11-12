/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.Biduality.Constructible

/-!
# Constructible Verdier biduality with coefficients a finite extension `E` of `ℚ_ℓ`

Let `E ⊆ ℚ̄_ℓ` be a finite extension of `ℚ_ℓ` with ring of integers `𝒪_E`, `k` a field of
characteristic `p ≠ ℓ` and `X` a separated `k`-scheme of finite type. This file defines the
Verdier formalism at the rational stage `Λ = E`, and proves biduality there (blueprint
`theorem-verdier-biduality--3`), from biduality for `𝒪_E`
(`ProEtale.CondensedRing.PadicIntegersRingObj.isIso_verdierBiduality`) by integral models:
the extension of scalars `T_X = E ⊗ᴸ_{𝒪_E} - : Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(X)⟦E⟧` is a localization,
hence essentially surjective, it commutes with internal homs and with `Ra_X^!`, so it carries
`δ_{K₀}` to `δ_{T_X K₀}`.

## Main definitions and results

- `ProEtale.CondensedRing.ContinuousMapRingObj.dualizingComplex`: `ω_X = Ra_X^! E`;
- `ProEtale.CondensedRing.ContinuousMapRingObj.verdierBiduality`: `δ_K : K ⟶ 𝔻_X 𝔻_X K`;
- `ProEtale.CondensedRing.ContinuousMapRingObj.isIso_verdierBiduality`: `δ_K` is an isomorphism
  for every bounded constructible `E`-complex `K`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.ContinuousMapRingObj

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : PadicAlgCl.FiniteIntermediateField ℓ)

variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

attribute [local instance] DerivedCategory.braidedCategory' in
/-- The Koszul braiding of the derived tensor product on `Dᵇc(X)⟦E̲⟧`: the restriction
(`ObjectProperty.fullBraidedSubcategory`) of the braiding `DerivedCategory.braidedCategory'` of
`D(Mod_{E_X})`. As `ProEtale.CondensedRing.boundedConstructibleBraiding`, it is not an
instance. -/
@[instance_reducible]
noncomputable def boundedConstructibleBraiding :
    BraidedCategory (Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧) :=
  ObjectProperty.fullBraidedSubcategory _

attribute [local instance] boundedConstructibleBraiding

/-- The **dualizing complex** `ω_X = Ra_X^! E` (`E`-coefficient), for the structure morphism
`a_X : X ⟶ Spec k`, the morphism `Over.mkIdTerminal.from X` to the terminal object. -/
noncomputable def dualizingComplex : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧ :=
  (boundedConstructibleUpperShriek ℓ E (Over.mkIdTerminal.from X)).obj (𝟙_ _)

variable {X}

/-- The **Verdier dual** `𝔻_X K = RHom(K, ω_X)` (`E`-coefficient). -/
noncomputable def verdierDual (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧) :
    Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧ :=
  (ihom K).obj (dualizingComplex ℓ E X)

/-- The **double-dual morphism** `δ_K : K ⟶ 𝔻_X 𝔻_X K` (`E`-coefficient): the transpose of the
evaluation pairing `𝔻_X K ⊗ᴸ K ⟶ K ⊗ᴸ 𝔻_X K ⟶ ω_X`. -/
noncomputable def verdierBiduality (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧) :
    K ⟶ verdierDual ℓ E (verdierDual ℓ E K) :=
  Verdier.bidualityMap (dualizingComplex ℓ E X) K

variable (X) in
/-- The extension of scalars of the integral dualizing complex is the rational one:
`T_X ω_{X, 𝒪_E} ≅ ω_{X, E}`, from the coefficient comparison for `Ra_X^!` along `𝒪_E ⟶ E`
(`boundedConstructibleUpperShriekExtendScalarsIso`) at the unit and the unit comparison of the
monoidal functor `T_X`. -/
noncomputable def integersDualizingComplexIso :
    (boundedConstructibleExtendScalars X.left ℓ E).obj
        (PadicIntegersRingObj.dualizingComplex ℓ E.1 X) ≅
      dualizingComplex ℓ E X :=
  (boundedConstructibleUpperShriekExtendScalarsIso ℓ E (Over.mkIdTerminal.from X)).app (𝟙_ _) ≪≫
    (boundedConstructibleUpperShriek ℓ E (Over.mkIdTerminal.from X)).mapIso
      (Functor.Monoidal.εIso (boundedConstructibleExtendScalars _ ℓ E)).symm

attribute [local instance] PadicIntegersRingObj.boundedConstructibleBraiding

/-- **Biduality along `𝒪_E ⟶ E`**: if the double-dual morphism `δ_{K₀}` of a bounded
constructible `𝒪_E`-complex is an isomorphism, so is the double-dual morphism of its extension
of scalars `E ⊗ᴸ_{𝒪_E} K₀`. -/
theorem isIso_verdierBiduality_extendScalars_obj
    (K₀ : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E.1⟧)
    (hK₀ : IsIso (PadicIntegersRingObj.verdierBiduality ℓ E.1 K₀)) :
    IsIso (verdierBiduality ℓ E ((boundedConstructibleExtendScalars X.left ℓ E).obj K₀)) := by
  let := boundedConstructibleExtendScalarsLaxBraided ℓ E X
  have hT := isIso_ihomComparison_boundedConstructibleExtendScalars ℓ E (X := X)
  have h₁ := (NatTrans.isIso_iff_isIso_app _).1 (hT K₀)
    (PadicIntegersRingObj.dualizingComplex ℓ E.1 X)
  have h₂ := (NatTrans.isIso_iff_isIso_app _).1
    (hT ((ihom K₀).obj (PadicIntegersRingObj.dualizingComplex ℓ E.1 X)))
    (PadicIntegersRingObj.dualizingComplex ℓ E.1 X)
  have : IsIso (toIhomIhom (PadicIntegersRingObj.dualizingComplex ℓ E.1 X) K₀) := hK₀
  have : IsIso (dualComparison (boundedConstructibleExtendScalars X.left ℓ E)
      (integersDualizingComplexIso ℓ E X).hom K₀) :=
    IsIso.comp_isIso
  have : IsIso (dualComparison (boundedConstructibleExtendScalars X.left ℓ E)
      (integersDualizingComplexIso ℓ E X).hom
      ((ihom K₀).obj (PadicIntegersRingObj.dualizingComplex ℓ E.1 X))) :=
    IsIso.comp_isIso
  exact (isIso_map_toIhomIhom_iff (boundedConstructibleExtendScalars X.left ℓ E)
    (integersDualizingComplexIso ℓ E X).hom K₀).1 inferInstance

/-- Blueprint `theorem-verdier-biduality--3`: **constructible Verdier biduality with coefficients
a finite extension `E` of `ℚ_ℓ`**. For every bounded constructible `E`-complex `K` on `X`, with
`ω_X = Ra_X^! E` and `𝔻_X = RHom(-, ω_X)`, the double-dual morphism `δ_K : K ⟶ 𝔻_X 𝔻_X K` is an
isomorphism. `K` has an integral model `K ≅ E ⊗ᴸ_{𝒪_E} K₀`
(`ProEtale.exists_boundedConstructibleExtendScalars_obj_iso`), and `δ_{K₀}` is an isomorphism
(`ProEtale.CondensedRing.PadicIntegersRingObj.isIso_verdierBiduality`). -/
theorem isIso_verdierBiduality (K : Dᵇc(X.left)⟦Profinite.continuousMapRingObj E.1⟧) :
    IsIso (verdierBiduality ℓ E K) := by
  have := noetherianSpace_left_of_over X
  obtain ⟨K₀, ⟨e⟩⟩ := exists_boundedConstructibleExtendScalars_obj_iso X.left ℓ E K
  have := isIso_verdierBiduality_extendScalars_obj ℓ E K₀
    (PadicIntegersRingObj.isIso_verdierBiduality ℓ E K₀)
  exact (Verdier.isIso_bidualityMap_iff_of_iso (dualizingComplex ℓ E X) e).1 this

end AlgebraicGeometry.ProEtale.CondensedRing.ContinuousMapRingObj
