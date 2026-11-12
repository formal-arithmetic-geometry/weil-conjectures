/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleIsIso
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicIntegralModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionConservative

/-!
# Isomorphisms reduce to finite coefficients

For each coefficient ring `Λ` let `θ_Λ : F_Λ ⟶ G_Λ` be a natural transformation of functors
`D^b_ctf(X, Λ) ⥤ D^b_ctf(Y, Λ)`, and assume that the coefficient changes `Λ ⟶ Λ'` commute with
`F` and `G` (commutation squares `ιF : F_Λ ⋙ T_Y ≅ T_X ⋙ F_Λ'`, `ιG`) compatibly with `θ`
(`CategoryTheory.NatTrans.SquareCompatible`). Then `θ_Λ` is an isomorphism as soon as the
`θ_A` are, for finite coefficient rings `A` (blueprint
`proposition-isomorphisms-reduce-finite-coefficients`):

* `𝒪_E` from `𝒪_E ⧸ ℓⁿ`, `n ≠ 0`: the reduction modulo `ℓⁿ` reflects isomorphisms (derived
  Nakayama), read on the small étale site
  (`AlgebraicGeometry.ProEtale.CondensedRing.isIso_app_of_squareCompatible_etaleReduction`) or
  on the pro-étale site
  (`AlgebraicGeometry.ProEtale.isIso_app_of_squareCompatible_integersModPowReduction`);
* `E` from `𝒪_E`: every bounded constructible `E`-complex has an integral model
  (`AlgebraicGeometry.ProEtale.isIso_app_of_squareCompatible_extendScalars`);
* `ℚ̄_ℓ` from the finite subextensions `E`: every bounded constructible `ℚ̄_ℓ`-complex descends
  to some `E`
  (`AlgebraicGeometry.ProEtale.isIso_app_of_squareCompatible_constructibleToPadicAlgCl`).

The compatibility hypothesis holds for transformations built from the six operations, their
units and counits and base change maps: compatibility is stable under composition, inversion and
whiskering (`WeilConjectures.CategoryTheory.Adjunction.SquareCompatible`), and holds for units
and counits of adjunctions along mate squares
(`WeilConjectures.CategoryTheory.Adjunction.SquareCompatibleMate`).
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

open scoped CondensedRing

section Integral

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {n : ℕ}
  {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]

/-- Blueprint `proposition-isomorphisms-reduce-finite-coefficients--2` (integral coefficients,
pro-étale reading of the finite level): let `θ : F ⟶ G` be a transformation of functors
`Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(Y)⟦𝒪_E⟧` compatible, along the reductions modulo `ℓⁿ`, `n ≠ 0`, with a
transformation `θ' : F' ⟶ G'` of functors `Dᵇc(X)⟦𝒪_E ⧸ ℓⁿ⟧ ⥤ Dᵇc(Y)⟦𝒪_E ⧸ ℓⁿ⟧`. If `θ'` is an
isomorphism at the reductions of bounded constructible `𝒪_E`-complexes, then `θ` is an
isomorphism (derived Nakayama). -/
theorem isIso_app_of_squareCompatible_integersModPowReduction (hn : n ≠ 0)
    {F G : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤ Dᵇc(Y)⟦Profinite.padicIntegersRingObj ℓ E⟧}
    {F' G' : Dᵇc(X)⟦Profinite.integersModPowRingObj ℓ E n⟧ ⥤
      Dᵇc(Y)⟦Profinite.integersModPowRingObj ℓ E n⟧} {θ : F ⟶ G} {θ' : F' ⟶ G'}
    {ιF : F ⋙ boundedConstructibleIntegersModPowReduction Y ℓ E n ≅
      boundedConstructibleIntegersModPowReduction X ℓ E n ⋙ F'}
    {ιG : G ⋙ boundedConstructibleIntegersModPowReduction Y ℓ E n ≅
      boundedConstructibleIntegersModPowReduction X ℓ E n ⋙ G'}
    (h : NatTrans.SquareCompatible ιF ιG θ θ')
    (hθ' : ∀ K, IsIso (θ'.app ((boundedConstructibleIntegersModPowReduction X ℓ E n).obj K)))
    (K : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E⟧) : IsIso (θ.app K) :=
  have := h.isIso_map_app K
  isIso_of_isIso_boundedConstructibleIntegersModPowReduction_map ℓ E Y
    (fun _ hC ↦ isZero_of_isIso_pow_zsmul_id Y ℓ E hn hC) (θ.app K) this

end Integral

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] (E : Type) [Field E]
  [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] {n : ℕ}
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- Blueprint `proposition-isomorphisms-reduce-finite-coefficients--2` (integral coefficients):
let `θ : F ⟶ G` be a transformation of functors `Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(Y)⟦𝒪_E⟧` compatible, along the
reductions modulo `ℓⁿ` read on the small étale site (`etaleReduction`), `n ≠ 0`, with a
transformation `θ' : F' ⟶ G'` of functors `D(X_ét, 𝒪_E ⧸ ℓⁿ) ⥤ D(Y_ét, 𝒪_E ⧸ ℓⁿ)` for the finite
ring `𝒪_E ⧸ ℓⁿ`. If `θ'` is an isomorphism at the reductions of bounded constructible
`𝒪_E`-complexes, then `θ` is an isomorphism (derived Nakayama,
`isIso_of_isIso_etaleReduction_map`). -/
theorem isIso_app_of_squareCompatible_etaleReduction (hn : n ≠ 0)
    {F G : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧ ⥤
      Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧}
    {F' G' : DerivedCategory (Sheaf X.left.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n))) ⥤
      DerivedCategory (Sheaf Y.left.smallEtaleTopology
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)))}
    {θ : F ⟶ G} {θ' : F' ⟶ G'}
    {ιF : F ⋙ etaleReduction ℓ E n Y ≅ etaleReduction ℓ E n X ⋙ F'}
    {ιG : G ⋙ etaleReduction ℓ E n Y ≅ etaleReduction ℓ E n X ⋙ G'}
    (h : NatTrans.SquareCompatible ιF ιG θ θ')
    (hθ' : ∀ K, IsIso (θ'.app ((etaleReduction ℓ E n X).obj K)))
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) : IsIso (θ.app K) :=
  have := h.isIso_map_app K
  isIso_of_isIso_etaleReduction_map ℓ E hn (θ.app K) this

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl

open scoped CondensedRing

variable {X Y : Scheme.{u}} (ℓ : ℕ) [Fact ℓ.Prime] [TopologicalSpace.NoetherianSpace X]

/-- Blueprint `proposition-isomorphisms-reduce-finite-coefficients--3` (finite extensions of
`ℚ_ℓ`): let `θ : F ⟶ G` be a transformation of functors `Dᵇc(X)⟦E⟧ ⥤ Dᵇc(Y)⟦E⟧` compatible,
along the extensions of scalars `E ⊗ᴸ_{𝒪_E} -`, with a transformation `θ₀ : F₀ ⟶ G₀` of functors
`Dᵇc(X)⟦𝒪_E⟧ ⥤ Dᵇc(Y)⟦𝒪_E⟧`. If `θ₀` is an isomorphism, so is `θ`: every bounded constructible
`E`-complex has an integral model (`exists_boundedConstructibleExtendScalars_obj_iso`). -/
theorem isIso_app_of_squareCompatible_extendScalars (E : FiniteIntermediateField ℓ)
    {F₀ G₀ : Dᵇc(X)⟦Profinite.padicIntegersRingObj ℓ E.1⟧ ⥤
      Dᵇc(Y)⟦Profinite.padicIntegersRingObj ℓ E.1⟧}
    {F G : Dᵇc(X)⟦Profinite.continuousMapRingObj E.1⟧ ⥤
      Dᵇc(Y)⟦Profinite.continuousMapRingObj E.1⟧} {θ₀ : F₀ ⟶ G₀} {θ : F ⟶ G}
    {ιF : F₀ ⋙ boundedConstructibleExtendScalars Y ℓ E ≅
      boundedConstructibleExtendScalars X ℓ E ⋙ F}
    {ιG : G₀ ⋙ boundedConstructibleExtendScalars Y ℓ E ≅
      boundedConstructibleExtendScalars X ℓ E ⋙ G}
    (h : NatTrans.SquareCompatible ιF ιG θ₀ θ) (hθ₀ : ∀ K₀, IsIso (θ₀.app K₀))
    (K : Dᵇc(X)⟦Profinite.continuousMapRingObj E.1⟧) : IsIso (θ.app K) :=
  h.isIso_app_of_exists_iso (exists_boundedConstructibleExtendScalars_obj_iso X ℓ E) hθ₀ K

/-- Blueprint `proposition-isomorphisms-reduce-finite-coefficients--4` (`ℚ̄_ℓ`): let
`θ : F ⟶ G` be a transformation of functors `Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(Y)⟦ℚ̄_ℓ⟧` compatible, along the
extensions of scalars `ℚ̄_ℓ ⊗ᴸ_E -` for the finite subextensions `E`, with transformations
`θ_E : F_E ⟶ G_E` of functors `Dᵇc(X)⟦E⟧ ⥤ Dᵇc(Y)⟦E⟧`. If every `θ_E` is an isomorphism, so is
`θ`: every bounded constructible `ℚ̄_ℓ`-complex descends to some finite subextension `E`
(`constructibleCocone_essSurjObj`). -/
theorem isIso_app_of_squareCompatible_constructibleToPadicAlgCl
    {F_ G_ : ∀ E : FiniteIntermediateField ℓ,
      PadicSubfieldConstructible X ℓ E ⥤ PadicSubfieldConstructible Y ℓ E}
    {F G : PadicAlgClConstructible X ℓ ⥤ PadicAlgClConstructible Y ℓ}
    {θ_ : ∀ E, F_ E ⟶ G_ E} {θ : F ⟶ G}
    {ιF : ∀ E, F_ E ⋙ constructibleToPadicAlgCl Y ℓ E ≅ constructibleToPadicAlgCl X ℓ E ⋙ F}
    {ιG : ∀ E, G_ E ⋙ constructibleToPadicAlgCl Y ℓ E ≅ constructibleToPadicAlgCl X ℓ E ⋙ G}
    (h : ∀ E, NatTrans.SquareCompatible (ιF E) (ιG E) (θ_ E) θ)
    (hθ_ : ∀ E K, IsIso ((θ_ E).app K)) (K : PadicAlgClConstructible X ℓ) :
    IsIso (θ.app K) := by
  obtain ⟨E, K_E, ⟨e⟩⟩ := constructibleCocone_essSurjObj X ℓ K
  have := hθ_ E K_E
  have := (h E).isIso_app_obj K_E
  exact (NatTrans.isIso_app_iff_of_iso θ e).1 this

end AlgebraicGeometry.ProEtale
