/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.NearbyCycles.HomComp
public import WeilConjectures.SixFunctors.NearbyCycles.OpenExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CoefficientChangeRestricted
public import WeilConjectures.Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.RingTheory.ProEtale.StrictlyHenselianRetraction

/-!

# Invariance of nearby cycles under change of strictly henselian trait

Let `ι : R₁ ⟶ R₂` be an injective local homomorphism of strictly henselian discrete valuation
rings, so that `g : S₂ = Spec R₂ ⟶ S₁ = Spec R₁` is a morphism of strictly henselian traits, with
compatible geometric generic points `Spec Ω₂ ⟶ Spec Ω₁` (`Ωᵢ` algebraically closed) and closed
points `Spec κᵢ ⟶ Sᵢ` (`κᵢ` separably closed). Let `N` be a model of finite type over `S₁` and
`M` its base change to `S₂`, related by a morphism of models `φ : M ⟶ N` whose square of total
spaces is cartesian. Deligne's theorem (SGA 4½, [Th. finitude], Prop. 3.7) says that the
formation of nearby cycles commutes with the change of trait: the pullback exchange
`α : g_s^* Ψ_N ⟶ Ψ_M g^*` is an isomorphism on complexes whose restriction to the geometric
generic fibre is bounded constructible
(`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`).

This is the common input of the trait-change step of Gabber's Künneth formula (for
`Spec K⟦t⟧ ⟶ Spec k'⟦t⟧`) and of the slice step of Deligne's finiteness theorem (for
`Spec K⟦t⟧ ⟶ S'`, `S'` the strict localization of `𝔸¹_S` at the generic point of its special
fibre).

## Proof outline (Deligne, loc. cit., 3.7–3.9)

By a limit argument and Zariski localization one may assume `N` affine, then projective over
`S₁`, and one argues by induction on the dimension `n` of the generic fibre. Let `C` be the cone
of `α`.
* (A) The cohomology sheaves of `C` have local sections with finite support: on the geometric
  generic fibres of the coordinate projections `X_s ⟶ 𝔸¹_s`, the nearby cycles are the
  invariants under a pro-`p` group of the nearby cycles over the strict localizations of `𝔸¹`
  (Th. finitude, Lemme 3.4), and the induction hypothesis applies to the slices, of dimension
  `n - 1`, over these strict localizations.
* (B) `RΓ(X_{s₂}, C) = 0`: by properness both sides compute the cohomology of the geometric generic
  fibres (proper base change), which is invariant under the extension `Ω₁ ⟶ Ω₂` of algebraically
  closed fields.
A complex with cohomology sheaves of finite support and no global cohomology on a proper scheme
vanishes, so `C = 0`.

## Coefficients

The theorem is deduced from its case with coefficients `𝔽_E = 𝒪_E/ϖ`
(`NearbyCyclesModel.Hom.isIso_map_exchangeRight_app_of_isPullback_trait_residueField`), the
statement proved by Deligne for torsion coefficients. The pullback exchange is invertible once the
base change morphism of `Rj_*`, restricted to the special fibre, is; an integral model of the
`ℚ̄_ℓ`-complex reduces this to `𝒪_E`-coefficients, and derived Nakayama (the complexes involved are
derived `ϖ`-complete, PR #1792) to `𝔽_E`-coefficients
(`CoefficientChangeRestricted.lean`).

## Unfinished

The case of `𝔽_E`-coefficients is `sorry`ed. Its proof is Deligne's induction above: step (A)
needs the generic slicing identification of Lemme 3.4 (Hochschild–Serre for the pro-`p` kernel,
with torsion coefficients, for which the action of the inertia group on nearby cycles is not
formalised) and the finite-support criterion for complexes not yet known to be bounded
constructible; step (B) needs proper base change and the proper exchange of nearby cycles.

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

section Abstract

/-- The pullback exchange, in abstract categories: with `θi`, `θε` invertible, it is invertible at
`o` if `IM` of the base change morphism `β` is invertible at `E_N o`; `β` is given together with
`β'` and a proof of `β' = β`. -/
private lemma isIso_pullbackExchange_app_aux
    {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category DY'] [Category DX'] [Category DTN]
    [Category DTM] [Category DGN] [Category DGM] [Category DY] [Category DX]
    {Fp' : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
    {JNs : DGN ⥤ DTN} {JMs : DGM ⥤ DTM} {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM}
    {F : DY ⥤ DX} (θi : IN ⋙ Fp' ⟶ T ⋙ IM) [IsIso θi] (β β' : JNs ⋙ T ⟶ G ⋙ JMs)
    (h : β' = β) (θε : EN ⋙ G ⟶ F ⋙ EM) [IsIso θε]
    (α : (EN ⋙ JNs ⋙ IN) ⋙ Fp' ⟶ F ⋙ EM ⋙ JMs ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JNs) θi ≫
      Functor.whiskerRight (Functor.whiskerLeft EN β ≫ Functor.whiskerRight θε JMs) IM)
    (o : DY) (hβ : IsIso (IM.map (β'.app (EN.obj o)))) : IsIso (α.app o) := by
  subst h hα
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp]
  infer_instance

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} in
/-- **The pullback exchange on the special fibre**: the pullback exchange `α_f` of a morphism of
models is invertible at `K` as soon as the base change morphism `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of
the square of geometric generic fibres, restricted to the special fibre by `Li_M^*`, is invertible
at `Lε_N^* K`. -/
theorem isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app (φ : M.Hom N f f')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hK : IsIso ((L((M.i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ N.j) (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j)).app ((L((N.ε)^*⟦Λ⟧)).obj K)))) :
    IsIso ((φ.pullbackExchange Λ).app K) :=
  isIso_pullbackExchange_app_aux (pullbackSquareComparison Λ φ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom).natTrans
    _ ((baseChangeMap_eq_exchangeRight Λ φ.commSq_j).symm.trans
      (φ.baseChangeMap_commSq_j_eq_mateEquiv Λ))
    (pullbackSquareComparison Λ φ.commSq_ε).hom (φ.pullbackExchange Λ) rfl K hK

variable {ℓ : ℕ} [Fact ℓ.Prime]
  {R₁ R₂ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁]
  [IsStrictlyHenselianLocalRing R₁] [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂]
  [IsStrictlyHenselianLocalRing R₂] {ι : R₁ →+* R₂}
  {Ω₁ Ω₂ : Type u} [Field Ω₁] [IsAlgClosed Ω₁] [Field Ω₂] [IsAlgClosed Ω₂]
  {a₁ : R₁ →+* Ω₁} {a₂ : R₂ →+* Ω₂} {c : Ω₁ →+* Ω₂}
  {κ₁ κ₂ : Type u} [Field κ₁] [IsSepClosed κ₁] [Field κ₂] [IsSepClosed κ₂]
  {b₁ : R₁ →+* κ₁} {b₂ : R₂ →+* κ₂}
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- **Invariance of nearby cycles under change of strictly henselian trait, torsion
coefficients** (SGA 4½, [Th. finitude], Prop. 3.7, for the coefficients `𝔽_E = 𝒪_E/ϖ`). In the
situation of `NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait`, the base
change morphism `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric generic fibres with
`𝔽_E`-coefficients, restricted to the special fibre of `M`, is invertible at the reduction
`𝔽_E ⊗ᴸ K₀` of every bounded constructible `𝒪_E`-complex `K₀` on the geometric generic fibre of
`N`. This is Deligne's theorem for torsion coefficients prime to the residue characteristic, the
statement proved in loc. cit.; `sorry`ed, see the module docstring. -/
theorem isIso_map_exchangeRight_app_of_isPullback_trait_residueField [IsLocalHom ι]
    (hι : Function.Injective ι) (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (hc : c.comp a₁ = a₂.comp ι) (hb₁ : RingHom.ker b₁ = maximalIdeal R₁)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) [Fact (ringChar κ₁ ≠ ℓ)]
    (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁)) [LocallyOfFiniteType q₁]
    [QuasiCompact q₁] [IsSeparated q₁] (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ₁))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ₂))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) N.generic))}
    (hK₀ : boundedConstructible _ K₀) :
    IsIso ((L((M.i)^*⟦Profinite.continuousMapRingObj.{u}
        (PadicAlgCl.integersResidueField ℓ E.1)⟧)).map
      ((Adjunction.exchangeRight (derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} (PadicAlgCl.integersResidueField ℓ E.1)) N.j)
        (derivedUpperStarLowerStarAdjunction
          (Profinite.continuousMapRingObj.{u} (PadicAlgCl.integersResidueField ℓ E.1)) M.j)
        (pullbackSquareComparison
          (Profinite.continuousMapRingObj.{u} (PadicAlgCl.integersResidueField ℓ E.1))
            φ.commSq_j)).app
        ((Mod.extendScalars (coefficientMap
          (Profinite.padicIntegersRingObjToResidueField ℓ E.1) N.generic)).leftDerivedFunctor.obj
            K₀))) :=
  sorry

/-- **Invariance of nearby cycles under change of strictly henselian trait** (SGA 4½,
[Th. finitude], Prop. 3.7). Let `ι : R₁ ⟶ R₂` be an injective local homomorphism of strictly
henselian discrete valuation rings, with compatible maps `aᵢ : Rᵢ ⟶ Ωᵢ` to algebraically closed
fields (`c ∘ a₁ = a₂ ∘ ι`) and maps `bᵢ : Rᵢ ⟶ κᵢ` with kernel the maximal ideal to separably
closed fields, `ℓ` invertible in `κ₁`. Let `N` be a model separated and of finite type over
`S₁ = Spec R₁` along `q₁` (generic fibre over `Spec Ω₁`, special fibre over `Spec κ₁`), `M` a
model over `S₂ = Spec R₂` along `q₂`, and `φ : M ⟶ N` a morphism of models whose square of total
spaces over `Spec ι` is cartesian and whose map of generic fibres lies over `Spec c`. Then the
pullback exchange `α : Lf'^* Ψ_N B ⟶ Ψ_M (Lf^* B)` is an isomorphism for every `B` whose
restriction `Lε^* B` to the geometric generic fibre of `N` is bounded constructible.

It is deduced from the case of torsion coefficients
(`NearbyCyclesModel.Hom.isIso_map_exchangeRight_app_of_isPullback_trait_residueField`): the
pullback exchange is invertible once the base change morphism of `Rj_*` restricted to the special
fibre is (`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app`);
an integral model `K₀` of `Lε^* B` reduces the question to `𝒪_E`-coefficients
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicAlgCl_of_integral`), and derived
Nakayama, for the derived complete `K₀`, to `𝔽_E`-coefficients
(`ProEtale.CondensedRing.isIso_map_baseChangeMap_app_padicIntegers_of_residueField`). -/
theorem isIso_pullbackExchange_app_of_isPullback_trait [IsLocalHom ι]
    (hι : Function.Injective ι) (ha₁ : Function.Injective a₁) (ha₂ : Function.Injective a₂)
    (hc : c.comp a₁ = a₂.comp ι) (hb₁ : RingHom.ker b₁ = maximalIdeal R₁)
    (hb₂ : RingHom.ker b₂ = maximalIdeal R₂) [Fact (ringChar κ₁ ≠ ℓ)]
    (φ : M.Hom N f f') (q₁ : N.total ⟶ Spec (.of R₁)) [LocallyOfFiniteType q₁]
    [QuasiCompact q₁] [IsSeparated q₁] (g₁ : N.generic ⟶ Spec (.of Ω₁))
    (hNj : IsPullback N.j g₁ q₁ (Spec.map (CommRingCat.ofHom a₁))) (p₁ : Y' ⟶ Spec (.of κ₁))
    (hNi : IsPullback N.i p₁ q₁ (Spec.map (CommRingCat.ofHom b₁)))
    (q₂ : M.total ⟶ Spec (.of R₂)) (g₂ : M.generic ⟶ Spec (.of Ω₂))
    (hMj : IsPullback M.j g₂ q₂ (Spec.map (CommRingCat.ofHom a₂))) (p₂ : X' ⟶ Spec (.of κ₂))
    (hMi : IsPullback M.i p₂ q₂ (Spec.map (CommRingCat.ofHom b₂)))
    (hφ : IsPullback φ.total q₂ q₁ (Spec.map (CommRingCat.ofHom ι)))
    (hgen : φ.generic ≫ g₁ = g₂ ≫ Spec.map (CommRingCat.ofHom c))
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Y))}
    (hB : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) N.generic)
      (L((N.ε)^*⟦Profinite.padicAlgClRingObj ℓ⟧).obj B)) :
    IsIso ((φ.pullbackExchange (Profinite.padicAlgClRingObj ℓ)).app B) := by
  -- finiteness and separation properties of the fibres, by base change
  have hq₂ : QuasiCompact q₂ := MorphismProperty.of_isPullback hφ ‹_›
  have hq₂' : QuasiSeparated q₂ := MorphismProperty.of_isPullback hφ inferInstance
  have : QuasiCompact g₁ := MorphismProperty.of_isPullback hNj ‹_›
  have : QuasiSeparated g₁ := MorphismProperty.of_isPullback hNj inferInstance
  have : LocallyOfFiniteType g₁ := MorphismProperty.of_isPullback hNj ‹_›
  have : QuasiCompact N.j := MorphismProperty.of_isPullback hNj.flip inferInstance
  have : QuasiSeparated N.j := MorphismProperty.of_isPullback hNj.flip inferInstance
  have : QuasiCompact g₂ := MorphismProperty.of_isPullback hMj hq₂
  have : QuasiSeparated g₂ := MorphismProperty.of_isPullback hMj hq₂'
  have : QuasiCompact M.j := MorphismProperty.of_isPullback hMj.flip inferInstance
  have : QuasiSeparated M.j := MorphismProperty.of_isPullback hMj.flip inferInstance
  have : QuasiCompact p₂ := MorphismProperty.of_isPullback hMi hq₂
  have : QuasiSeparated p₂ := MorphismProperty.of_isPullback hMi hq₂'
  have := QuasiCompact.compactSpace_of_compactSpace q₁
  have := quasiSeparatedSpace_of_quasiSeparated q₁
  have := QuasiCompact.compactSpace_of_compactSpace q₂
  have := quasiSeparatedSpace_of_quasiSeparated q₂
  have := QuasiCompact.compactSpace_of_compactSpace g₁
  have := quasiSeparatedSpace_of_quasiSeparated g₁
  have := QuasiCompact.compactSpace_of_compactSpace g₂
  have := quasiSeparatedSpace_of_quasiSeparated g₂
  have := QuasiCompact.compactSpace_of_compactSpace p₂
  have := quasiSeparatedSpace_of_quasiSeparated p₂
  have : IsNoetherian N.generic := isNoetherian_of_locallyOfFiniteType g₁
  have hint : ∀ (E : PadicAlgCl.FiniteIntermediateField ℓ)
      (K₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology N.generic) Ab.{u + 1})
        (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) N.generic))),
      boundedConstructible _ K₀ →
        IsIso ((L((M.i)^*⟦Profinite.padicIntegersRingObj ℓ E.1⟧)).map ((Adjunction.exchangeRight
          (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) N.j)
          (derivedUpperStarLowerStarAdjunction (Profinite.padicIntegersRingObj ℓ E.1) M.j)
          (pullbackSquareComparison (Profinite.padicIntegersRingObj ℓ E.1) φ.commSq_j)).app
            K₀)) := by
    intro E K₀ hK₀
    have : K₀.IsGE hK₀.1.1.choose := hK₀.1.1.choose_spec
    have hres := isIso_map_exchangeRight_app_of_isPullback_trait_residueField hι ha₁ ha₂ hc hb₁
      hb₂ φ q₁ g₁ hNj p₁ hNi q₂ g₂ hMj p₂ hMi hφ hgen E hK₀
    have h := isIso_map_baseChangeMap_app_padicIntegers_of_residueField ℓ E φ.commSq_j M.i K₀
      hK₀.1.1.choose (derivedCompleteIntegers_of_boundedConstructible hK₀)
      (by exact_mod_proofs hres)
    exact_mod_proofs h
  have key := isIso_map_baseChangeMap_app_padicAlgCl_of_integral ℓ φ.commSq_j M.i hB hint
  have := isIso_pullbackExchange_app_of_isIso_map_exchangeRight_app
    (Profinite.padicAlgClRingObj ℓ) φ B (by exact_mod_proofs key)
  exact_mod_proofs this

end NearbyCyclesModel.Hom

end AlgebraicGeometry.ProEtale.CondensedRing
