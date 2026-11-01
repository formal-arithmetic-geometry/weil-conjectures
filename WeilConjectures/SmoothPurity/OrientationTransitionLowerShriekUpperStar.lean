/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeUnitLowerStar
public import WeilConjectures.SmoothPurity.OrientationTransitionLowerShriekPullback
public import WeilConjectures.SmoothPurity.OrientationTransitionUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriekCanonical
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionUpperStarReading

/-!
# The reduction square for the pullbacks, and the proper piece of the reduction square for `Rf_!`

Write `Ψ` for the derived extension of scalars along `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ` on the étale site,
`Res` for the restriction of scalars and `T : red_{n+1} ⟶ red_n ⋙ Res` for the transpose of the
compatibility `β : Ψ(red_{n+1} K) ≅ red_n K` of `Ψ` with the reductions
(`ProEtale.CondensedRing.etaleReductionTransposeNatTrans`). This file (blueprint
`det-sp-purity-coefficient-change`) states:

* `ProEtale.CondensedRing.etaleReductionUpperStarIso_restrictScalars`: for any `f : Z ⟶ Y`, the
  canonical comparisons `f^* ⋙ red ≅ red ⋙ Lf^*` modulo `ℓⁿ⁺¹` and `ℓⁿ`
  (`ProEtale.CondensedRing.etaleReductionUpperStarIso`) are intertwined by `T` and the commutation
  of `Res` with `Lf^*` (`Etale.leftDerivedUpperStarRestrictScalarsIso`); it is assembled
  (`CategoryTheory.map_comp_app_comp_map_eq_of_cube`) from the étale and pro-étale pieces of
  `WeilConjectures.SmoothPurity.OrientationTransitionUpperStar`;
* `ProEtale.CondensedRing.mateEquiv_etaleReductionUpperStarIso_inv`: for a proper `p`, the
  comparison `Rp_! ⋙ red ≅ red ⋙ Rp_!` (`ProEtale.CondensedRing.etaleReductionLowerShriekIso`),
  followed by `Rp_! ≅ Rp_*`, is the mate of the pullback comparison under `p^* ⊣ Rp_!` and
  `Lp^* ⊣ Rp_*`;
* `Etale.app_comp_map_comp_derivedRestrictScalarsCompRightDerivedLowerStarIso_hom_app_eq`: over a
  general coefficient ring, the proper piece of the reduction square for `Rf_!` in restriction
  form follows from the two previous statements by transposition
  (`CategoryTheory.app_comp_map_mateEquiv_app_comp_mateEquiv_app_eq_of_map`)
  and the mate description of the commutation of `Res` with `Rp_*`
  (`Etale.mateEquiv_derivedUpperStarLowerStarAdjunction_leftDerivedUpperStarRestrictScalarsIso`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

section MateOfNatIsoRight

variable {C₁ C₂ D₁ D₂ : Type*} [Category* C₁] [Category* C₂] [Category* D₁] [Category* D₂]

/-- The mate under an adjunction whose right adjoint is replaced by an isomorphic functor
(`Adjunction.ofNatIsoRight`), against an unchanged adjunction: on `d`, it is `G` of the inverse
of the isomorphism at `d`, followed by the mate under the original adjunction. -/
lemma mateEquiv_ofNatIsoRight_left_app {G : C₁ ⥤ D₁} {H : C₂ ⥤ D₂} {L₁ : C₁ ⥤ C₂}
    {R₁ R₁' : C₂ ⥤ C₁} {L₂ : D₁ ⥤ D₂} {R₂ : D₂ ⥤ D₁} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : R₁ ≅ R₁') (α : TwoSquare G L₁ L₂ H) (d : C₂) :
    (mateEquiv (adj₁.ofNatIsoRight e) adj₂ α).app d =
      G.map (e.inv.app d) ≫ (mateEquiv adj₁ adj₂ α).app d := by
  simp only [mateEquiv, Adjunction.ofNatIsoRight, Equiv.coe_fn_mk]
  simp only [Functor.comp_obj, Functor.whiskerRight_comp, Functor.whiskerRight_twice,
    Category.assoc, Iso.inv_hom_id_assoc, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp]
  have h := α.natTrans.naturality (e.inv.app d)
  simp only [Functor.comp_map] at h
  rw [← adj₂.unit_naturality_assoc, ← R₂.map_comp_assoc, ← h, R₂.map_comp_assoc]

end MateOfNatIsoRight

section PastedMate

universe v₁ v₂ v₃ v₄ v₅ v₆

-- The category structures are implicit arguments, determined by unification with the explicit
-- arguments rather than by instance search, so that instantiations reuse the instance terms of
-- the given functors.
variable {A₁ A₂ B₁ B₂ C₁ C₂ : Type*} {_ : Category.{v₁} A₁} {_ : Category.{v₂} A₂}
  {_ : Category.{v₃} B₁} {_ : Category.{v₄} B₂} {_ : Category.{v₅} C₁} {_ : Category.{v₆} C₂}

/-- **The mate of a pasted pullback comparison is the pasted pushforward comparison.** Let
`c : L₁ ⋙ R_X ≅ R_Y ⋙ L` and `r : L ⋙ ρ_X ≅ ρ_Y ⋙ L₂` be comparisons of left adjoints
`L₁ ⊣ R₀`, `L ⊣ R`, `L₂ ⊣ R₂`, with mates `γ : R₀ ⋙ R_Y ⟶ R_X ⋙ R` (invertible) and
`δ : R ⋙ ρ_Y ≅ ρ_X ⋙ R₂`. Let `e : R₁ ≅ R₀`, `s : R₂' ≅ R₂`, and let `Φ` be the inverse of the
horizontal paste of `γ⁻¹ ≫ e⁻¹` and of `δ` followed by `s⁻¹`. Then the mate of the paste `u` of
`c` and `r` under `L₁ ⊣ R₁` (transported along `e`) and `L₂ ⊣ R₂` is `Φ` followed by `s`. -/
theorem mateEquiv_inv_app_eq_hComp_inv_app {eR_Y : A₁ ⥤ C₁} {eR_X : A₂ ⥤ C₂} {L₁ : A₁ ⥤ A₂}
    {R₀ R₁ : A₂ ⥤ A₁} (adj₀ : L₁ ⊣ R₀)
    (e : R₁ ≅ R₀) {L : B₁ ⥤ B₂} {R : B₂ ⥤ B₁} (adj : L ⊣ R) {L₂ : C₁ ⥤ C₂} {R₂ R₂' : C₂ ⥤ C₁}
    (adj₂ : L₂ ⊣ R₂) (s : R₂' ≅ R₂) {R_Y : A₁ ⥤ B₁} {R_X : A₂ ⥤ B₂} {ρ_Y : B₁ ⥤ C₁}
    {ρ_X : B₂ ⥤ C₂} (c : L₁ ⋙ R_X ≅ R_Y ⋙ L) (r : L ⋙ ρ_X ≅ ρ_Y ⋙ L₂)
    (γ : R₀ ⋙ R_Y ⟶ R_X ⋙ R) [IsIso γ] (hγ : mateEquiv adj₀ adj c.inv = γ)
    (δ : R ⋙ ρ_Y ≅ ρ_X ⋙ R₂) (hδ : (mateEquiv adj adj₂ r.inv).natTrans = δ.hom)
    (σ : R ⋙ ρ_Y ≅ ρ_X ⋙ R₂') (hσ : σ = δ ≪≫ Functor.isoWhiskerLeft ρ_X s.symm)
    (hY : R_Y ⋙ ρ_Y = eR_Y) (hX : R_X ⋙ ρ_X = eR_X)
    (Φ : R₁ ⋙ eR_Y ≅ eR_X ⋙ R₂')
    (hΦ : HEq Φ.inv (TwoSquare.hComp
      (TwoSquare.mk _ _ _ _ (inv γ ≫ Functor.whiskerRight e.inv R_Y))
      (TwoSquare.mk _ _ _ _ σ.inv)).natTrans)
    (u : L₁ ⋙ eR_X ≅ eR_Y ⋙ L₂)
    (hu : HEq u (Functor.isoWhiskerRight c ρ_X ≪≫ Functor.isoWhiskerLeft R_Y r)) (K : A₂) :
    (mateEquiv (adj₀.ofNatIsoRight e.symm) adj₂ u.inv).app K =
      Φ.hom.app K ≫ s.hom.app (eR_X.obj K) := by
  subst hX hY
  replace hΦ := eq_of_heq hΦ
  replace hu := eq_of_heq hu
  have hpaste : u.inv =
      TwoSquare.hComp (TwoSquare.mk _ _ _ _ c.inv) (TwoSquare.mk _ _ _ _ r.inv) := by
    subst hu
    ext K
    simp only [Functor.comp_obj, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, TwoSquare.hComp, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.comp_id, Category.id_comp]
  refine (mateEquiv_ofNatIsoRight_left_app adj₀ adj₂ e.symm u.inv K).trans ?_
  subst hσ
  rw [hpaste, mateEquiv_vcomp adj₀ adj adj₂,
    ← Iso.app_hom, ← Iso.inv_comp_eq, Iso.app_inv, hΦ]
  generalize mateEquiv adj adj₂ (TwoSquare.mk _ _ _ _ r.inv) = m₂ at hδ ⊢
  generalize mateEquiv adj₀ adj (TwoSquare.mk _ _ _ _ c.inv) = m₁ at hγ ⊢
  subst hγ
  obtain rfl : m₂ = δ.hom := hδ
  simp only [Functor.comp_obj, TwoSquare.hComp, Iso.trans_inv, Functor.isoWhiskerLeft_inv,
    Iso.symm_inv, Functor.whiskerLeft_comp, Functor.whiskerLeft_twice, Category.assoc,
    Functor.whiskerRight_comp, Functor.whiskerRight_twice, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map, Category.id_comp,
    TwoSquare.vComp]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  erw [NatIso.isIso_inv_app, IsIso.inv_hom_id]
  simp only [Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Functor.comp_obj,
    Category.comp_id]

end PastedMate

end CategoryTheory

namespace AlgebraicGeometry.Etale

section Generic

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X Y : Scheme.{u}}
  (p : X ⟶ Y) (d : ℕ)
  (hd : ∀ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), d < q →
    IsZero ((((p)_*[ModuleCat.{u + 1} Λ]).rightDerived q).obj F))

/-- **Compatibility of pushforward squares with the restriction of scalars, from the pullback
squares**: let `γ : R₁ ⋙ r₁ ≅ r₂ ⋙ Rp_*` and `γ' : R₁ ⋙ r₁' ≅ r₂' ⋙ Rp_*` be the mates, under
an adjunction `L₁ ⊣ R₁` and `Lp^* ⊣ Rp_*` (over `Λ` and `Λ'`), of squares
`θ : r₁ ⋙ Lp^* ⟶ L₁ ⋙ r₂` and `θ' : r₁' ⋙ Lp^* ⟶ L₁ ⋙ r₂'`. If `θ` and `θ'` are intertwined by
`T₁ : r₁ ⟶ r₁' ⋙ Res`, `T₂ : r₂ ⟶ r₂' ⋙ Res` and the commutation of `Res` with `Lp^*`
(`leftDerivedUpperStarRestrictScalarsIso`), then `γ` and `γ'` are intertwined by `T₁`, `T₂` and
the commutation of `Res` with `Rp_*` (`derivedRestrictScalarsCompRightDerivedLowerStarIso`). -/
theorem app_comp_map_comp_derivedRestrictScalarsCompRightDerivedLowerStarIso_hom_app_eq
    {C₁ C₂ : Type*} [Category C₁] [Category C₂] {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} (a₁ : L₁ ⊣ R₁)
    {r₁ : C₁ ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {r₂ : C₂ ⥤ DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {r₁' : C₁ ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    {r₂' : C₂ ⥤ DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    (T₁ : r₁ ⟶ r₁' ⋙ Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ)
    (T₂ : r₂ ⟶ r₂' ⋙ Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ)
    (θ : TwoSquare r₁ L₁ L((p)^*[ModuleCat.{u + 1} Λ]) r₂)
    (θ' : TwoSquare r₁' L₁ L((p)^*[ModuleCat.{u + 1} Λ']) r₂')
    (γ : R₁ ⋙ r₁ ≅ r₂ ⋙ R((p)_*[ModuleCat.{u + 1} Λ]))
    (γ' : R₁ ⋙ r₁' ≅ r₂' ⋙ R((p)_*[ModuleCat.{u + 1} Λ']))
    (h : ∀ K, L((p)^*[ModuleCat.{u + 1} Λ]).map (T₁.app K) ≫
        (leftDerivedUpperStarRestrictScalarsIso ρ p).hom.app (r₁'.obj K) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (θ'.app K) =
      θ.app K ≫ T₂.app (L₁.obj K))
    (hγ : ∀ N,
      (mateEquiv a₁ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p) θ).app N =
        γ.hom.app N)
    (hγ' : ∀ N,
      (mateEquiv a₁ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') p) θ').app N =
        γ'.hom.app N)
    (N : C₂) :
    γ.hom.app N ≫ R((p)_*[ModuleCat.{u + 1} Λ]).map (T₂.app N) ≫
        (derivedRestrictScalarsCompRightDerivedLowerStarIso ρ p d hd).hom.app (r₂'.obj N) =
      T₁.app (R₁.obj N) ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology ρ).map (γ'.hom.app N) := by
  have H := app_comp_map_mateEquiv_app_comp_mateEquiv_app_eq_of_map a₁
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') p) T₁ T₂
    (leftDerivedUpperStarRestrictScalarsIso ρ p).hom θ θ' h N
  rw [hγ, hγ', mateEquiv_derivedUpperStarLowerStarAdjunction_leftDerivedUpperStarRestrictScalarsIso
    ρ p d hd, ← Iso.app_inv, ← Category.assoc, Iso.comp_inv_eq, Iso.app_hom] at H
  rw [H, Category.assoc]

end Generic

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)

section UpperStar

variable {Z Y : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- Blueprint `det-sp-purity-coefficient-change`, the reduction square for the pullbacks: through
the transposes `T : red_{n+1} ⟶ red_n ⋙ Res` of `β`, the comparisons
`red ⋙ Lf^* ≅ f^* ⋙ red` modulo `ℓⁿ⁺¹` and `ℓⁿ` (inverses of `etaleReductionUpperStarIso`) are
intertwined by the commutation `Res ⋙ Lf^* ≅ Lf^* ⋙ Res` of the restriction of scalars with the
derived pullbacks (`Etale.leftDerivedUpperStarRestrictScalarsIso`). -/
theorem etaleReductionUpperStarIso_restrictScalars (f : Z ⟶ Y)
    (M : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E (n + 1))) f.left).map
        ((etaleReductionTransposeNatTrans ℓ E n Y).app M) ≫
      (Etale.leftDerivedUpperStarRestrictScalarsIso (integersModPowCoeffTransition ℓ E n)
        f.left).hom.app ((etaleReduction ℓ E n Y).obj M) ≫
      (Sheaf.derivedRestrictScalars Z.left.smallEtaleTopology
        (integersModPowCoeffTransition ℓ E n)).map
        ((etaleReductionUpperStarIso ℓ E n f).inv.app M) =
    (etaleReductionUpperStarIso ℓ E (n + 1) f).inv.app M ≫
      (etaleReductionTransposeNatTrans ℓ E n Z).app
        ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).obj M) := by
  have := AlgebraicGeometry.ProEtale.isIso_derivedRestrictScalarsCompComparisonLowerStarMap
    (integersModPowCoeffTransition_surjective ℓ E n) (ker_integersModPowCoeffTransition ℓ E n)
    Z.left
  exact map_comp_app_comp_map_eq_of_cube
    (rightDerivedComparisonBaseChange _ f.left) (rightDerivedComparisonBaseChange _ f.left)
    (derivedRestrictScalarsCompComparisonLowerStarMap _ Y.left)
    (derivedRestrictScalarsCompComparisonLowerStarMap _ Z.left)
    (Etale.leftDerivedUpperStarRestrictScalarsIso _ f.left).hom
    (AlgebraicGeometry.ProEtale.leftDerivedUpperStarRestrictScalarsIso _ f.left).hom
    _ _ _ _ (etaleReductionProEtaleTranspose ℓ E n Y M)
    (etaleReductionProEtaleTranspose ℓ E n Z
      ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ f).obj M))
    (etaleReductionUpperStarProEtaleMap ℓ E (n + 1) f M)
    (etaleReductionUpperStarProEtaleMap ℓ E n f M)
    (etaleReductionUpperStarIso_inv_app ℓ E (n + 1) f M)
    (etaleReductionUpperStarIso_inv_app ℓ E n f M)
    (etaleReductionTransposeNatTrans_app_comp ℓ E n Y M)
    (etaleReductionTransposeNatTrans_app_comp ℓ E n Z _)
    (AlgebraicGeometry.ProEtale.map_app_comp_rightDerivedComparisonBaseChange_app_comp_map_eq _
      f.left _)
    (map_etaleReductionProEtaleTranspose_comp_eq ℓ E n f M)

end UpperStar

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (p : X ⟶ Y) [IsProper p.left]

/-- The adjunction `p^* ⊣ Rp_!` on bounded constructible `𝒪_E`-complexes for a proper `p`: the
adjunction `p^* ⊣ Rp_*` transported along `Rp_! ≅ Rp_*`
(`boundedConstructibleLowerShriekIsoLowerStar_padicIntegers`). -/
noncomputable abbrev boundedConstructibleUpperStarLowerShriekAdjunction_padicIntegers :
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ p ⊣
      PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E p :=
  (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p).ofNatIsoRight
    (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E p).symm

-- unifying the categories of the generic lemma with those of the étale reductions (rather than
-- with those of the adjunctions) needs a deeper recursion in the elaborator
set_option maxRecDepth 20000 in
/-- Blueprint `det-sp-purity-coefficient-change`: for a proper `p`, the canonical comparison
`Rp_! ⋙ red ≅ red ⋙ Rp_!` (`etaleReductionLowerShriekIso`) followed by `Rp_! ≅ Rp_*` is the mate,
under `p^* ⊣ Rp_!` and `Lp^* ⊣ Rp_*`, of the inverse of the pullback comparison
`p^* ⋙ red ≅ red ⋙ Lp^*` (`etaleReductionUpperStarIso`). -/
theorem mateEquiv_etaleReductionUpperStarIso_inv (m : ℕ)
    (K : Dᵇc(X.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    have := HasCompactification.of_over p
    (mateEquiv (boundedConstructibleUpperStarLowerShriekAdjunction_padicIntegers ℓ E p)
      (Etale.derivedUpperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E m)) p.left)
      (etaleReductionUpperStarIso ℓ E m p).inv).app K =
    (etaleReductionLowerShriekIso ℓ E m p ≪≫ Functor.isoWhiskerLeft _
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar _ p.left)).hom.app K := by
  intro hc
  have := isIso_boundedConstructibleLowerStarIntegersModPowReduction_of_compatible ℓ E m p
    (integersModPowPullUnitCompatible ℓ E m p.left) (integersModPowPullδCompatible ℓ E m p.left)
  rw [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  exact mateEquiv_inv_app_eq_hComp_inv_app
    (R_Y := boundedConstructibleIntegersModPowReduction Y.left ℓ E m)
    (R_X := boundedConstructibleIntegersModPowReduction X.left ℓ E m)
    (ρ_Y := finiteEtaleReading ℓ E m Y) (ρ_X := finiteEtaleReading ℓ E m X)
    (eR_Y := etaleReduction ℓ E m Y) (eR_X := etaleReduction ℓ E m X)
    (PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E p)
    (boundedConstructibleLowerShriekIsoLowerStar_padicIntegers ℓ E p)
    (IntegersModPowRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E m p)
    (Etale.derivedUpperStarLowerStarAdjunction _ p.left)
    (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar _ p.left)
    (boundedConstructibleUpperStarIntegersModPowReductionIso ℓ E m p)
    (finiteEtaleReadingUpperStarIso ℓ E m p)
    (boundedConstructibleLowerStarIntegersModPowReduction ℓ E m p) rfl
    (finiteEtaleReadingLowerStarIso ℓ E m p) (mateEquiv_finiteEtaleReadingUpperStarIso_inv ℓ E m p)
    (finiteEtaleReadingLowerShriekIso ℓ E m p) rfl rfl rfl (etaleReductionLowerShriekIso ℓ E m p)
    (heq_of_eq rfl) (etaleReductionUpperStarIso ℓ E m p)
    (heq_of_eq (etaleReductionUpperStarIso_eq ℓ E m p)) K

end AlgebraicGeometry.ProEtale.CondensedRing
