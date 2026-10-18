/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
public import WeilConjectures.ConstructibleSheaf.RestrictScalars
public import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact

/-!
# Constructibility of direct images of constant sheaves: change of coefficients

Let `f : X ⟶ S` be a morphism of schemes and `Λ` a finite ring. We reduce the constructibility
of the higher direct images `Rᵠf_* M` of the constant sheaf with value a finite `Λ`-module `M`
to the case of the coefficient fields `𝔽_ℓ`, `ℓ` a prime dividing the characteristic of `Λ`.
This is the dévissage in the proof of `cor-fin-projective-curve-finite-group`.

## Main statements

- `AlgebraicGeometry.Etale.constantSheafCompRestrictScalarsIso`: constant sheaves commute with
  restriction of scalars.
- `AlgebraicGeometry.Etale.restrictScalarsHomologyRightDerivedLowerStarIso`: higher direct
  images commute with restriction of scalars.
- `AlgebraicGeometry.Scheme.IsConstructibleSheaf.of_restrictScalars_ringHom`: restriction of
  scalars along a ring homomorphism between finite rings reflects constructibility.
- `AlgebraicGeometry.Etale.constructibleHomology_rightDerivedLowerStar_constantSheaf_of_isMaximal`:
  dévissage of a finite module along a composition series.
- `AlgebraicGeometry.Etale.constructibleHomology_rightDerivedLowerStar_constantSheaf_of_zmod`:
  reduction to the coefficient fields `𝔽_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')

/-- Constant sheaves commute with restriction of scalars. -/
noncomputable def constantSheafCompRestrictScalarsIso (Y : Scheme.{u}) :
    constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ') ⋙
        Sheaf.restrictScalars Y.smallEtaleTopology φ ≅
      ModuleCat.restrictScalars.{u + 1} φ ⋙
        constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  ((constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ') terminalIsTerminal).comp
    (Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ)).leftAdjointUniq
    (((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).comp
      (constantSheafAdj Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        terminalIsTerminal)).ofNatIsoRight
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)))

/-- The higher direct images commute with restriction of scalars. -/
noncomputable def restrictScalarsHomologyRightDerivedLowerStarIso {X S : Scheme.{u}}
    (f : X ⟶ S) (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (q : ℤ) :
    (Sheaf.restrictScalars S.smallEtaleTopology φ).obj ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ'])).obj ((singleFunctor _ 0).obj F))) ≅
    (homologyFunctor _ q).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj
      ((singleFunctor _ 0).obj ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj F))) :=
  (Sheaf.restrictScalars S.smallEtaleTopology φ).mapIso ((homologyFunctor _ q).mapIso
      ((R((f)_*[ModuleCat.{u + 1} Λ'])).mapIso ((Plus.singleFunctorιIso _ 0).app F).symm ≪≫
      ((f)_*[ModuleCat.{u + 1} Λ'].rightDerivedFunctorPlusCompatibility.app _).symm)) ≪≫
    ((Sheaf.restrictScalars S.smallEtaleTopology φ).mapDerivedCategoryPlusHomologyFunctorIso
      q).app _ ≪≫
    (Plus.homologyFunctor _ q).mapIso ((derivedLowerStarRestrictScalarsIso φ f).app _) ≪≫
    (Plus.homologyFunctor _ q).mapIso ((R+((f)_*[ModuleCat.{u + 1} Λ])).mapIso
      (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusSingleFunctor
        0).app F)) ≪≫
    (homologyFunctor _ q).mapIso
      ((f)_*[ModuleCat.{u + 1} Λ].rightDerivedFunctorPlusCompatibility.app _ ≪≫
        (R((f)_*[ModuleCat.{u + 1} Λ])).mapIso ((Plus.singleFunctorιIso _ 0).app
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj F)))

end Etale

namespace Scheme

variable {X : Scheme.{u}} {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
  (ψ : A →+* B)

/-- For finite rings `A` and `B` and a ring homomorphism `ψ : A →+* B`, a sheaf of `B`-modules
whose restriction of scalars to `A` is finite locally constant is finite locally constant: its
underlying sheaf of sets is (`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_forget`). -/
lemma IsFiniteLocallyConstantSheaf.of_restrictScalars_ringHom
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    [h : IsFiniteLocallyConstantSheaf
      ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj G)] :
    IsFiniteLocallyConstantSheaf G := by
  refine IsFiniteLocallyConstantSheaf.of_forget G ⟨?_, ⟨fun Ω _ _ s ↦ ?_⟩⟩
  · obtain ⟨⟨𝒰, h𝒰⟩⟩ := h.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
    refine ⟨𝒰, fun i ↦ ?_⟩
    have := h𝒰 i
    exact inferInstanceAs (((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} A))).obj
      (((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj G).over _)).IsConstant _)
  · have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} A)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    have hfg := h.toIsFiniteSheaf.isFinitelyGenerated_sheafFiber Ω s
    rw [ModuleCat.isFinitelyGenerated_iff] at hfg
    have : Finite (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)).obj
        ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj G)) :=
      Module.finite_of_finite A
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite]
    exact @Finite.of_equiv _ _ this (((pointSmallEtale s).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} A))).app _).symm.toEquiv

/-- For finite rings `A` and `B` and a ring homomorphism `ψ : A →+* B`, a sheaf of `B`-modules
whose restriction of scalars to `A` is constructible is constructible: pullback to the strata
commutes with restriction of scalars
(`AlgebraicGeometry.Etale.upperStarRestrictScalarsIsoSheaf`). -/
lemma IsConstructibleSheaf.of_restrictScalars_ringHom
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (hG : IsConstructibleSheaf ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj G)) :
    IsConstructibleSheaf G := by
  obtain ⟨S, hS⟩ := hG
  refine ⟨S, fun i ↦ ?_⟩
  have : IsFiniteLocallyConstantSheaf ((Sheaf.restrictScalars X.smallEtaleTopology ψ ⋙
      Etale.upperStar (ModuleCat.{u + 1} A) (S.immersion i)).obj G) := hS i
  have : IsFiniteLocallyConstantSheaf ((Sheaf.restrictScalars _ ψ).obj
      ((Etale.upperStar (ModuleCat.{u + 1} B) (S.immersion i)).obj G)) :=
    IsFiniteLocallyConstantSheaf.of_iso
      ((Etale.upperStarRestrictScalarsIsoSheaf ψ (S.immersion i)).app G)
  exact IsFiniteLocallyConstantSheaf.of_restrictScalars_ringHom ψ _

end Scheme

namespace Etale

open _root_.DerivedCategory

variable {A : Type (u + 1)} [CommRing A] [Finite A]

/-- **Dévissage of constant coefficients.** Let `A` be a finite ring and `f : X ⟶ S`. If
`Rf_*(A ⧸ 𝔪)` has constructible homology sheaves for every maximal ideal `𝔪` of `A`, then so
has `Rf_* M` for every finite `A`-module `M`: a nonzero finite module `M` has a maximal proper
submodule `N`, with simple quotient `M ⧸ N ≅ A ⧸ 𝔪`, and the short exact sequence of constant
sheaves `0 ⟶ N ⟶ M ⟶ M ⧸ N ⟶ 0` gives a distinguished triangle after applying `Rf_*`. -/
lemma constructibleHomology_rightDerivedLowerStar_constantSheaf_of_isMaximal {X S : Scheme.{u}}
    (f : X ⟶ S)
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal →
      Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} A) S
        ((R((f)_*[ModuleCat.{u + 1} A])).obj ((singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj
            (ModuleCat.of A (A ⧸ 𝔪))))))
    (M : ModuleCat.{u + 1} A) [Finite M] :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} A) S
      ((R((f)_*[ModuleCat.{u + 1} A])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M))) := by
  set P := Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} A) S
  set F := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ⋙ singleFunctor _ 0 ⋙
    R((f)_*[ModuleCat.{u + 1} A])
  change P (F.obj M)
  suffices H : ∀ (n : ℕ) (M : ModuleCat.{u + 1} A), Finite M → Nat.card M ≤ n → P (F.obj M) from
    H _ M inferInstance le_rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ hn
  by_cases hM : Subsingleton M
  · exact P.prop_of_isZero (F.map_isZero (ModuleCat.isZero_of_subsingleton M))
  rw [not_subsingleton_iff_nontrivial] at hM
  obtain ⟨N, hN, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule A M)).resolve_left
    bot_ne_top
  have : IsSimpleModule A (M ⧸ N) := isSimpleModule_iff_isCoatom.2 hN
  obtain ⟨𝔪, h𝔪, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 this
  let T := ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ)
    (by ext x; simp)
  have hT : T.ShortExact := ShortComplex.ShortExact.mk'
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
      (LinearMap.exact_subtype_mkQ N))
    ((ModuleCat.mono_iff_injective _).2 N.injective_subtype)
    ((ModuleCat.epi_iff_surjective _).2 N.mkQ_surjective)
  have hT' := hT.map_of_exact (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
  have hD := (R((f)_*[ModuleCat.{u + 1} A])).map_distinguished _ hT'.singleTriangle_distinguished
  refine P.ext_of_isTriangulatedClosed₂ _ hD ?_ ?_
  · obtain ⟨x, hx⟩ : ∃ x : M, x ∉ N := by
      by_contra! hc
      exact hN.1 (eq_top_iff.2 fun x _ ↦ hc x)
    exact ih _ (lt_of_lt_of_le (Finite.card_subtype_lt hx) hn) (ModuleCat.of A N)
      inferInstance le_rfl
  · exact P.prop_of_iso (F.mapIso e.toModuleIso.symm) (h 𝔪 h𝔪)


/-- **Constant coefficients over a finite ring from prime-field coefficients.** Let `Λ` be a
finite ring and `f : X ⟶ S`. Suppose `Rf_* 𝔽_ℓ` has constructible homology sheaves for every
prime `ℓ` dividing the characteristic of `Λ`. Then `Rf_* M` has constructible homology sheaves
for every finite `Λ`-module `M`.

By dévissage (`constructibleHomology_rightDerivedLowerStar_constantSheaf_of_isMaximal`) it
suffices to treat `M = Λ ⧸ 𝔪 = k` for a maximal ideal `𝔪`. Restriction of scalars along
`Λ ⟶ k` and along `𝔽_ℓ ⟶ k`, `ℓ` the characteristic of `k`, commutes with constant sheaves
and higher direct images, preserves constructibility along `Λ ⟶ k` and reflects it along
`𝔽_ℓ ⟶ k`; and the finite `𝔽_ℓ`-module `k` is handled by dévissage over `𝔽_ℓ`. -/
lemma constructibleHomology_rightDerivedLowerStar_constantSheaf_of_zmod {X S : Scheme.{u}}
    (f : X ⟶ S) {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ∣ ringChar Λ →
      Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) S
        ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj ((singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
              (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))))))
    (M : ModuleCat.{u + 1} Λ) [Finite M] :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  refine constructibleHomology_rightDerivedLowerStar_constantSheaf_of_isMaximal f
    (fun 𝔪 h𝔪 q ↦ ?_) M
  let k := Λ ⧸ 𝔪
  let : Field k := Ideal.Quotient.field 𝔪
  have : Finite k := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  let ℓ := ringChar k
  have : Fact ℓ.Prime := ⟨CharP.prime_ringChar k⟩
  have hℓ : ℓ ∣ ringChar Λ := ringChar.dvd (by
    rw [← map_natCast (Ideal.Quotient.mk 𝔪), ringChar.Nat.cast_ringChar, map_zero])
  let φ : Λ →+* k := Ideal.Quotient.mk 𝔪
  let ψ : ULift.{u + 1} (ZMod ℓ) →+* k :=
    (ZMod.castHom (dvd_refl ℓ) k).comp ULift.ringEquiv.toRingHom
  let C := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)).obj (ModuleCat.of k k)
  let G := (homologyFunctor _ q).obj ((R((f)_*[ModuleCat.{u + 1} k])).obj
    ((singleFunctor _ 0).obj C))
  -- the case of `𝔽_ℓ`-coefficients
  have hF : Etale.DerivedCategory.constructibleHomology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) S
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
          ((ModuleCat.restrictScalars.{u + 1} ψ).obj (ModuleCat.of k k))))) := by
    have : Finite ((ModuleCat.restrictScalars.{u + 1} ψ).obj (ModuleCat.of k k)) :=
      inferInstanceAs (Finite k)
    refine constructibleHomology_rightDerivedLowerStar_constantSheaf_of_isMaximal f
      (fun 𝔫 h𝔫 ↦ ?_) _
    have h𝔫' : 𝔫 = ⊥ := (Ideal.eq_bot_or_top 𝔫).resolve_right h𝔫.ne_top
    exact (Etale.DerivedCategory.constructibleHomology _ S).prop_of_iso
      ((constantSheaf X.smallEtaleTopology _ ⋙ singleFunctor _ 0 ⋙ R((f)_*[_])).mapIso
        (Submodule.quotEquivOfEqBot 𝔫 h𝔫').toModuleIso.symm) (h ℓ hℓ)
  have hG : IsConstructibleSheaf G := by
    refine IsConstructibleSheaf.of_restrictScalars_ringHom ψ G ?_
    have : IsConstructibleSheaf ((homologyFunctor _ q).obj
        ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj ((singleFunctor _ 0).obj
          ((ModuleCat.restrictScalars.{u + 1} ψ ⋙ constantSheaf X.smallEtaleTopology
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj (ModuleCat.of k k))))) :=
      hF q
    have : IsConstructibleSheaf ((homologyFunctor _ q).obj
        ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj ((singleFunctor _ 0).obj
          ((Sheaf.restrictScalars X.smallEtaleTopology ψ).obj C)))) :=
      IsConstructibleSheaf.of_iso ((homologyFunctor _ q).mapIso
        ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).mapIso
          ((singleFunctor _ 0).mapIso
            ((constantSheafCompRestrictScalarsIso ψ X).app (ModuleCat.of k k)).symm)))
    exact IsConstructibleSheaf.of_iso
      ((restrictScalarsHomologyRightDerivedLowerStarIso ψ f C q).symm)
  have : IsConstructibleSheaf ((Sheaf.restrictScalars S.smallEtaleTopology φ).obj G) :=
    (isConstructibleSheaf_restrictScalars_iff 𝔪 G).2 hG
  let e : (ModuleCat.restrictScalars.{u + 1} φ).obj (ModuleCat.of k k) ≅
      ModuleCat.of Λ (Λ ⧸ 𝔪) :=
    LinearEquiv.toModuleIso
      { AddEquiv.refl k with
        map_smul' := fun r x ↦ (Algebra.smul_def r x).symm }
  exact IsConstructibleSheaf.of_iso (restrictScalarsHomologyRightDerivedLowerStarIso φ f C q ≪≫
    (homologyFunctor _ q).mapIso ((R((f)_*[ModuleCat.{u + 1} Λ])).mapIso
      ((singleFunctor _ 0).mapIso ((constantSheafCompRestrictScalarsIso φ X).app
        (ModuleCat.of k k) ≪≫
        (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso e))))

end Etale

end AlgebraicGeometry
