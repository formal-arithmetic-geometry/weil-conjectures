/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import WeilConjectures.ConstructibleSheaf.RestrictScalars
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage

/-!
# Higher direct images of finite constant sheaves by dévissage

Let `f : X ⟶ S` be a morphism of schemes and `Λ` a finite ring whose exponent is invertible on
`S`. If the higher direct images `Rᵠf_* 𝔽_ℓ` are constructible for every prime `ℓ` invertible on
`S`, then so are the higher direct images `Rᵠf_* M` of the constant sheaf on every finite
`Λ`-module `M`
(`AlgebraicGeometry.Etale.constructibleHomology_rightDerivedLowerStar_constantSheaf_of_zmod`).
This is the proof of `cor-fin-projective-curve-finite-group` from
`thm-fin-projective-curve-constant`: a finite module has a finite filtration whose successive
quotients are killed by primes, the constant sheaf functor is exact, and complexes with
constructible homology form a triangulated subcategory. A module killed by a prime `ℓ` is a
module over the finite `𝔽_ℓ`-algebra `Λ ⧸ ℓ`, and its constant sheaf is compared with constant
sheaves of `𝔽_ℓ`-modules by restriction of scalars, which commutes with the higher direct
images (`AlgebraicGeometry.Etale.restrictScalarsHomologyRightDerivedLowerStarIso`) and, between
finite rings, reflects constructibility
(`AlgebraicGeometry.Scheme.isConstructibleSheaf_of_restrictScalars`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Scheme

variable {R R' : Type (u + 1)} [CommRing R] [CommRing R'] (φ : R →+* R') {X : Scheme.{u}}

/-- For a morphism `φ : R →+* R'` of finite rings, a sheaf of `R'`-modules whose restriction of
scalars to `R` is finite locally constant is finite locally constant: its underlying sheaf of sets
is finite locally constant (`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_forget`). -/
lemma IsFiniteLocallyConstantSheaf.of_restrictScalars_of_finite [Finite R] [Finite R']
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R'))
    [h : IsFiniteLocallyConstantSheaf ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj G)] :
    IsFiniteLocallyConstantSheaf G := by
  refine IsFiniteLocallyConstantSheaf.of_forget G ⟨?_, ⟨fun Ω _ _ s ↦ ?_⟩⟩
  · obtain ⟨⟨𝒰, h𝒰⟩⟩ := h.toIsLocallyConstantSheaf.nonempty_locallyConstantDatum
    refine ⟨𝒰, fun i ↦ ?_⟩
    have := h𝒰 i
    exact inferInstanceAs (((sheafCompose _ (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj
      (((Sheaf.restrictScalars X.smallEtaleTopology φ).obj G).over _)).IsConstant _)
  · have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget (ModuleCat.{u + 1} R)) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    have hfg := h.isFinitelyGenerated_sheafFiber Ω s
    rw [ModuleCat.isFinitelyGenerated_iff] at hfg
    have : Finite (((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} R)).obj
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj G)) :=
      Module.finite_of_finite R
    rw [ConcreteCategory.isFinitelyGenerated_iff_finite]
    exact @Finite.of_equiv _ _ this (((pointSmallEtale s).sheafFiberCompIso
      (CategoryTheory.forget (ModuleCat.{u + 1} R))).app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj G)).symm.toEquiv

/-- **Restriction of scalars between finite rings reflects constructibility.** For a morphism
`φ : R →+* R'` of finite rings, a sheaf of `R'`-modules whose restriction of scalars to `R` is
constructible is constructible: pullback to the strata commutes with restriction of scalars
(`AlgebraicGeometry.Etale.isIso_upperStarRestrictScalars`). -/
theorem isConstructibleSheaf_of_restrictScalars [Finite R] [Finite R']
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R'))
    (h : IsConstructibleSheaf ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj G)) :
    IsConstructibleSheaf G := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun i ↦ ?_⟩
  have : IsFiniteLocallyConstantSheaf ((Etale.upperStar (ModuleCat.{u + 1} R)
      (S.immersion i)).obj ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj G)) := hS i
  have : IsFiniteLocallyConstantSheaf ((Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
      Etale.upperStar (ModuleCat.{u + 1} R) (S.immersion i)).obj G) := hS i
  have : IsFiniteLocallyConstantSheaf ((Sheaf.restrictScalars _ φ).obj
      ((Etale.upperStar (ModuleCat.{u + 1} R') (S.immersion i)).obj G)) :=
    IsFiniteLocallyConstantSheaf.of_iso
      (asIso ((Etale.upperStarRestrictScalars φ (S.immersion i)).natTrans.app G))
  exact IsFiniteLocallyConstantSheaf.of_restrictScalars_of_finite φ _

end Scheme

namespace Etale

open _root_.DerivedCategory

section RestrictScalars

variable {R R' : Type (u + 1)} [CommRing R] [CommRing R'] (φ : R →+* R') {X S : Scheme.{u}}
  (f : X ⟶ S)

/-- **Restriction of scalars commutes with the higher direct images**: for a ring morphism
`φ : R →+* R'` and a sheaf `G` of `R'`-modules, `res(Rᵠf_* G) ≅ Rᵠf_*(res G)`
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarRestrictScalars`). -/
noncomputable def restrictScalarsHomologyRightDerivedLowerStarIso (q : ℤ)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R')) :
    (Sheaf.restrictScalars S.smallEtaleTopology φ).obj ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} R'])).obj ((singleFunctor _ 0).obj G))) ≅
    (homologyFunctor _ q).obj ((R((f)_*[ModuleCat.{u + 1} R])).obj
      ((singleFunctor _ 0).obj ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj G))) :=
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G
  (Sheaf.restrictScalars S.smallEtaleTopology φ).mapIso ((homologyFunctor _ q).mapIso
      (((f)_*[ModuleCat.{u + 1} R']).rightDerivedFunctorPlusCompatibility.app K).symm) ≪≫
    ((Sheaf.restrictScalars S.smallEtaleTopology φ).mapDerivedCategoryPlusHomologyFunctorIso
      q).app _ ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (asIso ((rightDerivedLowerStarRestrictScalars φ f).app K)) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      (((f)_*[ModuleCat.{u + 1} R]).rightDerivedFunctorPlus.mapIso
        (((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlusSingleFunctor
          0).app G)) ≪≫
    (homologyFunctor _ q).mapIso
      (((f)_*[ModuleCat.{u + 1} R]).rightDerivedFunctorPlusCompatibility.app _)

/-- Restriction of scalars of a constant sheaf is the constant sheaf on the restricted module. -/
noncomputable def restrictScalarsConstantSheafIso (M : ModuleCat.{u + 1} R') :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R')).obj M) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)).obj
        ((ModuleCat.restrictScalars.{u + 1} φ).obj M) :=
  haveI : X.smallEtaleTopology.PreservesSheafification (ModuleCat.restrictScalars.{u + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction _
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  (constantCommuteCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} φ)).app M

end RestrictScalars

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Dévissage of constant coefficients.** If `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` is a short exact sequence
of `Λ`-modules and the higher direct images of the constant sheaves `M₁` and `M₃` are
constructible, so are those of `M₂`: the constant sheaf functor is exact, and complexes with
constructible homology form a triangulated subcategory. -/
lemma constructibleHomology_rightDerivedLowerStar_constantSheaf_of_shortExact
    {T : ShortComplex (ModuleCat.{u + 1} Λ)} (hT : T.ShortExact)
    (h₁ : Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₁))))
    (h₃ : Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₃)))) :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj T.X₂))) := by
  let P := (Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S).inverseImage
    (R((f)_*[ModuleCat.{u + 1} Λ]))
  have hT' := (hT.map_of_exact
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).singleTriangle_distinguished
  exact P.ext_of_isTriangulatedClosed₂ _ hT' h₁ h₃

omit [Finite Λ] in
/-- The higher direct images of the constant sheaf on a trivial module vanish. -/
lemma constructibleHomology_rightDerivedLowerStar_constantSheaf_of_subsingleton
    (M : ModuleCat.{u + 1} Λ) [Subsingleton M] :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := fun q ↦
  IsConstructibleSheaf.of_isZero ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    singleFunctor _ 0 ⋙ R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ homologyFunctor _ q).map_isZero
      (ModuleCat.isZero_of_subsingleton M))

/-- **Induction along cyclic submodules of prime order.** Suppose the higher direct images of the
constant sheaf are constructible on every cyclic submodule `Λ ∙ m` of a finite `Λ`-module, where
`m` has prime additive order. Then they are constructible on every finite `Λ`-module. -/
lemma constructibleHomology_rightDerivedLowerStar_constantSheaf_of_span
    (h : ∀ (M : ModuleCat.{u + 1} Λ) [Finite M] (m : M), (addOrderOf m).Prime →
      Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
        ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
            (ModuleCat.of Λ (Submodule.span Λ {m}))))))
    (M : ModuleCat.{u + 1} Λ) [Finite M] :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  induction hn : Nat.card M using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  rcases subsingleton_or_nontrivial M with hM | hM
  · exact constructibleHomology_rightDerivedLowerStar_constantSheaf_of_subsingleton f M
  obtain ⟨ℓ, hℓ, hℓM⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := M)).ne'
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨m, hm⟩ := exists_prime_addOrderOf_dvd_card' ℓ hℓM
  let N := Submodule.span Λ {m}
  let T := ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ (by ext; simp)
  have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T (LinearMap.exact_subtype_mkQ N)
    Subtype.val_injective N.mkQ_surjective
  have : Finite (M ⧸ N) := Finite.of_surjective _ N.mkQ_surjective
  refine constructibleHomology_rightDerivedLowerStar_constantSheaf_of_shortExact f hT
    (h M m (hm ▸ hℓ)) (ih _ ?_ (ModuleCat.of Λ (M ⧸ N)) rfl)
  have hcard := N.card_eq_card_quotient_mul_card
  have hN : 1 < Nat.card N := by
    have : Nontrivial N := ⟨⟨0, ⟨m, Submodule.mem_span_singleton_self m⟩, fun h0 ↦ by
      have : m = 0 := congrArg Subtype.val h0.symm
      rw [this, addOrderOf_zero] at hm
      exact hℓ.one_lt.ne' hm.symm⟩⟩
    exact Finite.one_lt_card
  have hpos : 0 < Nat.card (M ⧸ N) := Nat.card_pos
  subst hn
  change Nat.card (M ⧸ N) < Nat.card M
  have : Nat.card M = Nat.card N * Nat.card (M ⧸ N) := hcard
  rw [this]
  exact lt_mul_of_one_lt_left hpos hN

/-- The higher direct images of the constant sheaf `𝔽_ℓ` along `f`, for the coefficients
`ULift (ZMod ℓ)`, are constructible. This is the hypothesis of the dévissage, provided by
`thm-fin-projective-curve-constant` for projective families of curves. -/
def ZModDirectImagesConstructible (ℓ : ℕ) : Prop :=
  ∀ q : ℤ, IsConstructibleSheaf ((homologyFunctor _ q).obj
    ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj
      ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj
          (ModuleCat.of _ (ULift.{u + 1} (ZMod ℓ)))))))

omit [Finite Λ] in
/-- The higher direct images of constant sheaves are transported along isomorphisms of
modules. -/
lemma constructibleHomology_rightDerivedLowerStar_constantSheaf_of_iso
    {M N : ModuleCat.{u + 1} Λ} (e : M ≅ N)
    (h : Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N))) := fun q ↦
  let Φ := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
    singleFunctor _ 0 ⋙ R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ homologyFunctor _ q
  have : IsConstructibleSheaf (Φ.obj M) := h q
  IsConstructibleSheaf.of_iso (Φ.mapIso e)

/-- **Finite `𝔽_ℓ`-modules.** If the higher direct images of `𝔽_ℓ` are constructible, so are
those of the constant sheaf on every finite `𝔽_ℓ`-module, which is a successive extension of
copies of `𝔽_ℓ`. -/
lemma constructibleHomology_rightDerivedLowerStar_constantSheaf_zmod (ℓ : ℕ) [Fact ℓ.Prime]
    (h : ZModDirectImagesConstructible f ℓ) (M : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))
    [Finite M] :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))) S
      ((R((f)_*[ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ))])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod ℓ)))).obj M))) := by
  refine constructibleHomology_rightDerivedLowerStar_constantSheaf_of_span f
    (fun N _ m hm ↦ ?_) M
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hm
    exact Nat.not_prime_one hm
  exact constructibleHomology_rightDerivedLowerStar_constantSheaf_of_iso f
    (LinearEquiv.toModuleIso (LinearEquiv.toSpanNonzeroSingleton _ N m hm0)) h

/-- **Modules killed by a prime.** Let `ℓ` be a prime and `N` a finite `Λ`-module killed by `ℓ`.
If the higher direct images of `𝔽_ℓ` along `f` are constructible, so are those of the constant
sheaf `N`: it is a sheaf of modules over the finite ring `Λ ⧸ ℓ`, whose underlying sheaf of
`𝔽_ℓ`-modules is the constant sheaf on a finite `𝔽_ℓ`-module, and restriction of scalars
commutes with the higher direct images. -/
lemma constructibleHomology_rightDerivedLowerStar_constantSheaf_of_smul_eq_zero (ℓ : ℕ)
    [Fact ℓ.Prime] (h : ZModDirectImagesConstructible f ℓ) (N : ModuleCat.{u + 1} Λ)
    [Finite N] (hN : ∀ x : N, (ℓ : Λ) • x = 0) :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N))) := by
  let J : Ideal Λ := Ideal.span {(ℓ : Λ)}
  have hJ : Module.IsTorsionBySet Λ N J :=
    (Module.isTorsionBySet_span_singleton_iff _).2 fun x ↦ hN x
  let : Module (Λ ⧸ J) N := hJ.module
  let N' : ModuleCat.{u + 1} (Λ ⧸ J) := ModuleCat.of (Λ ⧸ J) N
  let eN : (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk J)).obj N' ≅ N :=
    LinearEquiv.toModuleIso
      { toFun x := (x : N)
        invFun x := x
        map_add' _ _ := rfl
        map_smul' r x := hJ.mk_smul r (x : N)
        left_inv _ := rfl
        right_inv _ := rfl }
  let ι : ULift.{u + 1} (ZMod ℓ) →+* Λ ⧸ J :=
    ((Ideal.Quotient.lift (Ideal.span {(ℓ : ℤ)}) (Int.castRingHom (Λ ⧸ J)) fun a ha ↦ by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [eq_intCast, Int.cast_mul, Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk J),
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_singleton _)), mul_zero]).comp
      (Int.quotientSpanNatEquivZMod ℓ).symm.toRingHom).comp ULift.ringEquiv.toRingHom
  have : Finite (Λ ⧸ J) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  have : Finite ((ModuleCat.restrictScalars.{u + 1} ι).obj N') := ‹Finite N›
  have hF := constructibleHomology_rightDerivedLowerStar_constantSheaf_zmod f ℓ h
    ((ModuleCat.restrictScalars.{u + 1} ι).obj N')
  refine constructibleHomology_rightDerivedLowerStar_constantSheaf_of_iso f eN fun q ↦ ?_
  have hG : IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} (Λ ⧸ J)])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ J))).obj N')))) := by
    refine isConstructibleSheaf_of_restrictScalars ι _ ?_
    have := hF q
    exact IsConstructibleSheaf.of_iso ((homologyFunctor _ q).mapIso
      ((R((f)_*[ModuleCat.{u + 1} _])).mapIso ((singleFunctor _ 0).mapIso
        (restrictScalarsConstantSheafIso ι N').symm)) ≪≫
      (restrictScalarsHomologyRightDerivedLowerStarIso ι f q _).symm)
  have := (isConstructibleSheaf_restrictScalars_iff J _).2 hG
  exact IsConstructibleSheaf.of_iso (restrictScalarsHomologyRightDerivedLowerStarIso
    (Ideal.Quotient.mk J) f q _ ≪≫ (homologyFunctor _ q).mapIso
      ((R((f)_*[ModuleCat.{u + 1} _])).mapIso ((singleFunctor _ 0).mapIso
        (restrictScalarsConstantSheafIso (Ideal.Quotient.mk J) N'))))

/-- **Dévissage to `𝔽_ℓ`-coefficients.** Let `Λ` be a finite ring whose exponent is invertible on
`S`. If the higher direct images of `𝔽_ℓ` along `f : X ⟶ S` are constructible for every prime
`ℓ` invertible on `S`, then the higher direct images of the constant sheaf on every finite
`Λ`-module are constructible. -/
theorem constructibleHomology_rightDerivedLowerStar_constantSheaf_of_zmod
    [HasInvertibleExponent Λ S]
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : Γ(S, ⊤)) → ZModDirectImagesConstructible f ℓ)
    (M : ModuleCat.{u + 1} Λ) [Finite M] :
    Etale.DerivedCategory.constructibleHomology (ModuleCat.{u + 1} Λ) S
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))) := by
  obtain ⟨n, -, hn, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := S)
  refine constructibleHomology_rightDerivedLowerStar_constantSheaf_of_span f
    (fun N _ m hm ↦ ?_) M
  have : Fact (addOrderOf m).Prime := ⟨hm⟩
  have hdvd : addOrderOf m ∣ n := addOrderOf_dvd_of_nsmul_eq_zero (by
    rw [← Nat.cast_smul_eq_nsmul Λ, hn, zero_smul])
  have hℓ : IsUnit ((addOrderOf m : ℕ) : Γ(S, ⊤)) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast hdvd) hu
  refine constructibleHomology_rightDerivedLowerStar_constantSheaf_of_smul_eq_zero f
    (addOrderOf m) (h _ hℓ) _ fun x ↦ ?_
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 x.2
  ext
  change (addOrderOf m : Λ) • (x : N) = 0
  rw [← ha, smul_comm, Nat.cast_smul_eq_nsmul, addOrderOf_nsmul_eq_zero, smul_zero]

end Etale

end AlgebraicGeometry
