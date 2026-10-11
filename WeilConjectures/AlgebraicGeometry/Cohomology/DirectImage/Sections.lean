/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Cohomology.AcyclicResolution
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
public import WeilConjectures.AlgebraicGeometry.Cohomology.InjectiveFlasque

/-!
# Sections of higher direct images over an affine base

Over an affine base, the sections of `R^q f_* ℱ` are the cohomology `H^q(X, ℱ)` for a
quasi-compact separated morphism and a quasi-coherent `ℱ`. Also the compatibility of higher
direct images with flat base change and with restriction to opens, their quasi-coherence, and
their vanishing in high degrees.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

variable {X T : Scheme.{u}}
variable (f : X ⟶ T) (ℱ : X.Modules)

section QuasiCoherence

variable [QuasiCompact f] [QuasiSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

/-- **Quasi-coherence of the higher direct images.** For `f : X ⟶ T` quasi-compact and
quasi-separated and `ℱ` a quasi-coherent `𝒪_X`-module, the higher direct image `R^q f_* ℱ` is a
quasi-coherent `𝒪_T`-module for every `q` [Stacks, Tag 01XJ].

(blueprint: `sk-thm-picard-coherence`) -/
theorem isQuasicoherent_higherDirectImage (q : ℕ) :
    ((higherDirectImage f q).obj ℱ).IsQuasicoherent :=
  sorry

end QuasiCoherence
section Comparison

/-- Global sections along an isomorphism of `𝒪_X`-modules. -/
noncomputable def appTopAddEquiv {M N : X.Modules} (e : M ≅ N) : Γ(M, ⊤) ≃+ Γ(N, ⊤) :=
  ((Modules.toPresheaf X).mapIso e).app (Opposite.op ⊤) |>.addCommGroupIsoToAddEquiv

/-- The pushforward of an injective `𝒪_X`-module is acyclic, being flasque. -/
lemma subsingleton_H_pushforward_of_injective (I : X.Modules) [Injective I] (m : ℕ) :
    Subsingleton (((pushforward f).obj I).H (m + 1)) :=
  have := isFlasque_of_injective I
  have : TopCat.Presheaf.IsFlasque
      ((SheafOfModules.toSheaf T.ringCatSheaf).obj ((pushforward f).obj I)).obj :=
    inferInstanceAs (TopCat.Presheaf.IsFlasque
      (f.base _* ((SheafOfModules.toSheaf X.ringCatSheaf).obj I).obj))
  TopCat.Sheaf.IsFlasque.subsingleton_H m
    ((SheafOfModules.toSheaf T.ringCatSheaf).obj ((pushforward f).obj I))

/-- The module resolved by an injective resolution is its zeroth cycles. -/
noncomputable def _root_.CategoryTheory.InjectiveResolution.isoCyclesZero {C : Type*}
    [Category* C] [Abelian C] {Z : C} (I : InjectiveResolution Z) : Z ≅ I.cocomplex.cycles 0 :=
  IsLimit.conePointUniqueUpToIso I.isLimitKernelFork (I.cocomplex.cyclesIsKernel 0 1 (by simp))

variable [IsAffine T] [QuasiCompact f] [IsSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

/-- The cohomology sheaves of `f_* I`, for an injective resolution `I` of `ℱ`, are the higher
direct images of `ℱ`; over the affine `T` they are acyclic, being quasi-coherent. -/
lemma subsingleton_H_homology_pushforward (I : InjectiveResolution ℱ) (q m : ℕ) :
    Subsingleton ((HomologicalComplex.homology
      (((pushforward f).mapHomologicalComplex _).obj I.cocomplex) q).H (m + 1)) :=
  have := isQuasicoherent_higherDirectImage f ℱ q
  have : Subsingleton ((((pushforward f).rightDerived q).obj ℱ).H (m + 1)) :=
    subsingleton_H_succ_of_isAffine ((higherDirectImage f q).obj ℱ) m
  subsingleton_H_of_iso (I.isoRightDerivedObj (pushforward f) q) (m + 1)

/-- **`Γ(T, R^{n+1} f_* ℱ) ≅ H^{n+1}(X, ℱ)`** computed with an injective resolution `I` of `ℱ`:
`Γ(T, Hⁿ⁺¹(f_* I)) = Hⁿ⁺¹(Γ(X, I)) = Hⁿ⁺¹(X, ℱ)`, the first identification because the terms
and the cohomology sheaves of `f_* I` are acyclic on the affine `T`, the second because the terms
of `I` are acyclic. -/
noncomputable def sectionsHigherDirectImageSuccAddEquiv (I : InjectiveResolution ℱ) (n : ℕ) :
    Γ((higherDirectImage f (n + 1)).obj ℱ, ⊤) ≃+ ℱ.H (n + 1) :=
  let L := ((pushforward f).mapHomologicalComplex _).obj I.cocomplex
  have hL : ∀ j m, Subsingleton ((L.X j).H (m + 1)) := fun j m ↦
    subsingleton_H_pushforward_of_injective f (I.cocomplex.X j) m
  (appTopAddEquiv (I.isoRightDerivedObj (pushforward f) (n + 1))).trans <|
  (homologySectionsAddEquiv L hL (subsingleton_H_homology_pushforward f ℱ I) n).trans <|
  (cyclesQuotientAddEquiv L n).trans <|
  (AddEquiv.refl (sectionsCycles I.cocomplex n ⧸ sectionsBoundaries I.cocomplex n)).trans <|
  (cyclesQuotientAddEquiv I.cocomplex n).symm.trans <|
  (H.cyclesZeroSuccAddEquiv I.cocomplex I.cocomplex_exactAt_succ
    (fun _ m ↦ subsingleton_H_of_injective _ m) n).symm.trans <|
  H.mapAddEquiv I.isoCyclesZero.symm (n + 1)

lemma sectionsHigherDirectImageSuccAddEquiv_apply (I : InjectiveResolution ℱ) (n : ℕ)
    (x : Γ((higherDirectImage f (n + 1)).obj ℱ, ⊤)) :
    sectionsHigherDirectImageSuccAddEquiv f ℱ I n x =
      H.map I.isoCyclesZero.inv (n + 1) ((H.cyclesZeroSuccAddEquiv I.cocomplex
        I.cocomplex_exactAt_succ (fun _ m ↦ subsingleton_H_of_injective _ m) n).symm
        ((cyclesQuotientAddEquiv I.cocomplex n).symm
          (cyclesQuotientAddEquiv (((pushforward f).mapHomologicalComplex _).obj I.cocomplex) n
            (homologySectionsAddEquiv (((pushforward f).mapHomologicalComplex _).obj I.cocomplex)
              (fun j m ↦ subsingleton_H_pushforward_of_injective f (I.cocomplex.X j) m)
              (subsingleton_H_homology_pushforward f ℱ I) n
              (((I.isoRightDerivedObj (pushforward f) (n + 1)).hom.app ⊤) x))))) :=
  rfl

omit [IsAffine T] [QuasiCompact f] [IsSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] in
@[reassoc]
lemma _root_.CategoryTheory.InjectiveResolution.isoCyclesZero_hom_iCycles {C : Type*}
    [Category* C] [Abelian C] {Z : C} (I : InjectiveResolution Z) :
    I.isoCyclesZero.hom ≫ I.cocomplex.iCycles 0 = I.ι.f 0 :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

omit [IsAffine T] [QuasiCompact f] [IsSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] in
lemma _root_.CategoryTheory.InjectiveResolution.isoCyclesZero_inv_naturality {C : Type*}
    [Category* C] [Abelian C] {Y Z : C} (g : Z ⟶ Y) (I : InjectiveResolution Y)
    (J : InjectiveResolution Z) :
    J.isoCyclesZero.inv ≫ g =
      HomologicalComplex.cyclesMap (InjectiveResolution.desc g I J) 0 ≫ I.isoCyclesZero.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, ← cancel_mono (I.cocomplex.iCycles 0)]
  simp [InjectiveResolution.isoCyclesZero_hom_iCycles_assoc,
    InjectiveResolution.isoCyclesZero_hom_iCycles]

set_option maxHeartbeats 1600000 in
-- identifying sections of `f_* Iⁿ` and of `Iⁿ` over `⊤` unfolds `f ⁻¹ᵁ ⊤`
/-- The comparison `Γ(T, R^{n+1} f_* ℱ) ≅ H^{n+1}(X, ℱ)` is natural in `ℱ`. -/
lemma sectionsHigherDirectImageSuccAddEquiv_naturality (𝒢 : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢] (φ : ℱ ⟶ 𝒢)
    (I : InjectiveResolution ℱ) (J : InjectiveResolution 𝒢) (n : ℕ)
    (x : Γ((higherDirectImage f (n + 1)).obj ℱ, ⊤)) :
    sectionsHigherDirectImageSuccAddEquiv f 𝒢 J n
        (((higherDirectImage f (n + 1)).map φ).app ⊤ x) =
      H.map φ (n + 1) (sectionsHigherDirectImageSuccAddEquiv f ℱ I n x) := by
  let ψ := InjectiveResolution.desc φ J I
  let χ := ((pushforward f).mapHomologicalComplex _).map ψ
  have hK := I.cocomplex_exactAt_succ
  have hK' := J.cocomplex_exactAt_succ
  have hacyc : ∀ j m, Subsingleton ((I.cocomplex.X j).H (m + 1)) :=
    fun _ m ↦ subsingleton_H_of_injective _ m
  have hacyc' : ∀ j m, Subsingleton ((J.cocomplex.X j).H (m + 1)) :=
    fun _ m ↦ subsingleton_H_of_injective _ m
  have hL : ∀ j m, Subsingleton
      (((((pushforward f).mapHomologicalComplex _).obj I.cocomplex).X j).H (m + 1)) :=
    fun j m ↦ subsingleton_H_pushforward_of_injective f (I.cocomplex.X j) m
  have hL' : ∀ j m, Subsingleton
      (((((pushforward f).mapHomologicalComplex _).obj J.cocomplex).X j).H (m + 1)) :=
    fun j m ↦ subsingleton_H_pushforward_of_injective f (J.cocomplex.X j) m
  -- the derived functor side
  have h1 : ((J.isoRightDerivedObj (pushforward f) (n + 1)).hom.app ⊤)
      (((higherDirectImage f (n + 1)).map φ).app ⊤ x) =
      ((HomologicalComplex.homologyMap χ (n + 1)).app ⊤)
        (((I.isoRightDerivedObj (pushforward f) (n + 1)).hom.app ⊤) x) := by
    change ((((pushforward f).rightDerived (n + 1)).map φ ≫
      (J.isoRightDerivedObj (pushforward f) (n + 1)).hom).app ⊤) x = _
    rw [InjectiveResolution.isoRightDerivedObj_hom_naturality φ I J ψ
      (InjectiveResolution.desc_commutes_zero φ J I)]
    rfl
  let LI := ((pushforward f).mapHomologicalComplex _).obj I.cocomplex
  let a := homologySectionsAddEquiv LI hL (subsingleton_H_homology_pushforward f ℱ I) n
    (((I.isoRightDerivedObj (pushforward f) (n + 1)).hom.app ⊤) x)
  let b : sectionsCycles I.cocomplex n ⧸ sectionsBoundaries I.cocomplex n :=
    cyclesQuotientAddEquiv LI n a
  let c := (cyclesQuotientAddEquiv I.cocomplex n).symm b
  let w := (H.cyclesZeroSuccAddEquiv I.cocomplex hK hacyc n).symm c
  have hc : (cyclesQuotientAddEquiv J.cocomplex n).symm
      (QuotientAddGroup.map _ _ (sectionsCyclesMap ψ n) (sectionsBoundaries_le_comap ψ n) b) =
      QuotientAddGroup.map _ _ ((HomologicalComplex.cyclesMap ψ (n + 1)).app ⊤).hom
        (range_app_toCycles_le_comap ψ n) c := by
    rw [AddEquiv.symm_apply_eq, cyclesQuotientAddEquiv_naturality, AddEquiv.apply_symm_apply]
  have hw : (H.cyclesZeroSuccAddEquiv J.cocomplex hK' hacyc' n).symm
      (QuotientAddGroup.map _ _ ((HomologicalComplex.cyclesMap ψ (n + 1)).app ⊤).hom
        (range_app_toCycles_le_comap ψ n) c) =
      H.map (HomologicalComplex.cyclesMap ψ 0) (n + 1) w := by
    rw [AddEquiv.symm_apply_eq, H.cyclesZeroSuccAddEquiv_naturality ψ hK hacyc hK' hacyc',
      AddEquiv.apply_symm_apply]
  have hc' : (cyclesQuotientAddEquiv J.cocomplex n).symm
      (QuotientAddGroup.map _ _ (sectionsCyclesMap χ n) (sectionsBoundaries_le_comap χ n)
        (cyclesQuotientAddEquiv LI n a)) =
      QuotientAddGroup.map _ _ ((HomologicalComplex.cyclesMap ψ (n + 1)).app ⊤).hom
        (range_app_toCycles_le_comap ψ n) c := hc
  have key : (H.cyclesZeroSuccAddEquiv J.cocomplex hK' hacyc' n).symm
      ((cyclesQuotientAddEquiv J.cocomplex n).symm
        (QuotientAddGroup.map _ _ (sectionsCyclesMap χ n) (sectionsBoundaries_le_comap χ n)
          (cyclesQuotientAddEquiv LI n a))) =
      H.map (HomologicalComplex.cyclesMap ψ 0) (n + 1) w := by
    rw [hc', hw]
  rw [sectionsHigherDirectImageSuccAddEquiv_apply, sectionsHigherDirectImageSuccAddEquiv_apply, h1,
    homologySectionsAddEquiv_naturality χ hL (subsingleton_H_homology_pushforward f ℱ I) hL'
      (subsingleton_H_homology_pushforward f 𝒢 J), cyclesQuotientAddEquiv_naturality χ, key,
    ← H.map_comp_apply, ← H.map_comp_apply, InjectiveResolution.isoCyclesZero_inv_naturality]


/-- **`Γ(T, R⁰ f_* ℱ) ≅ H⁰(X, ℱ)`**: both are the global sections of `ℱ`. -/
noncomputable def sectionsHigherDirectImageZeroAddEquiv :
    Γ((higherDirectImage f 0).obj ℱ, ⊤) ≃+ ℱ.H 0 :=
  (appTopAddEquiv ((pushforward f).rightDerivedZeroIsoSelf.app ℱ)).trans
    (H.zeroLinearEquiv ℱ).symm.toAddEquiv

omit [IsAffine T] [QuasiCompact f] [IsSeparated f]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] in
lemma sectionsHigherDirectImageZeroAddEquiv_naturality (𝒢 : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢] (φ : ℱ ⟶ 𝒢)
    (x : Γ((higherDirectImage f 0).obj ℱ, ⊤)) :
    sectionsHigherDirectImageZeroAddEquiv f 𝒢 (((higherDirectImage f 0).map φ).app ⊤ x) =
      H.map φ 0 (sectionsHigherDirectImageZeroAddEquiv f ℱ x) := by
  have h : (((pushforward f).rightDerivedZeroIsoSelf.app 𝒢).hom.app ⊤)
      (((higherDirectImage f 0).map φ).app ⊤ x) =
      (((pushforward f).map φ).app ⊤)
        (((pushforward f).rightDerivedZeroIsoSelf.app ℱ).hom.app ⊤ x) := by
    change ((((pushforward f).rightDerived 0).map φ ≫
      ((pushforward f).rightDerivedZeroIsoSelf.app 𝒢).hom).app ⊤) x = _
    rw [Iso.app_hom, (pushforward f).rightDerivedZeroIsoSelf.hom.naturality φ]
    rfl
  change (H.zeroLinearEquiv 𝒢).symm (((pushforward f).rightDerivedZeroIsoSelf.app 𝒢).hom.app ⊤
      (((higherDirectImage f 0).map φ).app ⊤ x)) =
    H.map φ 0 ((H.zeroLinearEquiv ℱ).symm
      (((pushforward f).rightDerivedZeroIsoSelf.app ℱ).hom.app ⊤ x))
  rw [h, LinearEquiv.symm_apply_eq, H.zeroLinearEquiv_map, LinearEquiv.apply_symm_apply]
  rfl

end Comparison

section RightDerivedGlobalSections

variable (X) in
/-- The global sections functor `X.Modules ⥤ Ab`. -/
noncomputable def globalSectionsFunctor : X.Modules ⥤ Ab.{u} :=
  Modules.toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (Opposite.op ⊤)

instance : (globalSectionsFunctor X).Additive where
  map_add := rfl

instance : PreservesFiniteLimits (globalSectionsFunctor X) :=
  have : PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤) ⋙
      forget₂ (ModuleCat Γ(X, ⊤)) Ab) := comp_preservesFiniteLimits _ _
  preservesFiniteLimits_of_natIso (Iso.refl _ :
    SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤) ⋙ forget₂ (ModuleCat Γ(X, ⊤)) Ab ≅
      globalSectionsFunctor X)

/-- In the complex of global sections of `K`, the image of `Γ(Kⁿ)` among the cocycles of degree
`n + 1` is the subgroup of coboundaries. -/
lemma range_abToCycles_globalSections (K : CochainComplex X.Modules ℕ) (n : ℕ) :
    AddMonoidHom.range
        ((((globalSectionsFunctor X).mapHomologicalComplex _).obj K).sc' n (n + 1)
          (n + 2)).abToCycles = sectionsBoundaries K n := by
  ext ⟨x, hx⟩
  simp only [AddMonoidHom.mem_range, AddSubgroup.mem_addSubgroupOf]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext hy⟩

variable [HasInjectiveResolutions X.Modules]

/-- **Sheaf cohomology is the right derived functor of global sections**:
`R^{n+1} Γ(X, ℱ) ≅ H^{n+1}(X, ℱ)`, computed with an injective resolution `I` of `ℱ`. Both sides
are the cohomology of the complex `Γ(X, I)`, the right side because injective `𝒪_X`-modules
are acyclic. -/
noncomputable def rightDerivedGlobalSectionsSuccAddEquiv (I : InjectiveResolution ℱ) (n : ℕ) :
    ((globalSectionsFunctor X).rightDerived (n + 1)).obj ℱ ≃+ ℱ.H (n + 1) :=
  let C := ((globalSectionsFunctor X).mapHomologicalComplex _).obj I.cocomplex
  ((I.isoRightDerivedObj (globalSectionsFunctor X) (n + 1)) ≪≫
    C.homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp) ≪≫
    (C.sc' n (n + 1) (n + 2)).abHomologyIso).addCommGroupIsoToAddEquiv.trans <|
  (QuotientAddGroup.quotientAddEquivOfEq
    (range_abToCycles_globalSections I.cocomplex n)).trans <|
  (cyclesQuotientAddEquiv I.cocomplex n).symm.trans <|
  (H.cyclesZeroSuccAddEquiv I.cocomplex I.cocomplex_exactAt_succ
    (fun _ m ↦ subsingleton_H_of_injective _ m) n).symm.trans <|
  H.mapAddEquiv I.isoCyclesZero.symm (n + 1)


/-- **Sheaf cohomology is the right derived functor of global sections**: for every `q`,
`R^q Γ(X, ℱ) ≅ H^q(X, ℱ)` (in degree `0` both sides are `Γ(X, ℱ)`). -/
theorem nonempty_rightDerived_globalSections_addEquiv_H (q : ℕ) :
    Nonempty (((globalSectionsFunctor X).rightDerived q).obj ℱ ≃+ ℱ.H q) := by
  cases q with
  | zero =>
    exact ⟨((globalSectionsFunctor X).rightDerivedZeroIsoSelf.app ℱ).addCommGroupIsoToAddEquiv.trans
      (H.zeroLinearEquiv ℱ).symm.toAddEquiv⟩
  | succ n => exact ⟨rightDerivedGlobalSectionsSuccAddEquiv ℱ (injectiveResolution ℱ) n⟩

end RightDerivedGlobalSections

/-- **The sections of the higher direct images over an affine base, naturally.** Over an affine
base, for `f` quasi-compact and separated, the global sections of `R^q f_* ℱ` are the sheaf
cohomology `H^q(X, ℱ)`, by additive isomorphisms natural in the quasi-coherent module `ℱ`.

This is the comparison between the right derived functors of `f_*` inside `X.Modules` and the
`Ext`-groups in abelian sheaves of `AlgebraicGeometry.Scheme.Modules.H`. It holds because
injective `𝒪_X`-modules are flasque, the pushforward of a flasque module is flasque, flasque
sheaves are acyclic for `H`, and, `T` being affine and `R^p f_* ℱ` quasi-coherent, the global
sections functor of `T` is exact on them [Stacks, Tags 01XJ and 0BDY]. -/
theorem exists_addEquiv_sections_higherDirectImage_H [IsAffine T] [QuasiCompact f]
    [IsSeparated f] [HasInjectiveResolutions X.Modules] (q : ℕ) :
    ∃ e : ∀ (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ],
        Γ((higherDirectImage f q).obj ℱ, ⊤) ≃+ ℱ.H q,
      ∀ (ℱ 𝒢 : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]
        [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) 𝒢] (φ : ℱ ⟶ 𝒢)
        (x : Γ((higherDirectImage f q).obj ℱ, ⊤)),
        e 𝒢 (((higherDirectImage f q).map φ).app ⊤ x) = H.map φ q (e ℱ x) := by
  cases q with
  | zero =>
    exact ⟨fun ℱ _ ↦ sectionsHigherDirectImageZeroAddEquiv f ℱ,
      fun ℱ 𝒢 _ _ φ x ↦ sectionsHigherDirectImageZeroAddEquiv_naturality f ℱ 𝒢 φ x⟩
  | succ n =>
    exact ⟨fun ℱ _ ↦ sectionsHigherDirectImageSuccAddEquiv f ℱ (injectiveResolution ℱ) n,
      fun ℱ 𝒢 _ _ φ x ↦ sectionsHigherDirectImageSuccAddEquiv_naturality f ℱ 𝒢 φ _ _ n x⟩

/-- **The sections of the higher direct images over an affine base, linearly.** Over an affine
base the global sections of the `q`-th higher direct image are the sheaf cohomology of `ℱ`,
`Γ(T, R^q f_* ℱ) ≅ H^q(X, ℱ)`, by an isomorphism which is linear along `f^♯ : Γ(T, ⊤) → Γ(X, ⊤)`.

This is the comparison between the two cohomology theories used in the Picard-framework block:
the right derived functors of `f_*` inside `X.Modules` on the one hand, and the `Ext`-groups in
abelian sheaves of `AlgebraicGeometry.Scheme.Modules.H` on the other. The additive comparison
is `AlgebraicGeometry.Scheme.Modules.exists_addEquiv_sections_higherDirectImage_H`; being natural
in `ℱ`, it is compatible with multiplication by global functions of `T`, which `R^q f_*` turns
into multiplication by their images in `Γ(X, ⊤)`
(`AlgebraicGeometry.Scheme.Modules.higherDirectImage_map_smulHom`).

Over `T = Spec κ` for a field `κ`, this is the identification of the `q`-th direct image to a
point with `H^q` as `κ`-vector spaces, used in the local model of the proof of
`thm-pc-semicontinuity-base-change`. -/
theorem exists_bijective_semilinearMap_sections_higherDirectImage_H [IsAffine T] [QuasiCompact f]
    [IsSeparated f] [HasInjectiveResolutions X.Modules]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ∃ e : Γ((higherDirectImage f q).obj ℱ, ⊤) →ₛₗ[f.appTop.hom] ℱ.H q, Function.Bijective e := by
  obtain ⟨e, he⟩ := exists_addEquiv_sections_higherDirectImage_H f q
  refine ⟨{ toFun := e ℱ, map_add' := map_add _, map_smul' := fun a x ↦ ?_ }, (e ℱ).bijective⟩
  have h : a • x = ((higherDirectImage f q).map (ℱ.smulHom (f.appTop a))).app ⊤ x := by
    rw [higherDirectImage_map_smulHom, smulHom_app_apply]
    congr 1
    exact (congrArg (fun φ ↦ φ a) (T.presheaf.map_id _)).symm
  rw [h, he]
  rfl

/-- Over an affine base the global sections of the `q`-th higher direct image are the sheaf
cohomology of `ℱ`: `Γ(T, R^q f_* ℱ) ≅ H^q(X, ℱ)`. See
`AlgebraicGeometry.Scheme.Modules.exists_bijective_semilinearMap_sections_higherDirectImage_H`
for the linearity of this isomorphism. -/
theorem nonempty_sections_higherDirectImage_iso_H [IsAffine T] [QuasiCompact f] [IsSeparated f]
    [HasInjectiveResolutions X.Modules]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (Γ((higherDirectImage f q).obj ℱ, ⊤) ≃+ ℱ.H q) :=
  have ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H f ℱ q
  ⟨AddEquiv.ofBijective e.toAddMonoidHom he⟩

/-- **The fibre dimension is the dimension of the direct image to the point.** For `f`
quasi-compact and separated, `h^q(t) = dim_{κ(t)} H^q(X_t, ℱ_t)` is the dimension of the global
sections of `R^q (f_t)_* ℱ_t` for the fibre `f_t : X_t ⟶ Spec κ(t)`, as a vector space over the
field `Γ(Spec κ(t), ⊤) ≅ κ(t)`. -/
theorem hFiber_eq_finrank_sections_higherDirectImage [QuasiCompact f] [IsSeparated f] (t : T)
    [HasInjectiveResolutions (f.fiber t).Modules]
    [SheafOfModules.IsQuasicoherent (R := (f.fiber t).ringCatSheaf)
      ((Modules.pullback (f.fiberι t)).obj ℱ)] (q : ℕ) :
    ℱ.hFiber f q t = Module.finrank Γ(Spec (T.residueField t), ⊤)
      Γ((higherDirectImage (f.fiberToSpecResidueField t) q).obj
        ((Modules.pullback (f.fiberι t)).obj ℱ), ⊤) := by
  have : IsSeparated (f.fiberToSpecResidueField t) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  have : QuasiCompact (f.fiberToSpecResidueField t) := by
    unfold Scheme.Hom.fiberToSpecResidueField
    infer_instance
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H
    (f.fiberToSpecResidueField t) ((Modules.pullback (f.fiberι t)).obj ℱ) q
  let j := (AddEquiv.ofBijective e.toAddMonoidHom he).symm
  let := f.fiberOverSpecResidueField t
  refine congrArg Cardinal.toNat (rank_eq_of_equiv_equiv _ j
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (T.residueField t)).inv) ?_)
  intro c h
  obtain ⟨y, rfl⟩ := he.2 h
  have hc : c • e y = e ((Scheme.ΓSpecIso (T.residueField t)).inv c • y) := by
    rw [smul_H_eq_globalSectionsRingHom_smul, e.map_smulₛₗ]
    rfl
  have hj (z) : j (e z) = z := (AddEquiv.ofBijective e.toAddMonoidHom he).symm_apply_apply z
  rw [hc, hj, hj]

/-- **The direct images to the spectrum of a field.** For a scheme `X` over a field `K`, with
structure morphism quasi-compact and separated, and a quasi-coherent `𝒪_X`-module `ℱ`, the
global sections of `R^q f_* ℱ` are `H^q(X, ℱ)` as `K`-vector spaces. This is
`AlgebraicGeometry.Scheme.Modules.exists_bijective_semilinearMap_sections_higherDirectImage_H`
over `Spec K`, where `K` acts on both sides through `Γ(Spec K, ⊤)`. -/
theorem nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H (K : Type u) [Field K]
    [X.Over (Spec (.of K))] [QuasiCompact (X ↘ Spec (.of K))] [IsSeparated (X ↘ Spec (.of K))]
    [HasInjectiveResolutions X.Modules]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty ((moduleSpecΓFunctor (R := .of K)).obj
      ((higherDirectImage (X ↘ Spec (.of K)) q).obj ℱ) ≃ₗ[K] ℱ.H q) := by
  obtain ⟨e, he⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H
    (X ↘ Spec (.of K)) ℱ q
  let M := (moduleSpecΓFunctor (R := .of K)).obj ((higherDirectImage (X ↘ Spec (.of K)) q).obj ℱ)
  refine ⟨LinearEquiv.ofBijective (M := M)
    { toFun := e, map_add' := e.map_add, map_smul' := fun c x ↦ ?_ } he⟩
  let y : Γ((higherDirectImage (X ↘ Spec (.of K)) q).obj ℱ, ⊤) := x
  have h : (c • x : M) = (Scheme.ΓSpecIso (.of K)).inv c • y := smul_top_eq (R := .of K) _ c y
  exact (congrArg e h).trans ((e.map_smulₛₗ _ y).trans
    (smul_H_eq_globalSectionsRingHom_smul K ℱ q c (e y)).symm)

section BaseChange

variable [HasInjectiveResolutions X.Modules]

/-- **The higher direct images commute with restriction to an open subscheme of the base.** Let
`g : T' ⟶ T` be an open immersion, and let `f' : X' ⟶ T'` and `g' : X' ⟶ X` be the base change
of `f` along `g`, in the cartesian square `sq`
```
X' --g'--> X
|          |
f'         f
v          v
T' --g---> T
```
Then `R^q f'_* (g'^* ℱ) ≅ (R^q f_* ℱ)|_{T'}` for every `q`.

This is flat base change along an open immersion, and holds for any `f` and any `ℱ`: restriction
to an open subscheme preserves injective `𝒪_X`-modules and commutes with the pushforward. -/
theorem nonempty_higherDirectImage_iso_restrict {T' X' : Scheme.{u}} (g : T' ⟶ T)
    [IsOpenImmersion g] (g' : X' ⟶ X) (f' : X' ⟶ T') [HasInjectiveResolutions X'.Modules]
    (sq : IsPullback g' f' f g) (q : ℕ) :
    Nonempty ((higherDirectImage f' q).obj ((Modules.pullback g').obj ℱ) ≅
      ((higherDirectImage f q).obj ℱ).restrict g) :=
  sorry

open MonoidalCategory in
/-- **The projection formula** for an invertible module. For `f : X ⟶ T`, an `𝒪_X`-module `ℱ`
and an invertible `𝒪_T`-module `𝒩`, `R^q f_* (ℱ ⊗ f^* 𝒩) ≅ R^q f_* ℱ ⊗ 𝒩` for every `q`: twisting
by an invertible module pulled back from the base commutes with the higher direct images.

The blueprint states the projection formula `Rf_* E ⊗^𝕃 K ≅ Rf_* (E ⊗^𝕃 Lf^* K)` in the derived
category `D_QCoh` for `f` quasi-compact and quasi-separated, and deduces this case `K = 𝒩[0]`.
There is no derived category of `X.Modules` here, so only this case is stated, through the
higher direct images; it holds for every `f` and `ℱ`, as both sides are computed locally on
`T`, where `𝒩 ≅ 𝒪_T`.

(blueprint: `lem-pc-projection-formula`) -/
theorem nonempty_higherDirectImage_tensorObj_pullback_iso (𝒩 : T.Modules) [𝒩.IsInvertible]
    (q : ℕ) :
    Nonempty ((higherDirectImage f q).obj (ℱ ⊗ (Modules.pullback f).obj 𝒩) ≅
      (higherDirectImage f q).obj ℱ ⊗ 𝒩) :=
  sorry

end BaseChange


section Vanishing

variable [QuasiCompact f] [IsSeparated f] [HasInjectiveResolutions X.Modules]
  [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ]

/-- **Local vanishing of the higher direct images in large degrees.** For `f : X ⟶ T`
quasi-compact and separated and `ℱ` a quasi-coherent `𝒪_X`-module, every point `t` of `T` has an
open neighbourhood `U` and a bound `d` with `R^q f_* ℱ|_U = 0` for all `q ≥ d`.

Take for `U` an affine open neighbourhood of `t`: then `f ⁻¹ᵁ U` is covered by finitely many,
say `d`, affine opens whose intersections are affine, and the Čech complex of this cover
computes `R f_* ℱ|_U` [Stacks, Tag 01XD], so `R^q f_* ℱ|_U = 0` for `q ≥ d`.

The bound is only local on `T`: over `T = ⨆ₙ Spec k` with `X = ⨆ₙ ℙⁿ_k` and `ℱ = 𝒪(-n-1)` on
the `n`-th piece, `R^n f_* ℱ ≠ 0` for every `n`.

(blueprint: `sk-thm-picard-coherence`) -/
theorem exists_isZero_higherDirectImage_restrict (t : T) :
    ∃ (U : T.Opens) (d : ℕ), t ∈ U ∧
      ∀ q ≥ d, IsZero (((higherDirectImage f q).obj ℱ).restrict U.ι) :=
  sorry

/-- **Vanishing of the higher direct images in large degrees over a quasi-compact base.** In the
situation of `AlgebraicGeometry.Scheme.Modules.exists_isZero_higherDirectImage_restrict`, if `T`
is quasi-compact then `R^q f_* ℱ = 0` for all large `q`: finitely many of the neighbourhoods
given there cover `T`, and one takes for `N` the maximum of their bounds.

(blueprint: `sk-thm-picard-coherence`) -/
theorem exists_isZero_higherDirectImage [CompactSpace T] :
    ∃ N, ∀ q ≥ N, IsZero ((higherDirectImage f q).obj ℱ) :=
  sorry

end Vanishing

end AlgebraicGeometry.Scheme.Modules
