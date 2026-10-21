/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers
public import Sheaf.CategoryTheory.StrictRoosModel
public import Sheaf.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Sheaf.Paper.PrincipalKoszulRoosPresentationComparison
import Sheaf.Paper.PrincipalKoszulRoosReflector
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients

/-! # The canonical regular-quotient completion unit

Source: Stacks Project, algebraization.tex, Tags 0999, 099B and 0A0E,
lemma-derived-completion-koszul; sites-cohomology.tex, Tag 0941;
Bhatt--Scholze, Lemma 3.4.12
(blueprint: lem-pur-regular-quotient-completion-unit).

The quotient tower is indexed by `n : ℕ`, representing the positive power `n+1`.
Its tensor order is the canonical symmetric model `(O/a^(n+1))[0] ⊗ P`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false


universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (R : Sheaf J CommRingCat.{u})

-- Choose the standard degreewise product directly, avoiding recursive limit search.
local instance (priority := 1100)
    (H : ℕ → CochainComplex (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) : HasProduct H :=
  (@HomologicalComplex.instHasLimitsOfShape _ ℤ (Discrete ℕ) _ _ (.up ℤ) _
    (SheafOfModules.hasLimitsOfShape.{u} (D := Discrete ℕ)
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R))).has_limit
        (Discrete.functor H)

/-- The strict quotient augmentation is the degree-zero Koszul augmentation followed
by the canonical Koszul-to-quotient map. Its components are exactly
`koszulRepresentativeQuotient`, by `koszulRepresentativeAugmentation_quotient`.
Source: Stacks Tags 0A0E and 0941
(blueprint: lem-pur-regular-quotient-completion-unit). -/
def regularQuotientAugmentation
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections) :
    (Functor.const ℕᵒᵖ).obj P ⟶ reductionTensorTower R P a :=
  koszulStrictAugmentation R P a ≫ koszulTensorTowerComparison R P a

/-- The actual shifted cone of one minus the quotient-tower shift on products.
Source: Stacks Tags 0A0E and 0941
(blueprint: lem-pur-regular-quotient-completion-unit). -/
def regularQuotientCompletion
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections) :
    CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ :=
  roosF.obj (koszulTowerComplex R (reductionTensorTower R P a))

section
attribute [local irreducible] reductionTensorTower koszulTensorTower

set_option backward.isDefEq.respectTransparency true in
/-- The specified zero-component unit, constructed by the strict Roos augmentation.
In the canonical coordinates it is `(0,(q_n)_n)`, not a chosen lift in the derived
category. Compatibility is the naturality of the strict quotient augmentation.
Source: Stacks Tags 0A0E and 0941; Bhatt--Scholze Lemma 3.4.12
(blueprint: lem-pur-regular-quotient-completion-unit). -/
def regularQuotientCompletionUnit
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections) :
    P ⟶ regularQuotientCompletion R P a := by
  unfold regularQuotientCompletion
  exact principalTowerRoosUnit R P (reductionTensorTower R P a)
    (regularQuotientAugmentation R P a)

end

attribute [local irreducible] regularQuotientCompletionUnit principalKoszulRoosUnit
  principalTowerRoosUnit

set_option hygiene false in
local notation "𝓞" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
set_option hygiene false in
local notation "𝒜" => ringedSiteModules.{u} 𝓞

private theorem complete_of_iso
    [HasDerivedCategory.{w} 𝒜]
    [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (R.over V)))]
    (a : (SheafOfModules.unit 𝓞).sections)
    {N M : ringedSiteDerived R} (e : N ≅ M)
    (hM : IsLocallyDerivedRingedIdealComplete R _ (globalSectionMultiplication R a) M) :
    IsLocallyDerivedRingedIdealComplete R _ (globalSectionMultiplication R a) N := by
  intro V f hf
  exact (hM V f hf).of_iso ((derivedInternalHom (J.over V) (R.over V)).mapIso
    ((Iso.refl (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalization (R.over V) (ringedSliceSection R V f))))).prod
        ((ringedDerivedRestriction R V).mapIso e)))

private theorem reflection_unit_isIso_iff
    {D : Type*} [Category D] (W : D → Prop) {N M : D} (η : N ⟶ M)
    (hM : W M) (hbij : ∀ L, W L → Function.Bijective (fun f : M ⟶ L ↦ η ≫ f))
    (hiso : ∀ {X Y}, (X ≅ Y) → W Y → W X) : W N ↔ IsIso η := by
  constructor
  · intro hN
    obtain ⟨r, hr⟩ := (hbij N hN).surjective (𝟙 N)
    refine ⟨⟨r, hr, (hbij M hM).injective ?_⟩⟩
    simp only [← Category.assoc, hr, Category.id_comp, Category.comp_id]
  · intro hη
    exact hiso (asIso η) hM

set_option backward.defeqAttrib.useBackward false in
private theorem cone_cokernel_quasiIso
    {B : Type*} [Category* B] [Abelian B] {M N : B} (f : M ⟶ N) [Mono f] :
    QuasiIso (CochainComplex.mappingCone.descShortComplex
      ((ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).map
        (CochainComplex.singleFunctor B 0))) := by
  let S := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel f }
  have : PreservesFiniteLimits (CochainComplex.singleFunctor B 0) :=
    inferInstanceAs (PreservesFiniteLimits (HomologicalComplex.single B (.up ℤ) 0))
  have : PreservesFiniteColimits (CochainComplex.singleFunctor B 0) :=
    inferInstanceAs (PreservesFiniteColimits (HomologicalComplex.single B (.up ℤ) 0))
  exact CochainComplex.mappingCone.quasiIso_descShortComplex
    (hS.map_of_exact (CochainComplex.singleFunctor B 0))

private theorem principal_augmentation_quasiIso
    (a : (SheafOfModules.unit 𝓞).sections)
    (ha : Mono (globalSectionMultiplication R a)) (n : ℕ) :
    QuasiIso (principalAugmentation R a n) := by
  have hp (m : ℕ) : Mono (endoPow (globalSectionMultiplication R a) m) := by
    induction m with
    | zero => change Mono (𝟙 _); infer_instance
    | succ m hm => change Mono (endoPow _ m ≫ _); infer_instance
  have := hp (n + 1)
  exact cone_cokernel_quasiIso (endoPow (globalSectionMultiplication R a) (n + 1))

private theorem roos_map_quasiIso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]
    [HasCountableProducts A] [HasExactLimitsOfShape (Discrete ℕ) A]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ Y) [hf : QuasiIso f] :
    QuasiIso (roosF.map f) := by
  have (n : Discrete ℕ) : QuasiIso
      ((Discrete.natTrans (F := Discrete.functor (fun n : ℕ ↦ X.asFunctor.obj (op n)))
        (G := Discrete.functor (fun n : ℕ ↦ Y.asFunctor.obj (op n)))
        (fun n ↦ (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app
          (op n.as))).app n) :=
    (HomologicalComplex.quasiIso_iff_evaluation f).mp hf (op n.as)
  have hp : QuasiIso (roosPmap f) := HomologicalComplex.quasiIso_limMap _
  let τ := CochainComplex.mappingCone.triangleMap (roosU X) (roosU Y)
    (roosPmap f) (roosPmap f) (roosU_natural f)
  have hc : IsIso (DerivedCategory.Q.map (roosConeFunctor.map f)) :=
    CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂
      (DerivedCategory.Q.mapTriangle.map τ)
      (DerivedCategory.mappingCone_triangle_distinguished (roosU X))
      (DerivedCategory.mappingCone_triangle_distinguished (roosU Y))
      (inferInstance : IsIso (DerivedCategory.Q.map (roosPmap f)))
      (inferInstance : IsIso (DerivedCategory.Q.map (roosPmap f)))
  have : QuasiIso (roosConeFunctor.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp hc
  change QuasiIso ((roosConeFunctor.map f)⟦(-1 : ℤ)⟧')
  infer_instance

private theorem quotient_roos_comparison_quasiIso
    [HasDerivedCategory.{w} 𝒜] [HasExactLimitsOfShape (Discrete ℕ) 𝒜]
    (a : (SheafOfModules.unit 𝓞).sections)
    (ha : Mono (globalSectionMultiplication R a))
    (P : CochainComplex 𝒜 ℤ) (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    QuasiIso (roosF.map (koszulTowerComplexMap R (koszulTensorTowerComparison R P a))) := by
  let f := koszulTensorTowerComparison R P a
  have hl (n : ℕ) : QuasiIso (f.app (op n)) := by
    exact kFlatTensorPreservesQuasiIsoIndependentCoefficients R P hP
      (principalAugmentation R a n) (principal_augmentation_quasiIso R a ha n)
  have hf : QuasiIso (koszulTowerComplexMap R f) := by
    apply (HomologicalComplex.quasiIso_iff_evaluation _).mpr
    intro n
    exact hl n.unop
  exact roos_map_quasiIso (koszulTowerComplexMap R f)

private theorem strict_roos_triangle
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    [Abelian.HasKInjectiveResolutions B]
    [HasDerivedCategory.{w} B] [HasExactLimitsOfShape (Discrete ℕ) B]
    (X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ) :
    ∃ (_hprod : HasProduct (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
        (X.asFunctor.obj (op n))))
      (p : DerivedCategory.Q.{w}.obj (roosF.obj X) ⟶
        ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (X.asFunctor.obj (op n))))
      (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (X.asFunctor.obj (op n)))) ⟶
        (DerivedCategory.Q.{w}.obj (roosF.obj X))⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ DerivedCategory.Q.{w}.map
          (X.asFunctor.map (homOfLE (Nat.le_succ n)).op))
        (DerivedCategory.Q.{w}.obj (roosF.obj X)) p δ ∧
      ∀ n : ℕ, p ≫ Pi.π _ n = DerivedCategory.Q.{w}.map (roosEval X n) := by
  let F := fun n : ℕ ↦ X.asFunctor.obj (op n)
  let D := fun n : ℕ ↦ DerivedCategory.Q.{w}.obj (F n)
  let H : Fan D := Fan.mk (DerivedCategory.Q.{w}.obj (roosP X))
    (fun n ↦ DerivedCategory.Q.{w}.map (Pi.π F n))
  have hH : IsLimit H := DerivedCategory.isLimitFanQ F
  let : HasProduct D := ⟨⟨H, hH⟩⟩
  let e := hH.conePointUniqueUpToIso (productIsProduct D)
  have he (n : ℕ) : e.hom ≫ Pi.π D n = DerivedCategory.Q.{w}.map (Pi.π F n) :=
    hH.conePointUniqueUpToIso_hom_comp (productIsProduct D) ⟨n⟩
  let T := DerivedCategory.Q.{w}.mapTriangle.obj (CochainComplex.mappingCocone.triangle
    (roosU X))
  let p := DerivedCategory.Q.{w}.map (roosProj X) ≫ e.hom
  let δ := e.inv ≫ T.mor₃
  let d := fun n : ℕ ↦ DerivedCategory.Q.{w}.map
    (X.asFunctor.map (homOfLE (Nat.le_succ n)).op)
  have hd : DerivedCategory.Q.{w}.map (roosU X) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism d := by
    apply Pi.hom_ext
    intro n
    have hsπ (n : ℕ) : roosU X ≫ Pi.π F n = Pi.π F n -
        Pi.π F (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op := by
      exact (towerTransitionEndomorphism_eq_iff (K := F)
        (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op) _).mp rfl n
    simp only [Category.assoc, he, ← Functor.map_comp, hsπ, Functor.map_sub]
    simp only [d, towerTransitionEndomorphism, towerProductShift, Preadditive.sub_comp,
      Preadditive.comp_sub, Pi.lift_π]
    simp only [Functor.map_comp, ← Category.assoc, he]
    erw [Category.comp_id, he]
  have htri : IsDerivedLimitTriangle d (DerivedCategory.Q.{w}.obj (roosF.obj X)) p δ := by
    have hT : T ∈ distTriang _ :=
      DerivedCategory.mappingCocone_triangle_distinguished _
    exact (Pretriangulated.distinguished_iff_of_iso
      (Pretriangulated.Triangle.isoMk T (Pretriangulated.Triangle.mk p
        (towerTransitionEndomorphism d) δ) (Iso.refl _) e e
          (by change DerivedCategory.Q.map (CochainComplex.mappingCocone.fst (roosU X)) ≫
                e.hom = 𝟙 _ ≫ p
              rw [Category.id_comp]
              rfl) hd (by simp [δ]))).mp hT
  refine ⟨inferInstance, p, δ, htri, ?_⟩
  intro n
  dsimp only [p, roosEval]
  rw [Category.assoc, he, ← Functor.map_comp]

private theorem quotientAugmentation_app
    (P : CochainComplex 𝒜 ℤ) (a : (SheafOfModules.unit 𝓞).sections) (n : ℕ) :
    (regularQuotientAugmentation R P a).app (op n) =
      koszulRepresentativeQuotient R P a n :=
  koszulRepresentativeAugmentation_quotient R P a n

private theorem roos_augment_natural
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    [HasLimitsOfShape ℕᵒᵖ B]
    {X Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} {P : CochainComplex B ℤ}
    (f : X ⟶ Y) (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (γ' : ∀ n : ℕ, P ⟶ Y.asFunctor.obj (op n))
    (hγ' : ∀ n, γ' (n + 1) ≫ Y.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ' n)
    (hf : ∀ n, γ n ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n) = γ' n) :
    roosAugment γ hγ ≫ roosF.map f = roosAugment γ' hγ' := by
  rw [roosAugment_eq, roosAugment_eq, Category.assoc, ← roosι_natural,
    ← Category.assoc]
  congr 1
  apply limit.hom_ext
  intro n
  rw [Category.assoc]
  erw [limMap_π]
  erw [← Category.assoc, roosAugmentLimit_π, roosAugmentLimit_π]
  exact hf n.unop

private theorem principalTowerRoosUnit_comp
    (P : CochainComplex 𝒜 ℤ) (T T' : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T) (f : T ⟶ T') :
    principalTowerRoosUnit R P T γ ≫ roosF.map (koszulTowerComplexMap R f) =
      principalTowerRoosUnit R P T' (γ ≫ f) := by
  unfold principalTowerRoosUnit
  apply roos_augment_natural
  intro n
  rfl

private theorem roos_augment_eval
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    [HasLimitsOfShape ℕᵒᵖ B]
    {X : CochainComplex (ℕᵒᵖ ⥤ B) ℤ} {P : CochainComplex B ℤ}
    (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (hγ : ∀ n, γ (n + 1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n)
    (n : ℕ) : roosAugment γ hγ ≫ roosEval X n = γ n := by
  rw [roosAugment_eq, Category.assoc, roosι_eval, roosAugmentLimit_π]

section
attribute [local irreducible] reductionTensorTower koszulTensorTower

set_option backward.isDefEq.respectTransparency true in
private theorem koszulRoosUnit_comparison
    (P : CochainComplex 𝒜 ℤ) (a : (SheafOfModules.unit 𝓞).sections) :
    principalKoszulRoosUnit R P a ≫
        roosF.map (koszulTowerComplexMap R (X := koszulTensorTower R P a)
          (Y := reductionTensorTower R P a) (koszulTensorTowerComparison R P a)) =
      regularQuotientCompletionUnit R P a := by
  unfold principalKoszulRoosUnit regularQuotientCompletionUnit regularQuotientAugmentation
  exact principalTowerRoosUnit_comp R P (koszulTensorTower R P a)
    (reductionTensorTower R P a) (koszulStrictAugmentation R P a)
    (koszulTensorTowerComparison R P a)

end

private theorem reflection_roos_triangle_iff
    {B : Type*} [Category* B] [HasZeroObject B] [HasShift B ℤ] [Preadditive B]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B] [IsTriangulated B]
    {N M : B} (η : N ⟶ M) (W : B → Prop) (hM : W M)
    (hiff : W N ↔ IsIso η) (hW : ∀ {X Y}, (X ≅ Y) → W Y → W X)
    (F : ℕ → B) [HasProduct F] (d : ∀ n : ℕ, F (n + 1) ⟶ F n)
    (pM : M ⟶ ∏ᶜ F) (δM : ∏ᶜ F ⟶ M⟦(1 : ℤ)⟧)
    (htri : IsDerivedLimitTriangle d M pM δM)
    (q : ∀ n : ℕ, N ⟶ F n) (hq : ∀ n, η ≫ pM ≫ Pi.π F n = q n) :
    IsIso η ↔ ∃ (p : N ⟶ ∏ᶜ F) (δ : ∏ᶜ F ⟶ N⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle d N p δ ∧ ∀ n, p ≫ Pi.π F n = q n := by
  constructor
  · intro hη
    let i := asIso η
    let p := η ≫ pM
    let δ := δM ≫ (shiftFunctor _ (1 : ℤ)).map i.inv
    refine ⟨p, δ, ?_, fun n ↦ ?_⟩
    · apply Pretriangulated.isomorphic_distinguished _ htri _
      refine Pretriangulated.Triangle.isoMk _ _ i (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
      · simp [p, i]
      · simp
      · simp [δ, ← Functor.map_comp]
    · simpa only [p, Category.assoc] using hq n
  · rintro ⟨p, δ, ht, _⟩
    obtain ⟨φ, hp, hδ⟩ := Pretriangulated.complete_distinguished_triangle_morphism₁
      _ _ ht htri (𝟙 _) (𝟙 _) (by simp)
    let τ : Pretriangulated.Triangle.mk p (towerTransitionEndomorphism d) δ ⟶
        Pretriangulated.Triangle.mk pM (towerTransitionEndomorphism d) δM :=
      { hom₁ := φ
        hom₂ := 𝟙 _
        hom₃ := 𝟙 _
        comm₁ := hp
        comm₂ := by simp
        comm₃ := hδ }
    have : IsIso φ := Pretriangulated.isIso₁_of_isIso₂₃ τ ht htri
      (by dsimp [τ]; infer_instance) (by dsimp [τ]; infer_instance)
    exact hiff.mp (hW (asIso φ) hM)

attribute [local irreducible] reductionTensorTower koszulTensorTower

set_option maxHeartbeats 800000 in
-- The proof combines concrete tensor towers with derived products and their unit maps.
set_option backward.isDefEq.respectTransparency true in
/-- Completion is locally derived complete, and local completeness, invertibility of
its actual zero-component unit, and a Roos triangle with the prescribed quotient
components are equivalent. The ideal `(a)` is represented by multiplication by `a`
on the rank-one ring module; regularity makes this a mono. Thus its sectionwise
image is precisely the principal ideal on every slice.

Source: Stacks Tags 0999, 099B, 0A0E (lemma-derived-completion-koszul), and 0941;
Bhatt--Scholze Lemma 3.4.12 (blueprint: lem-pur-regular-quotient-completion-unit).

Proof plan:
1. Compare the strict one-generator Koszul tensor tower with the quotient tower.
   Every power of multiplication by `a` is injective. The regular Koszul reconstruction
   theorem makes this an augmentation-compatible derived-limit isomorphism, using
   K-flatness of `P`, without assuming that its individual terms are flat.
2. Exact countable products give the normalized strict Roos comparison for the
   quotient tower. Its augmentation normalization identifies this precise zero-component
   map with the derived quotient augmentation. Compose with the inverse of the Koszul
   comparison to identify it with the reflector's degree-zero Koszul unit.
3. The ringed Koszul completion reflector for the singleton list `(a)` is complete on
   every slice and for every local element of the generated ideal. Its unit is invertible
   exactly on complete objects. Transport these facts through the unit-compatible
   comparison, using preservation of isomorphisms by restriction and internal Hom.
4. If the specified unit is invertible, transport the natural distinguished Roos
   triangle of the strict-tower derived limit along its composite with the normalized
   comparison. The projection normalization gives precisely the quotient components.
5. Conversely regular Koszul reconstruction applied to the prescribed quotient Roos
   triangle identifies `P` with the Koszul completion. Reflector completeness transports
   back to `P`, and step 3 makes the specified unit invertible. An arbitrary triangle
   comparison is never identified with that unit.
-/
theorem regularQuotientCompletionUnit_criterion
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    [∀ V : C, HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat.{u} RingCat.{u})).obj (R.over V)))]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (a : (SheafOfModules.unit
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)).sections)
    (_ha : Mono (globalSectionMultiplication R a))
    (P : CochainComplex (ringedSiteModules.{u, u, u, u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (R := R) P) :
    IsLocallyDerivedRingedIdealComplete R
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
      (globalSectionMultiplication R a)
      (DerivedCategory.Q.{w}.obj (regularQuotientCompletion R P a)) ∧
    (IsLocallyDerivedRingedIdealComplete R
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
        (globalSectionMultiplication R a) (DerivedCategory.Q.{w}.obj P) ↔
      IsIso (DerivedCategory.Q.{w}.map (regularQuotientCompletionUnit R P a))) ∧
    (IsIso (DerivedCategory.Q.{w}.map (regularQuotientCompletionUnit R P a)) ↔
      ∃ (_hU : HasProduct (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
          ((reductionTensorTower R P a).obj (op n))))
        (p : DerivedCategory.Q.{w}.obj P ⟶ ∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
          ((reductionTensorTower R P a).obj (op n))))
        (δ : (∏ᶜ (fun n : ℕ ↦ DerivedCategory.Q.{w}.obj
          ((reductionTensorTower R P a).obj (op n)))) ⟶
          (DerivedCategory.Q.{w}.obj P)⟦(1 : ℤ)⟧),
        IsDerivedLimitTriangle
          (fun n : ℕ ↦ DerivedCategory.Q.{w}.map
            ((reductionTensorTower R P a).map (homOfLE (Nat.le_succ n)).op))
          (DerivedCategory.Q.{w}.obj P) p δ ∧
        ∀ n : ℕ, p ≫ Limits.Pi.π _ n =
          DerivedCategory.Q.{w}.map (koszulRepresentativeQuotient R P a n)) := by
  let K := roosF.obj (koszulTowerComplex R (koszulTensorTower R P a))
  let U := koszulTowerComplex R (reductionTensorTower R P a)
  let ηK := DerivedCategory.Q.{w}.map (principalKoszulRoosUnit R P a)
  let ηU := DerivedCategory.Q.{w}.map (regularQuotientCompletionUnit R P a)
  let c := roosF.map (koszulTowerComplexMap R (koszulTensorTowerComparison R P a))
  have hqc : QuasiIso c := quotient_roos_comparison_quasiIso R a _ha P _hP
  let hc : IsIso (DerivedCategory.Q.{w}.map c) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ c).mpr hqc
  let e : DerivedCategory.Q.{w}.obj K ≅ DerivedCategory.Q.{w}.obj
      (regularQuotientCompletion R P a) := @asIso _ _ _ _ (DerivedCategory.Q.{w}.map c) hc
  have hη : ηK ≫ e.hom = ηU := by
    change DerivedCategory.Q.map (principalKoszulRoosUnit R P a) ≫
      DerivedCategory.Q.map c = DerivedCategory.Q.map (regularQuotientCompletionUnit R P a)
    rw [← Functor.map_comp]
    exact congrArg DerivedCategory.Q.map (koszulRoosUnit_comparison R P a)
  obtain ⟨hK, hbij⟩ := principalKoszulRoos_reflector R a _ha P
  have hU := complete_of_iso R a e.symm hK
  have hiffK := reflection_unit_isIso_iff
    (IsLocallyDerivedRingedIdealComplete R _ (globalSectionMultiplication R a)) ηK
    hK hbij (fun i hi ↦ complete_of_iso R a i hi)
  have hiff : IsLocallyDerivedRingedIdealComplete R _
      (globalSectionMultiplication R a) (DerivedCategory.Q.{w}.obj P) ↔ IsIso ηU := by
    rw [hiffK, ← hη, isIso_comp_right_iff]
  refine ⟨hU, hiff, ?_⟩
  let : IsGrothendieckAbelian.{u} 𝒜 := SheafOfModules.isGrothendieckAbelian _
  obtain ⟨hprod, pU, δU, htriU, hproj⟩ := strict_roos_triangle U
  have hcomponents (n : ℕ) : ηU ≫ pU ≫ Pi.π _ n =
      DerivedCategory.Q.{w}.map (koszulRepresentativeQuotient R P a n) := by
    calc
      ηU ≫ pU ≫ Pi.π _ n = ηU ≫ DerivedCategory.Q.map (roosEval U n) :=
        congrArg (fun f ↦ ηU ≫ f) (hproj n)
      _ = DerivedCategory.Q.map
          (regularQuotientCompletionUnit R P a ≫ roosEval U n) :=
        (DerivedCategory.Q.map_comp _ _).symm
      _ = _ := congrArg DerivedCategory.Q.map (by
        change regularQuotientCompletionUnit R P a ≫ roosEval U n = _
        unfold regularQuotientCompletionUnit principalTowerRoosUnit
        exact (roos_augment_eval _ _ n).trans (quotientAugmentation_app R P a n))
  have hh := reflection_roos_triangle_iff (F :=
    fun n : ℕ ↦ DerivedCategory.Q.{w}.obj ((reductionTensorTower R P a).obj (op n))) ηU
    (IsLocallyDerivedRingedIdealComplete R _ (globalSectionMultiplication R a)) hU hiff
    (fun i hi ↦ complete_of_iso R a i hi)
    (d := fun n : ℕ ↦ DerivedCategory.Q.{w}.map
      ((reductionTensorTower R P a).map (homOfLE (Nat.le_succ n)).op))
    pU δU htriU
    (fun n ↦ DerivedCategory.Q.{w}.map (koszulRepresentativeQuotient R P a n)) hcomponents
  constructor
  · intro h
    exact Exists.intro hprod (hh.mp h)
  · rintro ⟨hprod', p, δ, ht, hp⟩
    have heq : hprod' = hprod := Subsingleton.elim _ _
    subst hprod'
    exact hh.mpr ⟨p, δ, ht, hp⟩

end CategoryTheory
