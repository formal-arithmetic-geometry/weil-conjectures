/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.SecSmoothPurity.ScalarExtensionFunctor
public import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import Sheaf.SecSmoothPurity.ReductionExceptional
public import Sheaf.SecSmoothPurity.FiniteGeneralRing
public import Sheaf.Paper.FiniteSmoothCoefficientArrows
import all Sheaf.Paper.ExceptionalCoefficientComparison
import all Sheaf.Paper.FiniteSmoothLevelOfOrientation
import Sheaf.SecSmoothPurity.ReductionOrientation

/-! # Units, composition and purity under finite coefficient change

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction,
sk-lem-sp-reduction-compatibilities.md and its proof
(blueprint: det-sp-reduction-compatibilities).

The first two identities use the intrinsic constant-ring Dctf adjunctions. The third
uses the equivalent fixed-coefficient presentation of the general-ring purity node,
including its actual diagonal/Rees/integration normalization. No flatness is assumed.

## Main statements

* `reductionCompatibilities_unit`: coefficient change preserves the adjunction unit.
* `reductionCompatibilities_composition`: the exceptional comparisons satisfy the cocycle.
* `reductionCompatibilities_purity`: coefficient change preserves normalized smooth purity.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
open MonoidalCategory

private theorem scalarTargetNaturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategoryModule A Y) {L M : DerivedCategoryModule A X} (a : L ⟶ M) :
    (ordinaryScalar φ X).map
        (((derivedTensor (ModuleCat A) X).obj ((ordinaryFinitePullback A f).obj K)).map a) ≫
      compactScalarProjectionTarget φ f K M =
    compactScalarProjectionTarget φ f K L ≫
      ((derivedTensor (ModuleCat B) X).obj
        ((ordinaryFinitePullback B f).obj ((ordinaryScalar φ Y).obj K))).map
          ((ordinaryScalar φ X).map a) := by
  have h := (ExceptionalCoefficients.tensorIso φ X).hom.naturality
    (show (((ordinaryFinitePullback A f).obj K, L) ⟶
      ((ordinaryFinitePullback A f).obj K, M)) from (𝟙 _, a))
  have h' := ((derivedTensor (ModuleCat B) X).map
    ((scalarPullbackIso φ f).inv.app K)).naturality ((ordinaryScalar φ X).map a)
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  unfold compactScalarProjectionTarget
  erw [← Category.assoc, h, Category.assoc, h']
  exact (Category.assoc _ _ _).symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem ordinaryGammaCoefficient
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f]
    (N M : ℕ) (hA : (N : A) = 0) (hB : (M : B) = 0) (d : ℕ)
    (e : CoefficientLineComparison φ N M hA hB X)
    (a : dualizingComplex (ModuleCat A) f ≅ line A N hA X d)
    (b : dualizingComplex (ModuleCat B) f ≅ line B M hB X d)
    (hab : (ordinaryScalar φ X).map a.inv ≫
      ExceptionalCoefficients.dualizingScalarMap φ f = (e.tensorPower d).hom ≫ b.inv)
    (K : DerivedCategoryModule A Y) :
    (ordinaryScalar φ X).map (gamma A f _ a K) ≫ ExceptionalCoefficients.mateMap φ f K =
      (pullbackTwistComparison f d e K).hom ≫
        gamma B f _ b ((ordinaryScalar φ Y).obj K) := by
  have ht := ExceptionalCoefficients.tensorCompatibility φ f K
  unfold ExceptionalCoefficients.TensorCompatibility at ht
  simp only [gamma, Functor.map_comp, Category.assoc]
  erw [ht]
  unfold ExceptionalCoefficients.tensorDomainMap
  simp only [Category.assoc]
  erw [reassoc_of% (scalarTargetNaturality φ f K a.inv)]
  erw [← Functor.map_comp_assoc, hab, Functor.map_comp_assoc]
  change compactScalarProjectionTarget φ f K _ ≫
      ((derivedTensor (ModuleCat B) X).obj _).map (e.tensorPower d).hom ≫ _ = _
  simp only [compactScalarProjectionTarget, pullbackTwistComparison, Iso.trans_hom,
    Iso.app_hom, Iso.app_inv, Functor.prod_obj, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc]
  rfl

private theorem sourceFromOrigin_gamma
    {A : Type (u + 1)} [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (L : DerivedCategoryModule A X)
    (a : dualizingComplex (ModuleCat A) f ≅ L) (K : proCategory A Y)
    [hc : IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat A) Y).counit.app K)] :
    sourceFromOrigin A f L K ≫ proGamma A f L a K =
      (comparison A X).map (gamma A f L a ((origin A Y).obj K)) := by
  unfold proGamma
  have hs : sourceFromOrigin A f L K ≫ sourceToOrigin A f L K = 𝟙 _ := by
    dsimp only [sourceFromOrigin, sourceToOrigin, originInverse]
    rw [dif_pos hc, Category.assoc, ← (proSource A f L).map_comp_assoc,
      IsIso.hom_inv_id]
    erw [(proSource A f L).map_id, Category.id_comp, Iso.hom_inv_id]
  rw [← Category.assoc, hs, Category.id_comp]

private theorem scalarOriginCounit
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (Y : Scheme.{u}) [IsNoetherian Y]
    (K : proCategory A Y) (hK : IsCtf A Y K) :
    IsIso ((ProEtale.derivedComparisonAdjunction (ModuleCat B) Y).counit.app
      ((proScalar φ Y).obj K)) := by
  let a := ProEtale.derivedComparisonAdjunction (ModuleCat A) Y
  let b := ProEtale.derivedComparisonAdjunction (ModuleCat B) Y
  have : IsIso (a.counit.app K) := intrinsicOriginCounit A Y K hK
  have hplus := ExceptionalCoefficients.scalar_extension_plus_of_finiteTor φ Y
    ((origin A Y).obj K) (actualOriginCtf A Y K hK).2
  have := ProEtale.isIso_derivedComparisonAdjunction_unit_app (ModuleCat B) Y
    ((ordinaryScalar φ Y).obj ((origin A Y).obj K)) hplus
  have : IsIso (b.counit.app ((comparison B Y).obj
      ((ordinaryScalar φ Y).obj ((origin A Y).obj K)))) :=
    IsIso.of_isIso_fac_left (b.left_triangle_components _)
  let e : (comparison B Y).obj ((ordinaryScalar φ Y).obj ((origin A Y).obj K)) ≅
      (proScalar φ Y).obj K :=
    ((ProEtale.pbcComparisonReduction Y φ).app ((origin A Y).obj K)).symm ≪≫
      (proScalar φ Y).mapIso (asIso (a.counit.app K))
  exact (NatTrans.isIso_app_iff_of_iso b.counit e).mp inferInstance

private theorem proGammaCoefficient
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f]
    (N M : ℕ) (hA : (N : A) = 0) (hB : (M : B) = 0) (d : ℕ)
    (e : CoefficientLineComparison φ N M hA hB X)
    (a : dualizingComplex (ModuleCat A) f ≅ line A N hA X d)
    (b : dualizingComplex (ModuleCat B) f ≅ line B M hB X d)
    (h : ∀ K : DerivedCategoryModule A Y,
      (ordinaryScalar φ X).map (gamma A f _ a K) ≫
          ExceptionalCoefficients.mateMap φ f K =
        (pullbackTwistComparison f d e K).hom ≫
          gamma B f _ b ((ordinaryScalar φ Y).obj K))
    (K : proCategory A Y) (hK : IsCtf A Y K) :
    (proScalar φ X).map (proGamma A f _ a K) ≫ proCoefficientMap φ f K =
      proLambda f d e K ≫ proGamma B f _ b ((proScalar φ Y).obj K) := by
  have := scalarOriginCounit φ Y K hK
  unfold proLambda
  simp only [Category.assoc, sourceFromOrigin_gamma]
  unfold proGamma proCoefficientMap
  simp only [Functor.map_comp, Category.assoc]
  have hn := (ProEtale.pbcComparisonReduction X φ).hom.naturality
    (gamma A f _ a ((origin A Y).obj K))
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [reassoc_of% hn]
  erw [← (comparison B X).map_comp_assoc, h]
  simp only [Functor.map_comp, Category.assoc]
  have hg := ordinaryGammaNaturality B f _ b (originReductionMap φ Y K)
  have hg' := congrArg (comparison B X).map hg
  simp only [Functor.map_comp] at hg'
  erw [hg']

end AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.ProEtale

private theorem counitComparison_unit
    {C₁ D₁ C₂ D₂ : Type*} [Category C₁] [Category D₁]
    [Category C₂] [Category D₂]
    {F₁ : C₁ ⥤ D₁} {G₁ : D₁ ⥤ C₁} {F₂ : C₂ ⥤ D₂} {G₂ : D₂ ⥤ C₂}
    (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (S : C₁ ⥤ C₂) (T : D₁ ⥤ D₂)
    (b : F₁ ⋙ T ⟶ S ⋙ F₂) (c : G₁ ⋙ S ⟶ T ⋙ G₂)
    (hc : ∀ K, b.app (G₁.obj K) ≫ F₂.map (c.app K) ≫
      a₂.counit.app (T.obj K) = T.map (a₁.counit.app K))
    (M : C₁) [Epi (b.app M)] :
    S.map (a₁.unit.app M) ≫ c.app (F₁.obj M) ≫ G₂.map (b.app M) =
      a₂.unit.app (S.obj M) := by
  apply (a₂.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Functor.comp_obj, Category.assoc]
  have tr₁ : F₁.map (a₁.unit.app M) ≫ a₁.counit.app (F₁.obj M) = 𝟙 _ :=
    a₁.left_triangle_components M
  have tr₂ : F₂.map (a₂.unit.app (S.obj M)) ≫
      a₂.counit.app (F₂.obj (S.obj M)) = 𝟙 _ := a₂.left_triangle_components _
  rw [tr₂]
  apply (cancel_epi (b.app M)).mp
  have hn : F₂.map (G₂.map (b.app M)) ≫ a₂.counit.app (F₂.obj (S.obj M)) =
      a₂.counit.app (T.obj (F₁.obj M)) ≫ b.app M := a₂.counit.naturality (b.app M)
  have hb : T.map (F₁.map (a₁.unit.app M)) ≫ b.app (G₁.obj (F₁.obj M)) =
      b.app M ≫ F₂.map (S.map (a₁.unit.app M)) := b.naturality (a₁.unit.app M)
  calc
    _ = (b.app M ≫ F₂.map (S.map (a₁.unit.app M))) ≫
        F₂.map (c.app (F₁.obj M)) ≫
        (F₂.map (G₂.map (b.app M)) ≫ a₂.counit.app (F₂.obj (S.obj M))) := by
          simp only [Category.assoc]
    _ = (T.map (F₁.map (a₁.unit.app M)) ≫ b.app (G₁.obj (F₁.obj M))) ≫
        F₂.map (c.app (F₁.obj M)) ≫
        (a₂.counit.app (T.obj (F₁.obj M)) ≫ b.app M) := by rw [← hb, hn]
    _ = T.map (F₁.map (a₁.unit.app M)) ≫
        (b.app (G₁.obj (F₁.obj M)) ≫ F₂.map (c.app (F₁.obj M)) ≫
          a₂.counit.app (T.obj (F₁.obj M))) ≫ b.app M := by
          simp only [Category.assoc]
    _ = _ := by
          rw [hc, ← T.map_comp_assoc, tr₁, T.map_id]
          simp

private theorem counitComparison_composition
    {C₁ D₁ C₂ D₂ C₃ D₃ : Type*}
    [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    [Category C₃] [Category D₃]
    {F₁ : C₁ ⥤ D₁} {G₁ : D₁ ⥤ C₁} {F₂ : C₂ ⥤ D₂} {G₂ : D₂ ⥤ C₂}
    {F₃ : C₃ ⥤ D₃} {G₃ : D₃ ⥤ C₃}
    (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (a₃ : F₃ ⊣ G₃)
    (S₁₂ : C₁ ⥤ C₂) (S₂₃ : C₂ ⥤ C₃) (S₁₃ : C₁ ⥤ C₃)
    (T₁₂ : D₁ ⥤ D₂) (T₂₃ : D₂ ⥤ D₃) (T₁₃ : D₁ ⥤ D₃)
    (ax : S₁₂ ⋙ S₂₃ ⟶ S₁₃) (ay : T₁₂ ⋙ T₂₃ ⟶ T₁₃)
    (b₁₂ : F₁ ⋙ T₁₂ ⟶ S₁₂ ⋙ F₂) (b₂₃ : F₂ ⋙ T₂₃ ⟶ S₂₃ ⋙ F₃)
    (b₁₃ : F₁ ⋙ T₁₃ ⟶ S₁₃ ⋙ F₃)
    (c₁₂ : G₁ ⋙ S₁₂ ⟶ T₁₂ ⋙ G₂) (c₂₃ : G₂ ⋙ S₂₃ ⟶ T₂₃ ⋙ G₃)
    (c₁₃ : G₁ ⋙ S₁₃ ⟶ T₁₃ ⋙ G₃)
    (h₁₂ : ∀ K, b₁₂.app (G₁.obj K) ≫ F₂.map (c₁₂.app K) ≫
      a₂.counit.app (T₁₂.obj K) = T₁₂.map (a₁.counit.app K))
    (h₂₃ : ∀ K, b₂₃.app (G₂.obj K) ≫ F₃.map (c₂₃.app K) ≫
      a₃.counit.app (T₂₃.obj K) = T₂₃.map (a₂.counit.app K))
    (h₁₃ : ∀ K, b₁₃.app (G₁.obj K) ≫ F₃.map (c₁₃.app K) ≫
      a₃.counit.app (T₁₃.obj K) = T₁₃.map (a₁.counit.app K))
    (hb : ∀ M, ay.app (F₁.obj M) ≫ b₁₃.app M =
      T₂₃.map (b₁₂.app M) ≫ b₂₃.app (S₁₂.obj M) ≫ F₃.map (ax.app M))
    (K : D₁) [Epi (T₂₃.map (b₁₂.app (G₁.obj K)))]
    [Epi (b₂₃.app (S₁₂.obj (G₁.obj K)))] :
    S₂₃.map (c₁₂.app K) ≫ c₂₃.app (T₁₂.obj K) ≫ G₃.map (ay.app K) =
      ax.app (G₁.obj K) ≫ c₁₃.app K := by
  apply (a₃.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
    Functor.comp_obj]
  apply (cancel_epi (T₂₃.map (b₁₂.app (G₁.obj K)) ≫
    b₂₃.app (S₁₂.obj (G₁.obj K)))).mp
  have hn : T₂₃.map (F₂.map (c₁₂.app K)) ≫ b₂₃.app (G₂.obj (T₁₂.obj K)) =
      b₂₃.app (S₁₂.obj (G₁.obj K)) ≫ F₃.map (S₂₃.map (c₁₂.app K)) :=
    b₂₃.naturality (c₁₂.app K)
  have hn' : F₃.map (G₃.map (ay.app K)) ≫ a₃.counit.app (T₁₃.obj K) =
      a₃.counit.app (T₂₃.obj (T₁₂.obj K)) ≫ ay.app K :=
    a₃.counit.naturality (ay.app K)
  calc
    _ = T₂₃.map (b₁₂.app (G₁.obj K)) ≫
        (b₂₃.app (S₁₂.obj (G₁.obj K)) ≫ F₃.map (S₂₃.map (c₁₂.app K))) ≫
        F₃.map (c₂₃.app (T₁₂.obj K)) ≫
        (F₃.map (G₃.map (ay.app K)) ≫ a₃.counit.app (T₁₃.obj K)) := by
          simp only [Category.assoc]
    _ = T₂₃.map (b₁₂.app (G₁.obj K)) ≫
        (T₂₃.map (F₂.map (c₁₂.app K)) ≫ b₂₃.app (G₂.obj (T₁₂.obj K))) ≫
        F₃.map (c₂₃.app (T₁₂.obj K)) ≫
        (a₃.counit.app (T₂₃.obj (T₁₂.obj K)) ≫ ay.app K) := by rw [← hn, hn']
    _ = T₂₃.map (b₁₂.app (G₁.obj K)) ≫ T₂₃.map (F₂.map (c₁₂.app K)) ≫
        (b₂₃.app (G₂.obj (T₁₂.obj K)) ≫ F₃.map (c₂₃.app (T₁₂.obj K)) ≫
          a₃.counit.app (T₂₃.obj (T₁₂.obj K))) ≫ ay.app K := by
          simp only [Category.assoc]
    _ = T₂₃.map (b₁₂.app (G₁.obj K)) ≫ T₂₃.map (F₂.map (c₁₂.app K)) ≫
        T₂₃.map (a₂.counit.app (T₁₂.obj K)) ≫ ay.app K := by rw [h₂₃]
    _ = T₂₃.map (b₁₂.app (G₁.obj K) ≫ F₂.map (c₁₂.app K) ≫
        a₂.counit.app (T₁₂.obj K)) ≫ ay.app K := by simp only [Functor.map_comp,
          Category.assoc]
    _ = ay.app (F₁.obj (G₁.obj K)) ≫ T₁₃.map (a₁.counit.app K) := by
          rw [h₁₂]
          exact ay.naturality (a₁.counit.app K)
    _ = (ay.app (F₁.obj (G₁.obj K)) ≫ b₁₃.app (G₁.obj K)) ≫
        F₃.map (c₁₃.app K) ≫ a₃.counit.app (T₁₃.obj K) := by rw [Category.assoc, h₁₃]
    _ = _ := by rw [hb]; simp only [Category.assoc]

/-- Coefficient change preserves the unit of the constructible compact-support adjunction.
The equation `hc` specifies exactly the counit-characterized comparison of the dependency;
it is written without an inverse by multiplying by the canonical support comparison.
Source: sk-lem-sp-reduction-compatibilities, clause (1)
(blueprint: det-sp-reduction-compatibilities).

Proof (node Steps 1--2): Scalar extension preserves Dctf and its canonical tensor and
pullback identifications. Transpose the displayed composite under the B-adjunction.
Naturality of the B-counit and hc identify its transpose with b_M, then the extended
A-counit, inverse b at G_A F_A M, and F_B of the extended A-unit. Naturality of b at
the A-unit and the A triangle identity reduce this to the identity. This is also the
transpose of the B-unit. Injectivity of the adjunction Hom bijection gives equality. -/
theorem reductionCompatibilities_unit
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (cpt : Compactification f)
    [cpt.Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (cpt.Z ↘ Spec (.of D.k))]
    [QuasiCompact (cpt.Z ↘ Spec (.of D.k))]
    [IsSeparated (cpt.Z ↘ Spec (.of D.k))]
    [cpt.i.IsOver (Spec (.of D.k))] [cpt.g.IsOver (Spec (.of D.k))]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A cpt.i cpt.g).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B cpt.i cpt.g).obj M.obj))
    (hSX : ∀ K : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj K.obj))
    (hSY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (adjA : reductionCtfCompactSupport A cpt.i cpt.g hFA ⊣ GA)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjB : reductionCtfCompactSupport B cpt.i cpt.g hFB ⊣ GB)
    (c : GA ⋙ reductionCtfScalar φ X hSX ⟶
      reductionCtfScalar φ Y hSY ⋙ GB)
    (hc : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionDirectImageComparison φ cpt.i cpt.g).app (GA.obj K).obj ≫
          (reductionCompactSupport B cpt.i cpt.g).map (c.app K).hom ≫
          (adjB.counit.app ((reductionCtfScalar φ Y hSY).obj K)).hom =
        (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom)
    (M : spFiniteConstructibleTorCategory X A) :
    (scalarExtensionFunctor φ X).map (adjA.unit.app M).hom ≫
        (c.app ((reductionCtfCompactSupport A cpt.i cpt.g hFA).obj M)).hom ≫
        (GB.map (ObjectProperty.homMk
          ((reductionDirectImageComparison φ cpt.i cpt.g).app M.obj))).hom =
      (adjB.unit.app ((reductionCtfScalar φ X hSX).obj M)).hom := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let b : reductionCtfCompactSupport A cpt.i cpt.g hFA ⋙
      reductionCtfScalar φ Y hSY ⟶ reductionCtfScalar φ X hSX ⋙
      reductionCtfCompactSupport B cpt.i cpt.g hFB :=
    { app := fun N ↦ ObjectProperty.homMk
        ((reductionDirectImageComparison φ cpt.i cpt.g).app N.obj)
      naturality := fun N N' g ↦ by
        ext
        exact (reductionDirectImageComparison φ cpt.i cpt.g).naturality g.hom }
  have hbounded : Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules X (proEtaleConstantRing X A)) i).obj M.obj)} := by
    obtain ⟨a, b, _, hab⟩ := M.property.1
    apply (Set.finite_Icc a b).subset
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi (hab i (Or.inl h))),
      le_of_not_gt (fun h ↦ hi (hab i (Or.inr h)))⟩
  have : IsIso ((reductionDirectImageComparison φ cpt.i cpt.g).app M.obj) :=
    (reductionDirectImage_isIso ℓ D.p D.prime.pos (Ne.symm _hℓ) D.k
      f cpt.i cpt.g cpt.comm.symm _hA _hB φ M.obj hbounded M.property.2.1 M.property.2.2).1
  have : IsIso (b.app M) :=
    (ObjectProperty.isIso_hom_iff _).mp
      (show IsIso ((reductionDirectImageComparison φ cpt.i cpt.g).app M.obj) from
        inferInstance)
  have hunit := counitComparison_unit adjA adjB
    (reductionCtfScalar φ X hSX) (reductionCtfScalar φ Y hSY) b c
    (fun K ↦ by ext; exact hc K) M
  exact congrArg (fun g ↦ g.hom) hunit

/-- Successive exceptional coefficient comparisons compose with the recorded scalar
associators on both schemes. The three comparisons are fixed by their counit equations.
Source: sk-lem-sp-reduction-compatibilities, clause (2)
(blueprint: det-sp-reduction-compatibilities).

Proof (node Step 3): Transpose the successive comparison under the C-adjunction.
The BC counit equation removes cBC. Naturality of bBC at cAB then moves the latter
through bBC inverse. The AB counit equation leaves scalar extension of the A-counit
followed by the two inverse support comparisons. The coefficient cocycle of
reductionDirectImage_cocycle, with naturality of the scalar associator, identifies
this with the transpose defining cAC. Injectivity of transposition proves equality.
All scalar associators are those normalized by K-flat balanced tensor in Step 1. -/
theorem reductionCompatibilities_composition
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (_hℓ : ℓ ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (cpt : Compactification f)
    [cpt.Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (cpt.Z ↘ Spec (.of D.k))]
    [QuasiCompact (cpt.Z ↘ Spec (.of D.k))]
    [IsSeparated (cpt.Z ↘ Spec (.of D.k))]
    [cpt.i.IsOver (Spec (.of D.k))] [cpt.g.IsOver (Spec (.of D.k))]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
    (_hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0) (φ : A →+* B)
    {C : Type u} [CommRing C] [Finite C]
    (_hC : ∃ n : ℕ, ∀ x : C, (ℓ ^ n) • x = 0) (ψ : B →+* C)
    (hFA : ∀ M : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor Y A ((reductionCompactSupport A cpt.i cpt.g).obj M.obj))
    (hFB : ∀ M : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor Y B ((reductionCompactSupport B cpt.i cpt.g).obj M.obj))
    (hFC : ∀ M : spFiniteConstructibleTorCategory X C,
      spFiniteConstructibleTor Y C ((reductionCompactSupport C cpt.i cpt.g).obj M.obj))
    (hABX : ∀ K : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X B ((scalarExtensionFunctor φ X).obj K.obj))
    (hABY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y B ((scalarExtensionFunctor φ Y).obj K.obj))
    (hBCX : ∀ K : spFiniteConstructibleTorCategory X B,
      spFiniteConstructibleTor X C ((scalarExtensionFunctor ψ X).obj K.obj))
    (hBCY : ∀ K : spFiniteConstructibleTorCategory Y B,
      spFiniteConstructibleTor Y C ((scalarExtensionFunctor ψ Y).obj K.obj))
    (hACX : ∀ K : spFiniteConstructibleTorCategory X A,
      spFiniteConstructibleTor X C ((scalarExtensionFunctor (ψ.comp φ) X).obj K.obj))
    (hACY : ∀ K : spFiniteConstructibleTorCategory Y A,
      spFiniteConstructibleTor Y C ((scalarExtensionFunctor (ψ.comp φ) Y).obj K.obj))
    (GA : spFiniteConstructibleTorCategory Y A ⥤ spFiniteConstructibleTorCategory X A)
    (adjA : reductionCtfCompactSupport A cpt.i cpt.g hFA ⊣ GA)
    (GB : spFiniteConstructibleTorCategory Y B ⥤ spFiniteConstructibleTorCategory X B)
    (adjB : reductionCtfCompactSupport B cpt.i cpt.g hFB ⊣ GB)
    (GC : spFiniteConstructibleTorCategory Y C ⥤ spFiniteConstructibleTorCategory X C)
    (adjC : reductionCtfCompactSupport C cpt.i cpt.g hFC ⊣ GC)
    (cAB : GA ⋙ reductionCtfScalar φ X hABX ⟶
      reductionCtfScalar φ Y hABY ⋙ GB)
    (hcAB : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionDirectImageComparison φ cpt.i cpt.g).app (GA.obj K).obj ≫
          (reductionCompactSupport B cpt.i cpt.g).map (cAB.app K).hom ≫
          (adjB.counit.app ((reductionCtfScalar φ Y hABY).obj K)).hom =
        (scalarExtensionFunctor φ Y).map (adjA.counit.app K).hom)
    (cBC : GB ⋙ reductionCtfScalar ψ X hBCX ⟶
      reductionCtfScalar ψ Y hBCY ⋙ GC)
    (hcBC : ∀ K : spFiniteConstructibleTorCategory Y B,
      (reductionDirectImageComparison ψ cpt.i cpt.g).app (GB.obj K).obj ≫
          (reductionCompactSupport C cpt.i cpt.g).map (cBC.app K).hom ≫
          (adjC.counit.app ((reductionCtfScalar ψ Y hBCY).obj K)).hom =
        (scalarExtensionFunctor ψ Y).map (adjB.counit.app K).hom)
    (cAC : GA ⋙ reductionCtfScalar (ψ.comp φ) X hACX ⟶
      reductionCtfScalar (ψ.comp φ) Y hACY ⋙ GC)
    (hcAC : ∀ K : spFiniteConstructibleTorCategory Y A,
      (reductionDirectImageComparison (ψ.comp φ) cpt.i cpt.g).app (GA.obj K).obj ≫
          (reductionCompactSupport C cpt.i cpt.g).map (cAC.app K).hom ≫
          (adjC.counit.app ((reductionCtfScalar (ψ.comp φ) Y hACY).obj K)).hom =
        (scalarExtensionFunctor (ψ.comp φ) Y).map (adjA.counit.app K).hom)
    (K : spFiniteConstructibleTorCategory Y A) :
    (scalarExtensionFunctor ψ X).map (cAB.app K).hom ≫
        (cBC.app ((reductionCtfScalar φ Y hABY).obj K)).hom ≫
        (GC.map (ObjectProperty.homMk
          ((scalarExtensionFunctor_composition φ ψ Y).hom.app K.obj))).hom =
      (scalarExtensionFunctor_composition φ ψ X).hom.app (GA.obj K).obj ≫
        (cAC.app K).hom := by
  classical
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
  let : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  let bAB : reductionCtfCompactSupport A cpt.i cpt.g hFA ⋙
      reductionCtfScalar φ Y hABY ⟶ reductionCtfScalar φ X hABX ⋙
      reductionCtfCompactSupport B cpt.i cpt.g hFB :=
    { app := fun N ↦ ObjectProperty.homMk
        ((reductionDirectImageComparison φ cpt.i cpt.g).app N.obj)
      naturality := fun N N' g ↦ by
        ext
        exact (reductionDirectImageComparison φ cpt.i cpt.g).naturality g.hom }
  let bBC : reductionCtfCompactSupport B cpt.i cpt.g hFB ⋙
      reductionCtfScalar ψ Y hBCY ⟶ reductionCtfScalar ψ X hBCX ⋙
      reductionCtfCompactSupport C cpt.i cpt.g hFC :=
    { app := fun N ↦ ObjectProperty.homMk
        ((reductionDirectImageComparison ψ cpt.i cpt.g).app N.obj)
      naturality := fun N N' g ↦ by
        ext
        exact (reductionDirectImageComparison ψ cpt.i cpt.g).naturality g.hom }
  let bAC : reductionCtfCompactSupport A cpt.i cpt.g hFA ⋙
      reductionCtfScalar (ψ.comp φ) Y hACY ⟶ reductionCtfScalar (ψ.comp φ) X hACX ⋙
      reductionCtfCompactSupport C cpt.i cpt.g hFC :=
    { app := fun N ↦ ObjectProperty.homMk
        ((reductionDirectImageComparison (ψ.comp φ) cpt.i cpt.g).app N.obj)
      naturality := fun N N' g ↦ by
        ext
        exact (reductionDirectImageComparison (ψ.comp φ) cpt.i cpt.g).naturality g.hom }
  let aX : reductionCtfScalar φ X hABX ⋙ reductionCtfScalar ψ X hBCX ⟶
      reductionCtfScalar (ψ.comp φ) X hACX :=
    { app := fun N ↦ ObjectProperty.homMk
        ((scalarExtensionFunctor_composition φ ψ X).hom.app N.obj)
      naturality := fun N N' g ↦ by
        ext
        exact (scalarExtensionFunctor_composition φ ψ X).hom.naturality g.hom }
  let aY : reductionCtfScalar φ Y hABY ⋙ reductionCtfScalar ψ Y hBCY ⟶
      reductionCtfScalar (ψ.comp φ) Y hACY :=
    { app := fun N ↦ ObjectProperty.homMk
        ((scalarExtensionFunctor_composition φ ψ Y).hom.app N.obj)
      naturality := fun N N' g ↦ by
        ext
        exact (scalarExtensionFunctor_composition φ ψ Y).hom.naturality g.hom }
  have bounded {R : Type u} [CommRing R] [Finite R]
      (M : spFiniteConstructibleTorCategory X R) :
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules X (proEtaleConstantRing X R)) i).obj M.obj)} := by
    obtain ⟨a, b, _, hab⟩ := M.property.1
    apply (Set.finite_Icc a b).subset
    intro i hi
    exact ⟨le_of_not_gt (fun h ↦ hi (hab i (Or.inl h))),
      le_of_not_gt (fun h ↦ hi (hab i (Or.inr h)))⟩
  have : IsIso (bAB.app (GA.obj K)) :=
    (ObjectProperty.isIso_hom_iff _).mp
      ((reductionDirectImage_isIso ℓ D.p D.prime.pos (Ne.symm _hℓ) D.k
        f cpt.i cpt.g cpt.comm.symm _hA _hB φ (GA.obj K).obj (bounded _)
        (GA.obj K).property.2.1 (GA.obj K).property.2.2).1)
  have : IsIso (bBC.app ((reductionCtfScalar φ X hABX).obj (GA.obj K))) :=
    (ObjectProperty.isIso_hom_iff _).mp
      ((reductionDirectImage_isIso ℓ D.p D.prime.pos (Ne.symm _hℓ) D.k
        f cpt.i cpt.g cpt.comm.symm _hB _hC ψ
        ((reductionCtfScalar φ X hABX).obj (GA.obj K)).obj (bounded _)
        ((reductionCtfScalar φ X hABX).obj (GA.obj K)).property.2.1
        ((reductionCtfScalar φ X hABX).obj (GA.obj K)).property.2.2).1)
  have hcomp := counitComparison_composition adjA adjB adjC
    (reductionCtfScalar φ X hABX) (reductionCtfScalar ψ X hBCX)
    (reductionCtfScalar (ψ.comp φ) X hACX)
    (reductionCtfScalar φ Y hABY) (reductionCtfScalar ψ Y hBCY)
    (reductionCtfScalar (ψ.comp φ) Y hACY) aX aY bAB bBC bAC cAB cBC cAC
    (fun N ↦ by ext; exact hcAB N) (fun N ↦ by ext; exact hcBC N)
    (fun N ↦ by ext; exact hcAC N)
    (fun N ↦ by
      ext
      exact reductionDirectImage_cocycle ℓ D.p D.prime.pos (Ne.symm _hℓ) D.k
        f cpt.i cpt.g cpt.comm.symm _hA _hB _hC φ ψ N.obj (bounded _)
        N.property.2.1 N.property.2.2) K
  exact congrArg (fun g ↦ g.hom) hcomp

/-- Scalar extension carries the diagonal/DNC-normalized smooth purity map to the
same map over the new finite ring, under canonical pullback/twist balancing.
`alphaA` and `alphaB` are precisely the orientations of finiteGeneralRingSmoothPurity:
OrientationNormalized retains the actual diagonal mate, the t=1-normalized Rees
comparison and the inverse integration-transposed bundle arrow. `e` retains the
scalar/root-generator normalization; it is not an arbitrary Tate-line isomorphism.
Source: sk-lem-sp-reduction-compatibilities, clause (3)
(blueprint: det-sp-reduction-compatibilities).

Proof (node Steps 1 and 4--8): The scalar monoidal and pullback identifications are
balanced tensor maps on flat K-flat representatives, respecting symmetry and shifts.
For the fixed compactification apply ringedExchangeTensorCoherence to its proper part
and the extension-by-zero tensor comparison to its open part. On the open part both
orders extend sections by zero and multiply the same B-scalars. Pasting gives the
projection/scalar square. FiniteRingCompactSupportProjection makes its projection
maps invertible on the bounded intrinsically constructible inputs omega_A and K.
Transpose the tensor map h using inverse projection followed by the counit at A_Y.
The projection square, naturality and the counit equation defining c identify the
two tensor-map transposes, hence c (h_A)_B = h_B rho. Choose one positive ell-power
annihilating both A and B. finiteGeneralRingSmoothPurity identifies each orientation
with extension of the same prime-power diagonal orientation. Clause (2), already
stated above, gives delta (o_A)_B = o_B; exponent independence permits this common
choice. Finally gamma_R = h_R (1 tensor o_R). Substitute the two equalities to obtain
c (gamma_A)_B = gamma_B lambda. Intrinsic finite-ring comparison identifies the fixed
module presentation used here with the ordinary uncompleted constant-ring category. -/
theorem reductionCompatibilities_purity
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    [HasCompactification f]
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (n : ℕ) (hn : 1 ≤ n)
    (hA : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} A) = 0)
    (hB : ((ℓ ^ n : ℕ) : ULift.{u + 1, u} B) = 0)
    (geometry : Etale.FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (alphaA : Etale.dualizingComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ≅
      Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} A) (ℓ ^ n) hA X d)
    (alphaB : Etale.dualizingComplex (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f ≅
      Etale.FiniteSmoothPurity.line (ULift.{u + 1, u} B) (ℓ ^ n) hB X d)
    (_ha : @Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} A) _ _
      (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n) hA X Y
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
          (X ↘ Spec (.of D.k))
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
          (X ↘ Spec (.of D.k)) } f _
      (@quasiCompact_of_compactSpace X Y f
        (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
        (quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k)))) _ d geometry
      ((finiteGeneralRingPrimeSetting D ℓ hℓ n hn).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) alphaA)
    (_hb : @Etale.FiniteSmoothPurity.OrientationNormalized (ULift.{u + 1, u} B) _ _
      (ℓ ^ n) (pow_pos (Fact.out : ℓ.Prime).pos n) hB X Y
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
          (X ↘ Spec (.of D.k))
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
          (X ↘ Spec (.of D.k)) } f _
      (@quasiCompact_of_compactSpace X Y f
        (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
        (quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k)))) _ d geometry
      ((finiteGeneralRingPrimeSetting D ℓ hℓ n hn).diagonalExponent_isUnit
        (X ↘ Spec (.of D.k))) alphaB)
    (e : Etale.FiniteSmoothPurity.CoefficientLineComparison
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) (ℓ ^ n) (ℓ ^ n) hA hB X)
    (K : Etale.FiniteSmoothPurity.proCategory (ULift.{u + 1, u} A) Y)
    (_hK : Etale.FiniteSmoothPurity.IsCtf (ULift.{u + 1, u} A) Y K) :
    (Etale.FiniteSmoothPurity.proScalar (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).map
        (Etale.FiniteSmoothPurity.proGamma (ULift.{u + 1, u} A) f _ alphaA K) ≫
        Etale.FiniteSmoothPurity.proCoefficientMap
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) f K =
      Etale.FiniteSmoothPurity.proLambda f d e K ≫
        Etale.FiniteSmoothPurity.proGamma (ULift.{u + 1, u} B) f _ alphaB
          ((Etale.FiniteSmoothPurity.proScalar
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).obj K) := by
  let : IsNoetherian X :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (X ↘ Spec (.of D.k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
        (X ↘ Spec (.of D.k)) }
  let : IsNoetherian Y :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (Y ↘ Spec (.of D.k))
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
        (Y ↘ Spec (.of D.k)) }
  let : QuasiCompact f :=
    @quasiCompact_of_compactSpace X Y f
      (QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of D.k)))
      (quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of D.k)))
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  have : LocallyOfFiniteType f := inferInstance
  have ho := reductionOrientation D ℓ hℓ f d φ n hn hA hB geometry alphaA alphaB
    _ha _hb e
  apply Etale.FiniteSmoothPurity.proGammaCoefficient
    (RingHom.ulift.{u + 1, u + 1, u, u} φ) f (ℓ ^ n) (ℓ ^ n) hA hB d e
      alphaA alphaB _ K _hK
  intro L
  exact Etale.FiniteSmoothPurity.ordinaryGammaCoefficient
    (RingHom.ulift.{u + 1, u + 1, u, u} φ) f (ℓ ^ n) (ℓ ^ n) hA hB d e
      alphaA alphaB ho L

end AlgebraicGeometry.ProEtale
