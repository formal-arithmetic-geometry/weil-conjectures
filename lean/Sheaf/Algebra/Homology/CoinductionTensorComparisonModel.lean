/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Algebra.Homology.DerivedCoinductionAdjunction
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.Monoidal

/-! # A counit-normalized model of the tensor/coinduction comparison

Source: Stacks Project, dualizing.tex, Tags 0A70 and 0A71, and more-algebra.tex,
Tag 06Y6 (blueprint: lem-trf-coinduction-tensor-comparison-model).

The second-factor tensor functor and its computation map are the published ones.
The mixed tensor presents a generator `x ⊗ h` as `h ⊗ (1 ⊗ x)`; allowing the
extension scalar `b` gives the generator `h ⊗ (b ⊗ x)`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u wR wB

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings TensorProduct

namespace ModuleCat

variable {R B : Type u} [CommRing R] [CommRing B] (f : R →+* B)
  [HasDerivedCategory.{wR} (ModuleCat.{u} R)]
  [HasDerivedCategory.{wB} (ModuleCat.{u} B)]

/-- Tensor with the coinduced complex of a representative of `R[0]`, using the existing
left-derived tensor functor. Its universal computation comparison fixes the functor up to
the unique compatible isomorphism. Source: Stacks 06Y6 and 0A71
(blueprint: lem-trf-coinduction-tensor-comparison-model). -/
abbrev coinductionTensorSource (J : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} B) :=
  ((DerivedCategory.exists_derivedTensor_second_factor_functor f).2.choose).obj
    ((coinductionComplexFunctor f).obj J)

/-- The existing left-derived tensor computation map for the coinduced second factor.
Source: Stacks 06Y6 and 0A71
(blueprint: lem-trf-coinduction-tensor-comparison-model). -/
abbrev coinductionTensorSourceComparison (J : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q ⋙ coinductionTensorSource f J ⟶
      ((mixedTensor f).flip.map₂CochainComplex).flip.obj
        ((coinductionComplexFunctor f).obj J) ⋙ DerivedCategory.Q :=
  (DerivedCategory.exists_derivedTensor_second_factor_functor f).2.choose_spec.choose
    ((coinductionComplexFunctor f).obj J)

/-- The generator formula for tensoring the evaluation-at-one counit. In the extension
presentation it evaluates `h` at the extension scalar `b`.
Source: Stacks 0A70, 0A71 and the explicit tensor-counit calculation
(blueprint: lem-trf-coinduction-tensor-comparison-model). -/
def coinductionTensorEvaluationFormula
    (F J : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : ((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
      ((((mixedTensor f).flip.map₂CochainComplex).obj F).obj
        ((coinductionComplexFunctor f).obj J)) ⟶ F ⊗ J) : Prop :=
  ∀ (p r n : ℤ) (hpr : p + r = n) (x : F.X p)
    (h : ((coinductionComplexFunctor f).obj J).X r) (b : B),
    (e.f n).hom
      ((HomologicalComplex.ιMapBifunctor F ((coinductionComplexFunctor f).obj J)
        (mixedTensor f).flip (.up ℤ) p r n hpr).hom (h ⊗ₜ[B] (b ⊗ₜ[R, f] x))) =
      (HomologicalComplex.ιTensorObj F J p r n hpr).hom
        (x ⊗ₜ[R] (CoextendScalars.equiv f (J.X r) h b))

/-- The adjunct normalization: tensor the evaluation counit, invert `1_F ⊗ η`, and
apply the right unit identification. Quantification over all K-flat representatives
fixes the derived map, rather than selecting an arbitrary natural transformation.
Source: Stacks 0A70, 0A71 and 06Y6
(blueprint: lem-trf-coinduction-tensor-comparison-model). -/
def CoinductionTensorCounitNormalized
    (J : CochainComplex (ModuleCat.{u} R) ℤ)
    (η : 𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ) ⟶ J)
    (σ : coinductionTensorSource f J ⟶ derivedCoinduction f) : Prop :=
  ∀ (F : CochainComplex (ModuleCat.{u} R) ℤ),
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F →
    ∃ s : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj (F ⊗ J),
      s.hom = DerivedCategory.Q.map ((ρ_ F).inv ≫ F ◁ η) ∧
    ∃ e : ((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
        ((((mixedTensor f).flip.map₂CochainComplex).obj F).obj
          ((coinductionComplexFunctor f).obj J)) ⟶ F ⊗ J,
      coinductionTensorEvaluationFormula f F J e ∧
      (restrictScalars f).mapDerivedCategory.map (σ.app (DerivedCategory.Q.obj F)) ≫
          (derivedCoinductionAdjunction f).counit.app (DerivedCategory.Q.obj F) =
        (restrictScalars f).mapDerivedCategory.map
            ((coinductionTensorSourceComparison f J).app F) ≫
          (restrictScalars f).mapDerivedCategoryFactors.hom.app _ ≫
          DerivedCategory.Q.map e ≫ s.inv

/-- The balanced Hom/tensor formula on each direct-sum summand. This is the underlying
ordinary Hom/tensor evaluation formula as well as its `B`-linear coinduction version;
the chain-map type imposes the signed differential equation.
Source: Stacks 0A70, 0A71 and the explicit tensor-counit calculation
(blueprint: lem-trf-coinduction-tensor-comparison-model). -/
def coinductionTensorChainFormula
    (F J I : CochainComplex (ModuleCat.{u} R) ℤ) (q : F ⊗ J ⟶ I)
    (t : ((((mixedTensor f).flip.map₂CochainComplex).obj F).obj
      ((coinductionComplexFunctor f).obj J)) ⟶ ((coinductionComplexFunctor f).obj I)) :
    Prop :=
  ∀ (p r n : ℤ) (hpr : p + r = n) (x : F.X p)
    (h : ((coinductionComplexFunctor f).obj J).X r) (b b' : B),
    CoextendScalars.equiv f (I.X n)
      ((t.f n).hom
        ((HomologicalComplex.ιMapBifunctor F ((coinductionComplexFunctor f).obj J)
          (mixedTensor f).flip (.up ℤ) p r n hpr).hom
            (h ⊗ₜ[B] (b ⊗ₜ[R, f] x)))) b' =
      (q.f n).hom ((HomologicalComplex.ιTensorObj F J p r n hpr).hom
        (x ⊗ₜ[R] (CoextendScalars.equiv f (J.X r) h (b' * b))))

/-- The canonical tensor/coinduction comparison, with all representatives and its counit
normalization. No flatness, perfectness, Noetherian or boundedness assumptions are made;
no invertibility of the comparison is asserted.
Source: Stacks 0A70 and 0A71, explicit tensor-counit calculation, and 06Y6
(blueprint: lem-trf-coinduction-tensor-comparison-model).

Proof:
1. For every K-flat F, tensoring the quasi-isomorphism η with F gives a
quasi-isomorphism F → F ⊗ J. Composing it with q gives the displayed identification
of I with K. K-injective replacements exist by def-pur-derived-internal-hom.
Apply lem-trf-derived-coinduction-adjunction to J and I to obtain the displayed dual
model and target model, with their coextension actions and evaluation counits.
The computation map of lem-pc-derived-tensor-second-factor-functor is invertible on F,
so the mixed total tensor is the source model; no flatness of J or B is required.
2. Define t(x ⊗ h)(b') = q(x ⊗ h(b')). The R-balancing relation follows from
R-linearity of q. The action (b • h)(b') = h(b'b) makes t B-linear. Since B[0] has
zero differential, the Hom differentials are postcomposition by d_J and d_I. The
chain-map equation for q and d(x ⊗ h) = dx ⊗ h + (-1)^p x ⊗ dh give the
chain-map equation for t. Direct-sum inputs have finite support, so no interchange
of an infinite sum and a product is involved (def-pur-hom-complex and
 def-pc-tensor-complex-sheaves).
3. Evaluation at one gives U(t) followed by evaluation = e followed by q. The
localized q is the composite of the identification of I with K and the inverse of
1_F ⊗ η. The representative counit equation of
lem-trf-derived-coinduction-adjunction therefore identifies the localization of t
with the adjunct of the tensor-counit map, exactly CoinductionTensorCounitNormalized.
The chain maps define the adjunct on all K-flat representatives. Their compatibility
under quasi-isomorphisms descends through localization. The adjunction bijection then
gives existence and uniqueness of σ with this normalization.
4. Forgetting the B-action leaves exactly the same formula q(x ⊗ h(b')) on the
ordinary Hom complexes (def-pur-derived-internal-hom); there is no extra sign or map.
5. Every K-flat and K-injective choice gives the same adjunct, so the localized
comparisons agree. Naturality follows by applying the counit to both composites
for any derived morphism u and using injectivity of the adjunction bijection.
For a comparison k between resolutions of R[0] commuting with their unit maps
after localization (such a k exists by K-injectivity),
the second-factor tensor comparison has the same tensor-counit adjunct. Uniqueness
therefore gives the last equation. Common K-injective comparisons give independence
for arbitrary resolutions, and the universally quantified representative equation
gives independence of F, its identification with K, I and q. -/
theorem coinduction_tensor_comparison_model
    (J : CochainComplex (ModuleCat.{u} R) ℤ) [J.IsKInjective]
    (η : 𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ) ⟶ J) [QuasiIso η] :
    (∃ d : (derivedCoinduction f).obj
        (DerivedCategory.Q.obj (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ))) ≅
          DerivedCategory.Q.obj ((coinductionComplexFunctor f).obj J),
      d.hom = (derivedCoinduction f).map (DerivedCategory.Q.map η) ≫
        (derivedCoinductionModel f J).hom) ∧
    (∀ (F : CochainComplex (ModuleCat.{u} R) ℤ),
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F →
      IsIso ((coinductionTensorSourceComparison f J).app F)) ∧
    ∃ σ : coinductionTensorSource f J ⟶ derivedCoinduction f,
      CoinductionTensorCounitNormalized f J η σ ∧
      (∀ τ : coinductionTensorSource f J ⟶ derivedCoinduction f,
        CoinductionTensorCounitNormalized f J η τ → τ = σ) ∧
      (∀ (K K' : DerivedCategory (ModuleCat.{u} R)) (u : K ⟶ K'),
        σ.app K ≫ (derivedCoinduction f).map u =
          (coinductionTensorSource f J).map u ≫ σ.app K') ∧
      (∀ (K : DerivedCategory (ModuleCat.{u} R))
        (F : CochainComplex (ModuleCat.{u} R) ℤ)
        (hF : (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat F)
        (c : DerivedCategory.Q.obj F ≅ K)
        (I : CochainComplex (ModuleCat.{u} R) ℤ) [I.IsKInjective]
        (q : F ⊗ J ⟶ I) [QuasiIso q],
        ∃ a : K ≅ DerivedCategory.Q.obj I,
          c.hom ≫ a.hom = DerivedCategory.Q.map ((ρ_ F).inv ≫ F ◁ η ≫ q) ∧
        ∃ t : ((((mixedTensor f).flip.map₂CochainComplex).obj F).obj
            ((coinductionComplexFunctor f).obj J)) ⟶
              ((coinductionComplexFunctor f).obj I),
          coinductionTensorChainFormula f F J I q t ∧
          σ.app K ≫ (derivedCoinduction f).map a.hom ≫
              (derivedCoinductionModel f I).hom =
            (coinductionTensorSource f J).map c.inv ≫
              (coinductionTensorSourceComparison f J).app F ≫ DerivedCategory.Q.map t ∧
          ∃ e : ((restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
              ((((mixedTensor f).flip.map₂CochainComplex).obj F).obj
                ((coinductionComplexFunctor f).obj J)) ⟶ F ⊗ J,
            coinductionTensorEvaluationFormula f F J e ∧
            ((restrictScalars f).mapHomologicalComplex (.up ℤ)).map t ≫
                coinductionEvaluation f I = e ≫ q) ∧
      (∀ (J' : CochainComplex (ModuleCat.{u} R) ℤ) [J'.IsKInjective]
        (η' : 𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ) ⟶ J') [QuasiIso η']
        (σ' : coinductionTensorSource f J' ⟶ derivedCoinduction f),
        CoinductionTensorCounitNormalized f J' η' σ' →
        (∃ k : J ⟶ J',
          DerivedCategory.Q.map η ≫ DerivedCategory.Q.map k = DerivedCategory.Q.map η') ∧
        (∀ (k : J ⟶ J'),
          DerivedCategory.Q.map η ≫ DerivedCategory.Q.map k = DerivedCategory.Q.map η' →
          IsIso (((DerivedCategory.exists_derivedTensor_second_factor_functor f).2.choose).map
            ((coinductionComplexFunctor f).map k)) ∧
          (((DerivedCategory.exists_derivedTensor_second_factor_functor f).2.choose).map
            ((coinductionComplexFunctor f).map k)) ≫ σ' = σ)) := by
  sorry

end ModuleCat
