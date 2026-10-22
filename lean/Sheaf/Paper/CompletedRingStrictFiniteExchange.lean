/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module
public import Sheaf.Paper.CompletedFiniteComparisonModels
import Sheaf.Paper.NormalizedFiniteComparisonExistence
import Sheaf.Paper.CompletedFiniteScalarExchange
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Sheaf.Paper.CompletedStrictOpenExchange
public import Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedExtensionZeroBaseChange
/-!
# Strict finite open exchange over completed rings
Source: blueprint sec-six-functors-basics/sk-prop-sf-cbc,
lem-cbc-completed-extension-zero-comparison.proof.md, finite exchange before Rlim;
Stacks 03DI, 03DJ, 04J0, 06XN and 099N
(blueprint: lem-cbc-completed-ring-strict-finite-exchange).
This identifies the simultaneous strict exchange with the canonical finite
open-unit exchange, on reductions of arbitrary unbounded completed-ring objects.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped ZeroObject
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  Functor.leftAdjoint limit
variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'}
  {j : U ⟶ X} {g : X' ⟶ X} (sq : OpenImmersionSquare gU j' j g)
open AlgebraicGeometry.ProEtale.StrictTower
attribute [-instance] CategoryTheory.catToReflQuiver in
private def complexCounit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh) :
    DerivedCategory.Q ⋙ LF ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso C).inv LF ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (.up ℤ)) ε ≫
    Functor.whiskerRight (F.mapHomotopyCategoryFactors (.up ℤ)).hom DerivedCategory.Qh ≫
    Functor.whiskerLeft (F.mapHomologicalComplex (.up ℤ))
      (DerivedCategory.quotientCompQhIso D).hom
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem complexCounit_app
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] (LF : DerivedCategory C ⥤ DerivedCategory D)
    (ε : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex C ℤ) :
    (complexCounit F LF ε).app P = Functor.leftDerivedCounitOnComplex F LF ε P := rfl
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finiteSourceModel_isIso (n : ℕ)
    (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P) :
    IsIso (cbcFiniteSourceModelMap d sq n P) := by
  have := pbcExtensionCounit_isIso (pbcAdicProjection U d n) P hP
  dsimp only [cbcFiniteSourceModelMap, cbcFiniteReductionModelMap, pbcComplexCounit]
  infer_instance
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem finiteTargetModel_isIso (n : ℕ)
    (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P) :
    IsIso (cbcFiniteTargetModelMap d sq n P) := by
  have := pbcExtensionCounit_isIso (pbcAdicProjection U d n) P hP
  dsimp only [cbcFiniteTargetModelMap, cbcFiniteReductionModelMap, pbcComplexCounit]
  infer_instance
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem kflat_resolutions (T : Scheme.{u})
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    ∃ (P : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) (s : P ⟶ K),
      CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion T d) P ∧
        QuasiIso s := by
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := pbcAdicCompletion T d) K
  exact ⟨P, s, hP, hs⟩
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tower_resolutions (T : Scheme.{u})
    (K : CochainComplex (pbcTowers T (pbcAdicCompletion T d)) ℤ) :
    ∃ (P : CochainComplex (pbcTowers T (pbcAdicCompletion T d)) ℤ) (s : P ⟶ K),
      (∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients
        (R := pbcAdicCompletion T d)
        ((((CategoryTheory.evaluation ℕᵒᵖ (pbcModules T (pbcAdicCompletion T d))).obj
          (op n)).mapHomologicalComplex (.up ℤ)).obj P)) ∧ QuasiIso s := by
  obtain ⟨R, s, hR, hs⟩ := cbcTowerKFlat_resolution d T K
  exact ⟨R, s, hR.1, hs⟩
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem naturality_ladder
    {C : Type*} [Category C]
    {x₀ x₁ x₂ x₃ y₁ y₂ r₀ r₁ r₂ r₃ s₁ s₂ : C}
    {a : x₀ ⟶ x₁} {b : x₁ ⟶ x₂} {c : x₂ ⟶ x₃}
    {d₀ : x₀ ⟶ y₁} {e : y₁ ⟶ y₂} {f : y₂ ⟶ x₃}
    {a' : r₀ ⟶ r₁} {b' : r₁ ⟶ r₂} {c' : r₂ ⟶ r₃}
    {d' : r₀ ⟶ s₁} {e' : s₁ ⟶ s₂} {f' : s₂ ⟶ r₃}
    {u₀ : r₀ ⟶ x₀} {u₁ : r₁ ⟶ x₁} {u₂ : r₂ ⟶ x₂}
    {u₃ : r₃ ⟶ x₃} {v₁ : s₁ ⟶ y₁} {v₂ : s₂ ⟶ y₂} [Epi u₀]
    (ha : u₀ ≫ a = a' ≫ u₁) (hb : u₁ ≫ b = b' ≫ u₂)
    (hc : u₂ ≫ c = c' ≫ u₃) (hr : a' ≫ b' ≫ c' = d' ≫ e' ≫ f')
    (hd : u₀ ≫ d₀ = d' ≫ v₁) (he : v₁ ≫ e = e' ≫ v₂)
    (hf : v₂ ≫ f = f' ≫ u₃) : a ≫ b ≫ c = d₀ ≫ e ≫ f := by
  apply (cancel_epi u₀).1
  rw [reassoc_of% ha, reassoc_of% hb, hc, reassoc_of% hr,
    reassoc_of% hd, reassoc_of% he, hf]
private theorem functor_normalization_descent
    {C D E F DC DD DE DF : Type*}
    [Category C] [Category D] [Category E] [Category F]
    [Category DC] [Category DD] [Category DE] [Category DF]
    (Q₀ : C ⥤ DC) (Q₁ : D ⥤ DD) (Q₂ : E ⥤ DE) (Q₃ : F ⥤ DF)
    (J : C ⥤ D) (J' : E ⥤ F) (G : D ⥤ F) (H : C ⥤ E)
    (LJ : DC ⥤ DD) (LJ' : DE ⥤ DF) (LG : DD ⥤ DF) (LH : DC ⥤ DE)
    (eJ : Q₀ ⋙ LJ ⟶ J ⋙ Q₁) (eJ' : Q₂ ⋙ LJ' ⟶ J' ⋙ Q₃)
    (cG : ∀ P : D, LG.obj (Q₁.obj P) ⟶ Q₃.obj (G.obj P))
    (cH : ∀ P : C, LH.obj (Q₀.obj P) ⟶ Q₂.obj (H.obj P))
    (nG : ∀ {P R : D} (s : P ⟶ R),
      LG.map (Q₁.map s) ≫ cG R = cG P ≫ Q₃.map (G.map s))
    (nH : ∀ {P R : C} (s : P ⟶ R),
      LH.map (Q₀.map s) ≫ cH R = cH P ≫ Q₂.map (H.map s))
    (β : LJ ⋙ LG ≅ LH ⋙ LJ') (τ : H ⋙ J' ⟶ J ⋙ G)
    {R P : C} (s : R ⟶ P) [IsIso (Q₀.map s)]
    (hr : HEq (β.inv.app (Q₀.obj R) ≫ LG.map (eJ.app R) ≫ cG (J.obj R))
      (LJ'.map (cH R) ≫ eJ'.app (H.obj R) ≫ Q₃.map (τ.app R))) :
    HEq (β.inv.app (Q₀.obj P) ≫ LG.map (eJ.app P) ≫ cG (J.obj P))
      (LJ'.map (cH P) ≫ eJ'.app (H.obj P) ≫ Q₃.map (τ.app P)) := by
  have hb := β.inv.naturality (Q₀.map s)
  simp only [Functor.comp_map] at hb
  have hj := congrArg LG.map (eJ.naturality s)
  simp only [Functor.comp_map, Functor.map_comp] at hj
  have hg := nG (J.map s)
  have hg' := congrArg LJ'.map (nH s)
  simp only [Functor.map_comp] at hg'
  have hj' := eJ'.naturality (H.map s)
  simp only [Functor.comp_map] at hj'
  have ht := τ.naturality s
  simp only [Functor.comp_map] at ht
  have ht' := congrArg Q₃.map ht
  simp only [Functor.map_comp] at ht'
  apply heq_of_eq
  exact naturality_ladder hb hj hg (eq_of_heq hr) hg' hj' ht'
private theorem derivedPairNormalization_of_covers
    {B C T V : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [Category T] [Abelian T] [Category V] [Abelian V]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory T] [HasDerivedCategory V]
    (F : B ⥤ T) [F.Additive] (G : C ⥤ V) [G.Additive]
    (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (H : T ⥤ V) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (LF : DerivedCategory B ⥤ DerivedCategory T)
    (LG : DerivedCategory C ⥤ DerivedCategory V)
    (εF : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : F ⋙ H ⟶ P ⋙ G) (M : CochainComplex B ℤ → Prop)
    (b : P.mapDerivedCategory ⋙ LG ≅ LF ⋙ H.mapDerivedCategory)
    (hnorm : DerivedPairExchangeNormalization F G P H LF LG εF εG e M b)
    (hcov : ∀ K : CochainComplex B ℤ,
      ∃ (R : CochainComplex B ℤ) (s : R ⟶ K), M R ∧ QuasiIso s) :
    DerivedPairExchangeNormalization F G P H LF LG εF εG e (fun _ ↦ True) b := by
  intro K _
  obtain ⟨R, s, hR, hs⟩ := hcov K
  have : QuasiIso s := hs
  have nG {K L : CochainComplex C ℤ} (s : K ⟶ L) :
      LG.map (DerivedCategory.Q.map s) ≫ Functor.leftDerivedCounitOnComplex G LG εG L =
      Functor.leftDerivedCounitOnComplex G LG εG K ≫
        DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map s) := by
    have h := (complexCounit G LG εG).naturality s
    simpa only [Functor.comp_map, complexCounit_app] using h
  have nF {K L : CochainComplex B ℤ} (s : K ⟶ L) :
      LF.map (DerivedCategory.Q.map s) ≫ Functor.leftDerivedCounitOnComplex F LF εF L =
      Functor.leftDerivedCounitOnComplex F LF εF K ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map s) := by
    have h := (complexCounit F LF εF).naturality s
    simpa only [Functor.comp_map, complexCounit_app] using h
  exact functor_normalization_descent
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (P.mapHomologicalComplex (.up ℤ)) (H.mapHomologicalComplex (.up ℤ))
    (G.mapHomologicalComplex (.up ℤ)) (F.mapHomologicalComplex (.up ℤ))
    P.mapDerivedCategory H.mapDerivedCategory LG LF
    P.mapDerivedCategoryFactors.hom H.mapDerivedCategoryFactors.hom
    (Functor.leftDerivedCounitOnComplex G LG εG)
    (Functor.leftDerivedCounitOnComplex F LF εF) @nG @nF b
    (e.mapHomologicalComplex (.up ℤ)) s (hnorm R hR)
private theorem comparison_diagram
    {C : Type*} [Category C] {A B A₁ B₁ A₂ B₂ T S T₁ S₁ : C}
    {a : A ⟶ B} {s : B ⟶ S} {t : A ⟶ T}
    {b : B ⟶ B₁} {c : A ⟶ A₁} {β : A₁ ⟶ B₁}
    {p : B₁ ⟶ B₂} {q : A₁ ⟶ A₂} {w : A₂ ⟶ B₂}
    {v : A₂ ⟶ T₁} {u : B₂ ⟶ S₁} {δ : T ⟶ S}
    {ms : S ⟶ S₁} {mt : T ⟶ T₁} {k : T₁ ⟶ S₁} [Mono ms]
    (hs : b ≫ p ≫ u = s ≫ ms) (ht : c ≫ q ≫ v = t ≫ mt)
    (hm : a ≫ b = c ≫ β) (he : β ≫ p = q ≫ w)
    (hl : w ≫ u = v ≫ k) (hf : δ ≫ ms = mt ≫ k) : a ≫ s = t ≫ δ := by
  apply (cancel_mono ms).1
  simp only [Category.assoc]
  rw [← hs, reassoc_of% hm, reassoc_of% he, hl, reassoc_of% ht, ← hf]
private theorem functor_comparison_diagram
    {C T X V Y B D DY DD : Type*}
    [Category C] [Category T] [Category X] [Category V] [Category Y]
    [Category B] [Category D] [Category DY] [Category DD]
    (R : C ⥤ T) (J : T ⥤ X) (G : X ⥤ Y) (H : T ⥤ V) (J' : V ⥤ Y)
    (E : Y ⥤ D) (S : C ⥤ B) (FS FT : B ⥤ D)
    (QY : Y ⥤ DY) (QD : D ⥤ DD)
    (LE : DY ⥤ DD)
    (eE : QY ⋙ LE ⟶ E ⋙ QD)
    (τ : H ⋙ J' ⟶ J ⋙ G)
    (σ : R ⋙ J ⋙ G ⋙ E ⟶ S ⋙ FS) (θ : R ⋙ H ⋙ J' ⋙ E ⟶ S ⋙ FT)
    (δ : FT ⟶ FS) (P : C)
    {A₀ B₀ : DY} {S₀ T₀ : DD} (a : A₀ ⟶ B₀)
    (b : B₀ ⟶ QY.obj (G.obj (J.obj (R.obj P))))
    (c : A₀ ⟶ QY.obj (J'.obj (H.obj (R.obj P))))
    (s : LE.obj B₀ ⟶ S₀) (t : LE.obj A₀ ⟶ T₀)
    (ms : S₀ ⟶ QD.obj (FS.obj (S.obj P)))
    (mt : T₀ ⟶ QD.obj (FT.obj (S.obj P)))
    (ζ : T₀ ⟶ S₀) [_hms : Mono ms]
    (hs : HEq (LE.map b ≫ eE.app (G.obj (J.obj (R.obj P))) ≫
      QD.map (σ.app P)) (s ≫ ms))
    (ht : HEq (LE.map c ≫ eE.app (J'.obj (H.obj (R.obj P))) ≫
      QD.map (θ.app P)) (t ≫ mt))
    (hm : a ≫ b = c ≫ QY.map (τ.app (R.obj P)))
    (hl : E.map (τ.app (R.obj P)) ≫ σ.app P =
      θ.app P ≫ δ.app (S.obj P))
    (hf : ζ ≫ ms = mt ≫ QD.map (δ.app (S.obj P))) :
    LE.map a ≫ s = t ≫ ζ := by
  have hm' := congrArg LE.map hm
  simp only [Functor.map_comp] at hm'
  have he := eE.naturality (τ.app (R.obj P))
  simp only [Functor.comp_map] at he
  have hl' := congrArg QD.map hl
  simp only [Functor.map_comp] at hl'
  exact comparison_diagram (eq_of_heq hs) (eq_of_heq ht) hm' he hl' hf
private theorem ordinary_functor_comparison_diagram
    {C T X V Y B D DY DD : Type*}
    [Category C] [Category T] [Category X] [Category V] [Category Y]
    [Category B] [Category D] [Category DY] [Category DD]
    [HasZeroMorphisms C] [HasZeroMorphisms T] [HasZeroMorphisms X]
    [HasZeroMorphisms V] [HasZeroMorphisms Y] [HasZeroMorphisms B] [HasZeroMorphisms D]
    (R : C ⥤ T) (J : T ⥤ X) (G : X ⥤ Y) (H : T ⥤ V) (J' : V ⥤ Y)
    (E : Y ⥤ D) (S : C ⥤ B) (FS FT : B ⥤ D)
    [hR : R.PreservesZeroMorphisms] [hJ : J.PreservesZeroMorphisms] [hG : G.PreservesZeroMorphisms]
    [hH : H.PreservesZeroMorphisms]
    [hJp : J'.PreservesZeroMorphisms]
    [hE : E.PreservesZeroMorphisms]
    [hS : S.PreservesZeroMorphisms]
    [hFS : FS.PreservesZeroMorphisms]
    [hFT : FT.PreservesZeroMorphisms]
    (QY : CochainComplex Y ℤ ⥤ DY) (QD : CochainComplex D ℤ ⥤ DD)
    (LE : DY ⥤ DD)
    (eE : QY ⋙ LE ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ QD)
    (τ : H ⋙ J' ⟶ J ⋙ G)
    (σ : R ⋙ J ⋙ G ⋙ E ⟶ S ⋙ FS) (θ : R ⋙ H ⋙ J' ⋙ E ⟶ S ⋙ FT)
    (δ : FT ⟶ FS) (P : CochainComplex C ℤ)
    {A₀ B₀ : DY} {S₀ T₀ : DD} (a : A₀ ⟶ B₀)
    (b : B₀ ⟶ QY.obj ((G.mapHomologicalComplex (.up ℤ)).obj
      ((J.mapHomologicalComplex (.up ℤ)).obj ((R.mapHomologicalComplex (.up ℤ)).obj P))))
    (c : A₀ ⟶ QY.obj ((J'.mapHomologicalComplex (.up ℤ)).obj
      ((H.mapHomologicalComplex (.up ℤ)).obj ((R.mapHomologicalComplex (.up ℤ)).obj P))))
    (s : LE.obj B₀ ⟶ S₀) (t : LE.obj A₀ ⟶ T₀)
    (ms : S₀ ⟶ QD.obj ((FS.mapHomologicalComplex (.up ℤ)).obj
      ((S.mapHomologicalComplex (.up ℤ)).obj P)))
    (mt : T₀ ⟶ QD.obj ((FT.mapHomologicalComplex (.up ℤ)).obj
      ((S.mapHomologicalComplex (.up ℤ)).obj P)))
    (ζ : T₀ ⟶ S₀) [_hms : Mono ms]
    (hs : HEq (LE.map b ≫ eE.app ((G.mapHomologicalComplex (.up ℤ)).obj
      ((J.mapHomologicalComplex (.up ℤ)).obj ((R.mapHomologicalComplex (.up ℤ)).obj P))) ≫
      QD.map ((σ.mapHomologicalComplex (.up ℤ)).app P)) (s ≫ ms))
    (ht : HEq (LE.map c ≫ eE.app ((J'.mapHomologicalComplex (.up ℤ)).obj
      ((H.mapHomologicalComplex (.up ℤ)).obj ((R.mapHomologicalComplex (.up ℤ)).obj P))) ≫
      QD.map ((θ.mapHomologicalComplex (.up ℤ)).app P)) (t ≫ mt))
    (hm : a ≫ b = c ≫ QY.map ((τ.mapHomologicalComplex (.up ℤ)).app
      ((R.mapHomologicalComplex (.up ℤ)).obj P)))
    (hl : ∀ M : C, E.map (τ.app (R.obj M)) ≫ σ.app M = θ.app M ≫ δ.app (S.obj M))
    (hf : ζ ≫ ms = mt ≫ QD.map ((δ.mapHomologicalComplex (.up ℤ)).app
      ((S.mapHomologicalComplex (.up ℤ)).obj P))) : LE.map a ≫ s = t ≫ ζ := by
  refine functor_comparison_diagram
    (R.mapHomologicalComplex (.up ℤ)) (J.mapHomologicalComplex (.up ℤ))
    (G.mapHomologicalComplex (.up ℤ)) (H.mapHomologicalComplex (.up ℤ))
    (J'.mapHomologicalComplex (.up ℤ)) (E.mapHomologicalComplex (.up ℤ))
    (S.mapHomologicalComplex (.up ℤ)) (FS.mapHomologicalComplex (.up ℤ))
    (FT.mapHomologicalComplex (.up ℤ)) QY QD LE eE
    (τ.mapHomologicalComplex (.up ℤ)) (σ.mapHomologicalComplex (.up ℤ))
    (θ.mapHomologicalComplex (.up ℤ)) (δ.mapHomologicalComplex (.up ℤ)) P
    a b c s t ms mt ζ hs ht hm ?_ hf
  apply HomologicalComplex.hom_ext
  intro i
  exact hl (P.X i)
private theorem compose_naturality_normalization
    {C : Type*} [Category C] {x y z w a₁ a₂ a₃ : C}
    {a : x ⟶ y} {b : y ⟶ z} {c : x ⟶ w} {d₀ : w ⟶ z}
    {e : z ⟶ a₁} {f : a₁ ⟶ a₃} {g₀ : y ⟶ a₂} {h : a₂ ⟶ a₃}
    (hn : a ≫ b = c ≫ d₀) (hr : HEq (b ≫ e ≫ f) (g₀ ≫ h)) :
    c ≫ d₀ ≫ e ≫ f = a ≫ g₀ ≫ h := by
  rw [← reassoc_of% hn, eq_of_heq hr]
private theorem derivedPair_model_square
    {B C T V Z : Type*} [Category B] [Abelian B] [Category C] [Abelian C]
    [Category T] [Abelian T] [Category V] [Abelian V] [Category Z] [Abelian Z]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory T] [HasDerivedCategory V] [HasDerivedCategory Z]
    (F : B ⥤ T) [F.Additive] (G : C ⥤ V) [G.Additive]
    (P : B ⥤ C) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (H : T ⥤ V) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (LF : DerivedCategory B ⥤ DerivedCategory T)
    (LG : DerivedCategory C ⥤ DerivedCategory V)
    (εF : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (e : F ⋙ H ⟶ P ⋙ G)
    (b : P.mapDerivedCategory ⋙ LG ≅ LF ⋙ H.mapDerivedCategory)
    (hnorm : DerivedPairExchangeNormalization F G P H LF LG εF εG e (fun _ ↦ True) b)
    (R : Z ⥤ B) [R.Additive] (LR : DerivedCategory Z ⥤ DerivedCategory B)
    (K : CochainComplex Z ℤ)
    (ρ : LR.obj (DerivedCategory.Q.obj K) ⟶
      DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj K)) :
    b.inv.app (LR.obj (DerivedCategory.Q.obj K)) ≫
      LG.map (P.mapDerivedCategory.map ρ ≫ P.mapDerivedCategoryFactors.hom.app
        ((R.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      Functor.leftDerivedCounitOnComplex G LG εG
        ((P.mapHomologicalComplex (.up ℤ)).obj
          ((R.mapHomologicalComplex (.up ℤ)).obj K)) =
    H.mapDerivedCategory.map (LF.map ρ ≫ Functor.leftDerivedCounitOnComplex F LF εF
      ((R.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj K)) ≫
      DerivedCategory.Q.map ((e.mapHomologicalComplex (.up ℤ)).app
        ((R.mapHomologicalComplex (.up ℤ)).obj K)) := by
  have hn := b.inv.naturality ρ
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  exact compose_naturality_normalization hn (hnorm _ trivial)
private theorem derivedPair_finite_comparison
    {C T X V Y B D : Type*}
    [Category C] [Abelian C] [Category T] [Abelian T]
    [Category X] [Abelian X] [Category V] [Abelian V]
    [Category Y] [Abelian Y] [Category B] [Abelian B] [Category D] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory T] [HasDerivedCategory X]
    [HasDerivedCategory V] [HasDerivedCategory Y] [HasDerivedCategory B]
    [HasDerivedCategory D]
    (R : C ⥤ T) (J : T ⥤ X) (G : X ⥤ Y) (H : T ⥤ V) (J' : V ⥤ Y)
    (E : Y ⥤ D) (S : C ⥤ B) (FS FT : B ⥤ D)
    [hR : R.Additive] [hJ : J.Additive] [hG : G.Additive] [hH : H.Additive]
    [hJp : J'.Additive] [hE : E.Additive] [hS : S.Additive]
    [hFS : FS.Additive] [hFT : FT.Additive]
    [hJL : PreservesFiniteLimits J] [hJC : PreservesFiniteColimits J]
    [hJpL : PreservesFiniteLimits J'] [hJpC : PreservesFiniteColimits J']
    [hEL : PreservesFiniteLimits E] [hEC : PreservesFiniteColimits E]
    (LR : DerivedCategory C ⥤ DerivedCategory T)
    (LG : DerivedCategory X ⥤ DerivedCategory Y)
    (LH : DerivedCategory T ⥤ DerivedCategory V)
    (εG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (εH : DerivedCategory.Qh ⋙ LH ⟶ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (β : J.mapDerivedCategory ⋙ LG ≅ LH ⋙ J'.mapDerivedCategory)
    (τ : H ⋙ J' ⟶ J ⋙ G)
    (hnorm : DerivedPairExchangeNormalization H G J J' LH LG εH εG τ
      (fun _ ↦ True) β)
    (σ : R ⋙ J ⋙ G ⋙ E ⟶ S ⋙ FS) (θ : R ⋙ H ⋙ J' ⋙ E ⟶ S ⋙ FT)
    (δ : FT ⟶ FS) (P : CochainComplex C ℤ)
    (ρ : LR.obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj ((R.mapHomologicalComplex (.up ℤ)).obj P)) :
    let a := β.inv.app (LR.obj (DerivedCategory.Q.obj P))
    let b := LG.map (J.mapDerivedCategory.map ρ ≫ J.mapDerivedCategoryFactors.hom.app
        ((R.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      Functor.leftDerivedCounitOnComplex G LG εG
        ((J.mapHomologicalComplex (.up ℤ)).obj ((R.mapHomologicalComplex (.up ℤ)).obj P))
    let c := J'.mapDerivedCategory.map (LH.map ρ ≫
        Functor.leftDerivedCounitOnComplex H LH εH
          ((R.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      J'.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj P))
    ∀ {S₀ T₀ : DerivedCategory D}
      (s : E.mapDerivedCategory.obj (LG.obj (J.mapDerivedCategory.obj
        (LR.obj (DerivedCategory.Q.obj P)))) ⟶ S₀)
      (t : E.mapDerivedCategory.obj (J'.mapDerivedCategory.obj
        (LH.obj (LR.obj (DerivedCategory.Q.obj P)))) ⟶ T₀)
      (ms : S₀ ⟶ DerivedCategory.Q.obj ((FS.mapHomologicalComplex (.up ℤ)).obj
        ((S.mapHomologicalComplex (.up ℤ)).obj P)))
      (mt : T₀ ⟶ DerivedCategory.Q.obj ((FT.mapHomologicalComplex (.up ℤ)).obj
        ((S.mapHomologicalComplex (.up ℤ)).obj P)))
      (ζ : T₀ ⟶ S₀) [_hms : Mono ms],
      HEq (E.mapDerivedCategory.map b ≫ E.mapDerivedCategoryFactors.hom.app
          ((G.mapHomologicalComplex (.up ℤ)).obj ((J.mapHomologicalComplex (.up ℤ)).obj
            ((R.mapHomologicalComplex (.up ℤ)).obj P))) ≫
        DerivedCategory.Q.map ((σ.mapHomologicalComplex (.up ℤ)).app P)) (s ≫ ms) →
      HEq (E.mapDerivedCategory.map c ≫ E.mapDerivedCategoryFactors.hom.app
          ((J'.mapHomologicalComplex (.up ℤ)).obj ((H.mapHomologicalComplex (.up ℤ)).obj
            ((R.mapHomologicalComplex (.up ℤ)).obj P))) ≫
        DerivedCategory.Q.map ((θ.mapHomologicalComplex (.up ℤ)).app P)) (t ≫ mt) →
      (∀ M : C, E.map (τ.app (R.obj M)) ≫ σ.app M = θ.app M ≫ δ.app (S.obj M)) →
      (ζ ≫ ms = mt ≫ DerivedCategory.Q.map ((δ.mapHomologicalComplex (.up ℤ)).app
        ((S.mapHomologicalComplex (.up ℤ)).obj P))) →
      E.mapDerivedCategory.map a ≫ s = t ≫ ζ := by
  dsimp only
  intro S₀ T₀ s t ms mt ζ _hms hs ht hl hf
  refine ordinary_functor_comparison_diagram R J G H J' E S FS FT
    DerivedCategory.Q DerivedCategory.Q E.mapDerivedCategory E.mapDerivedCategoryFactors.hom
    τ σ θ δ P (β.inv.app (LR.obj (DerivedCategory.Q.obj P))) _ _
    s t ms mt ζ hs ht ?_ hl hf
  simpa only [Category.assoc] using
    derivedPair_model_square H G J J' LH LG εH εG τ β hnorm R LR P ρ
section
attribute [local implicit_reducible] cbcStrictOpen Functor.mapHomologicalComplex
  catToReflQuiver
attribute [local irreducible] Functor.mapDerivedCategory
  cbcStrictOpenModule completedTowerModulePullback completedModulePullback
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
private theorem strict_normalization_everywhere :
    DerivedPairExchangeNormalization
      (completedTowerModulePullback gU d) (completedTowerModulePullback g d)
      (cbcStrictOpenModule d j sq.isOpenImmersion)
      (cbcStrictOpenModule d j' sq.isOpenImmersion')
      (completedTowerPullback gU d) (completedTowerPullback g d)
      (completedTowerPullbackCounit gU d) (completedTowerPullbackCounit g d)
      (cbcStrictInverseModule d sq) (fun _ ↦ True) (cbcStrictExchange d sq) := by
  have := cbcStrictOpenModule_additive d j sq.isOpenImmersion
  have := cbcStrictOpenModule_additive d j' sq.isOpenImmersion'
  have hnorm : CbcStrictExchangeNormalization d sq (cbcStrictExchange d sq) := by
    simpa only [cbcStrictExchange] using (cbcStrictExchange_existsUnique d sq).exists.choose_spec
  exact derivedPairNormalization_of_covers
    (completedTowerModulePullback gU d) (completedTowerModulePullback g d)
    (cbcStrictOpenModule d j sq.isOpenImmersion)
    (cbcStrictOpenModule d j' sq.isOpenImmersion')
    (completedTowerPullback gU d) (completedTowerPullback g d)
    (completedTowerPullbackCounit gU d) (completedTowerPullbackCounit g d)
    (cbcStrictInverseModule d sq) _ (cbcStrictExchange d sq) hnorm (tower_resolutions d U)
end
/-- Both finite comparison maps exist uniquely with their representative normalizations.
Source: Stacks 099N, 03DI, 06XN
(blueprint: lem-cbc-completed-ring-strict-finite-exchange).
Proof: use the normalized finite-evaluation comparison for completed tower pullback.
Open extension commutes with reduction by the summand tensor map [p] tensor b to
[p tensor b restricted to the open]. The constant-section comparisons and the
finite open/pullback scalar mates then give cbcSourceLevel and cbcTargetLevel on
ordinary models. Their tensor formulas agree with the universal counits. Flatness
of constant-to-completed coefficients makes these comparisons invertible on
K-flat representatives. Resolve an arbitrary complex and descend the natural
comparisons; the representative equations determine them uniquely. -/
theorem cbcFiniteComparisons_existsUnique (n : ℕ) :
    (∃! e : completedReductionTower U d ⋙ cbcStrictOpen d j sq.isOpenImmersion ⋙
          completedTowerPullback g d ⋙ pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
        cbcFiniteReduction d U n ⋙ (cbcFiniteSource d sq n).mapDerivedCategory,
      CbcSourceFiniteNormalization d sq n e) ∧
    (∃! e : completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
          cbcStrictOpen d j' sq.isOpenImmersion' ⋙
            pbcTowerEvaluation X' (pbcAdicCompletion X' d) n ≅
        cbcFiniteReduction d U n ⋙ (cbcFiniteTarget d sq n).mapDerivedCategory,
      CbcTargetFiniteNormalization d sq n e)  := by
  obtain ⟨⟨e, he⟩, ⟨f, hf⟩⟩ := cbcNormalizedFiniteComparison_exists d sq n
  constructor
  · refine ⟨e, he, ?_⟩
    intro z hz
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (pbcModules U (pbcAdicCompletion U d)) (.up ℤ))
    intro K
    obtain ⟨P, s, hP, hs⟩ := kflat_resolutions d U K
    have : QuasiIso s := hs
    have hmodel := finiteSourceModel_isIso d sq n P hP
    have hp : z.hom.app (DerivedCategory.Q.obj P) = e.hom.app
        (DerivedCategory.Q.obj P) := by
      apply (cancel_mono (cbcFiniteSourceModelMap d sq n P)).1
      exact eq_of_heq ((hz P hP).symm.trans (he P hP))
    apply (cancel_epi ((completedReductionTower U d ⋙
      cbcStrictOpen d j sq.isOpenImmersion ⋙ completedTowerPullback g d ⋙
      pbcTowerEvaluation X' (pbcAdicCompletion X' d) n).map (DerivedCategory.Q.map s))).1
    rw [z.hom.naturality, e.hom.naturality, hp]
  · refine ⟨f, hf, ?_⟩
    intro z hz
    apply Iso.ext
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (pbcModules U (pbcAdicCompletion U d)) (.up ℤ))
    intro K
    obtain ⟨P, s, hP, hs⟩ := kflat_resolutions d U K
    have : QuasiIso s := hs
    have hmodel := finiteTargetModel_isIso d sq n P hP
    have hp : z.hom.app (DerivedCategory.Q.obj P) = f.hom.app
        (DerivedCategory.Q.obj P) := by
      apply (cancel_mono (cbcFiniteTargetModelMap d sq n P)).1
      exact eq_of_heq ((hz P hP).symm.trans (hf P hP))
    apply (cancel_epi ((completedReductionTower U d ⋙ completedTowerPullback gU d ⋙
      cbcStrictOpen d j' sq.isOpenImmersion' ⋙
      pbcTowerEvaluation X' (pbcAdicCompletion X' d) n).map (DerivedCategory.Q.map s))).1
    rw [z.hom.naturality, f.hom.naturality, hp]
/-- The canonical finite source identification, with its fixed counit equation.
Source: Stacks 099N (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
@[irreducible] def cbcSourceFiniteComparison (n : ℕ) :=
  (cbcFiniteComparisons_existsUnique d sq n).1.exists.choose
/-- The canonical finite target identification, with the same representative convention.
Source: Stacks 099N (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
@[irreducible] def cbcTargetFiniteComparison (n : ℕ) :=
  (cbcFiniteComparisons_existsUnique d sq n).2.exists.choose
/-- The finite inverse exchange with its completed-ring action, before localization.
Its component is exactly the open-unit adjunct, not an unrelated derived morphism.
Source: Stacks 03DI (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
def cbcFiniteInverse (n : ℕ) : cbcFiniteTarget d sq n ⟶ cbcFiniteSource d sq n :=
  Functor.whiskerRight
    (@singleBetaInv.{u} (cbcFiniteRing d n) _ U' U X' X gU j' j g
      sq.isOpenImmersion sq.isOpenImmersion' sq.w) (cbcFiniteRes d X' n)
/-- The finite inverse is invertible for the chosen cartesian square.
Source: Stacks 03DI (blueprint: lem-cbc-completed-ring-strict-finite-exchange).
Proof: apply finite open base change to IsPullback.of_iso_pullback for the chosen
square. Scalar restriction preserves the resulting isomorphism. -/
@[instance] theorem cbcFiniteInverse_isIso (n : ℕ) : IsIso (cbcFiniteInverse d sq n) := by
  let := sq.isOpenImmersion
  let := sq.isOpenImmersion'
  have := singleBetaInv_isIso (cbcFiniteRing d n) gU j' j g sq.w
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd)
  unfold cbcFiniteInverse
  infer_instance
/-- The canonical finite exchange after restriction of its finite scalar action.
Source: Stacks 03DI (blueprint: lem-cbc-completed-ring-strict-finite-exchange). -/
def cbcFiniteExchange (n : ℕ) :=
  Functor.mapDerivedCategoryNatIso (asIso (cbcFiniteInverse d sq n)).symm
private theorem ordinary_level_inverse (n : ℕ)
    (M : pbcModules U (pbcAdicCompletion U d)) :
    ((CategoryTheory.evaluation ℕᵒᵖ (pbcModules X' (pbcAdicCompletion X' d))).obj (op n)).map
        ((cbcStrictInverseModule d sq).app ((completedReductionModuleTowerFunctor U d).obj M)) ≫
      (cbcSourceLevel d sq n).hom.app M =
    (cbcTargetLevel d sq n).hom.app M ≫
      (cbcFiniteInverse d sq n).app ((cbcFiniteReductionModule d U n).obj M) := by
  simp only [CategoryTheory.evaluation_obj_map, cbcStrictInverseModule,
    cbcStrictInverseComponent, cbcSourceLevel, cbcTargetLevel, cbcFiniteInverse,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Category.assoc]
  have hn := (cbcUnderivedInverseExchange d sq).naturality
    ((cbcFiniteLevel d U n).hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj, CategoryTheory.evaluation_obj_obj] at hn ⊢
  erw [← reassoc_of% hn, ← cbcFiniteScalarExchange_inverse d sq n
    ((cbcFiniteReductionModule d U n).obj M)]
private theorem finite_model_inverse (n : ℕ)
    (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ) :
    (cbcFiniteExchange d sq n).inv.app
        ((cbcFiniteReduction d U n).obj (DerivedCategory.Q.obj P)) ≫
        cbcFiniteSourceModelMap d sq n P =
      cbcFiniteTargetModelMap d sq n P ≫ DerivedCategory.Q.map
        (((cbcFiniteInverse d sq n).mapHomologicalComplex (.up ℤ)).app
          (((cbcFiniteReductionModule d U n).mapHomologicalComplex (.up ℤ)).obj P)) := by
  have hn := (cbcFiniteExchange d sq n).inv.naturality (cbcFiniteReductionModelMap d U n P)
  dsimp only [cbcFiniteSourceModelMap, cbcFiniteTargetModelMap]
  rw [← Category.assoc, ← hn, Category.assoc]
  have he := Functor.mapDerivedCategoryNatIso_fac (asIso (cbcFiniteInverse d sq n))
    (((cbcFiniteReductionModule d U n).mapHomologicalComplex (.up ℤ)).obj P)
  simp only [asIso_hom] at he
  dsimp only [cbcFiniteExchange]
  erw [he]
  exact (Category.assoc _ _ _).symm
section
attribute [local implicit_reducible] cbcStrictOpen Functor.mapHomologicalComplex
  catToReflQuiver completedReductionCoefficient reductionCoefficientSystem
attribute [local irreducible] Functor.mapDerivedCategory
  cbcStrictOpenModule completedTowerModulePullback completedModulePullback
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
private theorem inverse_on_kflat (n : ℕ)
    (P : CochainComplex (pbcModules U (pbcAdicCompletion U d)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := pbcAdicCompletion U d) P) :
    (pbcTowerEvaluation X' (pbcAdicCompletion X' d) n).map
        ((cbcReductionStrictExchange d sq).inv.app (DerivedCategory.Q.obj P)) ≫
        (cbcSourceFiniteComparison d sq n).hom.app (DerivedCategory.Q.obj P) =
      (cbcTargetFiniteComparison d sq n).hom.app (DerivedCategory.Q.obj P) ≫
        (cbcFiniteExchange d sq n).inv.app
          ((cbcFiniteReduction d U n).obj (DerivedCategory.Q.obj P)) := by
  have hsource : CbcSourceFiniteNormalization d sq n (cbcSourceFiniteComparison d sq n) := by
    simpa only [cbcSourceFiniteComparison] using
      (cbcFiniteComparisons_existsUnique d sq n).1.exists.choose_spec
  have htarget : CbcTargetFiniteNormalization d sq n (cbcTargetFiniteComparison d sq n) := by
    simpa only [cbcTargetFiniteComparison] using
      (cbcFiniteComparisons_existsUnique d sq n).2.exists.choose_spec
  have := cbcStrictOpenModule_additive d j sq.isOpenImmersion
  have := cbcStrictOpenModule_additive d j' sq.isOpenImmersion'
  have := completedReductionModuleTowerFunctor_additive U d
  have := completedTowerModulePullback_additive g d
  have := completedTowerModulePullback_additive gU d
  have := cbcFiniteReductionModule_additive d U n
  have := cbcFiniteSource_additive d sq n
  have := cbcFiniteTarget_additive d sq n
  have := cbcFiniteSource_limits d sq n
  have := cbcFiniteSource_colimits d sq n
  have := cbcFiniteTarget_limits d sq n
  have := cbcFiniteTarget_colimits d sq n
  have := finiteSourceModel_isIso d sq n P hP
  let R₀ : pbcModules U (pbcAdicCompletion U d) ⥤
      pbcTowers U (pbcAdicCompletion U d) := completedReductionModuleTowerFunctor U d
  have : R₀.Additive := by
    set_option backward.isDefEq.respectTransparency false in infer_instance
  dsimp only [cbcReductionStrictExchange, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app]
  exact derivedPair_finite_comparison R₀
    (cbcStrictOpenModule d j sq.isOpenImmersion)
    (completedTowerModulePullback g d) (completedTowerModulePullback gU d)
    (cbcStrictOpenModule d j' sq.isOpenImmersion')
    ((CategoryTheory.evaluation ℕᵒᵖ
      (pbcModules X' (pbcAdicCompletion X' d))).obj (op n))
    (cbcFiniteReductionModule d U n) (cbcFiniteSource d sq n) (cbcFiniteTarget d sq n)
    (completedReductionTower U d) (completedTowerPullback g d) (completedTowerPullback gU d)
    (completedTowerPullbackCounit g d) (completedTowerPullbackCounit gU d)
    (cbcStrictExchange d sq) (cbcStrictInverseModule d sq)
    (strict_normalization_everywhere d sq)
    (cbcSourceLevel d sq n).hom (cbcTargetLevel d sq n).hom (cbcFiniteInverse d sq n) P
    (cbcReductionModelMap d U P)
    ((cbcSourceFiniteComparison d sq n).hom.app (DerivedCategory.Q.obj P))
    ((cbcTargetFiniteComparison d sq n).hom.app (DerivedCategory.Q.obj P))
    (cbcFiniteSourceModelMap d sq n P) (cbcFiniteTargetModelMap d sq n P)
    ((cbcFiniteExchange d sq n).inv.app
      ((cbcFiniteReduction d U n).obj (DerivedCategory.Q.obj P)))
    (hsource P hP) (htarget P hP)
    (ordinary_level_inverse d sq n) (finite_model_inverse d sq n P)
    (_hms := @IsIso.mono_of_iso _ _ _ _ (cbcFiniteSourceModelMap d sq n P)
      (finiteSourceModel_isIso d sq n P hP))
    (hR := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hJ := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hG := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hH := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hJp := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hE := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hS := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hFS := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hFT := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hJL := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hJC := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hJpL := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hJpC := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hEL := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
    (hEC := by
      set_option backward.isDefEq.respectTransparency false in
        set_option backward.isDefEq.respectTransparency.types false in
          infer_instance)
end
private theorem natTrans_eq_of_covers
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    {F G : D ⥤ E} (a b : F ⟶ G)
    (h : ∀ K : C, ∃ P : C, ∃ s : P ⟶ K,
      IsIso (Q.map s) ∧ a.app (Q.obj P) = b.app (Q.obj P)) : a = b := by
  apply Localization.natTrans_ext Q W
  intro K
  obtain ⟨P, s, hs, hp⟩ := h K
  have := hs
  apply (cancel_epi (F.map (Q.map s))).1
  exact (a.naturality (Q.map s)).trans
    ((congrArg (fun k ↦ k ≫ G.map (Q.map s)) hp).trans
      (b.naturality (Q.map s)).symm)
private theorem forward_square_of_inverse
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {X Y : D} (α : A ≅ B) (δ : X ≅ Y)
    (s : F.obj A ⟶ X) (t : F.obj B ⟶ Y)
    (h : F.map α.inv ≫ s = t ≫ δ.inv) : F.map α.hom ≫ t = s ≫ δ.hom := by
  apply (cancel_epi (F.map α.inv)).1
  rw [← Category.assoc, ← F.map_comp, α.inv_hom_id, F.map_id, Category.id_comp]
  rw [← Category.assoc, h, Category.assoc, δ.inv_hom_id, Category.comp_id]
/-- Strict finite exchange over the completed coefficient rings, on every reduction
K_bullet, with canonical finite components and their specified inverse mates.
Source: blueprint finite-exchange/reduction identification before Rlim;
Stacks 03DI, 03DJ, 04J0, 06XN and 099N
(blueprint: lem-cbc-completed-ring-strict-finite-exchange).
Proof: the chosen strict exchange already satisfies its objectwise K-flat counit
normalization. A functorial flat replacement of the entire strict tower, together
with naturality, extends this equation to arbitrary tower complexes. Apply it to
an ordinary reduction tower and evaluate at the finite level. The ordinary scalar
compatibility of inverse exchanges gives the resulting equality degree by degree.
The source and target finite comparisons have the same representative equations;
cancel their invertible model maps on K-flat representatives. Naturality and
localization extensionality descend the inverse square to every derived object.
Finally cancel the inverse exchanges to obtain the displayed forward square. -/
theorem completedRingStrictFiniteExchange :
    CbcStrictExchangeNormalization d sq (cbcStrictExchange d sq) ∧
      ∀ (K : DerivedCategory (pbcModules U (pbcAdicCompletion U d))) (n : ℕ),
        HEq
          ((pbcTowerEvaluation X' (pbcAdicCompletion X' d) n).map
            ((cbcReductionStrictExchange d sq).hom.app K) ≫
          (cbcTargetFiniteComparison d sq n).hom.app K)
          ((cbcSourceFiniteComparison d sq n).hom.app K ≫
          (cbcFiniteExchange d sq n).hom.app ((cbcFiniteReduction d U n).obj K)) := by
  constructor
  · simpa only [cbcStrictExchange] using
      (cbcStrictExchange_existsUnique d sq).exists.choose_spec
  · let E := pbcTowerEvaluation X' (pbcAdicCompletion X' d)
    have hi (n : ℕ) :
        Functor.whiskerRight (cbcReductionStrictExchange d sq).inv (E n) ≫
            (cbcSourceFiniteComparison d sq n).hom =
          (cbcTargetFiniteComparison d sq n).hom ≫
            Functor.whiskerLeft (cbcFiniteReduction d U n) (cbcFiniteExchange d sq n).inv := by
      let a := Functor.whiskerRight (cbcReductionStrictExchange d sq).inv (E n) ≫
        (cbcSourceFiniteComparison d sq n).hom
      let b := (cbcTargetFiniteComparison d sq n).hom ≫
        Functor.whiskerLeft (cbcFiniteReduction d U n) (cbcFiniteExchange d sq n).inv
      change a = b
      apply natTrans_eq_of_covers DerivedCategory.Q
        (HomologicalComplex.quasiIso (pbcModules U (pbcAdicCompletion U d)) (.up ℤ))
      intro K
      obtain ⟨P, s, hP, hs⟩ := kflat_resolutions d U K
      have : QuasiIso s := hs
      refine ⟨P, s, inferInstance, ?_⟩
      exact inverse_on_kflat d sq n P hP
    intro K n
    apply heq_of_eq
    have h := NatTrans.congr_app (hi n) K
    change (E n).map ((cbcReductionStrictExchange d sq).inv.app K) ≫
        (cbcSourceFiniteComparison d sq n).hom.app K =
      (cbcTargetFiniteComparison d sq n).hom.app K ≫
        (cbcFiniteExchange d sq n).inv.app ((cbcFiniteReduction d U n).obj K) at h
    exact forward_square_of_inverse (E n) ((cbcReductionStrictExchange d sq).app K)
      ((cbcFiniteExchange d sq n).app ((cbcFiniteReduction d U n).obj K)) _ _ h
end AlgebraicGeometry.Scheme
