/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.ZlFrameworkPbc.ZlCompactificationOpenDiagram
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SixFunctors.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.FourierTransform.FdPullbackComparison
public import WeilConjectures.AlgebraicGeometry.Complete.CompleteProetaleStrictTowerRealization
import WeilConjectures.DeligneLaumon.ZlFrameworkPbc.ZlFrameworkQuotientAugmentation
import WeilConjectures.AlgebraicGeometry.Integral.IntegralRingedOpenPullSupport
import WeilConjectures.AlgebraicGeometry.Ringed.RingedOpenExtensionUnit
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation

/-! # Framework open exchange in its own coefficient presentation
Source: thm-cbc-qbar.proof.md, integral strict quotient construction
(blueprint: def-zl-framework-open-exchange).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.ZlFrameworkPbc
open PurCompactSupport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary pullback with the framework completed coefficient sheaf.
Source: Stacks 099N(5) (blueprint: def-zl-framework-open-exchange). -/
abbrev frameworkModulePull {U T : Scheme.{u}} (h : U ⟶ T) :=
  proEtaleRingModulePullback h ((completed l E).ring T)
    ((completed l E).ring U) ((completed l E).pull h)

/-- The canonical quotient-unit/Roos normalization. It specifies every first-coordinate
projection on inverse-image generators and the entire shifted coordinate as zero.
Source: Stacks 099N(5), 08TC (blueprint: def-zl-framework-open-exchange). -/
def FrameworkPullChainSpec {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ)
    (ξ : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E h).obj P) : Prop :=
  (∀ (n : ℕ) (i : ℤ) (V : T.ProEt) (x : (P.X i).val.obj (op V)),
    ((ξ ≫ CochainComplex.mappingCocone.fst
        (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P)) ≫
      Pi.π (fun n ↦
        ((integralOperationsPullbackTowerFunctor l E h).obj P).obj (op n)) n).f i).val.app
        (op ((proEtaleBaseChange h).obj V))
      (((proEtaleRingModuleAdjunction h ((completed l E).ring T)
        ((completed l E).ring U) ((completed l E).pull h)).unit.app (P.X i)).val.app
          (op V) x) =
      integralOperationsPullbackGenerator l E h n
        (((unrestrictedIntegralFiniteComplex l E T n).obj P).X i) V
        (unrestrictedIntegralTensorSection l E T n (P.X i) (op V) 1 x)) ∧
  (∀ (i j : ℤ) (hij : i + -1 = j), ξ.f i ≫
    (CochainComplex.mappingCocone.snd
      (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P))).v
        i j hij = 0)

private theorem coconeDegree_ext
    {A : Type*} [Category* A] [Preadditive A] [HasBinaryBiproducts A]
    {P K L : CochainComplex A ℤ} (φ : K ⟶ L)
    (f g : P ⟶ CochainComplex.mappingCocone φ) (i : ℤ)
    (hf : f.f i ≫ (CochainComplex.mappingCocone.fst φ).f i =
      g.f i ≫ (CochainComplex.mappingCocone.fst φ).f i)
    (hs : f.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega) =
      g.f i ≫ (CochainComplex.mappingCocone.snd φ).v i (i - 1) (by omega)) :
    f.f i = g.f i := by
  have hi := CochainComplex.mappingCocone.id_X φ i (i - 1) (by omega)
  calc
    f.f i = f.f i ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f.f i ≫ _ := congrArg (f.f i ≫ ·) hi.symm
    _ = g.f i ≫ _ := by
      rw [Preadditive.comp_add, Preadditive.comp_add, reassoc_of% hf, reassoc_of% hs]
    _ = g.f i := by rw [hi, Category.comp_id]

private theorem frameworkPullChain_ext {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ)
    (ξ η : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E h).obj P)
    (hξ : FrameworkPullChainSpec l E h P ξ)
    (hη : FrameworkPullChainSpec l E h P η) : ξ = η := by
  have hf : ξ ≫ CochainComplex.mappingCocone.fst
      (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P)) =
      η ≫ CochainComplex.mappingCocone.fst
        (scalarRoosBoundary ((integralOperationsPullbackTowerFunctor l E h).obj P)) := by
    apply Pi.hom_ext
    intro n
    ext i : 1
    apply ((proEtaleRingModuleAdjunction h ((completed l E).ring T)
      ((completed l E).ring U) ((completed l E).pull h)).homEquiv (P.X i) _).injective
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (hξ.1 n i V.unop x).trans (hη.1 n i V.unop x).symm
  ext i : 1
  have hfi := congrArg (fun z ↦ z.f i) hf
  have hs := (hξ.2 i (i - 1) (by omega)).trans (hη.2 i (i - 1) (by omega)).symm
  exact coconeDegree_ext _ ξ η i hfi hs

/-- The quotient-unit comparison is uniquely determined before localization.
Source: Stacks 099N(5), 08TC (blueprint: def-zl-framework-open-exchange).
Proof: apply inverse image to the quotient augmentation x maps to 1 tensor x at
all levels simultaneously. These maps commute with quotient transitions, so the
first-coordinate product map and zero shifted coordinate form a chain map to Roos.
The inverse-image generators generate after sheafification. Product projections
and the two cocone coordinates therefore determine the chain map uniquely. -/
theorem frameworkPullChain_existsUnique {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :
    ∃! ξ : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      (integralOperationsPullbackComplexFunctor l E h).obj P,
      FrameworkPullChainSpec l E h P ξ := by
  obtain ⟨γ, hγ, hgen⟩ := frameworkQuotientAugmentation_exists l E h P
  let C := (integralOperationsPullbackTowerFunctor l E h).obj P
  let α : ((frameworkModulePull l E h).mapHomologicalComplex (.up ℤ)).obj P ⟶
      ∏ᶜ fun n : ℕ ↦ C.obj (op n) := Pi.lift γ
  have hα : α ≫ scalarRoosBoundary C = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [α, scalarRoosBoundary, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Category.comp_id, Category.assoc, Pi.lift_π,
      Preadditive.sub_comp, zero_comp]
    rw [← Category.assoc, Pi.lift_π]
    exact sub_eq_zero.mpr (hγ n).symm
  let ξ := CochainComplex.mappingCocone.lift (scalarRoosBoundary C) α 0 (by simp [hα])
  have hξ : FrameworkPullChainSpec l E h P ξ := by
    constructor
    · intro n i V x
      have hf : ξ ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
          Pi.π (fun n : ℕ ↦ C.obj (op n)) n = γ n := by
        rw [← Category.assoc, CochainComplex.mappingCocone.lift_fst, Pi.lift_π]
      exact (congrArg (fun f ↦ (f.f i).val.app (op ((proEtaleBaseChange h).obj V))
        (((proEtaleRingModuleAdjunction h ((completed l E).ring T)
          ((completed l E).ring U) ((completed l E).pull h)).unit.app (P.X i)).val.app
            (op V) x)) hf).trans (hgen n i V x)
    · intro i j hij
      exact CochainComplex.mappingCocone.lift_f_snd_v (scalarRoosBoundary C) α 0
        (by simp [hα]) i j hij
  exact ⟨ξ, hξ, fun η hη ↦ frameworkPullChain_ext l E h P η ξ hη hξ⟩

/-- The specified whole quotient-diagram augmentation into its Roos realization.
Source: Stacks 099N(5), 08TC (blueprint: def-zl-framework-open-exchange). -/
def frameworkPullChain {U T : Scheme.{u}} (h : U ⟶ T)
    (P : CochainComplex (integralTowerModules l E T) ℤ) :=
  (frameworkPullChain_existsUnique l E h P).exists.choose

/-- Open inverse image preserves the completed constructible realization, with the
whole quotient-unit normalization. No PBC presentation or comparison enters this type.
Source: Stacks 099N(5), 09BQ (blueprint: def-zl-framework-open-exchange).
Proof: open inverse image is exact and preserves products. Apply it to the strict
quotient diagram of a flat K-flat representative. The quotient-unit map just
constructed becomes its canonical completion augmentation. Complete constructible
inputs have invertible augmentation; the Roos product and shifted coordinates
identify it with the defining integral pullback realization. Descent from good
representatives supplies naturality and uniqueness with this equation. -/
theorem frameworkOpenPullRealization_existsUnique {U T : Scheme.{u}} (h : U ⟶ T)
    [IsOpenImmersion h] [QuasiCompact h]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : T, Invertible (l : T.residueField x)] :
    ∃! a : (sfIntegralConstructible l E T).ι ⋙ pull (completed l E) h ≅
      constructibleIntegralPullback l E h ⋙ (sfIntegralConstructible l E U).ι,
      ∀ (P : (integralOperationsGoodComplex l E T).FullSubcategory)
        (hP : sfIntegralConstructible l E T (DerivedCategory.Q.obj P.obj)),
        a.hom.app ⟨DerivedCategory.Q.obj P.obj, hP⟩ ≫
          (integralDerivedPullbackComparison l E h).hom.app P =
        (frameworkModulePull l E h).mapDerivedCategoryFactors.hom.app P.obj ≫
          DerivedCategory.Q.map (frameworkPullChain l E h P.obj) := by
  sorry

/-- The framework pullback realization fixed by quotient and shifted Roos coordinates.
Source: Stacks 099N(5) (blueprint: def-zl-framework-open-exchange). -/
def frameworkOpenPullRealization {U T : Scheme.{u}} (h : U ⟶ T)
    [IsOpenImmersion h] [QuasiCompact h]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : T, Invertible (l : T.residueField x)] :=
  (frameworkOpenPullRealization_existsUnique l E h).exists.choose

/-- Framework pullback around a commutative square, using the specified coefficient
compositors. Source: Stacks 07A7 (blueprint: def-zl-framework-open-exchange). -/
def frameworkSquare {A B C T : Scheme.{u}}
    (a : A ⟶ B) (b : A ⟶ C) (c : B ⟶ T) (d : C ⟶ T)
    (h : a ≫ c = b ≫ d) :
    pull (completed l E) c ⋙ pull (completed l E) a ≅
      pull (completed l E) d ⋙ pull (completed l E) b :=
  (geometricPullComposition (completed l E) a c (completedPull_comp l E a c)).symm ≪≫
    eqToIso (congrArg (fun g ↦ pull (completed l E) g) h) ≪≫
    geometricPullComposition (completed l E) b d (completedPull_comp l E b d)

variable (D : FiniteFieldDatum.{u}) (G : OpenDiagram D l)

/-- The framework proper adjunction mate; it is fixed before any endpoint comparison.
Source: Stacks 07A7 (blueprint: def-zl-framework-open-exchange). -/
def frameworkProperMate :
    push (completed l E) G.c.g ⋙ pull (completed l E) G.v ⟶
      pull (completed l E) G.w ⋙ push (completed l E) G.c'.g :=
  mateEquiv
    (proEtaleRingDerivedAdjunction G.c.g _ _ ((completed l E).pull G.c.g))
    (proEtaleRingDerivedAdjunction G.c'.g _ _ ((completed l E).pull G.c'.g))
    (frameworkSquare l E G.w G.c'.g G.c.g G.v G.properSquare.w).inv

/-- Inverse open exchange, defined by the framework open-adjunction unit transpose.
Source: Stacks 03S6 (blueprint: def-zl-framework-open-exchange). -/
def frameworkOpenMate :
    pull (completed l E) G.u ⋙ (openExtension (completed l E) G.c'.i).mapDerivedCategory ⟶
      (openExtension (completed l E) G.c.i).mapDerivedCategory ⋙ pull (completed l E) G.w :=
  ((mateEquiv (openDerivedAdjunction (completed l E) G.c.i)
    (openDerivedAdjunction (completed l E) G.c'.i)).symm
      (TwoSquare.mk _ _ _ _
        (frameworkSquare l E G.u G.c'.i G.c.i G.w G.openSquare.w).hom)).natTrans

/-- The two framework coefficient paths agree over a commutative Cartesian square.
Source: Stacks 07A7 (blueprint: def-zl-framework-open-exchange).
Proof: completedPull_comp identifies each path with the coefficient map for its
composite. The supplied commutativity equality identifies these composites, hence
their inverse-image coefficient maps. This proves heterogeneous equality without
choosing another coefficient identification. -/
theorem frameworkRingedSquare_coherent {A B C T : Scheme.{u}}
    {a : A ⟶ B} {b : A ⟶ C} {c : B ⟶ T} {d : C ⟶ T}
    (sq : ChosenCartesianSquare a b c d) :
    HEq (proEtaleRingCompositeCoefficients a c ((completed l E).ring T)
      ((completed l E).ring B) ((completed l E).ring A)
      ((completed l E).pull c) ((completed l E).pull a))
      (proEtaleRingCompositeCoefficients b d ((completed l E).ring T)
        ((completed l E).ring C) ((completed l E).ring A)
        ((completed l E).pull d) ((completed l E).pull b)) := by
  rw [← completedPull_comp l E a c, ← completedPull_comp l E b d]
  exact congr_arg_heq (fun q : A ⟶ T ↦ (completed l E).pull q) sq.w

/-- The ringed square in the framework's own completed presentation.
Source: Stacks 07A7 (blueprint: def-zl-framework-open-exchange). -/
def frameworkRingedSquare {A B C T : Scheme.{u}}
    {a : A ⟶ B} {b : A ⟶ C} {c : B ⟶ T} {d : C ⟶ T}
    (sq : ChosenCartesianSquare a b c d) : StrictTowerRingedSquare sq where
  RY := (completed l E).ring T
  RX := (completed l E).ring B
  RY' := (completed l E).ring C
  RX' := (completed l E).ring A
  cf := (completed l E).pull c
  cg := (completed l E).pull d
  cg' := (completed l E).pull a
  cf' := (completed l E).pull b
  coherent := frameworkRingedSquare_coherent l E sq

private theorem inverseMateIsoOfUnitSupport
    {A B C F : Type*} [Category A] [Category B] [Category C] [Category F]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ F} {R₂ : F ⥤ C}
    {V : A ⥤ C} {W : B ⥤ F} (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    [IsIso a₁.unit] [IsIso a₂.unit] (d : R₁ ⋙ V ≅ W ⋙ R₂)
    (hs : ∀ M, L₂.essImage (W.obj (L₁.obj M))) :
    IsIso ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans := by
  have := a₂.fullyFaithfulLOfIsIsoUnit.full
  have := a₂.fullyFaithfulLOfIsIsoUnit.faithful
  have h (M : A) :
      IsIso (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ d.hom)).app M) := by
    have : IsIso (a₂.counit.app (W.obj (L₁.obj M))) :=
      a₂.isIso_counit_app_iff_mem_essImage.mpr (hs M)
    simpa [mateEquiv, Functor.map_comp] using
      (inferInstance : IsIso (L₂.map (V.map (a₁.unit.app M)) ≫
        L₂.map (d.hom.app (L₁.obj M)) ≫ a₂.counit.app _))
  let := h
  exact NatIso.isIso_of_isIso_app _

private theorem ordinaryOpenUnit {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] : IsIso (openAdjunction (completed l E) j).unit := by
  exact proEtaleRingOpenAdjunction_unit_isIso j ((completed l E).ring T)
    ((completed l E).ring U) ((completed l E).pull j)

private theorem exactOpenUnit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : L ⊣ R) [IsIso a.unit] :
    IsIso a.onDerivedCategory.unit := by
  have h (M : DerivedCategory A) :
      IsIso (a.onDerivedCategory.unit.app M) := by
    rw [← NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Q.objObjPreimageIso M)]
    dsimp only [Adjunction.onDerivedCategory]
    rw [Adjunction.localization_unit_app]
    have : IsIso ((a.mapHomologicalComplex (.up ℤ)).unit.app
        (DerivedCategory.Q.objPreimage M)) := by
      have hn (n : ℤ) : IsIso (((a.mapHomologicalComplex (.up ℤ)).unit.app
          (DerivedCategory.Q.objPreimage M)).f n) := by
        change IsIso (a.unit.app _)
        infer_instance
      let := hn
      exact HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  let := h
  exact NatIso.isIso_of_isIso_app _

private def frameworkModuleOpenIso :
    frameworkModulePull l E G.u ⋙ openExtension (completed l E) G.c'.i ≅
      openExtension (completed l E) G.c.i ⋙ frameworkModulePull l E G.w := by
  let R := completed l E
  let r := frameworkRingedSquare l E G.openSquare.toChosenCartesianSquare
  have := ordinaryOpenUnit l E G.c.i
  have := ordinaryOpenUnit l E G.c'.i
  let β := ((mateEquiv (openAdjunction R G.c.i) (openAdjunction R G.c'.i)).symm
    (TwoSquare.mk _ _ _ _ r.exchangeModuleSquare.inv)).natTrans
  have : IsIso β := inverseMateIsoOfUnitSupport (openAdjunction R G.c.i)
    (openAdjunction R G.c'.i) r.exchangeModuleSquare.symm (fun M ↦
      proEtaleRingPullback_openSupport G.u G.c'.i G.c.i G.w
        (IsPullback.of_iso_pullback G.openSquare.toCommSq G.openSquare.isoPullback
          G.openSquare.hom_fst G.openSquare.hom_snd)
        (R.ring G.c.Z) (R.ring G.X) (R.ring G.c'.Z) (R.ring G.U)
        (R.pull G.c.i) (R.pull G.w) (R.pull G.c'.i) M)
  exact asIso β

/-- The specified open mate is invertible on a Cartesian open square.
Source: Stacks 03S6 (blueprint: def-zl-framework-open-exchange).
Proof: ordinary pullback preserves the essential image of extension by zero on
this Cartesian square. The slice presentation makes both open units invertible,
so the inverse mate is a composite of images of those units, the coefficient-square
isomorphism, and a counit on an object in the open essential image. Each factor
is invertible. Exact localization carries an ordinary exchange isomorphism to an
isomorphism witnessing derived open support and preserves invertibility of the
units. The same factorization then proves invertibility of the specified derived
mate, without requiring equality of two chosen comparison formulas. -/
theorem frameworkOpenMate_isIso : IsIso (frameworkOpenMate l E D G) := by
  let e := Functor.mapDerivedCategorySquareIso (frameworkModuleOpenIso l E D G)
  have := ordinaryOpenUnit l E G.c.i
  have := ordinaryOpenUnit l E G.c'.i
  have : IsIso (openDerivedAdjunction (completed l E) G.c.i).unit := by
    exact exactOpenUnit (openAdjunction (completed l E) G.c.i)
  have : IsIso (openDerivedAdjunction (completed l E) G.c'.i).unit := by
    exact exactOpenUnit (openAdjunction (completed l E) G.c'.i)
  exact inverseMateIsoOfUnitSupport (openDerivedAdjunction (completed l E) G.c.i)
    (openDerivedAdjunction (completed l E) G.c'.i)
    (frameworkSquare l E G.u G.c'.i G.c.i G.w G.openSquare.w)
    (fun M ↦ ⟨(pull (completed l E) G.u).obj M, ⟨e.app M⟩⟩)

/-- Proper mate first, then the framework open-adjunction comparison. All functors
use completed framework coefficients. The qcqs support and quotient-unit pullback
realizations below identify its endpoints with the actual recorded Roos endpoints.
Source: thm-cbc-qbar.proof.md, integral ordered exchange
(blueprint: def-zl-framework-open-exchange). -/
def frameworkAmbientExchange :
    image (completed l E) G.c ⋙ pull (completed l E) G.v ⟶
      pull (completed l E) G.u ⋙ image (completed l E) G.c' :=
  Functor.whiskerLeft (openExtension (completed l E) G.c.i).mapDerivedCategory
      (frameworkProperMate l E D G) ≫
    Functor.whiskerRight
      (@inv _ _ _ _ (frameworkOpenMate l E D G) (frameworkOpenMate_isIso l E D G))
      (push (completed l E) G.c'.g)


/-- Framework inverse image on strict towers, before localization.
Source: Stacks 07A7 (blueprint: def-zl-framework-open-exchange). -/
abbrev frameworkTowerPull {U T : Scheme.{u}} (h : U ⟶ T) :=
  exchangeTowerPull h ((completed l E).ring T) ((completed l E).ring U)
    ((completed l E).pull h)

/-- Framework direct image on the one derived category of strict diagrams.
Source: Stacks 0A07 (blueprint: def-zl-framework-open-exchange). -/
abbrev frameworkTowerPush {U T : Scheme.{u}} (h : U ⟶ T) :=
  exchangeTowerPush h ((completed l E).ring T) ((completed l E).ring U)
    ((completed l E).pull h)

/-- Extension by zero of entire framework diagrams, with every transition retained.
Source: Stacks 03DI (blueprint: def-zl-framework-open-exchange). -/
abbrev frameworkTowerOpen {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (openExtension (completed l E) j)).mapDerivedCategory

/-- The open adjunction on framework diagrams, derived from the ordinary unit.
Source: Stacks 03DI (blueprint: def-zl-framework-open-exchange). -/
def frameworkTowerOpenAdj {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    frameworkTowerOpen l E j ⊣ frameworkTowerPull l E j :=
  Adjunction.ofNatIsoRight
    (((openAdjunction (completed l E) j).whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction)
    (exchangeTowerModulePull j ((completed l E).ring T) ((completed l E).ring U)
      ((completed l E).pull j)).rightDerivedFunctorIsoMapDerivedCategory

/-- The framework proper mate on the whole strict coefficient diagram.
Source: Stacks 07A7 (blueprint: def-zl-framework-open-exchange). -/
def frameworkTowerProperMate :=
  (frameworkRingedSquare l E G.properSquare).exchangeTowerMate

/-- The inverse open comparison, transposed under the framework tower adjunction.
Source: Stacks 03S6 (blueprint: def-zl-framework-open-exchange). -/
def frameworkTowerOpenMate :
    frameworkTowerPull l E G.u ⋙ frameworkTowerOpen l E G.c'.i ⟶
      frameworkTowerOpen l E G.c.i ⋙ frameworkTowerPull l E G.w :=
  ((mateEquiv (frameworkTowerOpenAdj l E G.c.i)
    (frameworkTowerOpenAdj l E G.c'.i)).symm
      (TwoSquare.mk _ _ _ _
        ((frameworkRingedSquare l E
          G.openSquare.toChosenCartesianSquare).exchangeTowerSquare.inv))).natTrans

private theorem frameworkTowerUnit {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] : IsIso (frameworkTowerOpenAdj l E j).unit := by
  have := ordinaryOpenUnit l E j
  let a := (openAdjunction (completed l E) j).whiskerRight ℕᵒᵖ
  have h : ∀ M, IsIso (a.unit.app M) := by
    intro M
    have hn : ∀ n, IsIso ((a.unit.app M).app n) := by
      intro n
      change IsIso ((openAdjunction (completed l E) j).unit.app (M.obj n))
      infer_instance
    let := hn
    exact NatIso.isIso_of_isIso_app _
  let := h
  have : IsIso a.unit := NatIso.isIso_of_isIso_app _
  have := exactOpenUnit a
  have := a.onDerivedCategory.fullyFaithfulLOfIsIsoUnit.full
  have := a.onDerivedCategory.fullyFaithfulLOfIsIsoUnit.faithful
  exact (frameworkTowerOpenAdj l E j).unit_isIso_of_L_fully_faithful

/-- Cartesian open exchange is invertible already on framework strict diagrams.
Source: Stacks 03S6 (blueprint: def-zl-framework-open-exchange).
Proof: take the ordinary open exchange isomorphism termwise, retaining every
transition map, and localize to obtain an isomorphism witnessing open support on
derived strict towers. The termwise ordinary open unit is invertible, and its
exact localization shows the derived tower open functor is fully faithful.
Consequently the actual tower adjunction also has invertible unit. Factor its
inverse mate as the image of a unit, the square isomorphism, and the counit at the
supported object. All three factors are invertible. -/
theorem frameworkTowerOpenMate_isIso : IsIso (frameworkTowerOpenMate l E D G) := by
  let r := frameworkRingedSquare l E G.openSquare.toChosenCartesianSquare
  let t₁ := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (frameworkModulePull l E G.u)
  let t₂ := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (openExtension (completed l E) G.c'.i)
  let s₁ := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (openExtension (completed l E) G.c.i)
  let s₂ := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (frameworkModulePull l E G.w)
  let e := Functor.mapDerivedCategorySquareIso
    (F₁ := t₁) (F₂ := t₂) (G₁ := s₁) (G₂ := s₂)
    ((Functor.whiskeringRight ℕᵒᵖ _ _).mapIso (frameworkModuleOpenIso l E D G))
  have := frameworkTowerUnit l E G.c.i
  have := frameworkTowerUnit l E G.c'.i
  exact inverseMateIsoOfUnitSupport (frameworkTowerOpenAdj l E G.c.i)
    (frameworkTowerOpenAdj l E G.c'.i) r.exchangeTowerSquare.symm
    (fun M ↦ ⟨(frameworkTowerPull l E G.u).obj M, ⟨e.app M⟩⟩)

/-- The ordered framework exchange, proper mate first and then the open comparison,
formed before either total inverse limit or finite evaluation.
Source: thm-cbc-qbar.proof.md (blueprint: def-zl-framework-open-exchange). -/
def frameworkTowerExchange :
    frameworkTowerOpen l E G.c.i ⋙ frameworkTowerPush l E G.c.g ⋙
        frameworkTowerPull l E G.v ⟶
      frameworkTowerPull l E G.u ⋙ frameworkTowerOpen l E G.c'.i ⋙
        frameworkTowerPush l E G.c'.g :=
  Functor.whiskerLeft (frameworkTowerOpen l E G.c.i) (frameworkTowerProperMate l E D G) ≫
    Functor.whiskerRight
      (@inv _ _ _ _ (frameworkTowerOpenMate l E D G)
        (frameworkTowerOpenMate_isIso l E D G)) (frameworkTowerPush l E G.c'.g)

/-- The actual strict quotient diagram of an ordinary framework module. Its
transition is the existing sheafified quotient map s tensor x ↦ rho(s) tensor x.
Source: Bhatt--Scholze 3.5.2 (blueprint: def-zl-framework-open-exchange). -/
def frameworkModuleQuotientTower (W : Scheme.{u}) :
    integralTowerModules l E W ⥤ exchangeTowers W ((completed l E).ring W) :=
  (Functor.ofOpSequence (X := fun n ↦ sfReductionRestricted l E W n)
    (sfReductionTransition l E W)).flip

/-- Additivity of the quotient diagram, read at every index before localization.
Source: Stacks 03CZ (blueprint: def-zl-framework-open-exchange).
Proof: each scalar extension and restriction is additive. The tower maps and
addition are pointwise, so their composites preserve zero and sums. -/
theorem frameworkModuleQuotientTower_additive (W : Scheme.{u}) :
    (frameworkModuleQuotientTower l E W).Additive := by
  constructor
  intro M N f g
  apply NatTrans.ext
  funext n
  exact (sfReductionRestricted l E W n.unop).map_add

attribute [instance] frameworkModuleQuotientTower_additive

/-- One simultaneous quotient complex, localized in the category of strict towers.
It is applied to flat K-flat representatives, never to independently chosen reductions.
Source: Bhatt--Scholze 3.5.2 (blueprint: def-zl-framework-open-exchange). -/
def frameworkStrictQuotients (W : Scheme.{u})
    (P : CochainComplex (integralTowerModules l E W) ℤ) :=
  DerivedCategory.Q.obj
    (((frameworkModuleQuotientTower l E W).mapHomologicalComplex (.up ℤ)).obj P)

/-- Framework direct-image/total-limit comparison, fixed as the adjunction conjugate
of the constant-diagram inverse-image comparison, including its ordinary units.
Source: Stacks 0A07 (blueprint: def-zl-framework-open-exchange). -/
def frameworkPushLimit {U T : Scheme.{u}} (h : U ⟶ T) :
    completedRlim U ((completed l E).ring U) ⋙ push (completed l E) h ≅
      frameworkTowerPush l E h ⋙ completedRlim T ((completed l E).ring T) :=
  conjugateIsoEquiv
    ((proEtaleRingDerivedAdjunction h _ _ ((completed l E).pull h)).comp
      (cbcRealizationLimitAdj U ((completed l E).ring U)))
    ((cbcRealizationLimitAdj T ((completed l E).ring T)).comp
      (exchangeTowerAdjunction h _ _ ((completed l E).pull h)))
    (cbcRealizationConst (frameworkModulePull l E h)).symm

/-- Source endpoint on the framework diagram, by open/limit, proper/limit and
inverse-image/limit in that order. All are the canonical constant-diagram mates.
Source: Stacks 09BP, 0A07 (blueprint: def-zl-framework-open-exchange). -/
def frameworkStrictSource
    (M : DerivedCategory (exchangeTowers G.X ((completed l E).ring G.X))) :
    (pull (completed l E) G.v).obj
        ((image (completed l E) G.c).obj
          ((completedRlim G.X ((completed l E).ring G.X)).obj M)) ⟶
      (completedRlim G.V ((completed l E).ring G.V)).obj
        ((frameworkTowerPull l E G.v).obj ((frameworkTowerPush l E G.c.g).obj
          ((frameworkTowerOpen l E G.c.i).obj M))) :=
  (pull (completed l E) G.v).map
      ((push (completed l E) G.c.g).map
        ((cbcRealizationLimitMap (openExtension (completed l E) G.c.i)).app M)) ≫
    (pull (completed l E) G.v).map
      ((frameworkPushLimit l E G.c.g).hom.app ((frameworkTowerOpen l E G.c.i).obj M)) ≫
    (cbcRealizationLimitMap (frameworkModulePull l E G.v)).app
      ((frameworkTowerPush l E G.c.g).obj ((frameworkTowerOpen l E G.c.i).obj M))

/-- Target endpoint uses the framework inverse-image/limit, open/limit and
proper/limit comparisons, with the same ordinary units as the source.
Source: Stacks 09BP, 0A07 (blueprint: def-zl-framework-open-exchange). -/
def frameworkStrictTarget
    (M : DerivedCategory (exchangeTowers G.X ((completed l E).ring G.X))) :
    (image (completed l E) G.c').obj
        ((pull (completed l E) G.u).obj
          ((completedRlim G.X ((completed l E).ring G.X)).obj M)) ⟶
      (completedRlim G.V ((completed l E).ring G.V)).obj
        ((frameworkTowerPush l E G.c'.g).obj ((frameworkTowerOpen l E G.c'.i).obj
          ((frameworkTowerPull l E G.u).obj M))) :=
  (push (completed l E) G.c'.g).map
      (((openExtension (completed l E) G.c'.i).mapDerivedCategory).map
        ((cbcRealizationLimitMap (frameworkModulePull l E G.u)).app M)) ≫
    (push (completed l E) G.c'.g).map
      ((cbcRealizationLimitMap (openExtension (completed l E) G.c'.i)).app
        ((frameworkTowerPull l E G.u).obj M)) ≫
    (frameworkPushLimit l E G.c'.g).hom.app
      ((frameworkTowerOpen l E G.c'.i).obj ((frameworkTowerPull l E G.u).obj M))

/-- The whole strict-diagram normalization of the framework ambient exchange.
This equation is in the derived strict-diagram category followed by total Rlim;
it does not infer equality of maps from their separate finite evaluations.
Source: thm-cbc-qbar.proof.md, ordered quotient-diagram exchange
(blueprint: def-zl-framework-open-exchange).
Proof: transpose the proper map using the tower adjunction. The conjugate defining
frameworkPushLimit preserves its unit and counit, so the proper square commutes
before evaluation. Transpose the open map with frameworkTowerOpenAdj: the
constant-diagram mate preserves the open unit, hence this square also commutes.
Compose in the stated proper-then-open order. Functorial total inverse limit
preserves the resulting equality. In particular it holds on the strict quotient
complex of one flat K-flat representative, with every transition retained. -/
theorem frameworkAmbientExchange_strict
    (M : DerivedCategory (exchangeTowers G.X ((completed l E).ring G.X))) :
    frameworkStrictSource l E D G M ≫
        (completedRlim G.V ((completed l E).ring G.V)).map
          ((frameworkTowerExchange l E D G).app M) =
      (frameworkAmbientExchange l E D G).app
          ((completedRlim G.X ((completed l E).ring G.X)).obj M) ≫
        frameworkStrictTarget l E D G M := by
  sorry

/-- The framework exchange on its recorded support and pullback endpoints. The source
and target factors are exclusively the framework's projection-normalized support and
whole quotient-unit pullback realizations. There is no coefficient-presentation J,
comparison S or T, or completed PBC exchange in its defining equation.
Source: thm-cbc-qbar.proof.md (blueprint: def-zl-framework-open-exchange). -/
@[irreducible] def frameworkExchange (hl : l ≠ D.p)
    (K : sfIntegralConstructibleCategory l E G.X) :
    ((constructibleIntegralPullback l E G.v).obj
      ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
        G.c E).obj K)).obj ⟶
    ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl)
      G.c' E).obj ((constructibleIntegralPullback l E G.u).obj K)).obj :=
  (frameworkOpenPullRealization l E G.v).inv.app
      ((sfCompactSupportFiniteIntegralFunctor l D.k (coefficientPrimeUnit l D hl) G.c E).obj K) ≫
    (pull (completed l E) G.v).map
      ((sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) G.c).inv.app K) ≫
    (frameworkAmbientExchange l E D G).app K.obj ≫
    (image (completed l E) G.c').map
      ((frameworkOpenPullRealization l E G.u).hom.app K) ≫
    (sfQcqsCompactSupportRealization l E D.k (coefficientPrimeUnit l D hl) G.c').hom.app
      ((constructibleIntegralPullback l E G.u).obj K)

end WeilConjectures.ZlFrameworkPbc
