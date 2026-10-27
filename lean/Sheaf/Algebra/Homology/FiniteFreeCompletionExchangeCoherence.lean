/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel
public import Sheaf.Algebra.Homology.FiniteFreeCompletionExchange
public import Sheaf.Algebra.Homology.CompletionRepresentativeAccessors
public import Sheaf.Algebra.Homology.ScalarTensorSection
public import Sheaf.Algebra.Homology.ArithmeticRoosMap
public import Sheaf.Algebra.Homology.RoosRepresentativeComposition
import Sheaf.Algebra.Homology.FiniteFreeQuotientRoosComparison
import Sheaf.Algebra.Homology.FiniteFreeQuotientRoosHorizontalCoherence
import Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent
import Sheaf.Algebra.Homology.IdentityQuotientRoosNormalization
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients

/-! # Coherence of finite free completion exchange

Source: Stacks Project, sites-cohomology.tex, Tag 0941, and the coefficient-tower
and identity refinement in the DAG proof, steps 1--10.
(blueprint: lem-pur-finite-free-completion-exchange-coherence).

The ordinary associator is fixed on sheafified tensor generators, and the derived
associator is fixed by the recorded cochain counits. Exchanges retain the existing
representative specification, including both actual Roos coordinates.
-/

@[expose] public section
set_option autoImplicit false
-- Avoid re-synthesizing the site instances in the section-variable linter.
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r wR wS wV x y xA xB xD yA yB yD xA₀ xB₀ xD₀ yA₀ yB₀ yD₀ zA zB zD
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic
open scoped ChangeOfRings

namespace CategoryTheory.PrincipalQuotientCompletion


attribute [local irreducible] RepresentativeComparison
  quotientTower roosF SheafOfModules.monoidalCategory
  strictRoosMapOfSquare
  Functor.mapHomologicalComplexCompIso

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S V : Sheaf J CommRingCat.{r}} {a : R ⟶ S} {b : S ⟶ V}
  [HasDerivedCategory.{wR}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
  [HasDerivedCategory.{wS}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
  [HasDerivedCategory.{wV}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J V))]


attribute [local irreducible] scalarTensorSection arithmeticRoosMap
  CochainComplex.IsKFlatIndependentCoefficients

section compositionProof
attribute [local irreducible] quotientMap quotientProduct roosχ

/-- Scalar reassociation with explicit functors and normalization predicates.
Source: Stacks 03EK, 06YY (blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
structure ScalarAssociatorData
    {A : Type xA₀} [Category.{yA₀} A] [Preadditive A]
    {B : Type xB₀} [Category.{yB₀} B] [Preadditive B]
    {D : Type xD₀} [Category.{yD₀} D] [Preadditive D]
    {DA : Type xA} [Category.{yA} DA] {DB : Type xB} [Category.{yB} DB]
    {DD : Type xD} [Category.{yD} DD]
    (E : A ⥤ B) [E.Additive] (F : B ⥤ D) [F.Additive] (G : A ⥤ D) [G.Additive]
    (T : DA ⥤ DB) (U : DB ⥤ DD) (V : DA ⥤ DD)
    (QA : CochainComplex A ℤ ⥤ DA) (QB : CochainComplex B ℤ ⥤ DB)
    (QD : CochainComplex D ℤ ⥤ DD)
    (ηa : QA ⋙ T ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ QB)
    (ηb : QB ⋙ U ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ QD)
    (ηba : QA ⋙ V ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ QD)
    (balancedFormula : (E ⋙ F ≅ G) → Prop) (good : CochainComplex A ℤ → Prop) where
  /-- The ordinary associator. -/
  ordinary : E ⋙ F ≅ G
  /-- Its prescribed normalization. -/
  balanced : balancedFormula ordinary
  /-- The derived associator. -/
  derived : T ⋙ U ≅ V
  /-- Its computation on resolving objects. -/
  computes : ∀ P, good P → derived.hom.app (QA.obj P) ≫ ηba.app P =
    U.map (ηa.app P) ≫ ηb.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫
      QD.map ((Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom.app P)

/-- The original balanced scalar associator, specialized from explicit functor data.
Source: Stacks 03EK, 06YT, 06YY
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
abbrev BalancedScalarAssociator
    (Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a)
    (Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b)
    (Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b)) :=
  ScalarAssociatorData Fa.E Fb.E Fba.E Fa.T Fb.T Fba.T
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q Fa.ε Fb.ε Fba.ε
    (fun ordinary ↦ ∀ M (U : Cᵒᵖ) (s : S.obj.obj U) (q : V.obj.obj U) (x : M.val.obj U),
      (ordinary.hom.app M).val.app U
        (scalarTensorSection Fb (Fa.E.obj M) U q (scalarTensorSection Fa M U s x)) =
          scalarTensorSection Fba M U (b.hom.app U s * q) x)
    (CochainComplex.IsKFlatIndependentCoefficients (R := R))

/-- The original ordinary projection of the balanced scalar associator.
Source: Stacks 03EK and 06YY
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
abbrev BalancedScalarAssociator.ordinary
    {Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a}
    {Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b}
    {Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b)}
    (α : BalancedScalarAssociator Fa Fb Fba) := ScalarAssociatorData.ordinary α

/-- The original balanced projection of the balanced scalar associator.
Source: Stacks 03EK and 06YY
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
abbrev BalancedScalarAssociator.balanced
    {Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a}
    {Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b}
    {Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b)}
    (α : BalancedScalarAssociator Fa Fb Fba) := ScalarAssociatorData.balanced α

/-- The original derived projection of the balanced scalar associator.
Source: Stacks 03EK and 06YY
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
abbrev BalancedScalarAssociator.derived
    {Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a}
    {Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b}
    {Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b)}
    (α : BalancedScalarAssociator Fa Fb Fba) := ScalarAssociatorData.derived α

/-- The original computes projection of the balanced scalar associator.
Source: Stacks 03EK and 06YY
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
abbrev BalancedScalarAssociator.computes
    {Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a}
    {Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b}
    {Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b)}
    (α : BalancedScalarAssociator Fa Fb Fba) := ScalarAssociatorData.computes α

/-- The scalar multiplication identification for identity extension, with its derived
normalization. Source: Stacks 03EK and 06YY, DAG proof step 9
(blueprint: lem-pur-finite-free-completion-exchange-coherence). -/
structure BalancedScalarUnit
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wR} (𝟙 R)) where
  /-- Ordinary multiplication. -/
  ordinary : F.E ≅ 𝟭 _
  /-- Multiplication on every sheafified tensor generator. -/
  balanced : ∀ M (U : Cᵒᵖ) (s : R.obj.obj U) (x : M.val.obj U),
    (ordinary.hom.app M).val.app U (scalarTensorSection F M U s x) = s • x
  /-- The induced derived multiplication identification. -/
  derived : F.T ≅ 𝟭 _
  /-- Its canonical K-flat normalization. -/
  computes : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
    derived.hom.app (DerivedCategory.Q.obj P) =
      F.ε.app P ≫ DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)


open SheafOfModules

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem finiteFree_exact
    {R S : Sheaf J CommRingCat.{r}} {φ : R ⟶ S}
    [HasDerivedCategory.{wR} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (hfree : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ)).obj
          (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        ∐ (fun _ : Fin d ↦ SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R))))
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (uS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (hu : ∀ U : Cᵒᵖ, IsUnit (@id (S.obj.obj U) (uS.val U)))
    (e : ℕ) (he : 1 ≤ e)
    (hrelation : ∀ U : Cᵒᵖ,
      φ.hom.app U (@id (R.obj.obj U) (t.val U)) =
        (@id (S.obj.obj U) (uS.val U)) * (@id (S.obj.obj U) (vS.val U)) ^ e)
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))] :
    PreservesFiniteLimits F.E ∧ PreservesFiniteColimits F.E := by
  obtain ⟨d⟩ := finiteFreeQuotientRoosComparison F hfree t vS uS hu e he hrelation
  exact ⟨d.exact_limits, d.exact_colimits⟩

private theorem scalarCounit_isIso
    {R' S' : Sheaf J CommRingCat.{r}} {φ : R' ⟶ S'}
    [HasDerivedCategory.{wR} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R'))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S'))]
    (F : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    [PreservesFiniteLimits F.E] [PreservesFiniteColimits F.E] : IsIso F.ε := by
  let := F.universal
  apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    (W := HomologicalComplex.quasiIso _ (.up ℤ)) F.T F.ε
  intro P P' f hf
  have : QuasiIso f := hf
  change IsIso (DerivedCategory.Q.map ((extendedComplex F).map f))
  infer_instance

private theorem natTrans_eq_on_resolving
    {A : Type xA} [Category.{yA} A] {B : Type xB} [Category.{yB} B]
    {F G : A ⥤ B} (good : A → Prop)
    (hres : ∀ P, ∃ (K : A) (p : K ⟶ P), good K ∧ IsIso (F.map p))
    (α β : F ⟶ G) (h : ∀ K, good K → α.app K = β.app K) : α = β := by
  ext P
  obtain ⟨K, p, hK, hp⟩ := hres P
  let : IsIso (F.map p) := hp
  apply (cancel_epi (F.map p)).1
  exact (α.naturality p).trans
    ((congrArg (· ≫ G.map p) (h K hK)).trans (β.naturality p).symm)

private theorem composite_normalization_all
    {A₀ : Type xA₀} [Category.{yA₀} A₀]
    {B₀ : Type xB₀} [Category.{yB₀} B₀] {D₀ : Type xD₀} [Category.{yD₀} D₀]
    {A : Type xA} [Category.{yA} A] {B : Type xB} [Category.{yB} B]
    {D : Type xD} [Category.{yD} D]
    (QA : A₀ ⥤ A) (QB : B₀ ⥤ B) (QD : D₀ ⥤ D)
    (Ea : A₀ ⥤ B₀) (Eb : B₀ ⥤ D₀) (Eba : A₀ ⥤ D₀)
    (Ta : A ⥤ B) (Tb : B ⥤ D) (Tba : A ⥤ D)
    (ηa : QA ⋙ Ta ⟶ Ea ⋙ QB) (ηb : QB ⋙ Tb ⟶ Eb ⋙ QD)
    (ηba : QA ⋙ Tba ⟶ Eba ⋙ QD) (c : Ea ⋙ Eb ⟶ Eba)
    (d : Ta ⋙ Tb ⟶ Tba) (good : A₀ → Prop)
    (hres : ∀ P, ∃ (K : A₀) (p : K ⟶ P), good K ∧ IsIso (QA.map p))
    (h : ∀ P, good P → d.app (QA.obj P) ≫ ηba.app P =
      Tb.map (ηa.app P) ≫ ηb.app (Ea.obj P) ≫ QD.map (c.app P)) :
    ∀ P, d.app (QA.obj P) ≫ ηba.app P =
      Tb.map (ηa.app P) ≫ ηb.app (Ea.obj P) ≫ QD.map (c.app P) := by
  let γ : QA ⋙ (Ta ⋙ Tb) ⟶ Eba ⋙ QD := Functor.whiskerLeft QA d ≫ ηba
  let δ : QA ⋙ (Ta ⋙ Tb) ⟶ Eba ⋙ QD :=
    (Functor.associator QA Ta Tb).inv ≫ Functor.whiskerRight ηa Tb ≫
      (Functor.associator Ea QB Tb).hom ≫ Functor.whiskerLeft Ea ηb ≫
      (Functor.associator Ea Eb QD).inv ≫ Functor.whiskerRight c QD
  have he : γ = δ := natTrans_eq_on_resolving good (fun P ↦ by
    obtain ⟨K, p, hK, hp⟩ := hres P
    let : IsIso (QA.map p) := hp
    refine ⟨K, p, hK, ?_⟩
    change IsIso (Tb.map (Ta.map (QA.map p)))
    infer_instance) γ δ (by
      intro P hP
      simpa only [γ, δ, NatTrans.comp_app, Functor.associator_inv_app,
        Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        Category.id_comp, Category.comp_id, Functor.id_obj, Category.assoc] using h P hP)
  intro P
  simpa only [γ, δ, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id, Functor.id_obj, Category.assoc] using
      NatTrans.congr_app he P

private theorem exists_balancedScalarAssociator
    (Fa : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a)
    (Fb : DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b)
    (Fba : DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b))
    :
    ∃ α : BalancedScalarAssociator Fa Fb Fba, ∀ P,
      α.derived.hom.app (DerivedCategory.Q.obj P) ≫ Fba.ε.app P =
        Fb.T.map (Fa.ε.app P) ≫ Fb.ε.app ((extendedComplex Fa).obj P) ≫
          DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexCompIso α.ordinary (.up ℤ)).hom.app P) := by
  classical
  obtain ⟨ordinary, hord, derived, hderived, _⟩ :=
    RingedKFlatWord.scalar_associator a b Fa Fb Fba
  let good (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R)) ℤ) :=
    P.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)
  have hres (P) : ∃ (K : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R)) ℤ) (p : K ⟶ P),
      good K ∧ IsIso (DerivedCategory.Q.{wR}.map p) := by
    obtain ⟨K, p, hk, hf, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
    let : QuasiIso p := hp
    exact ⟨K, p, ⟨hk, fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso R (K.X n)).symm (hf n)⟩, inferInstance⟩
  have hc := composite_normalization_all
    (A₀ := CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R)) ℤ)
    (B₀ := CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S)) ℤ)
    (D₀ := CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J V)) ℤ)
    (A := DerivedCategory.{wR} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R)))
    (B := DerivedCategory.{wS} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J S)))
    (D := DerivedCategory.{wV} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J V)))
    DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (extendedComplex Fa) (extendedComplex Fb) (extendedComplex Fba)
    Fa.T Fb.T Fba.T Fa.ε Fb.ε Fba.ε
    (Functor.mapHomologicalComplexCompIso ordinary (.up ℤ)).hom derived.hom
    good hres (fun P hP ↦ hderived P hP.1 hP.2)
  exact ⟨⟨ordinary, hord, derived, fun P _ ↦ hc P⟩, hc⟩

private theorem inverseComposition
    {A : Type xA} [Category.{yA} A]
    {H I J K L M N O D : A}
    (da : H ⟶ I) (aa : J ⟶ I) (db : J ⟶ K) (ab : L ⟶ K)
    (ds : I ⟶ M) (ar : K ⟶ M) (ac : L ⟶ M)
    (m : L ⟶ N) (m' : M ⟶ O) (dba : D ⟶ O) (aba : N ⟶ O) (c : H ⟶ D)
    [IsIso aa] [IsIso ab] [IsIso aba]
    (hsq : aa ≫ ds = db ≫ ar) (hcomp : ab ≫ ar = ac)
    (hcoord : da ≫ ds ≫ m' = c ≫ dba) (hnat : m ≫ aba = ac ≫ m') :
    da ≫ inv aa ≫ db ≫ inv ab ≫ m = c ≫ dba ≫ inv aba := by
  apply (cancel_mono aba).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hnat, ← hcomp]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  simp only [Category.assoc]
  rw [← Category.assoc db, hsq.symm]
  simp only [← Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  simpa only [Category.assoc] using hcoord

private theorem exchangeSquareComposition
    {A : Type xA} [Category.{yA} A] {B : Type xB} [Category.{yB} B]
    {D : Type xD} [Category.{yD} D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    (CA : A ⥤ A) (CB : B ⥤ B) (CD : D ⥤ D)
    (α : F ⋙ G ⟶ H)
    (ea : CA ⋙ F ⟶ F ⋙ CB) (eb : CB ⋙ G ⟶ G ⋙ CD) (ec : CA ⋙ H ⟶ H ⋙ CD)
    {X U : A} {Y V : B} {Z W : D}
    (p : F.obj X ⟶ Y) (q : CA.obj X ⟶ U) (qS : CB.obj Y ⟶ V)
    (qV : CD.obj Z ⟶ W) (c : G.obj Y ⟶ Z) (h : H.obj X ⟶ Z)
    (a' : F.obj U ⟶ V) (b' : G.obj V ⟶ W) (ac : H.obj U ⟶ W)
    [IsIso h] [IsIso qV]
    (ha : ea.app X ≫ CB.map p ≫ qS = F.map q ≫ a')
    (hb : eb.app Y ≫ CD.map c ≫ qV = G.map qS ≫ b')
    (hc : ec.app X ≫ CD.map h ≫ qV = H.map q ≫ ac)
    (hp : α.app X ≫ h = G.map p ≫ c)
    (hab : G.map a' ≫ b' = α.app U ≫ ac) :
    G.map (ea.app X) ≫ eb.app (F.obj X) ≫ CD.map (α.app X) =
      α.app (CA.obj X) ≫ ec.app X := by
  apply (cancel_mono (CD.map h ≫ qV)).1
  have hn : G.map (CB.map p) ≫ eb.app Y = eb.app (F.obj X) ≫ CD.map (G.map p) :=
    eb.naturality p
  have hnα : G.map (F.map q) ≫ α.app U = α.app (CA.obj X) ≫ H.map q :=
    α.naturality q
  simp only [Category.assoc]
  rw [← CD.map_comp_assoc, hp, CD.map_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (eb.app (F.obj X)), ← hn]
  simp only [Category.assoc]
  rw [hb]
  rw [← G.map_comp_assoc, ← G.map_comp_assoc, Category.assoc (ea.app X), ha, G.map_comp]
  rw [Category.assoc, hab, ← Category.assoc, hnα, Category.assoc, ← hc]

private theorem rightFractionThree
    {D : Type xD} [Category.{yD} D] {A B C D' E F G : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D') (d : D' ⟶ E)
    (r : A ⟶ F) (s : F ⟶ G) (t : G ⟶ E) [IsIso d]
    (h : a ≫ b ≫ c ≫ d = r ≫ s ≫ t) :
    a ≫ b ≫ c = r ≫ s ≫ t ≫ inv d := by
  apply (cancel_mono d).1
  simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using h

private theorem fractionNaturality
    {A : Type xA} [Category.{yA} A] {B : Type xB} [Category.{yB} B]
    (T : A ⥤ B) {H I X : A} {H' I' X' : B}
    (d : H ⟶ I) (a : X ⟶ I) (d' : H' ⟶ I') (a' : X' ⟶ I')
    (h : T.obj H ⟶ H') (j : T.obj I ⟶ I') (k : T.obj X ⟶ X')
    [IsIso a] [IsIso a']
    (hd : T.map d ≫ j = h ≫ d') (ha : T.map a ≫ j = k ≫ a') :
    T.map (d ≫ inv a) ≫ k = h ≫ d' ≫ inv a' := by
  apply (cancel_mono a').1
  simp only [T.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← ha, ← Category.assoc (T.map (inv a)), ← T.map_comp,
    IsIso.inv_hom_id, T.map_id, Category.id_comp]
  exact hd

private theorem horizontalAssembly
    {D : Type xD} [Category.{yD} D]
    {A B C D' E F G H I : D}
    (p : A ⟶ B) (l : B ⟶ C) (ec : C ⟶ D') (eb : B ⟶ E)
    (k : E ⟶ D') (lb : D' ⟶ F) (m : F ⟶ H) (c : E ⟶ G) (lba : G ⟶ H)
    (α : A ⟶ I) (ε : I ⟶ G)
    (hl : l ≫ ec = eb ≫ k) (hk : k ≫ lb ≫ m = c ≫ lba)
    (hc : α ≫ ε = p ≫ eb ≫ c) :
    p ≫ l ≫ ec ≫ lb ≫ m = α ≫ ε ≫ lba := by
  rw [← Category.assoc l, hl]
  simp only [Category.assoc]
  rw [hk]
  simpa only [Category.assoc] using congrArg (· ≫ lba) hc.symm

private theorem extendSquare
    {D : Type xD} [Category.{yD} D] (C : D ⥤ D)
    {X Y Z W W' A : D} (ε : X ⟶ C.obj Y) (p : Y ⟶ Z)
    (d : Z ⟶ A) (q : C.obj Z ⟶ W) (q' : C.obj A ⟶ W')
    (m : W ⟶ W') (r : X ⟶ W) (hb : ε ≫ C.map p ≫ q = r)
    (hn : C.map d ≫ q' = q ≫ m) :
    ε ≫ C.map (p ≫ d) ≫ q' = r ≫ m := by
  simp only [C.map_comp, Category.assoc]
  rw [hn]
  simpa only [Category.assoc] using congrArg (· ≫ m) hb

private theorem reassociateFive
    {D : Type xD} [Category.{yD} D] {A B C D' E F : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D') (d : D' ⟶ E) (e : E ⟶ F) :
    (a ≫ b) ≫ (c ≫ d) ≫ e = a ≫ b ≫ c ≫ d ≫ e := by
  simp only [Category.assoc]

private theorem mappedInverseComposition
    {A : Type xA} [Category.{yA} A] {B : Type xB} [Category.{yB} B]
    (Q : A ⥤ B) {H I J K L M N O D : A}
    (da : H ⟶ I) (aa : J ⟶ I) (db : J ⟶ K) (ab : L ⟶ K)
    (ds : I ⟶ M) (ar : K ⟶ M) (ac : L ⟶ M)
    (m : L ⟶ N) (m' : M ⟶ O) (dba : D ⟶ O) (aba : N ⟶ O) (c : H ⟶ D)
    [IsIso (Q.map aa)] [IsIso (Q.map ab)] [IsIso (Q.map aba)]
    (hsq : aa ≫ ds = db ≫ ar) (hcomp : ab ≫ ar = ac)
    (hcoord : da ≫ ds ≫ m' = c ≫ dba) (hnat : m ≫ aba = ac ≫ m') :
    Q.map da ≫ inv (Q.map aa) ≫ Q.map db ≫ inv (Q.map ab) ≫ Q.map m =
      Q.map c ≫ Q.map dba ≫ inv (Q.map aba) := by
  apply inverseComposition _ _ _ _ (Q.map ds) (Q.map ar) (Q.map ac)
    _ (Q.map m') (Q.map dba) (Q.map aba) (Q.map c)
  · simpa only [Q.map_comp] using congrArg Q.map hsq
  · simpa only [Q.map_comp] using congrArg Q.map hcomp
  · simpa only [Q.map_comp] using congrArg Q.map hcoord
  · simpa only [Q.map_comp] using congrArg Q.map hnat

private theorem localizedExchangeComposition
    {A₀ : Type xA₀} [Category.{yA₀} A₀]
    {B₀ : Type xB₀} [Category.{yB₀} B₀] {D₀ : Type xD₀} [Category.{yD₀} D₀]
    {A : Type xA} [Category.{yA} A] {B : Type xB} [Category.{yB} B]
    {D : Type xD} [Category.{yD} D]
    (QA : A₀ ⥤ A) (QB : B₀ ⥤ B) (QD : D₀ ⥤ D)
    (Ea : A₀ ⥤ B₀) (Eb : B₀ ⥤ D₀) (Eba : A₀ ⥤ D₀)
    (Ta : A ⥤ B) (Tb : B ⥤ D) (Tba : A ⥤ D)
    (ηa : QA ⋙ Ta ⟶ Ea ⋙ QB) (ηb : QB ⋙ Tb ⟶ Eb ⋙ QD)
    (ηba : QA ⋙ Tba ⟶ Eba ⋙ QD)
    (H : D₀ ⥤ D₀) (CR : A ⥤ A) (CS : B ⥤ B) (CV : D ⥤ D)
    (κV : QD ⋙ CV ⟶ H ⋙ QD)
    (α : Ea ⋙ Eb ≅ Eba) (αD : Ta ⋙ Tb ≅ Tba)
    (εa : CR ⋙ Ta ⟶ Ta ⋙ CS) (εb : CS ⋙ Tb ⟶ Tb ⋙ CV)
    (εba : CR ⋙ Tba ⟶ Tba ⋙ CV)
    (P X : A₀) (Y I : B₀) (J K L : D₀)
    (κR : CR.obj (QA.obj P) ⟶ QA.obj X)
    (κS : CS.obj (QB.obj (Ea.obj P)) ⟶ QB.obj Y)
    (da : Ea.obj X ⟶ I) (aa : Y ⟶ I)
    (db : Eb.obj Y ⟶ J) (ab : H.obj (Eb.obj (Ea.obj P)) ⟶ J)
    (dba : Eba.obj X ⟶ K) (aba : H.obj (Eba.obj P) ⟶ K)
    (ds : Eb.obj I ⟶ L) (ar : J ⟶ L)
    (ac : H.obj (Eb.obj (Ea.obj P)) ⟶ L) (m' : L ⟶ K)
    (hη : IsIso (ηba.app P)) (hκ : IsIso (κV.app (Eba.obj P)))
    (haa : IsIso (QB.map aa)) (hab : IsIso (QD.map ab)) (haba : IsIso (QD.map aba))
    (hηbY : IsIso (ηb.app Y)) (hηbI : IsIso (ηb.app I))
    (hrepA : εa.app (QA.obj P) ≫ CS.map (ηa.app P) ≫ κS ≫ QB.map aa =
      Ta.map κR ≫ ηa.app X ≫ QB.map da)
    (hrepB : εb.app (QB.obj (Ea.obj P)) ≫ CV.map (ηb.app (Ea.obj P)) ≫
        κV.app (Eb.obj (Ea.obj P)) ≫ QD.map ab =
      Tb.map κS ≫ ηb.app Y ≫ QD.map db)
    (hrepBA : εba.app (QA.obj P) ≫ CV.map (ηba.app P) ≫
        κV.app (Eba.obj P) ≫ QD.map aba =
      Tba.map κR ≫ ηba.app X ≫ QD.map dba)
    (hcP : αD.hom.app (QA.obj P) ≫ ηba.app P =
      Tb.map (ηa.app P) ≫ ηb.app (Ea.obj P) ≫ QD.map (α.hom.app P))
    (hcX : αD.hom.app (QA.obj X) ≫ ηba.app X =
      Tb.map (ηa.app X) ≫ ηb.app (Ea.obj X) ≫ QD.map (α.hom.app X))
    (hsq : Eb.map aa ≫ ds = db ≫ ar) (hcomp : ab ≫ ar = ac)
    (hcoord : Eb.map da ≫ ds ≫ m' = α.hom.app X ≫ dba)
    (hnat : H.map (α.hom.app P) ≫ aba = ac ≫ m') :
    Tb.map (εa.app (QA.obj P)) ≫ εb.app (Ta.obj (QA.obj P)) ≫
        CV.map (αD.hom.app (QA.obj P)) =
      αD.hom.app (CR.obj (QA.obj P)) ≫ εba.app (QA.obj P) := by
  let : IsIso (ηba.app P) := hη
  let : IsIso (κV.app (Eba.obj P)) := hκ
  let : IsIso (QB.map aa) := haa
  let : IsIso (QD.map ab) := hab
  let : IsIso (QD.map aba) := haba
  let : IsIso (ηb.app Y) := hηbY
  let : IsIso (ηb.app I) := hηbI
  have hm : QD.map (Eb.map aa) = inv (ηb.app Y) ≫ Tb.map (QB.map aa) ≫ ηb.app I := by
    apply (cancel_epi (ηb.app Y)).1
    simpa only [Category.assoc, IsIso.hom_inv_id_assoc, Functor.comp_map] using
      (ηb.naturality aa).symm
  let : IsIso (QD.map (Eb.map aa)) := by rw [hm]; infer_instance
  have hchain := mappedInverseComposition QD (Eb.map da) (Eb.map aa) db ab ds ar ac
    (H.map (α.hom.app P)) m' dba aba (α.hom.app X) hsq hcomp hcoord hnat
  let la := QB.map da ≫ inv (QB.map aa)
  let lb := QD.map db ≫ inv (QD.map ab)
  let lba := QD.map dba ≫ inv (QD.map aba)
  have hl : Tb.map la ≫ ηb.app Y = ηb.app (Ea.obj X) ≫
      QD.map (Eb.map da) ≫ inv (QD.map (Eb.map aa)) :=
    fractionNaturality Tb _ _ _ _ _ _ _ (ηb.naturality da) (ηb.naturality aa)
  have ha := rightFractionThree _ _ _ _ _ _ _ hrepA
  have hb := rightFractionThree _ _ _ _ _ _ _ hrepB
  have hab := rightFractionThree _ _ _ _ _ _ _ hrepBA
  let dP := QD.map (α.hom.app P)
  let mP := QD.map (H.map (α.hom.app P))
  have hb' : εb.app (QB.obj (Ea.obj P)) ≫ CV.map (ηb.app (Ea.obj P) ≫ dP) ≫
      κV.app (Eba.obj P) = Tb.map κS ≫ (ηb.app Y ≫ lb ≫ mP) := by
    simpa only [Category.assoc, lb] using extendSquare CV
      (εb.app (QB.obj (Ea.obj P))) (ηb.app (Ea.obj P)) dP
      (κV.app (Eb.obj (Ea.obj P))) (κV.app (Eba.obj P)) mP _ hb
      (κV.naturality (α.hom.app P))
  have hh : Tb.map (ηa.app X ≫ la) ≫ (ηb.app Y ≫ lb ≫ mP) =
      αD.hom.app (QA.obj X) ≫ (ηba.app X ≫ lba) := by
    have hc : (QD.map (Eb.map da) ≫ inv (QD.map (Eb.map aa))) ≫ lb ≫ mP =
        QD.map (α.hom.app X) ≫ lba :=
      (reassociateFive _ _ _ _ _).trans hchain
    simp only [Tb.map_comp, Category.assoc]
    exact horizontalAssembly (Tb.map (ηa.app X)) (Tb.map la) (ηb.app Y)
      (ηb.app (Ea.obj X)) _ lb mP _ lba _ _ hl hc hcX
  apply exchangeSquareComposition Ta Tb Tba CR CS CV αD.hom εa εb εba
    (ηa.app P) κR κS (κV.app (Eba.obj P)) (ηb.app (Ea.obj P) ≫ dP) (ηba.app P)
    (ηa.app X ≫ la) (ηb.app Y ≫ lb ≫ mP) (ηba.app X ≫ lba)
  · exact ha
  · exact hb'
  · exact hab
  · exact hcP
  · exact hh

private theorem representativeComposition_localized
    {A : Type xA₀} [Category.{yA₀} A] [Abelian A] [HasCountableProducts A]
    {B : Type xB₀} [Category.{yB₀} B] [Abelian B] [HasCountableProducts B]
    {D : Type xD₀} [Category.{yD₀} D] [Abelian D] [HasCountableProducts D]
    {LA : Type xA} [Category.{yA} LA] {LB : Type xB} [Category.{yB} LB]
    {LD : Type xD} [Category.{yD} LD]
    (QA : CochainComplex A ℤ ⥤ LA) (QB : CochainComplex B ℤ ⥤ LB)
    (QD : CochainComplex D ℤ ⥤ LD)
    (E : A ⥤ B) [E.Additive] (F : B ⥤ D) [F.Additive] (G : A ⥤ D) [G.Additive]
    (Ta : LA ⥤ LB) (Tb : LB ⥤ LD) (Tba : LA ⥤ LD)
    (ηa : QA ⋙ Ta ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ QB)
    (ηb : QB ⋙ Tb ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ QD)
    (ηba : QA ⋙ Tba ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ QD)
    (X : CochainComplex A ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (Y : CochainComplex B ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (Z : CochainComplex D ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
    (CR : LA ⥤ LA) (CS : LB ⥤ LB) (CV : LD ⥤ LD)
    (κR : QA ⋙ CR ⟶ (X ⋙ roosF) ⋙ QA)
    (κS : QB ⋙ CS ⟶ (Y ⋙ roosF) ⋙ QB)
    (κV : QD ⋙ CV ⟶ (Z ⋙ roosF) ⋙ QD)
    (α : E ⋙ F ≅ G) (αD : Ta ⋙ Tb ≅ Tba)
    (εa : CR ⋙ Ta ⟶ Ta ⋙ CS) (εb : CS ⋙ Tb ⟶ Tb ⋙ CV)
    (εba : CR ⋙ Tba ⟶ Tba ⋙ CV)
    (P : CochainComplex A ℤ) (e f : ℕ) (he : 1 ≤ e)
    (ra : RepresentativeRoosComparison E (X.obj P)
      (Y.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)) e)
    (rb : RepresentativeRoosComparison F (Y.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
      (Z.obj ((F.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj P))) f)
    (rba : RepresentativeRoosComparison G (X.obj P)
      (Z.obj ((G.mapHomologicalComplex (.up ℤ)).obj P)) (e * f))
    (d : RepresentativeComposition α (X.obj P)
      (Y.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
      (Z.obj ((F.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj P)))
      (Z.obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
      (Z.map ((Functor.mapHomologicalComplexCompIso α (.up ℤ)).hom.app P)) e f he ra rb rba)
    (hη : IsIso (ηba.app P))
    (hκ : IsIso (κV.app ((G.mapHomologicalComplex (.up ℤ)).obj P)))
    (haa : IsIso (QB.map ra.a)) (hab : IsIso (QD.map rb.a))
    (haba : IsIso (QD.map rba.a)) (hηb : IsIso ηb)
    (hrepA : εa.app (QA.obj P) ≫ CS.map (ηa.app P) ≫
      κS.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫ QB.map ra.a =
      Ta.map (κR.app P) ≫ ηa.app (roosF.obj (X.obj P)) ≫ QB.map ra.δ.hom)
    (hrepB : εb.app (QB.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      CV.map (ηb.app ((E.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      κV.app ((F.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj P)) ≫ QD.map rb.a =
      Tb.map (κS.app ((E.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        ηb.app (roosF.obj (Y.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))) ≫ QD.map rb.δ.hom)
    (hrepBA : εba.app (QA.obj P) ≫ CV.map (ηba.app P) ≫
      κV.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫ QD.map rba.a =
      Tba.map (κR.app P) ≫ ηba.app (roosF.obj (X.obj P)) ≫ QD.map rba.δ.hom)
    (hc : ∀ K, αD.hom.app (QA.obj K) ≫ ηba.app K =
      Tb.map (ηa.app K) ≫ ηb.app ((E.mapHomologicalComplex (.up ℤ)).obj K) ≫
        QD.map ((Functor.mapHomologicalComplexCompIso α (.up ℤ)).hom.app K))
    (hnat : roosF.map (Z.map
        ((Functor.mapHomologicalComplexCompIso α (.up ℤ)).hom.app P)) ≫ rba.a =
      d.restricted.a ≫ roosF.map ((complexRestriction D (e * f)).map
        (Z.map ((Functor.mapHomologicalComplexCompIso α (.up ℤ)).hom.app P)))) :
    Tb.map (εa.app (QA.obj P)) ≫ εb.app (Ta.obj (QA.obj P)) ≫
      CV.map (αD.hom.app (QA.obj P)) =
        αD.hom.app (CR.obj (QA.obj P)) ≫ εba.app (QA.obj P) := by
  let : IsIso ηb := hηb
  exact localizedExchangeComposition QA QB QD
    (E.mapHomologicalComplex (.up ℤ)) (F.mapHomologicalComplex (.up ℤ))
    (G.mapHomologicalComplex (.up ℤ)) Ta Tb Tba ηa ηb ηba (Z ⋙ roosF)
    CR CS CV κV (Functor.mapHomologicalComplexCompIso α (.up ℤ)) αD εa εb εba
    P (roosF.obj (X.obj P)) (roosF.obj (Y.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)))
    (roosF.obj ((complexRestriction B e).obj
      (Y.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))))
    (roosF.obj ((complexRestriction D f).obj
      (Z.obj ((F.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj P)))))
    (roosF.obj ((complexRestriction D (e * f)).obj
      (Z.obj ((G.mapHomologicalComplex (.up ℤ)).obj P))))
    (roosF.obj ((complexRestriction D (e * f)).obj
      (Z.obj ((F.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj P)))))
    (κR.app P) (κS.app ((E.mapHomologicalComplex (.up ℤ)).obj P))
    ra.δ.hom ra.a rb.δ.hom rb.a rba.δ.hom rba.a
    d.restricted.δ.hom d.arithmetic d.restricted.a
    (roosF.map ((complexRestriction D (e * f)).map
      (Z.map ((Functor.mapHomologicalComplexCompIso α (.up ℤ)).hom.app P))))
    hη hκ haa hab haba inferInstance inferInstance hrepA hrepB hrepBA (hc P) (hc _)
    d.arithmetic_square d.arithmetic_composition d.coordinates hnat


section genericRepresentatives
variable
    {A : Type xA₀} [Category.{yA₀} A] [Abelian A] [HasCountableProducts A]
    {B : Type xB₀} [Category.{yB₀} B] [Abelian B] [HasCountableProducts B]
    {D : Type xD₀} [Category.{yD₀} D] [Abelian D] [HasCountableProducts D]
    {LA : Type xA} [Category.{yA} LA] {LB : Type xB} [Category.{yB} LB]
    {LD : Type xD} [Category.{yD} LD]
    (QA : CochainComplex A ℤ ⥤ LA) (QB : CochainComplex B ℤ ⥤ LB)
    (QD : CochainComplex D ℤ ⥤ LD)
    (E : A ⥤ B) [E.Additive] (F : B ⥤ D) [F.Additive] (G : A ⥤ D) [G.Additive]
    (Ta : LA ⥤ LB) (Tb : LB ⥤ LD) (Tba : LA ⥤ LD)
    (ηa : QA ⋙ Ta ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ QB)
    (ηb : QB ⋙ Tb ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ QD)
    (ηba : QA ⋙ Tba ⟶ G.mapHomologicalComplex (.up ℤ) ⋙ QD)
    (X : CochainComplex A ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (Y : CochainComplex B ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (Z : CochainComplex D ℤ ⥤ CochainComplex (ℕᵒᵖ ⥤ D) ℤ)
    (CR : LA ⥤ LA) (CS : LB ⥤ LB) (CV : LD ⥤ LD)
    (κR : QA ⋙ CR ⟶ (X ⋙ roosF) ⋙ QA)
    (κS : QB ⋙ CS ⟶ (Y ⋙ roosF) ⋙ QB)
    (κV : QD ⋙ CV ⟶ (Z ⋙ roosF) ⋙ QD)
    (α : E ⋙ F ≅ G) (αD : Ta ⋙ Tb ≅ Tba)
    (εa : CR ⋙ Ta ≅ Ta ⋙ CS) (εb : CS ⋙ Tb ≅ Tb ⋙ CV)
    (εba : CR ⋙ Tba ≅ Tba ⋙ CV)
    (e f : ℕ) (he : 1 ≤ e)
    (good : CochainComplex A ℤ → Prop)
    (qA : ∀ (P : CochainComplex A ℤ) (n : ℕ), P ⟶ (X.obj P).asFunctor.obj (op n))
    (qB : ∀ (P : CochainComplex B ℤ) (n : ℕ), P ⟶ (Y.obj P).asFunctor.obj (op n))
    (qD : ∀ (P : CochainComplex D ℤ) (n : ℕ), P ⟶ (Z.obj P).asFunctor.obj (op n))

include QA QB QD E F G Ta Tb Tba ηa ηb ηba X Y Z CR CS CV κR κS κV α αD εa εb εba
  e f he good in
private theorem coherenceOfRepresentatives
    (Ra : CochainComplex A ℤ → Type zA)
    (Rb : CochainComplex B ℤ → Type zB)
    (Rba : CochainComplex A ℤ → Type zD)
    (getA : ∀ P, Ra P → RepresentativeRoosComparison E (X.obj P)
      (Y.obj ((E.mapHomologicalComplex (.up ℤ)).obj P)) e)
    (getB : ∀ P, Rb P → RepresentativeRoosComparison F (Y.obj P)
      (Z.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) f)
    (getBA : ∀ P, Rba P → RepresentativeRoosComparison G (X.obj P)
      (Z.obj ((G.mapHomologicalComplex (.up ℤ)).obj P)) (e * f))
    (hdA : ∀ P (ra : Ra P), εa.hom.app (QA.obj P) ≫ CS.map (ηa.app P) ≫
      κS.app ((E.mapHomologicalComplex (.up ℤ)).obj P) ≫ QB.map (getA P ra).a =
      Ta.map (κR.app P) ≫ ηa.app (roosF.obj (X.obj P)) ≫ QB.map (getA P ra).δ.hom)
    (hdB : ∀ P (rb : Rb P), εb.hom.app (QB.obj P) ≫ CV.map (ηb.app P) ≫
      κV.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫ QD.map (getB P rb).a =
      Tb.map (κS.app P) ≫ ηb.app (roosF.obj (Y.obj P)) ≫ QD.map (getB P rb).δ.hom)
    (hdBA : ∀ P (rba : Rba P), εba.hom.app (QA.obj P) ≫ CV.map (ηba.app P) ≫
      κV.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫ QD.map (getBA P rba).a =
      Tba.map (κR.app P) ≫ ηba.app (roosF.obj (X.obj P)) ≫ QD.map (getBA P rba).δ.hom)
    (hrepA : ∀ P, good P → Nonempty
      (Ra P))
    (hrepB : ∀ P, good P → Nonempty
      (Rb ((E.mapHomologicalComplex (.up ℤ)).obj P)))
    (hrepBA : ∀ P, good P → Nonempty
      (Rba P))
    (hstrict : ∀ P, good P →
      ∀ (ra : Ra P)
        (rb : Rb ((E.mapHomologicalComplex (.up ℤ)).obj P))
        (rba : Rba P),
      ∃ d : RepresentativeComposition α (X.obj P)
        (Y.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
        (Z.obj ((F.mapHomologicalComplex (.up ℤ)).obj
          ((E.mapHomologicalComplex (.up ℤ)).obj P)))
        (Z.obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
        (Z.map ((Functor.mapHomologicalComplexCompIso α (.up ℤ)).hom.app P))
        e f he (getA P ra) (getB _ rb) (getBA P rba),
      roosF.map (Z.map ((Functor.mapHomologicalComplexCompIso α (.up ℤ)).hom.app P)) ≫
        (getBA P rba).a = d.restricted.a ≫ roosF.map ((complexRestriction D (e * f)).map
          (Z.map ((Functor.mapHomologicalComplexCompIso α (.up ℤ)).hom.app P))))
    (hη : ∀ P, good P → IsIso (ηba.app P))
    (hκ : ∀ P, good P → IsIso (κV.app ((G.mapHomologicalComplex (.up ℤ)).obj P)))
    (hηb : IsIso ηb)
    (hQB : ∀ {P P' : CochainComplex B ℤ} (p : P ⟶ P'), QuasiIso p → IsIso (QB.map p))
    (hQD : ∀ {P P' : CochainComplex D ℤ} (p : P ⟶ P'), QuasiIso p → IsIso (QD.map p))
    (hc : ∀ K, αD.hom.app (QA.obj K) ≫ ηba.app K =
      Tb.map (ηa.app K) ≫ ηb.app ((E.mapHomologicalComplex (.up ℤ)).obj K) ≫
        QD.map ((Functor.mapHomologicalComplexCompIso α (.up ℤ)).hom.app K)) :
    ∀ P, good P →
      (Tb.map (εa.hom.app (QA.obj P)) ≫ εb.hom.app (Ta.obj (QA.obj P)) ≫
        CV.map (αD.hom.app (QA.obj P)) =
          αD.hom.app (CR.obj (QA.obj P)) ≫ εba.hom.app (QA.obj P)) ∧
      ∃ (ra : Ra P)
        (rb : Rb ((E.mapHomologicalComplex (.up ℤ)).obj P))
        (rba : Rba P),
        Nonempty (RepresentativeComposition α (X.obj P)
          (Y.obj ((E.mapHomologicalComplex (.up ℤ)).obj P))
          (Z.obj ((F.mapHomologicalComplex (.up ℤ)).obj
            ((E.mapHomologicalComplex (.up ℤ)).obj P)))
          (Z.obj ((G.mapHomologicalComplex (.up ℤ)).obj P))
          (Z.map ((Functor.mapHomologicalComplexCompIso α (.up ℤ)).hom.app P))
          e f he (getA P ra) (getB _ rb) (getBA P rba)) := by
  intro P hP
  obtain ⟨ra⟩ := hrepA P hP
  obtain ⟨rb⟩ := hrepB P hP
  obtain ⟨rba⟩ := hrepBA P hP
  obtain ⟨d, hnat⟩ := hstrict P hP ra rb rba
  have h := representativeComposition_localized QA QB QD E F G Ta Tb Tba ηa ηb ηba
    X Y Z CR CS CV κR κS κV α αD εa.hom εb.hom εba.hom P e f he
    (getA P ra) (getB _ rb) (getBA P rba) d (hη P hP) (hκ P hP)
    (hQB (getA P ra).a (getA P ra).arithmetic_quasiIso)
    (hQD (getB _ rb).a (getB _ rb).arithmetic_quasiIso)
    (hQD (getBA P rba).a (getBA P rba).arithmetic_quasiIso) hηb
    (hdA P ra) (hdB _ rb) (hdBA P rba) hc hnat
  exact ⟨h, ra, rb, rba, ⟨d⟩⟩

end genericRepresentatives


private theorem matrix_zero
    {A : Type xA} [Category.{yA} A] [Preadditive A] [HasBinaryBiproducts A]
    {B : Type xB} [Category.{yB} B] [Preadditive B] [HasBinaryBiproducts B]
    (E : A ⥤ B) [E.Additive]
    {P X X₀ X₁ : A} {Y₀ Y₁ Z₀ Z₁ : B}
    (ν : P ⟶ X) (χ : X ⟶ X₀ ⊞ X₁) (q : P ⟶ X₁)
    (hν : ν ≫ χ = biprod.lift 0 q)
    (q' : E.obj P ⟶ Y₁) (c₀ : E.obj X₀ ⟶ Z₀) (c₁ : E.obj X₁ ⟶ Z₁)
    (b : Y₀ ⟶ Z₀) (s : Y₁ ⟶ Z₁) (hq : E.map q ≫ c₁ = q' ≫ s) :
    E.map ν ≫ biprod.lift (E.map (χ ≫ biprod.fst) ≫ c₀)
        (E.map (χ ≫ biprod.snd) ≫ c₁) =
      biprod.lift (0 : E.obj P ⟶ Y₀) q' ≫ biprod.map b s := by
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst,
      biprod.lift_fst_assoc, zero_comp]
    rw [← Category.assoc, ← E.map_comp, ← Category.assoc, hν,
      biprod.lift_fst, E.map_zero, zero_comp]
  · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
      biprod.lift_snd_assoc]
    rw [← Category.assoc, ← E.map_comp, ← Category.assoc, hν, biprod.lift_snd]
    exact hq

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem productAugmentationSquare
    {A : Type xA} [Category.{yA} A] [Abelian A] [HasCountableProducts A]
    {B : Type xB} [Category.{yB} B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (e : ℕ) (D : RepresentativeRoosComparison F X Y e)
    (P : CochainComplex A ℤ) (q : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
    (q' : ∀ n : ℕ, (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ Y.asFunctor.obj (op n))
    (hq : ∀ n : ℕ, (F.mapHomologicalComplex (.up ℤ)).map (q n) ≫
      D.β.hom.app (op n) = q' (e * (n + 1) - 1))
    (qp : P ⟶ roosP X)
    (qp' : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ roosP Y)
    (hqp : ∀ n, qp ≫ Pi.π _ n = q n)
    (hqp' : ∀ n, qp' ≫ Pi.π _ n = q' n) :
    (F.mapHomologicalComplex (.up ℤ)).map qp ≫ D.c =
      qp' ≫ selection e Y.asFunctor := by
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, D.product_formula, ← Category.assoc, ← Functor.map_comp,
    hqp, hq]
  change q' (e * (n + 1) - 1) =
    (qp' ≫ Pi.lift (fun j : ℕ ↦
      Pi.π (fun i : ℕ ↦ Y.asFunctor.obj (op i)) (e * (j + 1) - 1))) ≫
      Pi.π (fun j : ℕ ↦ Y.asFunctor.obj (op (e * (j + 1) - 1))) n
  rw [Category.assoc, Pi.lift_π, hqp']

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coneAugmentationSquare
    {A : Type xA} [Category.{yA} A] [Abelian A] [HasCountableProducts A]
    {B : Type xB} [Category.{yB} B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive]
    (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (Y : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (e : ℕ) (D : RepresentativeRoosComparison F X Y e)
    (P : CochainComplex A ℤ) (u : P ⟶ roosF.obj X)
    (v : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ roosF.obj Y)
    (q : P ⟶ roosP X) (q' : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ roosP Y)
    (hu : ∀ p : ℤ, u.f (p + 1) ≫ (roosχ X p).hom = biprod.lift 0 (q.f (p + 1)))
    (hv : ∀ p : ℤ, v.f (p + 1) ≫ (roosχ Y p).hom = biprod.lift 0 (q'.f (p + 1)))
    (hprod : (F.mapHomologicalComplex (.up ℤ)).map q ≫ D.c =
      q' ≫ selection e Y.asFunctor) :
    (F.mapHomologicalComplex (.up ℤ)).map u ≫ D.δ.hom = v ≫ D.a := by
  ext k : 1
  obtain ⟨p, hp⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change p + 1 = k at hp
  subst k
  apply (cancel_mono (roosχ ((complexRestriction B e).obj Y) p).hom).1
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [D.cone_formula, D.arithmetic_formula, ← Category.assoc, hv]
  dsimp only [Functor.mapHomologicalComplex_map_f]
  apply matrix_zero F (u.f (p + 1)) (roosχ X p).hom (q.f (p + 1)) (hu p)
    (q'.f (p + 1)) (D.c.f p) (D.c.f (p + 1))
    ((block e Y.asFunctor).f p) ((selection e Y.asFunctor).f (p + 1))
  exact congrArg (fun f ↦ f.f (p + 1)) hprod

private theorem natTrans_eq_of_resolutions
    {C D H : Type*} [Category C] [Category D] [Category H]
    (Q : C ⥤ D) (W : MorphismProperty C) [Q.IsLocalization W]
    (good : C → Prop)
    (hres : ∀ P, ∃ (K : C) (p : K ⟶ P), good K ∧ IsIso (Q.map p))
    {F G : D ⥤ H} (α β : F ⟶ G)
    (h : ∀ K, good K → α.app (Q.obj K) = β.app (Q.obj K)) : α = β := by
  apply Localization.natTrans_ext Q W
  intro P
  obtain ⟨K, p, hK, hp⟩ := hres P
  let : IsIso (Q.map p) := hp
  apply (cancel_epi (F.map (Q.map p))).1
  exact (α.naturality _).trans
    ((congrArg (· ≫ G.map (Q.map p)) (h K hK)).trans (β.naturality _).symm)

private theorem exchangeCoherenceDescent
    {A₀ A B D : Type*} [Category A₀] [Category A] [Category B] [Category D]
    (Q : A₀ ⥤ A) (W : MorphismProperty A₀) [Q.IsLocalization W]
    (good : A₀ → Prop)
    (hres : ∀ P, ∃ (K : A₀) (p : K ⟶ P), good K ∧ IsIso (Q.map p))
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    (CA : A ⥤ A) (CB : B ⥤ B) (CD : D ⥤ D)
    (α : F ⋙ G ⟶ H)
    (εa : CA ⋙ F ⟶ F ⋙ CB) (εb : CB ⋙ G ⟶ G ⋙ CD)
    (εba : CA ⋙ H ⟶ H ⋙ CD)
    (h : ∀ P, good P → G.map (εa.app (Q.obj P)) ≫ εb.app (F.obj (Q.obj P)) ≫
      CD.map (α.app (Q.obj P)) = α.app (CA.obj (Q.obj P)) ≫ εba.app (Q.obj P)) :
    ∀ X, G.map (εa.app X) ≫ εb.app (F.obj X) ≫ CD.map (α.app X) =
      α.app (CA.obj X) ≫ εba.app X := by
  let γ : CA ⋙ (F ⋙ G) ⟶ H ⋙ CD :=
    (Functor.associator CA F G).inv ≫ Functor.whiskerRight εa G ≫
      (Functor.associator F CB G).hom ≫ Functor.whiskerLeft F εb ≫
      (Functor.associator F G CD).inv ≫ Functor.whiskerRight α CD
  let δ : CA ⋙ (F ⋙ G) ⟶ H ⋙ CD := Functor.whiskerLeft CA α ≫ εba
  have he : γ = δ := natTrans_eq_of_resolutions Q W good hres γ δ (by
    intro P hP
    simpa only [γ, δ, NatTrans.comp_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp, Category.comp_id, Functor.id_obj, Category.assoc] using h P hP)
  intro X
  simpa only [γ, δ, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.id_comp, Category.comp_id, Category.assoc] using NatTrans.congr_app he X

private theorem unitCoherenceDescent
    {A₀ A B : Type*} [Category A₀] [Category A] [Category B]
    (Q : A₀ ⥤ A) (W : MorphismProperty A₀) [Q.IsLocalization W]
    (good : A₀ → Prop)
    (hres : ∀ P, ∃ (K : A₀) (p : K ⟶ P), good K ∧ IsIso (Q.map p))
    (F : A ⥤ B) (CA : A ⥤ A) (CB : B ⥤ B)
    (uA : 𝟭 A ⟶ CA) (uB : 𝟭 B ⟶ CB) (ε : CA ⋙ F ⟶ F ⋙ CB)
    (h : ∀ P, good P → F.map (uA.app (Q.obj P)) ≫ ε.app (Q.obj P) =
      uB.app (F.obj (Q.obj P))) :
    ∀ X, F.map (uA.app X) ≫ ε.app X = uB.app (F.obj X) := by
  let γ : F ⟶ F ⋙ CB :=
    (Functor.leftUnitor F).inv ≫ Functor.whiskerRight uA F ≫ ε
  have he : γ = Functor.whiskerLeft F uB :=
    natTrans_eq_of_resolutions Q W good hres γ _ (by
      intro P hP
      simpa only [γ, NatTrans.comp_app, Functor.leftUnitor_inv_app,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp] using h P hP)
  intro X
  simpa only [γ, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp] using
      NatTrans.congr_app he X

private theorem unitSquare
    {A : Type xA} [Category.{yA} A] {B : Type xB} [Category.{yB} B]
    (F : A ⥤ B) (CA : A ⥤ A) (CB : B ⥤ B)
    (uA : 𝟭 A ⟶ CA) (uB : 𝟭 B ⟶ CB) (ε : CA ⋙ F ⟶ F ⋙ CB)
    {P X : A} {Y Z W : B}
    (p : F.obj P ⟶ Y) (q : CA.obj P ⟶ X) (r : CB.obj Y ⟶ Z)
    (ηX : F.obj X ⟶ W) (δ : W ⟶ Z) (a : P ⟶ X) (b : Y ⟶ Z)
    [IsIso p] [IsIso r]
    (hrep : ε.app P ≫ CB.map p ≫ r = F.map q ≫ ηX ≫ δ)
    (hu : uA.app P ≫ q = a)
    (hn : F.map a ≫ ηX ≫ δ = p ≫ b)
    (hv : uB.app Y ≫ r = b) :
    F.map (uA.app P) ≫ ε.app P = uB.app (F.obj P) := by
  apply (cancel_mono (CB.map p ≫ r)).1
  simp only [Category.assoc]
  rw [hrep, ← F.map_comp_assoc, hu, hn]
  rw [← Category.assoc (uB.app _), ← uB.naturality p]
  simp only [Functor.id_map, Category.assoc]
  rw [hv]

private theorem unitFractionSquare
    {A : Type xA} [Category.{yA} A] {B : Type xB} [Category.{yB} B]
    (F : A ⥤ B) (CA : A ⥤ A) (CB : B ⥤ B)
    (uA : 𝟭 A ⟶ CA) (uB : 𝟭 B ⟶ CB) (ε : CA ⋙ F ⟶ F ⋙ CB)
    {P X : A} {Y Z W I : B}
    (p : F.obj P ⟶ Y) (q : CA.obj P ⟶ X) (r : CB.obj Y ⟶ Z)
    (ηX : F.obj X ⟶ W) (δ : W ⟶ I) (ar : Z ⟶ I) (a : P ⟶ X) (b : Y ⟶ Z)
    [IsIso p] [IsIso r] [har : IsIso ar]
    (hrep : ε.app P ≫ CB.map p ≫ r ≫ ar = F.map q ≫ ηX ≫ δ)
    (b' : Y ⟶ W)
    (hn : F.map a ≫ ηX = p ≫ b')
    (hcoord : b' ≫ δ = b ≫ ar)
    (hu : uA.app P ≫ q = a) (hv : uB.app Y ≫ r = b) :
    F.map (uA.app P) ≫ ε.app P = uB.app (F.obj P) := by
  apply unitSquare F CA CB uA uB ε p q (r ≫ ar) ηX δ a (b ≫ ar)
  · simpa only [Category.assoc, CB.map_comp] using hrep
  · exact hu
  · rw [← Category.assoc, hn, Category.assoc, hcoord]
  · simpa only [Category.assoc] using congrArg (· ≫ ar) hv

set_option backward.defeqAttrib.useBackward false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] Functor.mapHomologicalComplex DerivedCategory.Q in
private theorem representativeExchange_unit
    {R' S' : Sheaf J CommRingCat.{r}} {φ : R' ⟶ S'}
    [HasDerivedCategory.{wR} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R'))]
    [HasDerivedCategory.{wS} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S'))]
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} φ)
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R')).sections)
    (s : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S')).sections)
    (e : ℕ) (CR : Model R' t) (CS : Model S' s)
    (ε : CR.completion ⋙ F.T ≅ F.T ⋙ CS.completion)
    (hrep : ∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R') P →
      Nonempty (RepresentativeComparison F t s e CR CS ε P)) :
    ∀ Q, F.T.map (CR.unit.app Q) ≫ ε.hom.app Q = CS.unit.app (F.T.obj Q) := by
  have hunit (P) (hP : CochainComplex.IsKFlatIndependentCoefficients (R := R') P) :
      F.T.map (CR.unit.app (DerivedCategory.Q.obj P)) ≫
        ε.hom.app (DerivedCategory.Q.obj P) =
          CS.unit.app (F.T.obj (DerivedCategory.Q.obj P)) := by
    obtain ⟨rd⟩ := hrep P hP
    let d := rd.val
    have hq := rd.property.1
    have hd := rd.property.2
    let EC := extendedComplex F
    let X := sourceTower t P
    let Y := targetTower F s P
    have hprod := productAugmentationSquare F.E X Y e d P
      (quotientMap R' t P) (quotientMap S' s (EC.obj P)) hq
      (quotientProduct R' t P) (quotientProduct S' s (EC.obj P))
      (fun n ↦ by
        simpa only [quotientProduct, X] using Pi.lift_π (quotientMap R' t P) n)
      (fun n ↦ by
        simpa only [quotientProduct, Y, EC] using
          Pi.lift_π (quotientMap S' s ((extendedComplex F).obj P)) n)
    have haug := coneAugmentationSquare F.E X Y e d P
      (CR.augmentation P) (CS.augmentation (EC.obj P))
      (quotientProduct R' t P) (quotientProduct S' s (EC.obj P))
      (CR.coordinates P) (CS.coordinates (EC.obj P)) hprod
    let : IsIso (F.ε.app P) := F.computes P hP
    let : IsIso (CS.counit.app (EC.obj P)) := CS.computes _
      (SheafOfModules.changeOfRings_isKFlat_independentCoefficients
        φ P F.E F.obj_eq F.map_eq hP)
    let ha : IsIso (DerivedCategory.Q.{wS}.map d.a) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso.{wS} _ _).2 d.arithmetic_quasiIso
    exact unitFractionSquare
      (A := DerivedCategory.{wR} (ringedSiteModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R')))
      (B := DerivedCategory.{wS} (ringedSiteModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J S')))
      F.T CR.completion CS.completion CR.unit CS.unit ε.hom
      (F.ε.app P) (CR.counit.app P) (CS.counit.app (EC.obj P))
      (F.ε.app (roosF.obj X)) (DerivedCategory.Q.{wS}.map d.δ.hom)
      (DerivedCategory.Q.{wS}.map d.a) (DerivedCategory.Q.{wR}.map (CR.augmentation P))
      (DerivedCategory.Q.{wS}.map (CS.augmentation (EC.obj P))) hd
      (DerivedCategory.Q.{wS}.map (EC.map (CR.augmentation P)))
      (F.ε.naturality (CR.augmentation P))
      (by
        have h := congrArg (fun f ↦ DerivedCategory.Q.{wS}.map f) haug
        exact ((DerivedCategory.Q.{wS}.map_comp
          (EC.map (CR.augmentation P)) d.δ.hom).symm.trans h).trans
            (DerivedCategory.Q.{wS}.map_comp (CS.augmentation (EC.obj P)) d.a))
      (CR.unit_computes P) (CS.unit_computes (EC.obj P))
      (har := ha)
  exact unitCoherenceDescent
    (A₀ := CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R')) ℤ)
    (A := DerivedCategory.{wR} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R')))
    (B := DerivedCategory.{wS} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S')))
    DerivedCategory.Q.{wR} (HomologicalComplex.quasiIso _ (.up ℤ))
    (CochainComplex.IsKFlatIndependentCoefficients (R := R'))
    (fun P ↦ by
      obtain ⟨K, p, hK, _, hp, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R') P
      let : QuasiIso p := hp
      exact ⟨K, p, hK, inferInstance⟩)
    F.T CR.completion CS.completion CR.unit CS.unit ε.hom hunit



set_option backward.defeqAttrib.useBackward false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] Functor.mapHomologicalComplex DerivedCategory.Q in
/-- The specified completion exchanges compose with balanced scalar reassociation,
including their quotient units, actual Roos coordinates and normalized limit transport.

Source: Stacks Project, sites-cohomology.tex, Tag 0941, agent-formulated coefficient-tower
refinement, DAG proof steps 1--10
(blueprint: lem-pur-finite-free-completion-exchange-coherence).

Proof plan:
1. Resolve by an unbounded K-flat complex P using lem-pc-kflat-resolution.
lem-pur-derived-change-of-rings computes both extensions, and extension preserves
K-flatness by restriction of acyclic test complexes. Balanced scalar multiplication
and insertion of 1 give inverse chain associators and their natural derived descent.
2. Finite freeness makes scalar extension exact and identifies its product comparison
with the canonical map to finite tuples; rank zero gives the zero functor. Composed
bases show V is finite free over R. Only invertibility uses bases.
3. Use lem-pur-finite-free-completion-exchange to express each exchange as its actual
Roos tensor/product comparison followed by inverse arithmetic restriction.
4. The equal ideals a(t^n)S=(v^(en)) and b(v^m)V=(w^(fm)) identify the quotient maps.
Both balanced routes send ((rbar tensor s) tensor q) to (ba)(r)b(s)q modulo w^(efn).
Units affect the equality of ideals, never the residue formula or its transitions.
5. Project each tensor/product map to its nth factor. Naturality of the balanced
associator gives the same map; product universality proves equality on both signed
Roos coordinates. This yields RepresentativeComposition.coordinates.
6. Apply lem-pur-roos-additive-comparison: selection commutes with extension and the
weighted block map commutes because extension carries each finite sum and transition
to the corresponding one. This gives the arithmetic square for nonconstant rings.
7. Expanding the e blocks of length f gives the interval of length ef. Transition
composition and finite sum regrouping prove the arithmetic composition equation.
8. Multiply both derived routes by this specified arithmetic quasi-isomorphism.
Steps 5--7 identify them, and cancellation gives the displayed derived equation.
9. The quotient unit has coordinates (0, quotient family). Every preceding map
preserves these coordinates. All formulas commute with chain maps and descend
naturally along K-flat resolutions, so the equality holds for every Q in D(R).
10. lem-weil-strict-roos-comparison replaces each Roos vertex by its normalized
strict derived limit. Naturality moves these comparisons past the maps and the
intermediate inverse pairs cancel. The transport clause applies in particular to
these normalized identifications. No bound, completeness or perfectness is used. -/
theorem finiteFreeCompletionExchangeCoherence
    (Fa : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wS} a)
    (Fb : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wS, wV} b)
    (Fba : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wV} (a ≫ b))
    (_hfreeS : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map a)).obj
          (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ≅
        ∐ (fun _ : Fin d ↦ SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R))))
    (_hfreeV : ∃ d : ℕ, Nonempty
      ((SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map b)).obj
          (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J V)) ≅
        ∐ (fun _ : Fin d ↦ SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J S))))
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (vS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (w : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J V)).sections)
    (_ht : Mono (globalSectionMultiplication R t))
    (_hv : Mono (globalSectionMultiplication S vS))
    (_hw : Mono (globalSectionMultiplication V w))
    (uS : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)).sections)
    (z : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J V)).sections)
    (_hu : ∀ U : Cᵒᵖ, IsUnit (@id (S.obj.obj U) (uS.val U)))
    (_hz : ∀ U : Cᵒᵖ, IsUnit (@id (V.obj.obj U) (z.val U)))
    (e f : ℕ) (_he : 1 ≤ e) (_hf : 1 ≤ f)
    (_ha : ∀ U : Cᵒᵖ, a.hom.app U (@id (R.obj.obj U) (t.val U)) =
      (@id (S.obj.obj U) (uS.val U)) * (@id (S.obj.obj U) (vS.val U)) ^ e)
    (_hb : ∀ U : Cᵒᵖ, b.hom.app U (@id (S.obj.obj U) (vS.val U)) =
      (@id (V.obj.obj U) (z.val U)) * (@id (V.obj.obj U) (w.val U)) ^ f)
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J V))]
    [HasExactLimitsOfShape (Discrete ℕ) (Sheaf J AddCommGrpCat.{r})] :
    ∃ α : BalancedScalarAssociator Fa Fb Fba,
      ∀ (CR : Model R t) (CS : Model S vS) (CV : Model V w)
        (εa : CR.completion ⋙ Fa.T ≅ Fa.T ⋙ CS.completion)
        (εb : CS.completion ⋙ Fb.T ≅ Fb.T ⋙ CV.completion)
        (εba : CR.completion ⋙ Fba.T ≅ Fba.T ⋙ CV.completion),
      (∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        Nonempty (RepresentativeComparison Fa t vS e CR CS εa P)) →
      (∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := S) P →
        Nonempty (RepresentativeComparison Fb vS w f CS CV εb P)) →
      (∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        Nonempty (RepresentativeComparison Fba t w (e * f) CR CV εba P)) →
      (∀ Q, Fb.T.map (εa.hom.app Q) ≫ εb.hom.app (Fa.T.obj Q) ≫
        CV.completion.map (α.derived.hom.app Q) =
          α.derived.hom.app (CR.completion.obj Q) ≫ εba.hom.app Q) ∧
      (∀ Q, Fa.T.map (CR.unit.app Q) ≫ εa.hom.app Q = CS.unit.app (Fa.T.obj Q)) ∧
      (∀ Q, Fb.T.map (CS.unit.app Q) ≫ εb.hom.app Q = CV.unit.app (Fb.T.obj Q)) ∧
      (∀ Q, Fba.T.map (CR.unit.app Q) ≫ εba.hom.app Q = CV.unit.app (Fba.T.obj Q)) ∧
      (∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        ∃ (ra : RepresentativeComparison Fa t vS e CR CS εa P)
          (rb : RepresentativeComparison Fb vS w f CS CV εb ((extendedComplex Fa).obj P))
          (rba : RepresentativeComparison Fba t w (e * f) CR CV εba P),
          Nonempty (RepresentativeComposition α.ordinary
            (sourceTower t P) (targetTower Fa vS P)
            (targetTower Fb w ((extendedComplex Fa).obj P)) (targetTower Fba w P)
            ((quotientTower V w).map
              ((Functor.mapHomologicalComplexCompIso α.ordinary (.up ℤ)).hom.app P))
            e f _he ra.val rb.val rba.val)) ∧
      (∀ (D : DerivedCategory.{wV} (ringedSiteModules.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J V)) ⥤
          DerivedCategory.{wV} (ringedSiteModules.{r}
          (SheafOfModules.derivedChangeRingIndependentCoefficients J V)))
        (ρ : CV.completion ≅ D) Q,
        Fb.T.map (εa.hom.app Q) ≫ εb.hom.app (Fa.T.obj Q) ≫
          CV.completion.map (α.derived.hom.app Q) ≫ ρ.hom.app (Fba.T.obj Q) =
        α.derived.hom.app (CR.completion.obj Q) ≫ εba.hom.app Q ≫
          ρ.hom.app (Fba.T.obj Q)) := by
  classical
  let : PreservesFiniteLimits Fb.E :=
    (finiteFree_exact Fb _hfreeV vS w z _hz f _hf _hb).1
  let : PreservesFiniteColimits Fb.E :=
    (finiteFree_exact Fb _hfreeV vS w z _hz f _hf _hb).2
  obtain ⟨α, hc⟩ := exists_balancedScalarAssociator Fa Fb Fba
  refine ⟨α, ?_⟩
  intro CR CS CV εa εb εba hrepA hrepB hrepBA
  let κR : DerivedCategory.Q.{wR} ⋙ CR.completion ⟶
      ((quotientTower R t) ⋙ roosF) ⋙ DerivedCategory.Q.{wR} := by
    exact CR.counit
  let κS : DerivedCategory.Q.{wS} ⋙ CS.completion ⟶
      ((quotientTower S vS) ⋙ roosF) ⋙ DerivedCategory.Q.{wS} := by
    exact CS.counit
  let κV : DerivedCategory.Q.{wV} ⋙ CV.completion ⟶
      ((quotientTower V w) ⋙ roosF) ⋙ DerivedCategory.Q.{wV} := by
    exact CV.counit
  have hK := coherenceOfRepresentatives
    (A := ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
    (B := ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))
    (D := ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J V))
    (LA := DerivedCategory.{wR} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)))
    (LB := DerivedCategory.{wS} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)))
    (LD := DerivedCategory.{wV} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J V)))
    DerivedCategory.Q.{wR} DerivedCategory.Q.{wS} DerivedCategory.Q.{wV}
    Fa.E Fb.E Fba.E Fa.T Fb.T Fba.T Fa.ε Fb.ε Fba.ε
    (quotientTower R t) (quotientTower S vS) (quotientTower V w)
    CR.completion CS.completion CV.completion
    κR κS κV
    α.ordinary α.derived εa εb εba e f _he
    (CochainComplex.IsKFlatIndependentCoefficients (R := R))
    (fun P ↦ RepresentativeComparison Fa t vS e CR CS εa P)
    (fun P ↦ RepresentativeComparison Fb vS w f CS CV εb P)
    (fun P ↦ RepresentativeComparison Fba t w (e * f) CR CV εba P)
    (fun _ ra ↦ ra.val) (fun _ rb ↦ rb.val) (fun _ rba ↦ rba.val)
    (fun _ ra ↦ ra.property.2) (fun _ rb ↦ rb.property.2)
    (fun _ rba ↦ rba.property.2)
    hrepA (fun P hP ↦ hrepB _
      (SheafOfModules.changeOfRings_isKFlat_independentCoefficients a P
        Fa.E Fa.obj_eq Fa.map_eq hP)) hrepBA
    (fun P _ ra rb rba ↦ finiteFreeQuotientRoosHorizontalCoherence
      Fa Fb Fba α.ordinary α.balanced _hfreeV t vS w e f _he _hf P
      ra.val rb.val rba.val
      ra.property.1 rb.property.1 rba.property.1)
    (fun P hP ↦ Fba.computes P hP)
    (fun P hP ↦ CV.computes _
      (SheafOfModules.changeOfRings_isKFlat_independentCoefficients (a ≫ b) P
        Fba.E Fba.obj_eq Fba.map_eq hP))
    (scalarCounit_isIso Fb)
    (fun p hp ↦ (DerivedCategory.isIso_Q_map_iff_quasiIso.{wS} _ _).2 hp)
    (fun p hp ↦ (DerivedCategory.isIso_Q_map_iff_quasiIso.{wV} _ _).2 hp) hc
  -- Descend the equality from K-flat representatives.
  have hmain := exchangeCoherenceDescent
    (A₀ := CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
    (A := DerivedCategory.{wR} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)))
    (B := DerivedCategory.{wS} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S)))
    (D := DerivedCategory.{wV} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J V)))
    DerivedCategory.Q.{wR}
    (HomologicalComplex.quasiIso _ (.up ℤ))
    (CochainComplex.IsKFlatIndependentCoefficients (R := R))
    (fun P ↦ by
      obtain ⟨K, p, hK, _, hp, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
      let : QuasiIso p := hp
      exact ⟨K, p, hK, inferInstance⟩)
    Fa.T Fb.T Fba.T CR.completion CS.completion CV.completion
    α.derived.hom εa.hom εb.hom εba.hom (fun P hP ↦ (hK P hP).1)
  refine ⟨hmain, representativeExchange_unit Fa t vS e CR CS εa hrepA,
    representativeExchange_unit Fb vS w f CS CV εb hrepB,
    representativeExchange_unit Fba t w (e * f) CR CV εba hrepBA, ?_, ?_⟩
  · intro P hP
    exact (hK P hP).2
  · intro D ρ Q
    simpa only [Category.assoc] using
      congrArg (· ≫ ρ.hom.app (Fba.T.obj Q)) (hmain Q)



end compositionProof

open SheafOfModules

attribute [local irreducible] roosχ quotientMap quotientProduct

private theorem unit_normalization_all
    {A : Type xA} [Category.{yA} A] {B : Type xB} [Category.{yB} B]
    (Q : A ⥤ B) (E : A ⥤ A) (T : B ⥤ B)
    (η : Q ⋙ T ⟶ E ⋙ Q) (c : E ⟶ 𝟭 A) (d : T ⟶ 𝟭 B)
    (good : A → Prop)
    (hres : ∀ P, ∃ (K : A) (p : K ⟶ P), good K ∧ IsIso (Q.map p))
    (h : ∀ P, good P → d.app (Q.obj P) = η.app P ≫ Q.map (c.app P)) :
    ∀ P, d.app (Q.obj P) = η.app P ≫ Q.map (c.app P) := by
  let γ : Q ⋙ T ⟶ Q := Functor.whiskerLeft Q d ≫ (Functor.rightUnitor Q).hom
  let δ : Q ⋙ T ⟶ Q :=
    η ≫ Functor.whiskerRight c Q ≫ (Functor.leftUnitor Q).hom
  have he : γ = δ := natTrans_eq_on_resolving good (fun P ↦ by
    obtain ⟨K, p, hK, hp⟩ := hres P
    let : IsIso (Q.map p) := hp
    refine ⟨K, p, hK, ?_⟩
    change IsIso (T.map (Q.map p))
    infer_instance) γ δ (by
      intro P hP
      change d.app (Q.obj P) ≫ 𝟙 _ = η.app P ≫ Q.map (c.app P) ≫ 𝟙 _
      simpa only [Category.comp_id] using h P hP)
  intro P
  have hh := NatTrans.congr_app he P
  change d.app (Q.obj P) ≫ 𝟙 _ = η.app P ≫ Q.map (c.app P) ≫ 𝟙 _ at hh
  simpa only [Category.comp_id] using hh

private theorem exists_balancedScalarUnit
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wR} (𝟙 R)) :
    ∃ ι : BalancedScalarUnit F, ∀ P,
      let c := NatIso.mapHomologicalComplex ι.ordinary (.up ℤ) ≪≫
        Functor.mapHomologicalComplexIdIso _ _
      ι.derived.hom.app (DerivedCategory.Q.obj P) = F.ε.app P ≫
        DerivedCategory.Q.map (c.hom.app P) := by
  classical
  obtain ⟨ordinary, hord, derived, hderived, _⟩ := RingedKFlatWord.scalar_unit F
  let good (P : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R)) ℤ) :=
    P.IsKFlatIndependentCoefficients ∧ ∀ n : ℤ, IsFlatOnSite (R := R) (P.X n)
  have hres (P) : ∃ (K : CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R)) ℤ) (p : K ⟶ P),
      good K ∧ IsIso (DerivedCategory.Q.{wR}.map p) := by
    obtain ⟨K, p, hk, hf, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
    let : QuasiIso p := hp
    exact ⟨K, p, ⟨hk, fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso R (K.X n)).symm (hf n)⟩, inferInstance⟩
  let c : extendedComplex F ≅ 𝟭 _ := NatIso.mapHomologicalComplex ordinary (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ _
  have hc := unit_normalization_all
    (A := CochainComplex (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R)) ℤ)
    (B := DerivedCategory.{wR} (ringedSiteModules.{r}
      (derivedChangeRingIndependentCoefficients J R)))
    DerivedCategory.Q (extendedComplex F) F.T F.ε
    c.hom derived.hom good hres (fun P hP ↦ by
      rw [hderived P hP.1 hP.2]
      apply congrArg (fun f ↦ F.ε.app P ≫ DerivedCategory.Q.map f)
      ext i : 1
      simp only [c, Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
        Functor.mapHomologicalComplexIdIso_hom_app_f]
      erw [Category.comp_id])
  refine ⟨⟨ordinary, hord, derived, ?_⟩, hc⟩
  intro P _
  rw [hc P]
  apply congrArg (fun f ↦ F.ε.app P ≫ DerivedCategory.Q.map f)
  ext i : 1
  simp only [c, Iso.trans_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexIdIso_hom_app_f]
  erw [Category.comp_id]


set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem identityExchangeSquare
    {A B : Type*} [Category A] [Category B]
    (Q : A ⥤ B) (E H : A ⥤ A) (T C : B ⥤ B)
    (η : Q ⋙ T ⟶ E ⋙ Q) (κ : Q ⋙ C ⟶ H ⋙ Q)
    (c : E ≅ 𝟭 A) (ι : T ≅ 𝟭 B) (ε : C ⋙ T ⟶ T ⋙ C)
    (hc : ∀ P, ι.hom.app (Q.obj P) = η.app P ≫ Q.map (c.hom.app P))
    (P : A) {I : A} (δ : E.obj (H.obj P) ⟶ I) (ar : H.obj (E.obj P) ⟶ I)
    (hκ : IsIso (κ.app (E.obj P))) (har : IsIso (Q.map ar))
    (hd : δ = c.hom.app (H.obj P) ≫ H.map (c.inv.app P) ≫ ar)
    (hr : ε.app (Q.obj P) ≫ C.map (η.app P) ≫ κ.app (E.obj P) ≫ Q.map ar =
      T.map (κ.app P) ≫ η.app (H.obj P) ≫ Q.map δ) :
    ε.app (Q.obj P) ≫ C.map (ι.hom.app (Q.obj P)) = ι.hom.app (C.obj (Q.obj P)) := by
  let : IsIso (κ.app (E.obj P)) := hκ
  let : IsIso (Q.map ar) := har
  let B := C.map (Q.map (c.inv.app P)) ≫ κ.app (E.obj P) ≫ Q.map ar
  apply (cancel_mono B).1
  have hcancel : C.map (ι.hom.app (Q.obj P)) ≫ C.map (Q.map (c.inv.app P)) =
      C.map (η.app P) := by
    rw [← C.map_comp, hc, Category.assoc, ← Q.map_comp, c.hom_inv_id_app, Q.map_id]
    exact congrArg C.map (Category.comp_id (η.app P))
  have hn : C.map (Q.map (c.inv.app P)) ≫ κ.app (E.obj P) =
      κ.app P ≫ Q.map (H.map (c.inv.app P)) := κ.naturality (c.inv.app P)
  change (ε.app (Q.obj P) ≫ C.map (ι.hom.app (Q.obj P))) ≫ B =
    ι.hom.app (C.obj (Q.obj P)) ≫ B
  calc
    _ = T.map (κ.app P) ≫ η.app (H.obj P) ≫ Q.map δ := by
      simpa only [B, Category.assoc, reassoc_of% hcancel] using hr
    _ = T.map (κ.app P) ≫ ι.hom.app (Q.obj (H.obj P)) ≫
        Q.map (H.map (c.inv.app P)) ≫ Q.map ar := by
      rw [hd, Q.map_comp, Q.map_comp, hc]
      simp only [Category.assoc]
    _ = ι.hom.app (C.obj (Q.obj P)) ≫ κ.app P ≫
        Q.map (H.map (c.inv.app P)) ≫ Q.map ar := by
      have hnι : T.map (κ.app P) ≫ ι.hom.app (Q.obj (H.obj P)) =
          ι.hom.app (C.obj (Q.obj P)) ≫ κ.app P := ι.hom.naturality _
      simpa only [Category.assoc] using
        congrArg (· ≫ Q.map (H.map (c.inv.app P)) ≫ Q.map ar) hnι
    _ = _ := by
      dsimp only [B]
      rw [← Category.assoc (C.map (Q.map (c.inv.app P))), hn]
      simp only [Category.assoc]

private theorem identityUnitSquare
    {A : Type*} [Category A] (T C : A ⥤ A) (ι : T ≅ 𝟭 A)
    (u : 𝟭 A ⟶ C) (ε : C ⋙ T ⟶ T ⋙ C)
    (h : ∀ X, ε.app X ≫ C.map (ι.hom.app X) = ι.hom.app (C.obj X)) :
    ∀ X, T.map (u.app X) ≫ ε.app X = u.app (T.obj X) := by
  intro X
  apply (cancel_mono (C.map (ι.hom.app X))).1
  simp only [Category.assoc]
  rw [h, ι.hom.naturality]
  simpa only [Functor.id_map, Functor.id_obj] using u.naturality (ι.hom.app X)

private theorem identityCoherenceFromCochains
    {A B : Type*} [Category A] [Category B]
    (Q : A ⥤ B) (W : MorphismProperty A) [Q.IsLocalization W]
    (good : A → Prop)
    (hres : ∀ P, ∃ (K : A) (p : K ⟶ P), good K ∧ IsIso (Q.map p))
    (E H : A ⥤ A) (T C : B ⥤ B)
    (η : Q ⋙ T ⟶ E ⋙ Q) (κ : Q ⋙ C ⟶ H ⋙ Q)
    (c : E ≅ 𝟭 A) (ι : T ≅ 𝟭 B) (ε : C ⋙ T ⟶ T ⋙ C)
    (u : 𝟭 B ⟶ C)
    (hc : ∀ P, ι.hom.app (Q.obj P) = η.app P ≫ Q.map (c.hom.app P))
    (hdata : ∀ P, good P → ∃ (I : A)
      (δ : E.obj (H.obj P) ⟶ I) (ar : H.obj (E.obj P) ⟶ I),
      IsIso (κ.app (E.obj P)) ∧ IsIso (Q.map ar) ∧
      δ = c.hom.app (H.obj P) ≫ H.map (c.inv.app P) ≫ ar ∧
      ε.app (Q.obj P) ≫ C.map (η.app P) ≫ κ.app (E.obj P) ≫ Q.map ar =
        T.map (κ.app P) ≫ η.app (H.obj P) ≫ Q.map δ) :
    (∀ X, ε.app X ≫ C.map (ι.hom.app X) = ι.hom.app (C.obj X)) ∧
    (∀ X, T.map (u.app X) ≫ ε.app X = u.app (T.obj X)) := by
  have hh : ∀ X, ε.app X ≫ C.map (ι.hom.app X) = ι.hom.app (C.obj X) := by
    let γ : C ⋙ T ⟶ C := ε ≫ Functor.whiskerRight ι.hom C
    let δ : C ⋙ T ⟶ C := Functor.whiskerLeft C ι.hom
    have he : γ = δ := natTrans_eq_of_resolutions Q W good hres γ δ (by
      intro P hP
      obtain ⟨I, d, ar, hκ, har, hd, hr⟩ := hdata P hP
      exact identityExchangeSquare Q E H T C η κ c ι ε hc P d ar hκ har hd hr)
    intro X
    exact NatTrans.congr_app he X
  exact ⟨hh, identityUnitSquare T C ι u ε hh⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [local irreducible] Functor.mapHomologicalComplex DerivedCategory.Q in
/-- For identity coefficients and exponent one the specified exchange is identity
under scalar multiplication; its quotient augmentation is the same strict quotient unit.

Source: Stacks 03EK, 0941 and 0H9K, DAG proof steps 7 and 9
(blueprint: lem-pur-finite-free-completion-exchange-coherence).

Proof: Multiplication s tensor x to sx and x to 1 tensor x give inverse ordinary
identity-extension maps; they commute with all module maps and differentials.
K-flat computation descends them to the normalized derived unit. The canonical
product comparison and quotient maps become identities under multiplication.
For exponent one selection is identity and each weighted block has the single
identity-transition term. Thus both actual Roos coordinates of the exchange are
identity. Its quotient augmentation is (0, quotient family), so the unit equation
also holds. Localizing and using the normalized strict-Roos comparison preserves
these equations. This works for all unbounded Q and includes zero rings. -/
theorem finiteFreeCompletionExchangeIdentity
    (F : SheafOfModules.DerivedChangeOfRingsCochainModel.{u, v, r, wR, wR} (𝟙 R))
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (_ht : Mono (globalSectionMultiplication R t))
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasExactLimitsOfShape (Discrete ℕ) (Sheaf J AddCommGrpCat.{r})] :
    ∃ ι : BalancedScalarUnit F, ∀ (CR : Model R t)
      (ε : CR.completion ⋙ F.T ≅ F.T ⋙ CR.completion),
      (∀ P, CochainComplex.IsKFlatIndependentCoefficients (R := R) P →
        Nonempty (RepresentativeComparison F t t 1 CR CR ε P)) →
      (∀ Q, ε.hom.app Q ≫ CR.completion.map (ι.derived.hom.app Q) =
        ι.derived.hom.app (CR.completion.obj Q)) ∧
      (∀ Q, F.T.map (CR.unit.app Q) ≫ ε.hom.app Q = CR.unit.app (F.T.obj Q)) := by
  classical
  obtain ⟨ι, hι⟩ := exists_balancedScalarUnit F
  refine ⟨ι, ?_⟩
  intro CR ε hrep
  let c : extendedComplex F ≅ 𝟭 _ :=
    NatIso.mapHomologicalComplex ι.ordinary (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ _
  apply identityCoherenceFromCochains
    (A := CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
    (B := DerivedCategory.{wR} (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)))
    DerivedCategory.Q.{wR}
    (HomologicalComplex.quasiIso _ (.up ℤ))
    (CochainComplex.IsKFlatIndependentCoefficients (R := R))
    (fun P ↦ by
      obtain ⟨K, p, hK, _, hp, _⟩ :=
        CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := R) P
      let : QuasiIso p := hp
      exact ⟨K, p, hK, inferInstance⟩)
    (extendedComplex F) (quotientRoos R t) F.T CR.completion F.ε CR.counit
    c ι.derived ε.hom CR.unit hι
  intro P hP
  obtain ⟨rd⟩ := hrep P hP
  let d := rd.val
  have hq := rd.property.1
  have hd := rd.property.2
  have hδ := identityQuotientRoosNormalization F ι.ordinary t P d hq
  refine ⟨roosF.obj ((complexRestriction _ 1).obj (targetTower F t P)),
    ?_, ?_, ?_⟩
  · exact d.δ.hom
  · exact d.a
  · exact ⟨CR.computes _ (SheafOfModules.changeOfRings_isKFlat_independentCoefficients
      (𝟙 R) P F.E F.obj_eq F.map_eq hP),
    (DerivedCategory.isIso_Q_map_iff_quasiIso.{wR} _ _).2 d.arithmetic_quasiIso,
      hδ, hd⟩

end CategoryTheory.PrincipalQuotientCompletion

-- Keep normalized representatives in the original public API.
