module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.FiniteFreeCompletionExchangeCoherence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Localization.Predicate
import Sheaf.CategoryTheory.LocalizationLeftDerivedComparison
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients

/-! # Counit-normalized transport of scalar and sections coherence

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 0G7E, 06YY, 0D6D;
categories.tex, Tag 04VG; DAG proof steps 1--9
(blueprint: lem-weil-sections-scalar-derived-transport).

The five coherence equations use the same record before and after localization.
The scalar functors are the recorded sheafified extension and ordinary module extension.
Pure-tensor equations specify the ordinary associators and action units. All comparison
isomorphisms retain the specified universal cochain counits, on every representative.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe x y p q u v r dS dA
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace CategoryTheory.SectionsScalarTransport

private theorem preimageIso_app
    {B : Type*} [Category B] {D : Type*} [Category D]
    {E : Type*} [Category E] (Q : B ⥤ D) (W : MorphismProperty B)
    [Q.IsLocalization W] {F H : D ⥤ E} (e : Q ⋙ F ≅ Q ⋙ H) (P : B) :
    ((Localization.fullyFaithfulWhiskeringLeft Q W E).preimageIso e).hom.app
      (Q.obj P) = e.hom.app P :=
  congr_app ((Localization.fullyFaithfulWhiskeringLeft Q W E).map_preimage e.hom) P

private theorem preimageIso_fac
    {B : Type*} [Category B] {D : Type*} [Category D]
    {E : Type*} [Category E] (Q : B ⥤ D) (W : MorphismProperty B)
    [Q.IsLocalization W] {F H : D ⥤ E} {U V : B ⥤ E}
    (eF : Q ⋙ F ≅ U) (eH : Q ⋙ H ≅ V) (e : U ≅ V) (P : B) :
    ((Localization.fullyFaithfulWhiskeringLeft Q W E).preimageIso
      (eF ≪≫ e ≪≫ eH.symm)).hom.app (Q.obj P) ≫ eH.hom.app P =
        eF.hom.app P ≫ e.hom.app P := by
  rw [preimageIso_app]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id]

private def compComparison
    {B₀ B₁ B₂ D₀ D₁ D₂ : Type*}
    [Category B₀] [Category B₁] [Category B₂]
    [Category D₀] [Category D₁] [Category D₂]
    {Q₀ : B₀ ⥤ D₀} {Q₁ : B₁ ⥤ D₁} {Q₂ : B₂ ⥤ D₂}
    {F : B₀ ⥤ B₁} {H : B₁ ⥤ B₂} {Fd : D₀ ⥤ D₁} {Hd : D₁ ⥤ D₂}
    (s : Q₀ ⋙ Fd ≅ F ⋙ Q₁) (t : Q₁ ⋙ Hd ≅ H ⋙ Q₂) :
    Q₀ ⋙ (Fd ⋙ Hd) ≅ (F ⋙ H) ⋙ Q₂ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight s _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ t ≪≫ (Functor.associator _ _ _).symm

private theorem compComparison_hom
    {B₀ B₁ B₂ D₀ D₁ D₂ : Type*}
    [Category B₀] [Category B₁] [Category B₂]
    [Category D₀] [Category D₁] [Category D₂]
    {Q₀ : B₀ ⥤ D₀} {Q₁ : B₁ ⥤ D₁} {Q₂ : B₂ ⥤ D₂}
    {F : B₀ ⥤ B₁} {H : B₁ ⥤ B₂} {Fd : D₀ ⥤ D₁} {Hd : D₁ ⥤ D₂}
    (s : Q₀ ⋙ Fd ≅ F ⋙ Q₁) (t : Q₁ ⋙ Hd ≅ H ⋙ Q₂) (P : B₀) :
    (compComparison s t).hom.app P = Hd.map (s.hom.app P) ≫ t.hom.app (F.obj P) := by
  simp only [compComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]

private theorem unitComparison_hom
    {B D : Type*} [Category B] [Category D] {Q : B ⥤ D}
    {F : D ⥤ D} {U : B ⥤ B} (s : Q ⋙ F ≅ U ⋙ Q) (m : U ≅ 𝟭 B) (P : B) :
    (s ≪≫ Functor.isoWhiskerRight m Q ≪≫ Functor.leftUnitor Q ≪≫
      (Functor.rightUnitor Q).symm).hom.app P =
        s.hom.app P ≫ Q.map (m.hom.app P) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Category.comp_id]
  exact congrArg (fun z ↦ s.hom.app P ≫ z) (Category.comp_id (Q.map (m.hom.app P)))

private theorem compComparison_inv
    {B₀ B₁ B₂ D₀ D₁ D₂ : Type*}
    [Category B₀] [Category B₁] [Category B₂]
    [Category D₀] [Category D₁] [Category D₂]
    {Q₀ : B₀ ⥤ D₀} {Q₁ : B₁ ⥤ D₁} {Q₂ : B₂ ⥤ D₂}
    {F : B₀ ⥤ B₁} {H : B₁ ⥤ B₂} {Fd : D₀ ⥤ D₁} {Hd : D₁ ⥤ D₂}
    (s : Q₀ ⋙ Fd ≅ F ⋙ Q₁) (t : Q₁ ⋙ Hd ≅ H ⋙ Q₂) (P : B₀) :
    (compComparison s t).inv.app P = t.inv.app (F.obj P) ≫ Hd.map (s.inv.app P) := by
  simp only [compComparison, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]

private theorem inverse_rep
    {D : Type*} [Category D] {X Y A B : D}
    (e : X ≅ Y) (s : X ≅ A) (t : Y ≅ B) (u : A ≅ B)
    (h : e.hom ≫ t.hom = s.hom ≫ u.hom) :
    e.inv ≫ s.hom = t.hom ≫ u.inv := by
  apply (cancel_epi e.hom).1
  rw [e.hom_inv_id_assoc, ← Category.assoc, h, Category.assoc, u.hom_inv_id,
    Category.comp_id]

private theorem transport_four
    {B : Fin 4 → Type x} {D : Fin 4 → Type y}
    [∀ i, Category.{p} (B i)] [∀ i, Category.{q} (D i)]
    (Q : ∀ i, B i ⥤ D i) (W : MorphismProperty (B 0)) [(Q 0).IsLocalization W]
    (F : ∀ i j : Fin 4, i ≤ j → B i ⥤ B j)
    (Fd : ∀ i j : Fin 4, i ≤ j → D i ⥤ D j)
    (s : ∀ i j h, Q i ⋙ Fd i j h ≅ F i j h ⋙ Q j)
    (u : ∀ i j k (h : i ≤ j) (h' : j ≤ k), F i j h ⋙ F j k h' ≅ F i k (h.trans h'))
    (ud : ∀ i j k (h : i ≤ j) (h' : j ≤ k),
      Fd i j h ⋙ Fd j k h' ≅ Fd i k (h.trans h'))
    (rep : ∀ i j k h h' P,
      (ud i j k h h').hom.app ((Q i).obj P) ≫ (s i k (h.trans h')).hom.app P =
        (Fd j k h').map ((s i j h).hom.app P) ≫
          (s j k h').hom.app ((F i j h).obj P) ≫ (Q k).map ((u i j k h h').hom.app P))
    (four : ∀ P, (F 2 3 (by decide)).map ((u 0 1 2 (by decide) (by decide)).hom.app P) ≫
      (u 0 2 3 (by decide) (by decide)).hom.app P =
      (u 1 2 3 (by decide) (by decide)).hom.app ((F 0 1 (by decide)).obj P) ≫
        (u 0 1 3 (by decide) (by decide)).hom.app P) (X : D 0) :
    (Fd 2 3 (by decide)).map ((ud 0 1 2 (by decide) (by decide)).hom.app X) ≫
      (ud 0 2 3 (by decide) (by decide)).hom.app X =
      (ud 1 2 3 (by decide) (by decide)).hom.app ((Fd 0 1 (by decide)).obj X) ≫
        (ud 0 1 3 (by decide) (by decide)).hom.app X := by
  let l : (Fd 0 1 (by decide) ⋙ Fd 1 2 (by decide)) ⋙ Fd 2 3 (by decide) ⟶
      Fd 0 3 (by decide) :=
    Functor.whiskerRight (ud 0 1 2 (by decide) (by decide)).hom _ ≫
      (ud 0 2 3 (by decide) (by decide)).hom
  let r : (Fd 0 1 (by decide) ⋙ Fd 1 2 (by decide)) ⋙ Fd 2 3 (by decide) ⟶
      Fd 0 3 (by decide) :=
    Functor.whiskerLeft (Fd 0 1 (by decide)) (ud 1 2 3 (by decide) (by decide)).hom ≫
      (ud 0 1 3 (by decide) (by decide)).hom
  change l.app X = r.app X
  apply congr_app (Localization.natTrans_ext (Q 0) W (τ := l) (τ' := r) ?_) X
  intro P
  change (Fd 2 3 _).map ((ud 0 1 2 _ _).hom.app ((Q 0).obj P)) ≫
      (ud 0 2 3 _ _).hom.app ((Q 0).obj P) =
    (ud 1 2 3 _ _).hom.app ((Fd 0 1 _).obj ((Q 0).obj P)) ≫
      (ud 0 1 3 _ _).hom.app ((Q 0).obj P)
  apply (cancel_mono ((s 0 3 (by decide)).hom.app P)).1
  simp only [Category.assoc]
  rw [rep, rep, ← (Fd 2 3 (by decide)).map_comp_assoc, rep]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (s 2 3 (by decide)).hom.naturality
    ((u 0 1 2 (by decide) (by decide)).hom.app P)
  have hn' := (ud 1 2 3 (by decide) (by decide)).hom.naturality
    ((s 0 1 (by decide)).hom.app P)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hn'
  rw [reassoc_of% hn, ← reassoc_of% hn',
    reassoc_of% (rep 1 2 3 (by decide) (by decide) ((F 0 1 (by decide)).obj P))]
  simp only [← (Q 3).map_comp]
  rw [four]

/-- The five stipulated equations, including identity stages and the full four-stage
comparison. Composition is written in diagrammatic order.
Source: Stacks 04VG, finite-pasting argument, DAG steps 6--8
(blueprint: lem-weil-sections-scalar-derived-transport). -/
structure Coherent
    {V : Fin 4 → Type x} {W : Fin 4 → Type y}
    [∀ i, Category.{p} (V i)] [∀ i, Category.{q} (W i)]
    (T : ∀ i j : Fin 4, i ≤ j → V i ⥤ V j)
    (t : ∀ i j : Fin 4, i ≤ j → W i ⥤ W j)
    (G : ∀ i : Fin 4, V i ⥤ W i)
    (u : ∀ i j k (h : i ≤ j) (h' : j ≤ k), T i j h ⋙ T j k h' ≅ T i k (h.trans h'))
    (a : ∀ i j k (h : i ≤ j) (h' : j ≤ k), t i j h ⋙ t j k h' ≅ t i k (h.trans h'))
    (m : ∀ i, T i i le_rfl ≅ 𝟭 (V i))
    (μ : ∀ i, t i i le_rfl ≅ 𝟭 (W i))
    (θ : ∀ i j h, G i ⋙ t i j h ≅ T i j h ⋙ G j) : Prop where
  triple : ∀ i j k (h : i ≤ j) (h' : j ≤ k) (X : V i),
    (t j k h').map ((θ i j h).hom.app X) ≫
        (θ j k h').hom.app ((T i j h).obj X) ≫ (G k).map ((u i j k h h').hom.app X) =
      (a i j k h h').hom.app ((G i).obj X) ≫ (θ i k (h.trans h')).hom.app X
  unit : ∀ i (X : V i),
    (θ i i le_rfl).hom.app X ≫ (G i).map ((m i).hom.app X) =
      (μ i).hom.app ((G i).obj X)
  sheaf_four : ∀ X : V 0,
    (T 2 3 (by decide)).map ((u 0 1 2 (by decide) (by decide)).hom.app X) ≫
        (u 0 2 3 (by decide) (by decide)).hom.app X =
      (u 1 2 3 (by decide) (by decide)).hom.app ((T 0 1 (by decide)).obj X) ≫
        (u 0 1 3 (by decide) (by decide)).hom.app X
  module_four : ∀ X : W 0,
    (t 2 3 (by decide)).map ((a 0 1 2 (by decide) (by decide)).hom.app X) ≫
        (a 0 2 3 (by decide) (by decide)).hom.app X =
      (a 1 2 3 (by decide) (by decide)).hom.app ((t 0 1 (by decide)).obj X) ≫
        (a 0 1 3 (by decide) (by decide)).hom.app X
  iterated : ∀ X : V 0,
    (t 2 3 (by decide)).map ((t 1 2 (by decide)).map
        ((θ 0 1 (by decide)).hom.app X)) ≫
      (t 2 3 (by decide)).map ((θ 1 2 (by decide)).hom.app ((T 0 1 (by decide)).obj X)) ≫
      (θ 2 3 (by decide)).hom.app
        ((T 1 2 (by decide)).obj ((T 0 1 (by decide)).obj X)) ≫
      (G 3).map ((T 2 3 (by decide)).map
        ((u 0 1 2 (by decide) (by decide)).hom.app X) ≫
        (u 0 2 3 (by decide) (by decide)).hom.app X) =
      (t 2 3 (by decide)).map
        ((a 0 1 2 (by decide) (by decide)).hom.app ((G 0).obj X)) ≫
      (a 0 2 3 (by decide) (by decide)).hom.app ((G 0).obj X) ≫
      (θ 0 3 (by decide)).hom.app X

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasSheafify J AddCommGrpCat.{r}]
  (R : Fin 4 ⥤ Sheaf J CommRingCat.{r}) (A : Fin 4 ⥤ CommRingCat.{r})
  [∀ i, HasDerivedCategory.{dS}
    (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J (R.obj i)))]
  [∀ i, HasDerivedCategory.{dA} (ModuleCat.{r} (A.obj i))]
  (M : ∀ i j (h : i ≤ j),
    SheafOfModules.DerivedChangeOfRingsCochainModel (R.map (homOfLE h)))
  (G : ∀ i, ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J (R.obj i)) ⥤
      ModuleCat.{r} (A.obj i))
  [∀ i, (G i).Additive]

/-- Termwise application of the specified ordinary sheaf scalar functor.
Source: Stacks 06YY (blueprint: lem-weil-sections-scalar-derived-transport). -/
def T (i j : Fin 4) (h : i ≤ j) :=
  (M i j h).E.mapHomologicalComplex (.up ℤ)

/-- Termwise ordinary module scalar extension, with its actual coefficient map.
Source: Stacks 06YY (blueprint: lem-weil-sections-scalar-derived-transport). -/
def t (i j : Fin 4) (h : i ≤ j) :=
  (ModuleCat.extendScalars.{r, r, r} (A.map (homOfLE h)).hom).mapHomologicalComplex (.up ℤ)

/-- The termwise additive sections functors; K-flat preservation is not required.
Source: Stacks 04VG (blueprint: lem-weil-sections-scalar-derived-transport). -/
def g (i : Fin 4) := (G i).mapHomologicalComplex (.up ℤ)

variable
  (u₀ : ∀ i j k (h : i ≤ j) (h' : j ≤ k), T R M i j h ⋙ T R M j k h' ≅
    T R M i k (h.trans h'))
  (a₀ : ∀ i j k (h : i ≤ j) (h' : j ≤ k), t A i j h ⋙ t A j k h' ≅
    t A i k (h.trans h'))
  (m₀ : ∀ i, T R M i i le_rfl ≅ 𝟭 _)
  (μ₀ : ∀ i, t A i i le_rfl ≅ 𝟭 _)
  (θ₀ : ∀ i j h, g R A G i ⋙ t A i j h ≅ T R M i j h ⋙ g R A G j)

/-- Precisely the scalar normalizations and exactness assumptions of the node.
The pure-tensor equations characterize sheaf maps after sheafification; they do not
assert that every section of a sheaf tensor product is globally a pure tensor.
Source: Stacks 03EK, 06YY, 04VG, DAG steps 1, 3, 4
(blueprint: lem-weil-sections-scalar-derived-transport). -/
structure ChainHypotheses : Prop where
  sheaf_quasiIso : ∀ i j h {P Q} (f : P ⟶ Q), QuasiIso f →
    QuasiIso ((T R M i j h).map f)
  module_quasiIso : ∀ i j h {P Q} (f : P ⟶ Q), QuasiIso f →
    QuasiIso ((t A i j h).map f)
  sections_quasiIso : ∀ i {P Q} (f : P ⟶ Q), QuasiIso f →
    QuasiIso ((g R A G i).map f)
  sheaf_associator : ∀ i j k h h' P n U (s : (R.obj j).obj.obj U)
    (b : (R.obj k).obj.obj U) (x : (P.X n).val.obj U),
    (((u₀ i j k h h').hom.app P).f n).val.app U
      (PrincipalQuotientCompletion.scalarTensorSection (M j k h')
        ((M i j h).E.obj (P.X n)) U b
          (PrincipalQuotientCompletion.scalarTensorSection (M i j h) (P.X n) U s x)) =
      PrincipalQuotientCompletion.scalarTensorSection (M i k (h.trans h')) (P.X n) U
        ((R.map (homOfLE h')).hom.app U s * b) x
  module_associator : ∀ i j k h h' P n (s : A.obj j) (b : A.obj k) (x : (P.X n : Type r)),
    ((a₀ i j k h h').hom.app P).f n
      (b ⊗ₜ[A.obj j, (A.map (homOfLE h')).hom]
        (s ⊗ₜ[A.obj i, (A.map (homOfLE h)).hom] x)) =
      @id (((t A i k (h.trans h')).obj P).X n : Type r)
        (((A.map (homOfLE h')).hom s * b) ⊗ₜ[A.obj i,
          (A.map (homOfLE (h.trans h'))).hom] x)
  sheaf_unit : ∀ i P n U (s : (R.obj i).obj.obj U) (x : (P.X n).val.obj U),
    (((m₀ i).hom.app P).f n).val.app U
      (PrincipalQuotientCompletion.scalarTensorSection (M i i le_rfl) (P.X n) U s x) = s • x
  module_unit : ∀ i P n (s : A.obj i) (x : (P.X n : Type r)),
    ((μ₀ i).hom.app P).f n
      (@id (((t A i i le_rfl).obj P).X n : Type r)
        (@TensorProduct.tmul (A.obj i) _ (A.obj i : Type r) (P.X n : Type r) _ _
          ((ModuleCat.restrictScalars (A.map (homOfLE le_rfl)).hom).obj
            (ModuleCat.of (A.obj i) (A.obj i))).isModule (P.X n).isModule s x)) =
      @SMul.smul (A.obj i) (P.X n : Type r) (P.X n).isModule.toSMul s x
  coherent : Coherent (T R M) (t A) (g R A G) u₀ a₀ m₀ μ₀ θ₀

set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false

/-- A complete descended diagram, retaining all representative comparisons.
These are the specified localizations up to their unique factorization isomorphisms.
Source: Stacks 04VG, 06YY and 0D6D; DAG steps 1--8
(blueprint: lem-weil-sections-scalar-derived-transport). -/
structure DerivedTransport where
  barT : ∀ i j (_h : i ≤ j), DerivedCategory (ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J (R.obj i))) ⥤
      DerivedCategory (ringedSiteModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J (R.obj j)))
  td : ∀ i j (_h : i ≤ j), DerivedCategory (ModuleCat.{r} (A.obj i)) ⥤
    DerivedCategory (ModuleCat.{r} (A.obj j))
  gd : ∀ i, DerivedCategory (ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J (R.obj i))) ⥤
      DerivedCategory (ModuleCat.{r} (A.obj i))
  beta : ∀ i j h, DerivedCategory.Q ⋙ barT i j h ≅ T R M i j h ⋙ DerivedCategory.Q
  delta : ∀ i j h, DerivedCategory.Q ⋙ td i j h ≅ t A i j h ⋙ DerivedCategory.Q
  gamma : ∀ i, DerivedCategory.Q ⋙ gd i ≅ g R A G i ⋙ DerivedCategory.Q
  c : ∀ i j h, (M i j h).T ≅ barT i j h
  counit : ∀ i j h P,
    (c i j h).hom.app (DerivedCategory.Q.obj P) ≫ (beta i j h).hom.app P =
      (M i j h).ε.app P
  c_unique : ∀ i j h (c' : (M i j h).T ⟶ barT i j h),
    (∀ P, c'.app (DerivedCategory.Q.obj P) ≫ (beta i j h).hom.app P =
      (M i j h).ε.app P) → c' = (c i j h).hom
  sigma : ∀ i j h, DerivedCategory.Q ⋙ (M i j h).T ≅ T R M i j h ⋙ DerivedCategory.Q
  sigma_counit : ∀ i j h, (sigma i j h).hom = (M i j h).ε
  alpha : ∀ i j k h h', (M i j h).T ⋙ (M j k h').T ≅ (M i k (h.trans h')).T
  ad : ∀ i j k h h', td i j h ⋙ td j k h' ≅ td i k (h.trans h')
  md : ∀ i, (M i i le_rfl).T ≅ 𝟭 _
  mud : ∀ i, td i i le_rfl ≅ 𝟭 _
  theta : ∀ i j h, gd i ⋙ td i j h ≅ (M i j h).T ⋙ gd j
  alpha_rep : ∀ i j k h h' P,
    (alpha i j k h h').hom.app (DerivedCategory.Q.obj P) ≫
        (sigma i k (h.trans h')).hom.app P =
      (M j k h').T.map ((sigma i j h).hom.app P) ≫
        (sigma j k h').hom.app ((T R M i j h).obj P) ≫
        DerivedCategory.Q.map ((u₀ i j k h h').hom.app P)
  alpha_inv_rep : ∀ i j k h h' P,
    (alpha i j k h h').inv.app (DerivedCategory.Q.obj P) ≫
        (M j k h').T.map ((sigma i j h).hom.app P) ≫
        (sigma j k h').hom.app ((T R M i j h).obj P) =
      (sigma i k (h.trans h')).hom.app P ≫
        DerivedCategory.Q.map ((u₀ i j k h h').inv.app P)
  a_rep : ∀ i j k h h' P,
    (ad i j k h h').hom.app (DerivedCategory.Q.obj P) ≫
        (delta i k (h.trans h')).hom.app P =
      (td j k h').map ((delta i j h).hom.app P) ≫
        (delta j k h').hom.app ((t A i j h).obj P) ≫
        DerivedCategory.Q.map ((a₀ i j k h h').hom.app P)
  m_rep : ∀ i P,
    (md i).hom.app (DerivedCategory.Q.obj P) =
      (sigma i i le_rfl).hom.app P ≫ DerivedCategory.Q.map ((m₀ i).hom.app P)
  mu_rep : ∀ i P,
    (mud i).hom.app (DerivedCategory.Q.obj P) =
      (delta i i le_rfl).hom.app P ≫ DerivedCategory.Q.map ((μ₀ i).hom.app P)
  theta_rep : ∀ i j h P,
    (theta i j h).hom.app (DerivedCategory.Q.obj P) ≫
        (gd j).map ((sigma i j h).hom.app P) ≫
        (gamma j).hom.app ((T R M i j h).obj P) =
      (td i j h).map ((gamma i).hom.app P) ≫
        (delta i j h).hom.app ((g R A G i).obj P) ≫
        DerivedCategory.Q.map ((θ₀ i j h).hom.app P)
  theta_unique : ∀ i j h (θ' : gd i ⋙ td i j h ⟶ (M i j h).T ⋙ gd j),
    (∀ P, θ'.app (DerivedCategory.Q.obj P) ≫
        (gd j).map ((sigma i j h).hom.app P) ≫
        (gamma j).hom.app ((T R M i j h).obj P) =
      (td i j h).map ((gamma i).hom.app P) ≫
        (delta i j h).hom.app ((g R A G i).obj P) ≫
        DerivedCategory.Q.map ((θ₀ i j h).hom.app P)) → θ' = (theta i j h).hom
  coherent : Coherent (fun i j h ↦ (M i j h).T) td gd alpha ad md mud theta
  resolution_computation : ∀ i j h
    (P X : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J (R.obj i))) ℤ)
    (p₀ : P ⟶ X), QuasiIso p₀ →
    CochainComplex.IsKFlatIndependentCoefficients (R := R.obj i) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := R.obj i) (P.X n)) →
      ∃! e : (M i j h).T.obj (DerivedCategory.Q.obj X) ≅
        DerivedCategory.Q.obj ((T R M i j h).obj P),
        e.inv = (sigma i j h).inv.app P ≫ (M i j h).T.map (DerivedCategory.Q.map p₀)

  resolution_associator : ∀ i j k h h'
    (P X : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J (R.obj i))) ℤ)
    (p₀ : P ⟶ X), QuasiIso p₀ →
    CochainComplex.IsKFlatIndependentCoefficients (R := R.obj i) P →
    (∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := R.obj i) (P.X n)) →
      ∃ (left : ((M i j h).T ⋙ (M j k h').T).obj (DerivedCategory.Q.obj X) ≅
          DerivedCategory.Q.obj ((T R M j k h').obj ((T R M i j h).obj P)))
        (right : (M i k (h.trans h')).T.obj (DerivedCategory.Q.obj X) ≅
          DerivedCategory.Q.obj ((T R M i k (h.trans h')).obj P)),
        left.inv = (sigma j k h').inv.app ((T R M i j h).obj P) ≫
          (M j k h').T.map ((sigma i j h).inv.app P) ≫
          ((M i j h).T ⋙ (M j k h').T).map (DerivedCategory.Q.map p₀) ∧
        right.inv = (sigma i k (h.trans h')).inv.app P ≫
          (M i k (h.trans h')).T.map (DerivedCategory.Q.map p₀) ∧
        (alpha i j k h h').hom.app (DerivedCategory.Q.obj X) ≫ right.hom =
          left.hom ≫ DerivedCategory.Q.map ((u₀ i j k h h').hom.app P) ∧
        (alpha i j k h h').inv.app (DerivedCategory.Q.obj X) ≫ left.hom =
          right.hom ≫ DerivedCategory.Q.map ((u₀ i j k h h').inv.app P)

/-- Counit-normalized coherent transport and simultaneous resolving computations.
Source: Stacks 06YS, 0G7E, 06YY, 0D6D and 04VG
(blueprint: lem-weil-sections-scalar-derived-transport).

Proof, following the nine DAG steps:
1. Localize T, t and g by the inversion hypotheses. Whiskered factorization isomorphisms
   identify every composite with its chain composite (localization universal property).
2. Apply localizationLeftDerivedComparison to each specified universal cochain counit.
   Full faithfulness after Q gives the comparison c and its uniqueness.
3. Scalar extension preserves flat-term K-flat complexes (0G7E), using the
   independent-coefficient theorem and the site tensor comparison. A resolution is
   already supplied in each computation clause; no resolution existence is needed.
4. Descend the balanced associator using the composite counit comparison. Full
   faithfulness gives alpha_rep; cancellation gives alpha_inv_rep. These formulas
   specify the canonical scalar maps on the stipulated representatives.
5. Conjugate the localized theta by the inverse scalar comparison. Localization gives
   theta_rep and theta_unique; no preservation of K-flat complexes by G is needed.
6. Localize the triple equation and cancel adjacent c and inverse c. Naturality moves
   comparisons through the intermediate theta. The result is coherent.triple.
7. Transport the action unit through c and cancel; the chain action equation gives
   coherent.unit, including repeated indices without identifying extension with identity.
8. Each pasted word has its composite representative comparison. Conjugation preserves
   vertical composition and whiskering by cancellation of internal comparison factors.
   Apply this to both four-stage laws. The iterated equation follows by applying
   the triple law twice and naturality of theta at the inner associator.
9. Every resulting cell is a derived natural transformation. Naturality on a resolution
   identifies its representative formula with its component at the resolved complex;
   two resolutions therefore give the same component. The roof equation is the separate
   roof_naturality clause below. There are no boundedness or completeness assumptions. -/
theorem derived_transport
    (H : ChainHypotheses R A M G u₀ a₀ m₀ μ₀ θ₀) :
    Nonempty (DerivedTransport R A M G u₀ a₀ m₀ μ₀ θ₀) ∧
      (∀ i j h (P : CochainComplex (ringedSiteModules.{r}
        (SheafOfModules.derivedChangeRingIndependentCoefficients J (R.obj i))) ℤ),
        CochainComplex.IsKFlatIndependentCoefficients (R := R.obj i) P →
        (∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := R.obj i) (P.X n)) →
          CochainComplex.IsKFlatIndependentCoefficients (R := R.obj j)
            ((T R M i j h).obj P) ∧
          ∀ n : ℤ, SheafOfModules.IsFlatOnSite (R := R.obj j)
            (((T R M i j h).obj P).X n)) := by
  classical
  have hT (i j : Fin 4) (h : i ≤ j) :
      (HomologicalComplex.quasiIso _ (.up ℤ)).IsInvertedBy
        (T R M i j h ⋙ DerivedCategory.Q) := by
    intro P Q f hf
    have := H.sheaf_quasiIso i j h f hf
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map ((T R M i j h).map f)))
  have ht (i j : Fin 4) (h : i ≤ j) :
      (HomologicalComplex.quasiIso _ (.up ℤ)).IsInvertedBy
        (t A i j h ⋙ DerivedCategory.Q) := by
    intro P Q f hf
    have := H.module_quasiIso i j h f hf
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map ((t A i j h).map f)))
  have hg (i : Fin 4) :
      (HomologicalComplex.quasiIso _ (.up ℤ)).IsInvertedBy
        (g R A G i ⋙ DerivedCategory.Q) := by
    intro P Q f hf
    have := H.sections_quasiIso i f hf
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map ((g R A G i).map f)))
  let bT i j h := Localization.lift _ (hT i j h) DerivedCategory.Q
  let td i j h := Localization.lift _ (ht i j h) DerivedCategory.Q
  let gd i := Localization.lift _ (hg i) DerivedCategory.Q
  let beta i j h : DerivedCategory.Q ⋙ bT i j h ≅ T R M i j h ⋙ DerivedCategory.Q :=
    Localization.fac _ (hT i j h) DerivedCategory.Q
  let delta i j h : DerivedCategory.Q ⋙ td i j h ≅ t A i j h ⋙ DerivedCategory.Q :=
    Localization.fac _ (ht i j h) DerivedCategory.Q
  let gamma i : DerivedCategory.Q ⋙ gd i ≅ g R A G i ⋙ DerivedCategory.Q :=
    Localization.fac _ (hg i) DerivedCategory.Q
  let c i j h : (M i j h).T ≅ bT i j h := by
    let := (M i j h).universal
    exact Functor.localizationLeftDerivedComparison DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) _ _ _ (M i j h).ε (beta i j h)
  have hc i j h : Functor.whiskerLeft DerivedCategory.Q (c i j h).hom ≫
      (beta i j h).hom = (M i j h).ε := by
    let := (M i j h).universal
    apply Functor.localizationLeftDerivedComparison_fac
  let sigma i j h : DerivedCategory.Q ⋙ (M i j h).T ≅ T R M i j h ⋙ DerivedCategory.Q :=
    Functor.isoWhiskerLeft DerivedCategory.Q (c i j h) ≪≫ beta i j h
  have hs i j h : (sigma i j h).hom = (M i j h).ε := hc i j h
  let sc i j k h h' : DerivedCategory.Q ⋙ ((M i j h).T ⋙ (M j k h').T) ≅
      (T R M i j h ⋙ T R M j k h') ⋙ DerivedCategory.Q :=
    compComparison (sigma i j h) (sigma j k h')
  let ac i j k h h' : DerivedCategory.Q ⋙ (td i j h ⋙ td j k h') ≅
      (t A i j h ⋙ t A j k h') ⋙ DerivedCategory.Q :=
    compComparison (delta i j h) (delta j k h')
  let tc i j h : DerivedCategory.Q ⋙ (gd i ⋙ td i j h) ≅
      (g R A G i ⋙ t A i j h) ⋙ DerivedCategory.Q :=
    compComparison (gamma i) (delta i j h)
  let tg i j h : DerivedCategory.Q ⋙ ((M i j h).T ⋙ gd j) ≅
      (T R M i j h ⋙ g R A G j) ⋙ DerivedCategory.Q :=
    compComparison (sigma i j h) (gamma j)
  let alpha i j k h h' := (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _).preimageIso
      (sc i j k h h' ≪≫ Functor.isoWhiskerRight (u₀ i j k h h') DerivedCategory.Q ≪≫
        (sigma i k (h.trans h')).symm)
  let ad i j k h h' := (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _).preimageIso
      (ac i j k h h' ≪≫ Functor.isoWhiskerRight (a₀ i j k h h') DerivedCategory.Q ≪≫
        (delta i k (h.trans h')).symm)
  let md i := (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _).preimageIso
      (sigma i i le_rfl ≪≫ Functor.isoWhiskerRight (m₀ i) DerivedCategory.Q ≪≫
        Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
  let mud i := (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _).preimageIso
      (delta i i le_rfl ≪≫ Functor.isoWhiskerRight (μ₀ i) DerivedCategory.Q ≪≫
        Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm)
  let theta i j h := (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) _).preimageIso
      (tc i j h ≪≫ Functor.isoWhiskerRight (θ₀ i j h) DerivedCategory.Q ≪≫
        (tg i j h).symm)
  have halpha i j k h h' P :
      (alpha i j k h h').hom.app (DerivedCategory.Q.obj P) ≫
        (sigma i k (h.trans h')).hom.app P =
      (M j k h').T.map ((sigma i j h).hom.app P) ≫
        (sigma j k h').hom.app ((T R M i j h).obj P) ≫
        DerivedCategory.Q.map ((u₀ i j k h h').hom.app P) := by
    have he := preimageIso_fac DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) (sc i j k h h')
      (sigma i k (h.trans h')) (Functor.isoWhiskerRight (u₀ i j k h h') DerivedCategory.Q) P
    rw [compComparison_hom] at he
    simpa only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Category.assoc] using he
  have had i j k h h' P :
      (ad i j k h h').hom.app (DerivedCategory.Q.obj P) ≫
        (delta i k (h.trans h')).hom.app P =
      (td j k h').map ((delta i j h).hom.app P) ≫
        (delta j k h').hom.app ((t A i j h).obj P) ≫
        DerivedCategory.Q.map ((a₀ i j k h h').hom.app P) := by
    have he := preimageIso_fac DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) (ac i j k h h')
      (delta i k (h.trans h')) (Functor.isoWhiskerRight (a₀ i j k h h') DerivedCategory.Q) P
    rw [compComparison_hom] at he
    simpa only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Category.assoc] using he
  have hmd i P : (md i).hom.app (DerivedCategory.Q.obj P) =
      (sigma i i le_rfl).hom.app P ≫ DerivedCategory.Q.map ((m₀ i).hom.app P) := by
    dsimp only [md]
    rw [preimageIso_app, unitComparison_hom]
  have hmud i P : (mud i).hom.app (DerivedCategory.Q.obj P) =
      (delta i i le_rfl).hom.app P ≫ DerivedCategory.Q.map ((μ₀ i).hom.app P) := by
    dsimp only [mud]
    rw [preimageIso_app, unitComparison_hom]
  have htheta i j h P :
      (theta i j h).hom.app (DerivedCategory.Q.obj P) ≫
        (gd j).map ((sigma i j h).hom.app P) ≫
        (gamma j).hom.app ((T R M i j h).obj P) =
      (td i j h).map ((gamma i).hom.app P) ≫
        (delta i j h).hom.app ((g R A G i).obj P) ≫
        DerivedCategory.Q.map ((θ₀ i j h).hom.app P) := by
    have he := preimageIso_fac DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) (tc i j h) (tg i j h)
      (Functor.isoWhiskerRight (θ₀ i j h) DerivedCategory.Q) P
    rw [compComparison_hom, compComparison_hom] at he
    simpa only [Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Category.assoc] using he
  constructor
  · refine ⟨{
        barT := bT, td := td, gd := gd, beta := beta, delta := delta,
        gamma := gamma, c := c, sigma := sigma, sigma_counit := hs,
        alpha := alpha, ad := ad, md := md, mud := mud, theta := theta,
        alpha_rep := halpha, a_rep := had, m_rep := hmd, mu_rep := hmud,
        theta_rep := htheta, counit := ?_, c_unique := ?_, alpha_inv_rep := ?_,
        theta_unique := ?_, coherent := ?_, resolution_computation := ?_,
        resolution_associator := ?_ }⟩
    · intro i j h P
      exact congr_app (hc i j h) P
    · intro i j h c' hc'
      apply Localization.natTrans_ext DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (.up ℤ))
      intro P
      apply (cancel_mono ((beta i j h).hom.app P)).1
      exact (hc' P).trans (congr_app (hc i j h) P).symm
    · intro i j k h h' P
      have he := inverse_rep ((alpha i j k h h').app (DerivedCategory.Q.obj P))
        ((sc i j k h h').app P) ((sigma i k (h.trans h')).app P)
        (DerivedCategory.Q.mapIso ((u₀ i j k h h').app P)) (by
          change (alpha i j k h h').hom.app _ ≫ (sigma i k _).hom.app P =
            (sc i j k h h').hom.app P ≫ _
          rw [compComparison_hom]
          simpa only [Category.assoc, Functor.mapIso_hom, Iso.app_hom]
            using halpha i j k h h' P)
      change (alpha i j k h h').inv.app _ ≫ (sc i j k h h').hom.app P =
        (sigma i k _).hom.app P ≫ _ at he
      rw [compComparison_hom] at he
      simpa only [Category.assoc, Functor.mapIso_inv, Iso.app_inv] using he
    · intro i j h θ'  hθ'
      apply Localization.natTrans_ext DerivedCategory.Q
        (HomologicalComplex.quasiIso _ (.up ℤ))
      intro P
      apply (cancel_mono ((gd j).map ((sigma i j h).hom.app P) ≫
        (gamma j).hom.app ((T R M i j h).obj P))).1
      exact (hθ' P).trans (htheta i j h P).symm
    · clear_value theta ad alpha md mud tg tc ac sc sigma c gamma delta beta gd td bT
      have htriple : ∀ i j k (h : i ≤ j) (h' : j ≤ k) X,
          (td j k h').map ((theta i j h).hom.app X) ≫
            (theta j k h').hom.app ((M i j h).T.obj X) ≫
              (gd k).map ((alpha i j k h h').hom.app X) =
          (ad i j k h h').hom.app ((gd i).obj X) ≫
            (theta i k (h.trans h')).hom.app X := by
        intro i j k h h' X
        let l : (gd i ⋙ td i j h) ⋙ td j k h' ⟶ (M i k (h.trans h')).T ⋙ gd k :=
          Functor.whiskerRight (theta i j h).hom (td j k h') ≫
            Functor.whiskerLeft (M i j h).T (theta j k h').hom ≫
            Functor.whiskerRight (alpha i j k h h').hom (gd k)
        let r : (gd i ⋙ td i j h) ⋙ td j k h' ⟶ (M i k (h.trans h')).T ⋙ gd k :=
          Functor.whiskerLeft (gd i) (ad i j k h h').hom ≫ (theta i k (h.trans h')).hom
        change l.app X = r.app X
        apply congr_app (Localization.natTrans_ext DerivedCategory.Q
          (HomologicalComplex.quasiIso _ (.up ℤ)) (τ := l) (τ' := r) ?_) X
        intro P
        change (td j k h').map ((theta i j h).hom.app (DerivedCategory.Q.obj P)) ≫
            (theta j k h').hom.app ((M i j h).T.obj (DerivedCategory.Q.obj P)) ≫
            (gd k).map ((alpha i j k h h').hom.app (DerivedCategory.Q.obj P)) =
          (ad i j k h h').hom.app ((gd i).obj (DerivedCategory.Q.obj P)) ≫
            (theta i k (h.trans h')).hom.app (DerivedCategory.Q.obj P)
        apply (cancel_mono ((gd k).map ((sigma i k (h.trans h')).hom.app P) ≫
          (gamma k).hom.app ((T R M i k (h.trans h')).obj P))).1
        simp only [Category.assoc]
        rw [htheta]
        rw [← (gd k).map_comp_assoc, halpha]
        simp only [Functor.map_comp, Category.assoc]
        have hnθ := (theta j k h').hom.naturality ((sigma i j h).hom.app P)
        have hnγ := (gamma k).hom.naturality ((u₀ i j k h h').hom.app P)
        have hna := (ad i j k h h').hom.naturality ((gamma i).hom.app P)
        have hnδ := (delta j k h').hom.naturality ((θ₀ i j h).hom.app P)
        dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj,
          Functor.id_map] at hnθ hnγ hna hnδ
        rw [← Category.assoc ((theta j k h').hom.app _), ← hnθ]
        simp only [Category.assoc]
        rw [hnγ]
        rw [reassoc_of% (htheta j k h' ((T R M i j h).obj P))]
        simp only [← (td j k h').map_comp_assoc]
        rw [htheta]
        simp only [Functor.map_comp, Category.assoc]
        rw [reassoc_of% hnδ]
        rw [← Category.assoc ((ad i j k h h').hom.app _), ← hna]
        simp only [Category.assoc]
        rw [reassoc_of% (had i j k h h' ((g R A G i).obj P))]
        simp only [← DerivedCategory.Q.map_comp]
        rw [H.coherent.triple i j k h h' P]
      refine {
        triple := htriple
        unit := ?_
        sheaf_four := ?_
        module_four := ?_
        iterated := ?_ }
      · intro i X
        let l : gd i ⋙ td i i le_rfl ⟶ gd i :=
          (theta i i le_rfl).hom ≫ Functor.whiskerRight (md i).hom (gd i)
        let r : gd i ⋙ td i i le_rfl ⟶ gd i :=
          Functor.whiskerLeft (gd i) (mud i).hom
        change l.app X = r.app X
        apply congr_app (Localization.natTrans_ext DerivedCategory.Q
          (HomologicalComplex.quasiIso _ (.up ℤ)) (τ := l) (τ' := r) ?_) X
        intro P
        change (theta i i le_rfl).hom.app (DerivedCategory.Q.obj P) ≫
            (gd i).map ((md i).hom.app (DerivedCategory.Q.obj P)) =
          (mud i).hom.app ((gd i).obj (DerivedCategory.Q.obj P))
        apply (cancel_mono ((gamma i).hom.app P)).1
        rw [hmd]
        simp only [Functor.map_comp, Category.assoc]
        have hnγ := (gamma i).hom.naturality ((m₀ i).hom.app P)
        have hnμ := (mud i).hom.naturality ((gamma i).hom.app P)
        dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hnγ hnμ
        rw [hnγ, reassoc_of% (htheta i i le_rfl P), ← hnμ, hmud]
        simp only [← DerivedCategory.Q.map_comp]
        rw [H.coherent.unit i P]
      · exact transport_four (fun _ ↦ DerivedCategory.Q)
          (HomologicalComplex.quasiIso _ (.up ℤ)) (T R M)
          (fun i j h ↦ (M i j h).T) sigma u₀ alpha halpha H.coherent.sheaf_four
      · exact transport_four (fun _ ↦ DerivedCategory.Q)
          (HomologicalComplex.quasiIso _ (.up ℤ)) (t A) td delta a₀ ad had
          H.coherent.module_four
      · intro X
        simp only [Functor.map_comp]
        have hn := (theta 2 3 (by decide)).hom.naturality
          ((alpha 0 1 2 (by decide) (by decide)).hom.app X)
        dsimp only [Functor.comp_map, Functor.comp_obj] at hn
        rw [← reassoc_of% hn]
        simp only [← (td 2 3 (by decide)).map_comp_assoc]
        rw [htriple]
        simp only [Functor.map_comp, Category.assoc]
        rw [htriple]
    · intro i j h P X p hp _ _
      have := hp
      let e := ((M i j h).T.mapIso (asIso (DerivedCategory.Q.map p))).symm ≪≫
        (sigma i j h).app P
      refine ⟨e, rfl, ?_⟩
      intro e' he'
      change e'.inv = e.inv at he'
      exact Iso.ext_inv he'
    · intro i j k h h' P X p hp _ _
      have := hp
      let e := ((M i j h).T ⋙ (M j k h').T).mapIso
        (asIso (DerivedCategory.Q.map p))
      let left := e.symm ≪≫ (sc i j k h h').app P
      let right := ((M i k (h.trans h')).T.mapIso
        (asIso (DerivedCategory.Q.map p))).symm ≪≫ (sigma i k (h.trans h')).app P
      have heq : (alpha i j k h h').hom.app (DerivedCategory.Q.obj X) ≫ right.hom =
          left.hom ≫ DerivedCategory.Q.map ((u₀ i j k h h').hom.app P) := by
        have hn := (alpha i j k h h').hom.naturality (inv (DerivedCategory.Q.map p))
        dsimp only [Functor.comp_map] at hn
        dsimp only [left, right, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
          Functor.mapIso_inv, e, asIso_inv]
        rw [← Category.assoc, ← hn, Category.assoc]
        rw [halpha]
        rw [compComparison_hom]
        simp only [Category.assoc, Functor.comp_map]
      refine ⟨left, right, ?_, rfl, heq, ?_⟩
      · simp only [left, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_hom, e,
          Iso.app_inv, sc, compComparison_inv, asIso_hom, Category.assoc]
      · simpa only [Functor.mapIso_inv, Iso.app_inv] using
          inverse_rep ((alpha i j k h h').app (DerivedCategory.Q.obj X))
          left right (DerivedCategory.Q.mapIso ((u₀ i j k h h').app P)) heq
  · intro i j h P hk hf
    obtain ⟨hk', hf'⟩ := SheafOfModules.changeOfRings_isKFlat_of_flat_terms_independentCoefficients
      (R.map (homOfLE h)) P (M i j h).E (M i j h).obj_eq (M i j h).map_eq hk
      (fun n ↦ (exactFunctor _ _).prop_of_iso
        (SheafOfModules.siteSheafTensorRightIso (R := R.obj i) (P.X n)) (hf n))
    exact ⟨hk', fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (R := R.obj j) _).symm (hf' n)⟩

/-- Naturality of every descended cell on an arbitrary roof, with arbitrary specified
representative comparisons, hence also for every composite cell and every resolution.
Source: Stacks 04VG; DAG proof step 9
(blueprint: lem-weil-sections-scalar-derived-transport).

Proof: naturality on v gives tau_P = H(v) inverse composed with tau_C and F(v).
Substitute this in naturality on f and cancel F(v) with its inverse. Conjugate by the
specified representative comparisons eF and eH. This proves the displayed roof identity
for every derived cell, including units, associators, their inverses and all pastings. -/
theorem roof_naturality
    {B : Type x} [Category.{p} B] {D : Type y} [Category.{q} D]
    {E : Type u} [Category.{v} E] (Q : B ⥤ D) (F H : D ⥤ E)
    (Fc Hc : B ⥤ E) (eF : Q ⋙ F ≅ Fc) (eH : Q ⋙ H ≅ Hc)
    (τ : F ⟶ H) {X P Y : B} (v₀ : P ⟶ X) (f : P ⟶ Y) [IsIso (Q.map v₀)] :
    (eF.inv.app X ≫ τ.app (Q.obj X) ≫ eH.hom.app X) ≫
      eH.inv.app X ≫ inv (H.map (Q.map v₀)) ≫ H.map (Q.map f) ≫ eH.hom.app Y =
    eF.inv.app X ≫ inv (F.map (Q.map v₀)) ≫ F.map (Q.map f) ≫ eF.hom.app Y ≫
      (eF.inv.app Y ≫ τ.app (Q.obj Y) ≫ eH.hom.app Y) := by
  have hn : τ.app (Q.obj X) ≫ inv (H.map (Q.map v₀)) =
      inv (F.map (Q.map v₀)) ≫ τ.app (Q.obj P) := by
    apply (cancel_epi (F.map (Q.map v₀))).1
    rw [← Category.assoc, τ.naturality]
    simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
      IsIso.hom_inv_id_assoc]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc (τ.app (Q.obj X)), hn, Category.assoc,
    ← Category.assoc (τ.app (Q.obj P)), ← τ.naturality (Q.map f), Category.assoc]

end CategoryTheory.SectionsScalarTransport
