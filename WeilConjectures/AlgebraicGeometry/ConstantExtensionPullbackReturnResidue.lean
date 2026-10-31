/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstantExtensionWeilHeartData
public import WeilConjectures.AlgebraicGeometry.WeilIndSheafCategory
public import Mathlib.Algebra.Category.Ring.LinearAlgebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import WeilConjectures.AlgebraicGeometry.ZlWeilHeartLocalizationExact
import WeilConjectures.AlgebraicGeometry.ConstantExtensionReturnExactFunctor
import WeilConjectures.AlgebraicGeometry.ConstantExtensionPullbackSheetComparison
import WeilConjectures.AlgebraicGeometry.FiniteFieldBaseChangeResidueSurjective
import WeilConjectures.PointCount
import WeilConjectures.Mathlib.NumberTheory.Padics.Complex
import WeilConjectures.AlgebraicGeometry.ClosedPointField
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Finiteness.Cardinality

/-! # Constant-extension pullback, cyclic return and residue compositum

Source: Deligne, Weil II, (1.1.8), p.151, and paragraph after (1.1.10), p.152;
Stacks Project, Tag 01JT, and finite-field degree calculation.
(blueprint: lem-zl-constant-extension-pullback-return-residue)

The existing restriction specification records the unchanged carrier and its iterated
Weil structure. The normalization below additionally specifies every intermediate
transition, and the full return specifies the closing transition. Residue tensors are
pushouts in commutative rings of the actual two maps out of the finite base field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (m : ℕ) (hm : 1 ≤ m)
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]

/-- Adjacent semilinear sheets differ by geometric q-Frobenius.
Source: Deligne, Weil II, paragraph after (1.1.10), p.152.
(blueprint: lem-zl-constant-extension-pullback-return-residue)
Proof: substitute j=i+1 and expand the power of the same automorphism. Associativity
identifies the two composites; no linearity over the algebraic closure is required. -/
theorem constantExtensionCoordinate_succ (i j : Fin m) (h : j.val = i.val + 1) :
    constantExtensionSheet D m hm X₀ ≫
        ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ j.val).hom =
      (constantExtensionSheet D m hm X₀ ≫
        ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ i.val).hom) ≫
          (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom := by
  simp [h, pow_succ', Aut.Aut_mul_def, Category.assoc]

variable (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The zeroth coordinate is the distinguished-sheet pullback, by the identity law.
Source: Deligne, Weil II, paragraph after (1.1.10), p.152.
(blueprint: lem-zl-constant-extension-pullback-return-residue) -/
def constantExtensionZerothCoordinateIso :
    constantExtensionSheetPullAt D m hm X₀ l hl Ω ⟨0, hm⟩ ≅
      constantExtensionSheetPull D m hm X₀ l hl Ω :=
  eqToIso (congrArg (fun f ↦ @commonStageDerivedPullback l _ Ω _ _ _ _ _ f
    (sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀))
    (sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀)))
    (Category.comp_id (constantExtensionSheet D m hm X₀)))

/-- The actual transition in semilinear coordinates, with the normalized compositor.
Source: Deligne, Weil II, paragraph after (1.1.10), p.152.
(blueprint: lem-zl-constant-extension-pullback-return-residue) -/
def constantExtensionCoordinateStep
    (N : sfCommonStageWeilComplex D l hl (constantExtensionOriginalModel D m hm X₀) Ω)
    (i j : Fin m) (h : j.val = i.val + 1) :
    (constantExtensionSheetPullAt D m hm X₀ l hl Ω j).obj N.carrier ≅
      (constantExtensionSheetPullAt D m hm X₀ l hl Ω i).obj N.carrier :=
  letI := sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀)
  letI := sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
    (constantExtensionModel D m hm X₀)
  eqToIso (congrArg (fun f ↦ (commonStageDerivedPullback l Ω f).obj N.carrier)
    (constantExtensionCoordinate_succ D m hm X₀ i j h)) ≪≫
    (zlPullComp l Ω
      (constantExtensionSheet D m hm X₀ ≫
        ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ i.val).hom)
      (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom).app N.carrier ≪≫
    (constantExtensionSheetPullAt D m hm X₀ l hl Ω i).mapIso N.str

/-- Cyclic normalization of a restricted sheaf. Naturality fixes the coordinate maps
on all morphisms. The intermediate equations say that their transitions are identities;
the return equation then says that the last transition is precisely the new Weil map.
Source: Deligne, Weil II, paragraph after (1.1.10), p.152.
(blueprint: lem-zl-constant-extension-pullback-return-residue) -/
def ConstantExtensionPullbackNormalization
    (R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (G : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω) : Prop :=
  ∃ γ : ∀ i : Fin m,
      G ⋙ constantExtensionHeartForget D l hl Ω (constantExtensionOriginalModel D m hm X₀) ⋙
        constantExtensionSheetPullAt D m hm X₀ l hl Ω i ≅
      R ⋙ constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω
        (constantExtensionModel D m hm X₀),
    (∀ (F : sfCommonStageWeilSheaf D l hl X₀ Ω) (i j : Fin m)
      (h : j.val = i.val + 1),
      (constantExtensionCoordinateStep D m hm X₀ l hl Ω (G.obj F).obj i j h).hom ≫
          (γ i).hom.app F = (γ j).hom.app F) ∧
    (∀ F : sfCommonStageWeilSheaf D l hl X₀ Ω,
      (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀) Ω).map
        ((constantExtensionZerothCoordinateIso D m hm X₀ l hl Ω).inv.app
          (G.obj F).obj.carrier ≫ (γ ⟨0, hm⟩).hom.app F) ≫ (R.obj F).obj.str.hom =
      (constantExtensionReturnComparison D m hm X₀ l hl Ω (G.obj F).obj.carrier).hom ≫
        (constantExtensionSheetPull D m hm X₀ l hl Ω).map
          (constantExtensionWeilIterate D l hl Ω
            (constantExtensionOriginalModel D m hm X₀) (G.obj F).obj (m - 1)).hom ≫
        (constantExtensionZerothCoordinateIso D m hm X₀ l hl Ω).inv.app
          (G.obj F).obj.carrier ≫ (γ ⟨0, hm⟩).hom.app F)

section ProofGlue
open CategoryTheory.Functor

attribute [local implicit_reducible] constantExtensionDatum constantExtensionSheetPullAt

attribute [local irreducible] commonStageDerivedPullback rationalDerivedPullback
  constructibleIntegralPullback

private theorem heartForget_obj
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (F : sfCommonStageWeilSheaf D l hl Y₀ Ω) :
    (constantExtensionHeartForget D l hl Ω Y₀).obj F = F.obj.carrier := rfl

private theorem heartForget_map
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    {F F' : sfCommonStageWeilSheaf D l hl Y₀ Ω} (f : F ⟶ F') :
    (constantExtensionHeartForget D l hl Ω Y₀).map f = f.hom.hom.f := rfl

private theorem sheetReturnPullbackRestriction
    (T : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (hT : ConstantExtensionSheetSpec D m hm X₀ l hl Ω T) :
    ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω
      (zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀) ⋙ T) := by
  let := sfWeilPrimeInvertible D l hl X₀
  let := sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀)
  let := sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
    (constantExtensionModel D m hm X₀)
  let P := zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)
  obtain ⟨a, ha⟩ := hT
  let b : P ⋙ constantExtensionHeartForget D l hl Ω
        (constantExtensionOriginalModel D m hm X₀) ⋙
          constantExtensionSheetPull D m hm X₀ l hl Ω ≅
      constantExtensionHeartForget D l hl Ω X₀ ⋙
        constantExtensionFiberPull D m hm X₀ l hl Ω :=
    isoWhiskerLeft (constantExtensionHeartForget D l hl Ω X₀)
      (zlPullComp l Ω (constantExtensionSheet D m hm X₀)
        (zlFiberMap D (constantExtensionProjection D m hm X₀))).symm
  refine ⟨isoWhiskerLeft P a ≪≫ b, ?_⟩
  intro F
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    b, Iso.symm_hom, Functor.map_comp, Category.assoc]
  have hp := congrArg
    (fun f ↦ (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) Ω).map (a.hom.app (P.obj F)) ≫ f)
    (pullbackSheetReturnComparison D m hm X₀ l hl Ω F)
  apply hp.trans
  simpa only [P, b, isoWhiskerLeft_hom, whiskerLeft_app, Iso.symm_hom,
    Functor.comp_obj, heartForget_obj, Category.assoc] using congrArg
    (fun f ↦ f ≫ b.hom.app F) (ha (P.obj F))

private theorem restrictionSpecIso
    (R S : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (hR : ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω R)
    (hS : ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω S) : Nonempty (R ≅ S) := by
  obtain ⟨a, ha⟩ := hR
  obtain ⟨b, hb⟩ := hS
  let c := a ≪≫ b.symm
  refine ⟨NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
    (ObjectProperty.isoMk _ (CategoryTheory.Endofunctor.Algebra.isoMk (c.app F) ?_))) ?_⟩
  · change (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) Ω).map (c.hom.app F) ≫
        (S.obj F).obj.str.hom = (R.obj F).obj.str.hom ≫ c.hom.app F
    apply (cancel_mono (b.hom.app F)).mp
    simp only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.map_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← hb F]
    simpa only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id,
      Category.id_comp, Category.comp_id, Category.assoc] using ha F
  · intro F F' f
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply CategoryTheory.Endofunctor.Algebra.Hom.ext
    exact c.hom.naturality f

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

-- Generic square identities keep concrete pullback functors folded during checking.
private theorem isoSquare_inv
    {A : Type u₁} [Category.{v₁} A] (P : A ⥤ A) {X Y : A} (a : X ≅ Y)
    (s : P.obj X ⟶ X) (t : P.obj Y ⟶ Y)
    (h : P.map a.hom ≫ t = s ≫ a.hom) : P.map a.inv ≫ s = t ≫ a.inv := by
  apply (cancel_mono a.hom).mp
  rw [Category.assoc, ← h]
  simp only [← P.map_comp_assoc, Iso.inv_hom_id, P.map_id,
    Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem mapCompSquare
    {A : Type u₁} [Category.{v₁} A] (P : A ⥤ A) {X Y Z : A}
    (a : X ⟶ Y) (c : Y ⟶ Z)
    (r : P.obj X ⟶ X) (s : P.obj Y ⟶ Y) (t : P.obj Z ⟶ Z)
    (ha : P.map a ≫ s = r ≫ a) (hc : P.map c ≫ t = s ≫ c) :
    P.map (a ≫ c) ≫ t = r ≫ a ≫ c := by
  rw [P.map_comp, Category.assoc, hc, ← Category.assoc, ha, Category.assoc]

private theorem whiskeredIsoCancel
    {C : Type u₁} {A : Type u₂} {B : Type u₃} {E : Type u₄}
    [Category.{v₁} C] [Category.{v₂} A] [Category.{v₃} B] [Category.{v₄} E]
    (G : C ⥤ A) (H : A ⥤ B) (S₀ S : B ⥤ E) (V : C ⥤ E)
    (e : S₀ ≅ S) (b : G ⋙ H ⋙ S ≅ V) (F : C) :
    e.inv.app (H.obj (G.obj F)) ≫
      (isoWhiskerLeft G (isoWhiskerLeft H e) ≪≫ b).hom.app F = b.hom.app F := by
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Iso.inv_hom_id_app_assoc]

private theorem whiskeredIsoCompose
    {C : Type u₁} {A : Type u₂} {B : Type u₃} {E : Type u₄}
    [Category.{v₁} C] [Category.{v₂} A] [Category.{v₃} B] [Category.{v₄} E]
    (G : C ⥤ A) (T : A ⥤ B) (H : A ⥤ E) (K : B ⥤ E) (R : C ⥤ B)
    (a : T ⋙ K ≅ H) (c : G ⋙ T ≅ R) (F : C) :
    (isoWhiskerLeft G a.symm ≪≫ (Functor.associator G T K).symm ≪≫
      isoWhiskerRight c K).hom.app F = a.inv.app (G.obj F) ≫ K.map (c.hom.app F) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, Iso.symm_hom, Functor.associator_inv_app,
    Category.id_comp]

private def coordinateIsoOfComparisons
    {C : Type u₁} {A : Type u₂} {B : Type u₃}
    [Category.{v₁} C] [Category.{v₂} A] [Category.{v₃} B]
    (H : C ⥤ A) (P : A ⥤ A) (S T : A ⥤ B)
    (a : H ⋙ P ≅ H) (b : S ≅ P ⋙ T) : H ⋙ S ≅ H ⋙ T :=
  isoWhiskerLeft H b ≪≫ (Functor.associator H P T).symm ≪≫ isoWhiskerRight a T

private theorem coordinateIsoOfComparisons_hom_app
    {C : Type u₁} {A : Type u₂} {B : Type u₃}
    [Category.{v₁} C] [Category.{v₂} A] [Category.{v₃} B]
    (H : C ⥤ A) (P : A ⥤ A) (S T : A ⥤ B)
    (a : H ⋙ P ≅ H) (b : S ≅ P ⋙ T) (F : C) :
    (coordinateIsoOfComparisons H P S T a b).hom.app F =
      b.hom.app (H.obj F) ≫ T.map (a.hom.app F) := by
  simp only [coordinateIsoOfComparisons, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp]

private theorem coordinateIsoOfComparisons_eq_hom_app
    {C : Type u₁} {A : Type u₂} {B : Type u₃} {K : Type u₄}
    [Category.{v₁} C] [Category.{v₂} A] [Category.{v₃} B]
    (H : C ⥤ A) (P : A ⥤ A) (V : A ⥤ B) (Q : K → A ⥤ B)
    (a : H ⋙ P ≅ H) {x y : K} (h : x = y) (e : Q y ≅ P ⋙ V)
    (b : Q x ≅ P ⋙ V) (hb : b = eqToIso (congrArg Q h) ≪≫ e) (F : C) :
    (coordinateIsoOfComparisons H P (Q x) V a b).hom.app F =
        (eqToIso (congrArg (fun x ↦ (Q x).obj (H.obj F)) h)).hom ≫
          e.hom.app (H.obj F) ≫ V.map (a.hom.app F) := by
  subst b
  subst y
  simp only [coordinateIsoOfComparisons_hom_app, Iso.trans_hom,
    eqToIso_refl, Iso.refl_hom, Category.id_comp]

private def carrierWeilIso
    (G : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω) :
    (G ⋙ constantExtensionHeartForget D l hl Ω
      (constantExtensionOriginalModel D m hm X₀)) ⋙
        sfCommonStageWeilFrobeniusPullback D l hl
          (constantExtensionOriginalModel D m hm X₀) Ω ≅
      G ⋙ constantExtensionHeartForget D l hl Ω
        (constantExtensionOriginalModel D m hm X₀) :=
  NatIso.ofComponents (fun F ↦ (G.obj F).obj.str)
    (fun f ↦ (G.map f).hom.hom.h)

private theorem carrierWeilIso_hom_app
    (G : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    (carrierWeilIso D m hm X₀ l hl Ω G).hom.app F = (G.obj F).obj.str.hom := rfl

private def coordinatePullbackIso (i j : Fin m) (h : j.val = i.val + 1) :
    constantExtensionSheetPullAt D m hm X₀ l hl Ω j ≅
      sfCommonStageWeilFrobeniusPullback D l hl
        (constantExtensionOriginalModel D m hm X₀) Ω ⋙
          constantExtensionSheetPullAt D m hm X₀ l hl Ω i := by
  letI := sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀)
  letI := sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
    (constantExtensionModel D m hm X₀)
  exact
    eqToIso (congrArg (fun f ↦ commonStageDerivedPullback l Ω f)
      (constantExtensionCoordinate_succ D m hm X₀ i j h)) ≪≫
    zlPullComp l Ω
      (constantExtensionSheet D m hm X₀ ≫
        ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ i.val).hom)
      (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom

private def coordinateStepIso
    (G : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω)
    (i j : Fin m) (h : j.val = i.val + 1) :
    G ⋙ constantExtensionHeartForget D l hl Ω (constantExtensionOriginalModel D m hm X₀) ⋙
        constantExtensionSheetPullAt D m hm X₀ l hl Ω j ≅
      G ⋙ constantExtensionHeartForget D l hl Ω (constantExtensionOriginalModel D m hm X₀) ⋙
        constantExtensionSheetPullAt D m hm X₀ l hl Ω i :=
  (Functor.associator G
    (constantExtensionHeartForget D l hl Ω (constantExtensionOriginalModel D m hm X₀))
    (constantExtensionSheetPullAt D m hm X₀ l hl Ω j)).symm ≪≫
  coordinateIsoOfComparisons
    (G ⋙ constantExtensionHeartForget D l hl Ω (constantExtensionOriginalModel D m hm X₀))
    (sfCommonStageWeilFrobeniusPullback D l hl
      (constantExtensionOriginalModel D m hm X₀) Ω)
    (constantExtensionSheetPullAt D m hm X₀ l hl Ω j)
    (constantExtensionSheetPullAt D m hm X₀ l hl Ω i)
    (carrierWeilIso D m hm X₀ l hl Ω G)
    (coordinatePullbackIso D m hm X₀ l hl Ω i j h) ≪≫
  Functor.associator G
    (constantExtensionHeartForget D l hl Ω (constantExtensionOriginalModel D m hm X₀))
    (constantExtensionSheetPullAt D m hm X₀ l hl Ω i)

private theorem coordinateStepIso_hom_app
    (G : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
      sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω)
    (i j : Fin m) (h : j.val = i.val + 1)
    (F : sfCommonStageWeilSheaf D l hl X₀ Ω) :
    (coordinateStepIso D m hm X₀ l hl Ω G i j h).hom.app F =
      (constantExtensionCoordinateStep D m hm X₀ l hl Ω (G.obj F).obj i j h).hom := by
  let := sfWeilPrimeInvertible D l hl (constantExtensionOriginalModel D m hm X₀)
  let := sfWeilPrimeInvertible (constantExtensionDatum D m hm) l hl
    (constantExtensionModel D m hm X₀)
  simp only [coordinateStepIso, Iso.trans_hom, NatTrans.comp_app,
    Iso.symm_hom, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  change (coordinateIsoOfComparisons
    (G ⋙ constantExtensionHeartForget D l hl Ω (constantExtensionOriginalModel D m hm X₀))
    (sfCommonStageWeilFrobeniusPullback D l hl
      (constantExtensionOriginalModel D m hm X₀) Ω)
    (commonStageDerivedPullback l Ω
      (constantExtensionSheet D m hm X₀ ≫
        ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ j.val).hom))
    (constantExtensionSheetPullAt D m hm X₀ l hl Ω i)
    (carrierWeilIso D m hm X₀ l hl Ω G)
    (coordinatePullbackIso D m hm X₀ l hl Ω i j h)).hom.app F =
      (constantExtensionCoordinateStep D m hm X₀ l hl Ω (G.obj F).obj i j h).hom
  simpa only [constantExtensionCoordinateStep, carrierWeilIso_hom_app,
    Functor.comp_obj, heartForget_obj,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using
    coordinateIsoOfComparisons_eq_hom_app
      (G ⋙ constantExtensionHeartForget D l hl Ω
        (constantExtensionOriginalModel D m hm X₀))
      (sfCommonStageWeilFrobeniusPullback D l hl
        (constantExtensionOriginalModel D m hm X₀) Ω)
      (constantExtensionSheetPullAt D m hm X₀ l hl Ω i)
      (fun f ↦ commonStageDerivedPullback l Ω f)
      (carrierWeilIso D m hm X₀ l hl Ω G)
      (constantExtensionCoordinate_succ D m hm X₀ i j h)
      (zlPullComp l Ω
        (constantExtensionSheet D m hm X₀ ≫
          ((D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)) ^ i.val).hom)
        (D.geometricFrobenius (constantExtensionOriginalModel D m hm X₀)).hom)
      (coordinatePullbackIso D m hm X₀ l hl Ω i j h) rfl F

-- Construct the bounded chain in an abstract category before specializing to functors.
private def isoChain
    {A : Type u₁} [Category.{v₁} A] (m : ℕ) (hm : 1 ≤ m) (Q : Fin m → A) (R : A)
    (step : ∀ (i j : Fin m) (_h : j.val = i.val + 1), Q j ≅ Q i)
    (a : Q ⟨0, hm⟩ ≅ R) : (n : ℕ) → (hn : n < m) → Q ⟨n, hn⟩ ≅ R
  | 0, _ => a
  | n + 1, hn => step ⟨n, Nat.lt_trans (Nat.lt_succ_self n) hn⟩ ⟨n + 1, hn⟩ rfl ≪≫
      isoChain (m := m) (hm := hm) (Q := Q) (R := R) (step := step) (a := a) n
        (Nat.lt_trans (Nat.lt_succ_self n) hn)

private theorem isoChainNormalization
    {A : Type u₁} [Category.{v₁} A] (m : ℕ) (hm : 1 ≤ m) (Q : Fin m → A) (R : A)
    (step : ∀ (i j : Fin m) (_h : j.val = i.val + 1), Q j ≅ Q i)
    (a : Q ⟨0, hm⟩ ≅ R) :
    ∃ γ : ∀ i : Fin m, Q i ≅ R, γ ⟨0, hm⟩ = a ∧
      ∀ (i j : Fin m) (h : j.val = i.val + 1), step i j h ≪≫ γ i = γ j := by
  refine ⟨fun i ↦ isoChain (m := m) (hm := hm) (Q := Q) (R := R)
    (step := step) (a := a) i.val i.isLt, rfl, ?_⟩
  rintro ⟨i, hi⟩ ⟨j, hj⟩ h
  dsimp only at h
  subst j
  rfl

private theorem heartPullExact {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f₀ : X₀ ⟶ Y₀) :
    PreservesFiniteLimits (zlHeartPull D l hl Ω f₀) ∧
      PreservesFiniteColimits (zlHeartPull D l hl Ω f₀) := by
  let : (D.geometricFiber X₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber X₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  have hc := (constructible_pullback_t_exact D l hl Ω (Classical.arbitrary _)
    (W := (D.geometricFiber X₀).left) (X := (D.geometricFiber Y₀).left)
    (zlFiberMap D f₀)).2
  dsimp only [ConstructibleCommonStagePullbackComparison] at hc
  have hX : constructiblePullbackResidueUnits D l hl (D.geometricFiber X₀).left =
      (fun x ↦ sfWeilPrimeInvertible D l hl X₀ x) := Subsingleton.elim _ _
  have hY : constructiblePullbackResidueUnits D l hl (D.geometricFiber Y₀).left =
      (fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y) := Subsingleton.elim _ _
  rw [hX, hY] at hc
  obtain ⟨c⟩ := hc
  let P := sfCommonStageHeartProperty l (D.geometricFiber X₀).left Ω
  let e : c.heart ≅ zlHeartPull D l hl Ω f₀ :=
    (Functor.FullyFaithful.ofFullyFaithful P.ι).whiskeringRight _ |>.preimageIso
      (eqToIso c.heart_fac)
  let := c.heart_limits
  let := c.heart_colimits
  exact ⟨preservesFiniteLimits_of_natIso e, preservesFiniteColimits_of_natIso e⟩

private theorem localizationForgetExact
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (H : ZlLocalizationHeart D l hl Ω Y₀) :
    PreservesFiniteLimits (zlLocalizationForget D l hl Ω Y₀) ∧
      PreservesFiniteColimits (zlLocalizationForget D l hl Ω Y₀) := by
  let := H.underlying_abelian
  let := H.forget_additive
  let : ∀ {A B : sfCommonStageWeilSheaf D l hl Y₀ Ω} (f : A ⟶ B),
      CreatesLimit (parallelPair f 0) (zlLocalizationForget D l hl Ω Y₀) :=
    fun f ↦ H.kernels _ _ f
  let : ∀ {A B : sfCommonStageWeilSheaf D l hl Y₀ Ω} (f : A ⟶ B),
      CreatesColimit (parallelPair f 0) (zlLocalizationForget D l hl Ω Y₀) :=
    fun f ↦ H.cokernels _ _ f
  exact ⟨Functor.preservesFiniteLimits_of_preservesKernels _,
    Functor.preservesFiniteColimits_of_preservesCokernels _⟩

private theorem weilPullExact
    {W₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType W₀.hom] [QuasiCompact W₀.hom] [IsSeparated W₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f : W₀ ⟶ Y₀) :
    PreservesFiniteLimits (zlWeilPull D l hl Ω f) ∧
      PreservesFiniteColimits (zlWeilPull D l hl Ω f) := by
  obtain ⟨iota₀⟩ := PadicAlgCl.nonempty_ringEquiv_complex l
  let iota : Ω ≃+* ℂ :=
    (IsAlgClosure.equiv (Padic l) Ω (PadicAlgCl l)).toRingEquiv.trans iota₀
  obtain ⟨HW⟩ := (zlWeilHeartLocalizationExact D l hl Ω
    (X₀ := W₀) (U₀ := W₀) (Z₀ := W₀) iota).1
  obtain ⟨HY⟩ := (zlWeilHeartLocalizationExact D l hl Ω
    (X₀ := Y₀) (U₀ := Y₀) (Z₀ := Y₀) iota).1
  let := HW.underlying_abelian
  let := HY.underlying_abelian
  let U := zlLocalizationForget D l hl Ω W₀
  have hU := localizationForgetExact D l hl Ω W₀ HW
  have hV := localizationForgetExact D l hl Ω Y₀ HY
  let := hU.1
  let := hU.2
  let := hV.1
  let := hV.2
  let : U.ReflectsIsomorphisms := ⟨fun g hg ↦ by
    let : IsIso g.hom.hom.f := by
      change IsIso ((sfCommonStageHeartProperty l (D.geometricFiber W₀).left Ω).ι.map
        (U.map g))
      exact inferInstance
    let : IsIso ((CategoryTheory.Endofunctor.IsoAlgebra.forget _).map g.hom) := by
      change IsIso g.hom.hom.f
      infer_instance
    let : IsIso g.hom := isIso_of_reflects_iso g.hom
      (CategoryTheory.Endofunctor.IsoAlgebra.forget _)
    let : IsIso (((sfCommonStageHeartProperty l (D.geometricFiber W₀).left Ω).inverseImage
        (sfCommonStageWeilForget D l hl W₀ Ω)).ι.map g) := by
      change IsIso g.hom
      infer_instance
    exact isIso_of_reflects_iso g
      ((sfCommonStageHeartProperty l (D.geometricFiber W₀).left Ω).inverseImage
        (sfCommonStageWeilForget D l hl W₀ Ω)).ι⟩
  let : ReflectsFiniteLimits U := inferInstance
  let : ReflectsFiniteColimits U := inferInstance
  obtain ⟨hlim, hcol⟩ := heartPullExact D l hl Ω f
  let := hlim
  let := hcol
  let b : zlLocalizationForget D l hl Ω Y₀ ⋙ zlHeartPull D l hl Ω f ≅
      zlWeilPull D l hl Ω f ⋙ U := Iso.refl _
  let := preservesFiniteLimits_of_natIso b
  let := preservesFiniteColimits_of_natIso b
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ U,
    preservesFiniteColimits_of_reflects_of_preserves _ U⟩

/-- The constant-extension equivalence supplies the restriction data needed before normalization.
Source: Deligne, Weil II, (1.1.7)--(1.1.10), pp.150--152.
(blueprint: lem-zl-constant-extension-pullback-return-residue)
Proof: the normalized cyclic sheet equivalence identifies the actual restriction with the
inverse-image pullback, and exactness is detected on the constructible carriers. The
inverse equivalence supplies the natural comparison with the prescribed geometric pullback.
All these clauses are before the residue-field calculation and before the coordinate
normalization recorded separately below. -/
theorem constantExtensionRestriction_data :
    ∃ e : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ≌
        sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀) Ω,
      ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω
          (constantExtensionRestriction D m hm X₀ l hl Ω e) ∧
      PreservesFiniteLimits (constantExtensionRestriction D m hm X₀ l hl Ω e) ∧
      PreservesFiniteColimits (constantExtensionRestriction D m hm X₀ l hl Ω e) ∧
      Nonempty (constantExtensionRestriction D m hm X₀ l hl Ω e ⋙ e.inverse ≅
        zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)) := by
  obtain ⟨T, hT, hTeq⟩ := sheetReturnExactFunctor D m hm X₀ l hl Ω
  let := hTeq
  let e := T.asEquivalence
  let : IsSeparated (constantExtensionModel D m hm X₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm)))))
  let : IsSeparated (constantExtensionOriginalModel D m hm X₀).hom :=
    inferInstanceAs (IsSeparated ((constantExtensionModel D m hm X₀).hom ≫
      Spec.map (CommRingCat.ofHom (D.extensionEmbedding m hm))))
  obtain ⟨hlim, hcol⟩ := weilPullExact D l hl Ω (constantExtensionProjection D m hm X₀)
  let := hlim
  let := hcol
  refine ⟨e, sheetReturnPullbackRestriction D m hm X₀ l hl Ω T hT, ?_, ?_, ?_⟩
  · exact comp_preservesFiniteLimits _ _
  · exact comp_preservesFiniteColimits _ _
  · exact ⟨Functor.associator _ e.functor e.inverse ≪≫
      isoWhiskerLeft _ e.unitIso.symm ≪≫ Functor.rightUnitor _⟩


/-- The chosen equivalence supplies the cyclic normalization of restriction.
Source: Deligne, Weil II, paragraph after (1.1.10), p.152.
(blueprint: lem-zl-constant-extension-pullback-normalization)
(blueprint: lem-zl-constant-extension-pullback-return-residue)
Proof: transport a Weil object through the sheet-coordinate equivalence. The
successor and return comparison maps are the normalized compositors retained by
`ConstantExtensionRestrictionSpec`; their partial products give the component
isomorphisms `γ i`. Naturality of the transported equivalence gives the same
maps for every morphism, while the successor and return equations are exactly
the two clauses in `ConstantExtensionPullbackNormalization`. -/
theorem constantExtensionRestriction_normalization
    (e : sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω ≌
      sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
    (hR : ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω
      (constantExtensionRestriction D m hm X₀ l hl Ω e)) :
    ConstantExtensionPullbackNormalization D m hm X₀ l hl Ω
      (constantExtensionRestriction D m hm X₀ l hl Ω e)
      (constantExtensionRestriction D m hm X₀ l hl Ω e ⋙ e.inverse) := by
  let P := zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)
  let R := constantExtensionRestriction D m hm X₀ l hl Ω e
  let G := R ⋙ e.inverse
  change ConstantExtensionPullbackNormalization D m hm X₀ l hl Ω R G
  let U : G ≅ P :=
    Functor.associator P e.functor e.inverse ≪≫
      isoWhiskerLeft P e.unitIso.symm ≪≫ P.rightUnitor
  obtain ⟨T, hT, _⟩ := sheetReturnExactFunctor D m hm X₀ l hl Ω
  have hS := sheetReturnPullbackRestriction D m hm X₀ l hl Ω T hT
  obtain ⟨c₀⟩ := restrictionSpecIso D m hm X₀ l hl Ω (P ⋙ T) R hS hR
  let c : G ⋙ T ≅ R := isoWhiskerRight U T ≪≫ c₀
  obtain ⟨a, ha⟩ := hT
  let b : G ⋙ constantExtensionHeartForget D l hl Ω
        (constantExtensionOriginalModel D m hm X₀) ⋙
          constantExtensionSheetPull D m hm X₀ l hl Ω ≅
      R ⋙ constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω
        (constantExtensionModel D m hm X₀) :=
    isoWhiskerLeft G a.symm ≪≫
      (Functor.associator G T
        (constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω
          (constantExtensionModel D m hm X₀))).symm ≪≫
      isoWhiskerRight c
        (constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω
          (constantExtensionModel D m hm X₀))
  let z := isoWhiskerLeft G
    (isoWhiskerLeft
      (constantExtensionHeartForget D l hl Ω (constantExtensionOriginalModel D m hm X₀))
      (constantExtensionZerothCoordinateIso D m hm X₀ l hl Ω)) ≪≫ b
  obtain ⟨γ, hγ0, hγs⟩ := isoChainNormalization m hm
    (fun i ↦ G ⋙ constantExtensionHeartForget D l hl Ω
      (constantExtensionOriginalModel D m hm X₀) ⋙
        constantExtensionSheetPullAt D m hm X₀ l hl Ω i)
    (R ⋙ constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω
      (constantExtensionModel D m hm X₀))
    (fun i j h ↦ coordinateStepIso D m hm X₀ l hl Ω G i j h) z
  refine ⟨γ, ?_, ?_⟩
  · intro F i j h
    have hs := congrArg (fun e ↦ e.hom.app F) (hγs i j h)
    simpa only [Iso.trans_hom, NatTrans.comp_app, coordinateStepIso_hom_app] using hs
  · intro F
    have hret :
        (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀) Ω).map (a.inv.app (G.obj F)) ≫
            (T.obj (G.obj F)).obj.str.hom =
          (constantExtensionReturnComparison D m hm X₀ l hl Ω (G.obj F).obj.carrier).hom ≫
            (constantExtensionSheetPull D m hm X₀ l hl Ω).map
              (constantExtensionWeilIterate D l hl Ω
                (constantExtensionOriginalModel D m hm X₀) (G.obj F).obj (m - 1)).hom ≫
            a.inv.app (G.obj F) := by
      simpa only [Iso.app_inv, Functor.comp_obj, heartForget_obj, Category.assoc] using
        isoSquare_inv
          (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
            (constantExtensionModel D m hm X₀) Ω)
          (a.app (G.obj F)) (T.obj (G.obj F)).obj.str.hom
          ((constantExtensionReturnComparison D m hm X₀ l hl Ω
              (G.obj F).obj.carrier).hom ≫
            (constantExtensionSheetPull D m hm X₀ l hl Ω).map
              (constantExtensionWeilIterate D l hl Ω
                (constantExtensionOriginalModel D m hm X₀) (G.obj F).obj (m - 1)).hom)
          (by simpa only [Iso.app_hom, Category.assoc] using ha (G.obj F))
    have hc := (c.hom.app F).hom.hom.h
    change (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
      (constantExtensionModel D m hm X₀) Ω).map
        ((c.hom.app F).hom.hom.f) ≫ (R.obj F).obj.str.hom =
      (T.obj (G.obj F)).obj.str.hom ≫ (c.hom.app F).hom.hom.f at hc
    have hz :
        (constantExtensionZerothCoordinateIso D m hm X₀ l hl Ω).inv.app
            (G.obj F).obj.carrier ≫ z.hom.app F = b.hom.app F := by
      simpa only [z, Functor.comp_obj, heartForget_obj] using
        whiskeredIsoCancel G
          (constantExtensionHeartForget D l hl Ω (constantExtensionOriginalModel D m hm X₀))
          (constantExtensionSheetPullAt D m hm X₀ l hl Ω ⟨0, hm⟩)
          (constantExtensionSheetPull D m hm X₀ l hl Ω)
          (R ⋙ constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω
            (constantExtensionModel D m hm X₀))
          (constantExtensionZerothCoordinateIso D m hm X₀ l hl Ω) b F
    have hb : b.hom.app F = a.inv.app (G.obj F) ≫ (c.hom.app F).hom.hom.f := by
      simpa only [b, heartForget_map] using whiskeredIsoCompose G T
        (constantExtensionHeartForget D l hl Ω (constantExtensionOriginalModel D m hm X₀) ⋙
          constantExtensionSheetPull D m hm X₀ l hl Ω)
        (constantExtensionHeartForget (constantExtensionDatum D m hm) l hl Ω
          (constantExtensionModel D m hm X₀)) R a c F
    simp only [hγ0, hz, hb]
    simpa only [Category.assoc] using mapCompSquare
      (sfCommonStageWeilFrobeniusPullback (constantExtensionDatum D m hm) l hl
        (constantExtensionModel D m hm X₀) Ω)
      (a.inv.app (G.obj F)) (c.hom.app F).hom.hom.f
      ((constantExtensionReturnComparison D m hm X₀ l hl Ω (G.obj F).obj.carrier).hom ≫
        (constantExtensionSheetPull D m hm X₀ l hl Ω).map
          (constantExtensionWeilIterate D l hl Ω
            (constantExtensionOriginalModel D m hm X₀) (G.obj F).obj (m - 1)).hom)
      (T.obj (G.obj F)).obj.str.hom (R.obj F).obj.str.hom
      (by simpa only [Category.assoc] using hret) hc



end ProofGlue

/-- Restriction is the distinguished-sheet return of actual Weil pullback, and its
cyclic normalization glues back to that pullback before any direct image.
Source: Deligne, Weil II, paragraph after (1.1.10), p.152.
(blueprint: lem-zl-constant-extension-pullback-return-residue)
Proof:
1. In the sheet coordinates h_i=H^i j_0 the actual pullback has carriers P^i M
and transitions P^i theta. This follows from pi h_i=g_X^i and the associativity
of integralPullbackComposition, retained by zlPullComp at common coefficient stages.
2. Apply cyclicReturnExactEquivalence to the actual constructible heart and its
exact Frobenius equivalence. The return has carrier M and the composite theta^[m];
its arrow on a Weil morphism is the original carrier map. This is exactly the
natural carrier comparison and equation of ConstantExtensionRestrictionSpec.
3. Exactness is detected on carriers in the source (cycle length one) and target
fixed-pair hearts. Restriction leaves the carrier unchanged, hence preserves kernels
and cokernels and therefore all finite limits and colimits.
4. Put the returned carrier on every coordinate, identity transitions before the
last, and its return map on the last. Glue by the sheet equivalence. The partial
products of the actual transition arrows give the natural Weil isomorphism to the
actual pullback. They give precisely the intermediate and return equations below.
For m=1 there are no intermediate transitions. Empty and disconnected schemes and
nonlisse constructible carriers need no modification. -/
theorem constantExtensionPullbackReturn :
    ∃ R : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
        sfCommonStageWeilSheaf (constantExtensionDatum D m hm) l hl
          (constantExtensionModel D m hm X₀) Ω,
      ConstantExtensionRestrictionSpec D m hm X₀ l hl Ω R ∧
      PreservesFiniteLimits R ∧ PreservesFiniteColimits R ∧
      ∃ G : sfCommonStageWeilSheaf D l hl X₀ Ω ⥤
          sfCommonStageWeilSheaf D l hl (constantExtensionOriginalModel D m hm X₀) Ω,
        ConstantExtensionPullbackNormalization D m hm X₀ l hl Ω R G ∧
        Nonempty (G ≅ zlWeilPull D l hl Ω (constantExtensionProjection D m hm X₀)) := by
  obtain ⟨e, hspec, hlim, hcol, hiso⟩ :=
    constantExtensionRestriction_data D m hm X₀ l hl Ω
  refine ⟨constantExtensionRestriction D m hm X₀ l hl Ω e, hspec, hlim, hcol, ?_⟩
  refine ⟨constantExtensionRestriction D m hm X₀ l hl Ω e ⋙ e.inverse, ?_, hiso⟩
  exact constantExtensionRestriction_normalization D m hm X₀ l hl Ω e hspec

set_option backward.isDefEq.respectTransparency false in
set_option linter.unusedSectionVars false in
/-- The actual residue embeddings agree on k_0.
Source: Stacks Project, Tag 01JT, applied to constant base change.
(blueprint: lem-zl-constant-extension-pullback-return-residue)
Proof: the two structural composites in the base-change square coincide. Functoriality
of residue-field maps and their base-field algebra maps gives the stated equality. -/
theorem constantExtensionResidue_compatible
    (z : (constantExtensionModel D m hm X₀).left) :
    CommRingCat.ofHom (X₀.hom.residueFieldAlgebraMap
        ((constantExtensionProjection D m hm X₀).left z)) ≫
        (constantExtensionProjection D m hm X₀).left.residueFieldMap z =
      CommRingCat.ofHom (D.extensionEmbedding m hm) ≫
        CommRingCat.ofHom ((constantExtensionModel D m hm X₀).hom.residueFieldAlgebraMap z) := by
  apply Spec.map_injective
  simp only [Spec.map_comp, Scheme.Hom.specMap_residueFieldAlgebraMap]
  rw [← Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    Category.assoc, (constantExtensionProjection D m hm X₀).w]
  rfl

/-- The tensor kappa(x) tensor_{k_0} k_m, as the commutative-ring pushout of its
specified base maps. This is the tensor product without any arbitrary algebra choices.
Source: Stacks Project, Tag 01JT.
(blueprint: lem-zl-constant-extension-pullback-return-residue) -/
def constantExtensionResidueTensor (z : (constantExtensionModel D m hm X₀).left) :
    CommRingCat :=
  pushout (CommRingCat.ofHom (X₀.hom.residueFieldAlgebraMap
    ((constantExtensionProjection D m hm X₀).left z)))
    (CommRingCat.ofHom (D.extensionEmbedding m hm))

/-- The tensor map to kappa(z), induced by both actual residue embeddings.
Source: Stacks Project, Tag 01JT.
(blueprint: lem-zl-constant-extension-pullback-return-residue) -/
def constantExtensionResidueTensorMap (z : (constantExtensionModel D m hm X₀).left) :
    constantExtensionResidueTensor D m hm X₀ z ⟶
      (constantExtensionModel D m hm X₀).left.residueField z :=
  pushout.desc ((constantExtensionProjection D m hm X₀).left.residueFieldMap z)
    (CommRingCat.ofHom ((constantExtensionModel D m hm X₀).hom.residueFieldAlgebraMap z))
    (constantExtensionResidue_compatible D m hm X₀ z)

private theorem finiteField_power_iff
    {B K : Type u} [Field B] [Fintype B] [Field K] [Finite K] [Algebra B K]
    (n : ℕ) :
    (∀ x : K, x ^ (Fintype.card B ^ n) = x) ↔ Module.finrank B K ∣ n := by
  rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic B K,
    orderOf_dvd_iff_pow_eq_one]
  constructor
  · intro h
    ext x
    simpa only [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, AlgEquiv.one_apply] using h x
  · intro h x
    have hx := DFunLike.congr_fun h x
    simpa only [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, AlgEquiv.one_apply] using hx

private theorem finiteField_compositum_finrank
    {B E F K : Type u} [Field B] [Finite B] [Field E] [Finite E]
    [Field F] [Finite F] [Field K] [Finite K]
    [Algebra B E] [Algebra B F] [Algebra B K]
    (e : E →+* K) (f : F →+* K)
    (hgen : Subfield.closure (Set.range e ∪ Set.range f) = ⊤) :
    Module.finrank B K = Nat.lcm (Module.finrank B E) (Module.finrank B F) := by
  let := Fintype.ofFinite B
  have hK := (finiteField_power_iff (B := B) (K := K)
    (Module.finrank B K)).mpr dvd_rfl
  have hd : Module.finrank B E ∣ Module.finrank B K := by
    apply (finiteField_power_iff (B := B) (K := E) _).mp
    intro x
    apply e.injective
    rw [map_pow, hK]
  have hf : Module.finrank B F ∣ Module.finrank B K := by
    apply (finiteField_power_iff (B := B) (K := F) _).mp
    intro x
    apply f.injective
    rw [map_pow, hK]
  apply Nat.dvd_antisymm _ (Nat.lcm_dvd hd hf)
  apply (finiteField_power_iff (B := B) (K := K) _).mp
  have hE := (finiteField_power_iff (B := B) (K := E)
    (Nat.lcm (Module.finrank B E) (Module.finrank B F))).mpr (Nat.dvd_lcm_left _ _)
  have hF := (finiteField_power_iff (B := B) (K := F)
    (Nat.lcm (Module.finrank B E) (Module.finrank B F))).mpr (Nat.dvd_lcm_right _ _)
  have heq :
      ((FiniteField.frobeniusAlgEquivOfAlgebraic B K) ^
        Nat.lcm (Module.finrank B E) (Module.finrank B F)).toRingHom = RingHom.id K := by
    apply RingHom.eq_of_eqOn_of_field_closure_eq_top hgen
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · change ((FiniteField.frobeniusAlgEquivOfAlgebraic B K) ^
        Nat.lcm (Module.finrank B E) (Module.finrank B F)) (e x) = e x
      simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate]
      rw [← map_pow, hE]
    · change ((FiniteField.frobeniusAlgEquivOfAlgebraic B K) ^
        Nat.lcm (Module.finrank B E) (Module.finrank B F)) (f x) = f x
      simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate]
      rw [← map_pow, hF]
  intro x
  have hx := DFunLike.congr_fun heq x
  change ((FiniteField.frobeniusAlgEquivOfAlgebraic B K) ^
    Nat.lcm (Module.finrank B E) (Module.finrank B F)) x = x at hx
  simpa only [AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic, pow_iterate] using hx

private theorem pushout_field_generated
    {B E F : CommRingCat.{u}} {K : Type u} [Field K]
    {a : B ⟶ E} {b : B ⟶ F} (e : E ⟶ CommRingCat.of K) (f : F ⟶ CommRingCat.of K)
    (h : a ≫ e = b ≫ f) (hs : Function.Surjective (pushout.desc e f h).hom) :
    Subfield.closure (Set.range e.hom ∪ Set.range f.hom) = ⊤ := by
  let C := Subfield.closure (Set.range e.hom ∪ Set.range f.hom)
  let g := pushout.desc e f h
  have hspan := CommRingCat.closure_range_union_range_eq_top_of_isPushout
    (IsPushout.of_hasPushout a b)
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨t, rfl⟩ := hs x
  have ht : t ∈ Subring.closure
      (Set.range (pushout.inl a b) ∪ Set.range (pushout.inr a b)) := by
    rw [hspan]
    trivial
  change g.hom t ∈ C
  induction ht using Subring.closure_induction with
  | mem y hy =>
    rcases hy with (⟨y, rfl⟩ | ⟨y, rfl⟩)
    · change (pushout.inl a b ≫ g).hom y ∈ C
      rw [pushout.inl_desc]
      exact Subfield.subset_closure (Or.inl ⟨y, rfl⟩)
    · change (pushout.inr a b ≫ g).hom y ∈ C
      rw [pushout.inr_desc]
      exact Subfield.subset_closure (Or.inr ⟨y, rfl⟩)
  | zero => simpa only [map_zero] using C.zero_mem
  | one => simpa only [map_one] using C.one_mem
  | add x y _ _ hx hy => simpa only [map_add] using C.add_mem hx hy
  | neg x _ hx => simpa only [map_neg] using C.neg_mem hx
  | mul x y _ _ hx hy => simpa only [map_mul] using C.mul_mem hx hy

/-- A closed residue field is the field quotient selected by its point and is generated
by the images of kappa(x) and k_m. Its total degree is lcm(d,m), its relative degree
is R/d=m/gcd(d,m), and its cardinality is the fth power of the old residue cardinality.
Source: Deligne, Weil II (1.1.8), p.151; Stacks Project, Tag 01JT and Fields Tag 09HY.
(blueprint: lem-zl-constant-extension-pullback-return-residue)
Proof:
1. A closed point has finite residue field by closedPoint_iff_residueField_trdeg_zero_and_finite.
Its subfield kappa(x) is finite too, so the same criterion makes x closed.
2. The fibre-product residue-field theorem identifies kappa(z) with the fraction field
of the tensor quotient selected by z. The tensor is finite over the finite base.
Its prime quotient is a finite domain, hence a field: multiplication by a nonzero
element is injective, hence surjective. Thus it already equals its fraction field.
The quotient map is the specified tensor map, so both actual embeddings are retained;
sums of products of their images exhaust the tensor and generate the residue field.
3. Geometric-free arithmetic q-Frobenius on kappa(z) has order R. Its restrictions
to the two generating subfields have orders d and m, by the finite-field Frobenius
order theorem. Therefore lcm(d,m) divides R and its power fixes both generators,
so R divides lcm(d,m). They are equal.
4. Module.finrank_mul_finrank gives R=fd. Since d,m are positive, the gcd-lcm
identity gives f=R/d=m/gcd(d,m). A basis over kappa(x) identifies the underlying
finite set with kappa(x)^f, giving the cardinality formula. The assertions are
vacuous for the empty scheme and include every nonsplit tensor component. -/
theorem constantExtensionResidueCompositum
    (z : {z : (constantExtensionModel D m hm X₀).left //
      z ∈ closedPoints (constantExtensionModel D m hm X₀).left}) :
    (constantExtensionProjection D m hm X₀).left z.val ∈ closedPoints X₀.left ∧
    IsField (constantExtensionResidueTensor D m hm X₀ z.val ⧸
      RingHom.ker (constantExtensionResidueTensorMap D m hm X₀ z.val).hom) ∧
    (∃ e : (constantExtensionResidueTensor D m hm X₀ z.val ⧸
        RingHom.ker (constantExtensionResidueTensorMap D m hm X₀ z.val).hom) ≃+*
          (constantExtensionModel D m hm X₀).left.residueField z.val,
      e.toRingHom.comp (Ideal.Quotient.mk
        (RingHom.ker (constantExtensionResidueTensorMap D m hm X₀ z.val).hom)) =
          (constantExtensionResidueTensorMap D m hm X₀ z.val).hom) ∧
    Subfield.closure
      (Set.range ((constantExtensionProjection D m hm X₀).left.residueFieldMap z.val).hom ∪
        Set.range ((constantExtensionModel D m hm X₀).hom.residueFieldAlgebraMap z.val)) = ⊤ ∧
    localClosedPointDegree D (constantExtensionOriginalModel D m hm X₀) z =
      Nat.lcm (localClosedPointDegree D X₀ (constantExtensionClosedImage D m hm X₀ z)) m ∧
    constantExtensionResidueDegree D m hm X₀ z.val =
      localClosedPointDegree D (constantExtensionOriginalModel D m hm X₀) z /
        localClosedPointDegree D X₀ (constantExtensionClosedImage D m hm X₀ z) ∧
    constantExtensionResidueDegree D m hm X₀ z.val =
      m / Nat.gcd (localClosedPointDegree D X₀ (constantExtensionClosedImage D m hm X₀ z)) m ∧
    Nat.card ((constantExtensionModel D m hm X₀).left.residueField z.val) =
      Nat.card (X₀.left.residueField (constantExtensionClosedImage D m hm X₀ z).val) ^
        constantExtensionResidueDegree D m hm X₀ z.val := by
  let E := X₀.left.residueField ((constantExtensionProjection D m hm X₀).left z.val)
  let K := (constantExtensionModel D m hm X₀).left.residueField z.val
  let F := D.extensionSubfield m hm
  let : Algebra F K :=
    ((constantExtensionModel D m hm X₀).hom.residueFieldAlgebraMap z.val).toAlgebra
  have : Module.Finite F K :=
    ((constantExtensionModel D m hm X₀).hom.finite_residueField_of_isClosed z.val z.prop)
  have : Finite F := (constantExtensionField_properties D m hm).1
  have : Finite K := Module.finite_of_finite F
  let e : E →+* K :=
    ((constantExtensionProjection D m hm X₀).left.residueFieldMap z.val).hom
  have : Finite E := Finite.of_injective e e.injective
  let : Algebra D.k₀ E :=
    (X₀.hom.residueFieldAlgebraMap ((constantExtensionProjection D m hm X₀).left z.val)).toAlgebra
  let : Algebra E K := e.toAlgebra
  let : Algebra D.k₀ K :=
    ((constantExtensionOriginalModel D m hm X₀).hom.residueFieldAlgebraMap z.val).toAlgebra
  let : Algebra D.k₀ F := (D.extensionEmbedding m hm).toAlgebra
  have htower : IsScalarTower D.k₀ E K := by
    apply IsScalarTower.of_algebraMap_eq'
    exact (congrArg (fun f ↦ f.residueFieldAlgebraMap z.val)
      (constantExtensionProjection D m hm X₀).w.symm).trans
        (Scheme.Hom.residueFieldAlgebraMap_comp
          (constantExtensionProjection D m hm X₀).left X₀.hom z.val)
  have hs : Function.Surjective (constantExtensionResidueTensorMap D m hm X₀ z.val).hom := by
    exact finiteFieldBaseChangeResidue_surjective (D.extensionEmbedding m hm) X₀.hom
      z.val z.prop (constantExtensionResidue_compatible D m hm X₀ z.val)
  have hgen := pushout_field_generated
    ((constantExtensionProjection D m hm X₀).left.residueFieldMap z.val)
    (CommRingCat.ofHom ((constantExtensionModel D m hm X₀).hom.residueFieldAlgebraMap z.val))
    (constantExtensionResidue_compatible D m hm X₀ z.val) hs
  let q := (constantExtensionResidueTensorMap D m hm X₀ z.val).hom.quotientKerEquivOfSurjective hs
  have hF : Module.finrank D.k₀ F = m := by
    apply Nat.pow_right_injective (a := Nat.card D.k₀)
      (Finite.one_lt_card (α := D.k₀))
    change Nat.card D.k₀ ^ Module.finrank D.k₀ F = Nat.card D.k₀ ^ m
    exact (Module.natCard_eq_pow_finrank (K := D.k₀) (V := F)).symm.trans
      ((constantExtensionField_properties D m hm).2.1.trans
        (congrArg (fun n : ℕ ↦ n ^ m) D.card_base.symm))
  have hdegree : localClosedPointDegree D (constantExtensionOriginalModel D m hm X₀) z =
      Nat.lcm (localClosedPointDegree D X₀ (constantExtensionClosedImage D m hm X₀ z)) m := by
    change Module.finrank D.k₀ K = Nat.lcm (Module.finrank D.k₀ E) m
    exact (finiteField_compositum_finrank e
      ((constantExtensionModel D m hm X₀).hom.residueFieldAlgebraMap z.val) hgen).trans
        (congrArg (Nat.lcm (Module.finrank D.k₀ E)) hF)
  have hdiv : constantExtensionResidueDegree D m hm X₀ z.val =
      localClosedPointDegree D (constantExtensionOriginalModel D m hm X₀) z /
        localClosedPointDegree D X₀ (constantExtensionClosedImage D m hm X₀ z) := by
    exact (Module.finrank_div_finrank_cancel_left D.k₀ E K Module.finrank_pos.ne').symm
  have hclosed : (constantExtensionProjection D m hm X₀).left z.val ∈
      closedPoints X₀.left :=
    (closedPoint_iff_residueField_trdeg_zero_and_finite X₀.hom _).2.1.mpr inferInstance
  refine ⟨hclosed,
    q.toMulEquiv.isField (Field.toIsField K), ⟨q, ?_⟩, hgen, hdegree, hdiv, ?_, ?_⟩
  · ext t
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hs t
  · let d := localClosedPointDegree D X₀ (constantExtensionClosedImage D m hm X₀ z)
    have hd : 0 < d := localClosedPointDegree_pos D X₀ _
    apply hdiv.trans
    apply (congrArg (fun n : ℕ ↦ n / d) hdegree).trans
    change Nat.lcm d m / d = m / Nat.gcd d m
    rw [Nat.lcm, Nat.mul_div_assoc d (Nat.gcd_dvd_right d m), Nat.mul_div_right _ hd]
  · exact Module.natCard_eq_pow_finrank (K := E) (V := K)

end WeilConjectures
