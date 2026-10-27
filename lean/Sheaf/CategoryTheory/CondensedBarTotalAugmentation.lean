/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q37
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation

/-! # Compatible derived bar columns and their total augmentation

Source: main-20261015, six-functors direct-image proof, paragraph (3), internal-bar
expansion; Stacks Tags 070Y, 070K, 079P, 0133 and 012X
(blueprint: lem-sfb-condensed-bar-total-augmentation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.CondensedBar

section DerivedHelpers
variable {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
  [HasDerivedCategory.{u + 2} C] [HasDerivedCategory.{u + 2} D]

/-- The explicit resolution witness used by the recorded arbitrary-quasi-isomorphism API.
Source: Stacks 079P (blueprint: lem-sfb-condensed-bar-total-augmentation). -/
abbrev barEnoughKInjectives (K : CochainComplex C ℤ) :
    ∃ (I : CochainComplex C ℤ) (s : K ⟶ I), I.IsKInjective ∧ QuasiIso s :=
  ⟨(CochainComplex.kInjectiveResolutionFunctor.{u + 1} C).obj K,
    (CochainComplex.toKInjectiveResolution.{u + 1} C).app K,
    inferInstance, (CochainComplex.monoQuasiIso_toKInjectiveResolution_app C K).2⟩

/-- The recorded total right derived functor, with no alternative derived construction.
Source: Stacks 070K (blueprint: lem-sfb-condensed-bar-total-augmentation). -/
abbrev barRightDerived (H : C ⥤ D) [H.Additive] :=
  H.rightDerivedFunctorOfQuasiIsoResolutions (barEnoughKInjectives (C := C))

/-- The recorded derived unit, transported from the homotopy quotient to ordinary Q.
Source: Stacks 070Y (blueprint: lem-sfb-condensed-bar-total-augmentation). -/
def barUnitAt (H : C ⥤ D) [H.Additive] (K : CochainComplex C ℤ) :
    DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (barRightDerived H).obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
    DerivedCategory.Qh.map ((H.mapHomotopyCategoryFactors (.up ℤ)).inv.app K) ≫
    (H.rightDerivedFunctorOfQuasiIsoResolutionsUnit
      (barEnoughKInjectives (C := C))).app ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
    (barRightDerived H).map ((DerivedCategory.quotientCompQhIso C).hom.app K)

/-- Derive an operator using the bijection of the recorded derived-unit universal property.
The bijection determines this transformation uniquely, including the first action face.
Source: Stacks 070K (blueprint: lem-sfb-condensed-bar-total-augmentation). -/
def barDerivedOperator {H J : C ⥤ D} [H.Additive] [J.Additive] (α : H ⟶ J) :
    barRightDerived H ⟶ barRightDerived J :=
  ((H.rightDerivedFunctorOfQuasiIsoResolutions_universal
    (barEnoughKInjectives (C := C)) (barRightDerived J)).surjective
      (Functor.whiskerRight (α.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh ≫
        J.rightDerivedFunctorOfQuasiIsoResolutionsUnit
          (barEnoughKInjectives (C := C)))).choose

private theorem barOperator_equation {H J : C ⥤ D} [H.Additive] [J.Additive]
    (α : H ⟶ J) :
    H.rightDerivedFunctorOfQuasiIsoResolutionsUnit (barEnoughKInjectives (C := C)) ≫
        Functor.whiskerLeft DerivedCategory.Qh (barDerivedOperator α) =
      Functor.whiskerRight (α.mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh ≫
        J.rightDerivedFunctorOfQuasiIsoResolutionsUnit (barEnoughKInjectives (C := C)) := by
  exact ((H.rightDerivedFunctorOfQuasiIsoResolutions_universal
    (barEnoughKInjectives (C := C)) (barRightDerived J)).surjective _).choose_spec

private theorem barUnitAt_isIso (H : C ⥤ D) [H.Additive]
    (K : CochainComplex C ℤ) [K.IsKInjective] : IsIso (barUnitAt H K) := by
  have := H.rightDerivedFunctorOfQuasiIsoResolutionsUnit_isIso
    (barEnoughKInjectives (C := C)) K
  dsimp [barUnitAt]
  infer_instance

private theorem barDerivedOperator_id (H : C ⥤ D) [H.Additive] :
    barDerivedOperator (𝟙 H) = 𝟙 (barRightDerived H) := by
  apply (H.rightDerivedFunctorOfQuasiIsoResolutions_universal
    (barEnoughKInjectives (C := C)) _).injective
  dsimp only
  rw [barOperator_equation]
  simp

private theorem barDerivedOperator_comp {H J L : C ⥤ D}
    [H.Additive] [J.Additive] [L.Additive] (α : H ⟶ J) (β : J ⟶ L) :
    barDerivedOperator (α ≫ β) = barDerivedOperator α ≫ barDerivedOperator β := by
  apply (H.rightDerivedFunctorOfQuasiIsoResolutions_universal
    (barEnoughKInjectives (C := C)) _).injective
  dsimp only
  rw [Functor.whiskerLeft_comp, ← Category.assoc, barOperator_equation]
  simp only [Category.assoc, barOperator_equation, NatTrans.mapHomotopyCategory_comp,
    Functor.whiskerRight_comp]

set_option backward.isDefEq.respectTransparency.types false in
private theorem barUnitAt_operator {H J : C ⥤ D} [H.Additive] [J.Additive]
    (α : H ⟶ J) (K : CochainComplex C ℤ) :
    barUnitAt H K ≫ (barDerivedOperator α).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app K) ≫
        barUnitAt J K := by
  have he := congrArg (fun f ↦ f.app ((HomotopyCategory.quotient C (.up ℤ)).obj K))
    (barOperator_equation α)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at he
  change
    (H.rightDerivedFunctorOfQuasiIsoResolutionsUnit
      (barEnoughKInjectives (C := C))).app
        ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
      (barDerivedOperator α).app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj K)) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex α (.up ℤ)).app K)) ≫
      (J.rightDerivedFunctorOfQuasiIsoResolutionsUnit
        (barEnoughKInjectives (C := C))).app
          ((HomotopyCategory.quotient C (.up ℤ)).obj K) at he
  have hf (L : C ⥤ D) [L.Additive] : barUnitAt L K =
      (DerivedCategory.quotientCompQhIso D).inv.app
          ((L.mapHomologicalComplex (.up ℤ)).obj K) ≫
        (L.rightDerivedFunctorOfQuasiIsoResolutionsUnit
          (barEnoughKInjectives (C := C))).app
            ((HomotopyCategory.quotient C (.up ℤ)).obj K) ≫
        (barRightDerived L).map ((DerivedCategory.quotientCompQhIso C).hom.app K) := by
    unfold barUnitAt
    change _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ _ ≫ _ = _
    simp only [Functor.map_id, Category.id_comp]
  rw [hf H, hf J]
  simp only [Category.assoc]
  erw [(barDerivedOperator α).naturality]
  have he' := congrArg (fun f ↦
    (DerivedCategory.quotientCompQhIso D).inv.app
      ((H.mapHomologicalComplex (.up ℤ)).obj K) ≫ f ≫
    (barRightDerived J).map ((DerivedCategory.quotientCompQhIso C).hom.app K)) he
  simpa only [Category.assoc,
    DerivedCategory.quotientCompQhIso_inv_naturality_assoc] using he'


private def barComparison (H : C ⥤ D) [H.Additive]
    {K I : CochainComplex C ℤ} [I.IsKInjective] (s : K ⟶ I) [QuasiIso s] :
    (barRightDerived H).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj I) := by
  have := barUnitAt_isIso H I
  exact (barRightDerived H).mapIso (asIso (DerivedCategory.Q.map s)) ≪≫
    (asIso (barUnitAt H I)).symm

private theorem barComparison_operator {H J : C ⥤ D} [H.Additive] [J.Additive]
    (α : H ⟶ J) {K I : CochainComplex C ℤ} [I.IsKInjective]
    (s : K ⟶ I) [QuasiIso s] :
    (barDerivedOperator α).app (DerivedCategory.Q.obj K) ≫ (barComparison J s).hom =
      (barComparison H s).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app I) := by
  have := barUnitAt_isIso H I
  have := barUnitAt_isIso J I
  dsimp [barComparison]
  simp only [Category.assoc]
  rw [← cancel_mono (barUnitAt J I)]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← barUnitAt_operator, IsIso.inv_hom_id_assoc]
  exact ((barDerivedOperator α).naturality (DerivedCategory.Q.map s)).symm

omit [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 2} C]
  [HasDerivedCategory.{u + 2} D] in
private theorem barExtend_operator {H J : C ⥤ D} [H.Additive] [J.Additive]
    (α : H ⟶ J) (I : CochainComplex C ℕ) :
    (I.mapExtendIso ComplexShape.embeddingUpNat H).hom ≫
        HomologicalComplex.extendMap
          ((NatTrans.mapHomologicalComplex α (.up ℕ)).app I)
          ComplexShape.embeddingUpNat =
      (NatTrans.mapHomologicalComplex α (.up ℤ)).app
          (I.extend ComplexShape.embeddingUpNat) ≫
        (I.mapExtendIso ComplexShape.embeddingUpNat J).hom := by
  have h (o : Option ℕ) :
      (HomologicalComplex.mapExtendX I H o).hom ≫
        HomologicalComplex.extend.mapX
          ((NatTrans.mapHomologicalComplex α (.up ℕ)).app I) o =
      α.app (HomologicalComplex.extend.X I o) ≫
        (HomologicalComplex.mapExtendX I J o).hom := by
    cases o with
    | none => exact (isZero_zero D).eq_of_tgt _ _
    | some k =>
        simp [HomologicalComplex.mapExtendX, HomologicalComplex.extend.mapX,
          HomologicalComplex.extend.X]
  apply HomologicalComplex.hom_ext
  intro n
  exact h (ComplexShape.embeddingUpNat.r n)

end DerivedHelpers

variable {A : Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {F : InternalFunctions A} (B : BarDiagram (G := G) F)

/-- Evaluation of the actual cosimplicial diagram at the indicated bar degree.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-bar-total-augmentation). -/
def barColumn (p : ℕ) : Equivariant A G ⥤ Modules A :=
  B.diagram ⋙ (evaluation SimplexCategory (Modules A)).obj (SimplexCategory.mk p)

/-- Evaluation preserves the recorded additive bar maps.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-bar-total-augmentation). -/
instance barColumn_additive (p : ℕ) : (barColumn B p).Additive where
  map_add := by
    intros N P f g
    exact B.maps_additive f g p

/-- All cosimplicial operators, taken from the one actual equivariant diagram.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-bar-total-augmentation). -/
def barOperator {p r : ℕ} (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk r) :
    barColumn B p ⟶ barColumn B r where
  app N := (B.diagram.obj N).map θ
  naturality _ _ f := ((B.diagram.map f).naturality θ).symm

/-- The column functor is precisely second-variable internal Hom after forgetting the action.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-bar-total-augmentation). -/
def barColumnInternalIso (p : ℕ) :
    barColumn B p ≅ forgetAction ⋙ F.functor (power G p) :=
  NatIso.ofComponents (fun N ↦ B.term N p) (fun f ↦ B.maps f p)

/-- The vertical complex is the actual column of the specified double complex.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-bar-total-augmentation). -/
def barColumnComplexIso (p : ℕ) (I : CochainComplex (Equivariant A G) ℕ) :
    ((barColumn B p).mapHomologicalComplex (.up ℕ)).obj I ≅ (doubleComplex B I).X p :=
  Iso.refl _

/-- Canonical passage from degreewise column evaluation to the actual extended column.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-bar-total-augmentation). -/
def barExtendedColumnIso (p : ℕ) [HasZeroObject (Equivariant A G)]
    (I : CochainComplex (Equivariant A G) ℕ) :
    ((barColumn B p).mapHomologicalComplex (.up ℤ)).obj
        (I.extend ComplexShape.embeddingUpNat) ≅ extend ((doubleComplex B I).X p) :=
  HomologicalComplex.mapExtendIso I ComplexShape.embeddingUpNat (barColumn B p) ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (Modules A)).mapIso (barColumnComplexIso B p I)

/-- The internal-Hom identification on the whole vertical complex, with its action forgotten.
Source: blueprint paragraph (3) (blueprint: lem-sfb-condensed-bar-total-augmentation). -/
def barInternalColumnIso (p : ℕ) (I : CochainComplex (Equivariant A G) ℤ) :
    ((barColumn B p).mapHomologicalComplex (.up ℤ)).obj I ≅
      ((F.functor (power G p)).mapHomologicalComplex (.up ℤ)).obj
        ((forgetAction.mapHomologicalComplex (.up ℤ)).obj I) :=
  (NatIso.mapHomologicalComplex (barColumnInternalIso B p) (.up ℤ)).app I

variable [ActionAbelian A G] [IsGrothendieckAbelian.{u + 1} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Equivariant A G)]
  [HasDerivedCategory.{u + 2} (Modules A)]

/-- One specified resolution computes all derived columns, with the entire derived
cosimplicial diagram, and its actual invariant augmentation is a quasi-isomorphism.
Source: main-20261015 direct-image proof, paragraph (3), internal-bar expansion;
Stacks Tags 070Y, 070K, 079P, 0133 and 012X
(blueprint: lem-sfb-condensed-bar-total-augmentation).

Proof plan (the eight steps of the node).
1. Postcomposition by each equivariant resolution differential commutes with every
   cosimplicial operator. For the first face this is equivariance; the other faces and
   degeneracies are substitution of profinite parameters. Hence the two differentials
   commute, and their squares vanish by the complex and cosimplicial identities.
2. Exactness and preservation of injectives by U make UI a bounded-below injective
   resolution. Both I and UI are K-injective by
   lem-weil-pbc-bounded-below-injectives-kinjective. Grothendieck abelianness supplies
   resolutions of arbitrary complexes by lem-pur-kinjective-degreewise-existence.
3. Apply def-sfb-right-derived-functor to H_p and B_p. Its units on I and UI are
   invertible. Localizing a and Ua and inverting these units gives the displayed e_p
   and c_p. The displayed normalizations identify the actual columns, not just cohomology.
4. The derived-unit universal bijection defines every derived cosimplicial operator.
   Uniqueness gives its identity and composition laws, including the first action face.
5. Naturality at Qa and the unit equation give the displayed compatibility of e_p.
   Transport along e_p followed by c_p inverse gives the compatible RH_p columns.
6. Invariant inclusion commutes with the vertical differential; the horizontal
   differential kills it, since g acts identically on sections fixed after all base
   changes. The bar-zero coprojection, whose vertical sign is +1, gives the actual b_I.
7. The row hypothesis is equivalently that each single-object row augmentation is
   a quasi-isomorphism. Apply lem-sc-first-quadrant-column-augmentation to that actual
   map. Localization inverts its extension by zero in the ordinary derived category.
8. The diagonal p+q=n has n+1 pairs. The signed transpose multiplies each (p,q)
   summand by (-1)^(pq); the horizontal and vertical chain equations follow from
   s_(p+1,q)=(-1)^q s_(p,q) and (-1)^p s_(p,q+1)=s_(p,q). Its inverse has the same signs.
-/
theorem condensed_bar_total_augmentation
    [PreservesFiniteLimits (forgetAction (A := A) (G := G))]
    [PreservesFiniteColimits (forgetAction (A := A) (G := G))]
    [(forgetAction (A := A) (G := G)).PreservesInjectiveObjects]
    (V : Invariants A G) [PreservesFiniteLimits V.functor]
    (a : Augmentation V B) (t : TotalAugmentation V B a)
    {N : Equivariant A G} (I : InjectiveResolution N)
    (hrows : ∀ q : ℕ, QuasiIso (a.map.app (I.cocomplex.X q))) :
    (∀ p q : ℕ,
      ((doubleComplex B I.cocomplex).d p (p + 1)).f q ≫
          ((doubleComplex B I.cocomplex).X (p + 1)).d q (q + 1) =
        ((doubleComplex B I.cocomplex).X p).d q (q + 1) ≫
          ((doubleComplex B I.cocomplex).d p (p + 1)).f (q + 1)) ∧
    (∀ p : ℕ, IsIso (barUnitAt (barColumn B p) I.cochainComplex)) ∧
    (∀ p : ℕ, IsIso (barUnitAt (F.functor (power G p))
      ((forgetAction.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex))) ∧
    (∃ (e : ∀ p : ℕ,
        (barRightDerived (barColumn B p)).obj (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (Equivariant A G) 0).obj N)) ≅
          DerivedCategory.Q.obj (extend ((doubleComplex B I.cocomplex).X p)))
      (c : ∀ p : ℕ,
        (barRightDerived (F.functor (power G p))).obj (DerivedCategory.Q.obj
          ((forgetAction.mapHomologicalComplex (.up ℤ)).obj
            ((CochainComplex.singleFunctor (Equivariant A G) 0).obj N))) ≅
          DerivedCategory.Q.obj (extend ((doubleComplex B I.cocomplex).X p))),
      (∀ p : ℕ,
        (e p).hom ≫ (DerivedCategory.Q.mapIso
          (barExtendedColumnIso B p I.cocomplex)).inv ≫
            barUnitAt (barColumn B p) I.cochainComplex =
          (barRightDerived (barColumn B p)).map (DerivedCategory.Q.map I.ι')) ∧
      (∀ p : ℕ,
        (c p).hom ≫ (DerivedCategory.Q.mapIso
          (barExtendedColumnIso B p I.cocomplex)).inv ≫
            (DerivedCategory.Q.mapIso (barInternalColumnIso B p I.cochainComplex)).hom ≫
              barUnitAt (F.functor (power G p))
                ((forgetAction.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) =
          (barRightDerived (F.functor (power G p))).map (DerivedCategory.Q.map
            ((forgetAction.mapHomologicalComplex (.up ℤ)).map I.ι'))) ∧
      (∀ (p r : ℕ) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk r),
        (barDerivedOperator (barOperator B θ)).app
            (DerivedCategory.Q.obj
              ((CochainComplex.singleFunctor (Equivariant A G) 0).obj N)) ≫ (e r).hom =
          (e p).hom ≫ DerivedCategory.Q.map
            (HomologicalComplex.extendMap
              ((NatTrans.mapHomologicalComplex (barOperator B θ) (.up ℕ)).app I.cocomplex)
              ComplexShape.embeddingUpNat))) ∧
    (∀ (p r : ℕ) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk r)
      (K : CochainComplex (Equivariant A G) ℤ),
      barUnitAt (barColumn B p) K ≫
          (barDerivedOperator (barOperator B θ)).app (DerivedCategory.Q.obj K) =
        DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (barOperator B θ) (.up ℤ)).app K) ≫
          barUnitAt (barColumn B r) K) ∧
    (∀ p : ℕ, barDerivedOperator (barOperator B (𝟙 (SimplexCategory.mk p))) =
      𝟙 (barRightDerived (barColumn B p))) ∧
    (∀ (p r s : ℕ) (θ : SimplexCategory.mk p ⟶ SimplexCategory.mk r)
      (ψ : SimplexCategory.mk r ⟶ SimplexCategory.mk s),
      barDerivedOperator (barOperator B (θ ≫ ψ)) =
        barDerivedOperator (barOperator B θ) ≫ barDerivedOperator (barOperator B ψ)) ∧
    QuasiIso (t.map.app I.cocomplex) ∧
    IsIso (DerivedCategory.Q.map
      (HomologicalComplex.extendMap (t.map.app I.cocomplex) ComplexShape.embeddingUpNat)) ∧
    (∀ p q n : ℕ, ∀ h : p + q = n,
      (doubleComplex B I.cocomplex).ιTotal (.up ℕ) p q n h ≫
          ((doubleComplex B I.cocomplex).totalFlipIso (.up ℕ)).inv.f n =
        ((-1 : ℤˣ) ^ (p * q)) •
          (doubleComplex B I.cocomplex).flip.ιTotal (.up ℕ) q p n (by change q + p = n; omega)) ∧
    (∀ n : ℕ, Nat.card {pq : ℕ × ℕ // pq.1 + pq.2 = n} = n + 1) := by
  classical
  have hI : I.cochainComplex.IsKInjective := by
    dsimp only [InjectiveResolution.cochainComplex]
    infer_instance
  have hterms (n : ℤ) : Injective
      (((forgetAction (A := A) (G := G)).mapHomologicalComplex (.up ℤ)).obj
        I.cochainComplex |>.X n) := by
    change Injective (forgetAction.obj (I.cochainComplex.X n))
    exact Functor.injective_obj forgetAction _
  have hUI : CochainComplex.IsKInjective
      ((forgetAction.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) :=
    CochainComplex.isKInjective_of_injective _ 0
  have hu (p : ℕ) := barUnitAt_isIso (barColumn B p) I.cochainComplex
  have hv (p : ℕ) := barUnitAt_isIso (F.functor (power G p))
    ((forgetAction.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)
  let K := doubleComplex B I.cocomplex
  let j : (V.functor.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K.X 0 :=
    { f := fun n ↦ (a.map.app (I.cocomplex.X n)).f 0
      comm' := by
        intro n m h
        exact congrArg (fun f ↦ f.f 0) (a.map.naturality (I.cocomplex.d n m)).symm }
  have hj : j ≫ K.d 0 1 = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    change (a.map.app (I.cocomplex.X n)).f 0 ≫
      ((cochains B).obj (I.cocomplex.X n)).d 0 1 = 0
    rw [(a.map.app (I.cocomplex.X n)).comm]
    change ((CochainComplex.single₀ (Modules A)).obj _).d 0 1 ≫ _ = 0
    rw [HomologicalComplex.single_obj_d, zero_comp]
  have ht : QuasiIso (t.map.app I.cocomplex) := by
    apply HomologicalComplex₂.quasiIso_of_column_augmentation K _ j hj _
      (t.components I.cocomplex)
    intro n
    have he : (CochainComplex.fromSingle₀Equiv (K.flip.X n) _).symm
        ⟨j.f n, by simpa using congrArg (fun f ↦ f.f n) hj⟩ =
        a.map.app (I.cocomplex.X n) := by
      apply (CochainComplex.fromSingle₀Equiv (K.flip.X n) _).injective
      rfl
    rw [he]
    exact hrows n
  refine ⟨?_, hu, hv, ?_, ?_, ?_, ?_, ht, ?_, ?_, ?_⟩
  · intro p q
    exact (K.d p (p + 1)).comm q (q + 1)
  · let e := fun p ↦ barComparison (barColumn B p) I.ι' ≪≫
      DerivedCategory.Q.mapIso (barExtendedColumnIso B p I.cocomplex)
    let c := fun p ↦ barComparison (F.functor (power G p))
        ((forgetAction.mapHomologicalComplex (.up ℤ)).map I.ι') ≪≫
      DerivedCategory.Q.mapIso (barInternalColumnIso B p I.cochainComplex).symm ≪≫
      DerivedCategory.Q.mapIso (barExtendedColumnIso B p I.cocomplex)
    refine ⟨e, c, ?_, ?_, ?_⟩
    · intro p
      simp [e, barComparison, Category.assoc]
    · intro p
      simp [c, barComparison, Category.assoc]
    · intro p r θ
      have he := barComparison_operator (barOperator B θ) I.ι'
      have hx := congrArg DerivedCategory.Q.map
        (barExtend_operator (barOperator B θ) I.cocomplex)
      simp only [Functor.map_comp] at hx
      dsimp only [e, Iso.trans_hom, Functor.mapIso_hom]
      rw [← Category.assoc, he]
      simp only [Category.assoc]
      apply congrArg ((barComparison (barColumn B p) I.ι').hom ≫ ·)
      have hz (p : ℕ) : (barExtendedColumnIso B p I.cocomplex).hom =
          (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (barColumn B p)).hom := by
        change _ ≫ (ComplexShape.embeddingUpNat.extendFunctor (Modules A)).map
          (𝟙 _) = _
        simp only [Functor.map_id, Category.comp_id]
      simpa only [hz, InjectiveResolution.cochainComplex] using hx.symm
  · intro p r θ L
    exact barUnitAt_operator (barOperator B θ) L
  · intro p
    have he : barOperator B (𝟙 (SimplexCategory.mk p)) = 𝟙 (barColumn B p) := by
      apply NatTrans.ext
      funext N
      exact (B.diagram.obj N).map_id _
    rw [he, barDerivedOperator_id]
  · intro p r s θ ψ
    have he : barOperator B (θ ≫ ψ) = barOperator B θ ≫ barOperator B ψ := by
      apply NatTrans.ext
      funext N
      exact (B.diagram.obj N).map_comp θ ψ
    rw [he, barDerivedOperator_comp]
  · have := ht
    infer_instance
  · intro p q n h
    exact HomologicalComplex₂.ιTotal_totalFlipIso_f_inv K (.up ℕ) p q n h
  · intro n
    let e : {pq : ℕ × ℕ // pq.1 + pq.2 = n} ≃ Fin (n + 1) :=
      { toFun := fun x ↦ ⟨x.val.1, by omega⟩
        invFun := fun i ↦ ⟨(i.val, n - i.val), by omega⟩
        left_inv := by
          rintro ⟨⟨p, q⟩, h⟩
          apply Subtype.ext
          apply Prod.ext
          · rfl
          · dsimp
            omega
        right_inv := by intro i; rfl }
    simpa using Nat.card_congr e

end CategoryTheory.CondensedBar
