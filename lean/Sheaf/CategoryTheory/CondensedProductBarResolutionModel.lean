/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.CategoryTheory.CondensedProductBarComparison
public import Sheaf.CategoryTheory.CondensedBarTotalAugmentation
public import Sheaf.CategoryTheory.CondensedInjectiveBarRows
import Sheaf.CategoryTheory.CondensedProductBarCoordinates
import Sheaf.CategoryTheory.CondensedProductBarAugmentation
import Sheaf.CategoryTheory.CondensedActionInjectiveRestriction

/-! # One resolution for the product internal bar

Source: current blueprint direct-image stability, paragraph (3), formal internal-bar
expansion (blueprint: lem-sfb-condensed-product-bar-resolution-model).

The existing `ProductBar` specifies every operator on all profinite test objects.
Only those definitions are used from the downstream comparison module, never its theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction

namespace CategoryTheory.CondensedBar

section DerivedHelpers
variable {C D : Type (u + 2)} [Category.{u + 1} C] [Category.{u + 1} D]
  [Abelian C] [Abelian D] [IsGrothendieckAbelian.{u + 1} C]
  [HasDerivedCategory.{u + 2} C] [HasDerivedCategory.{u + 2} D]

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

end DerivedHelpers

variable {A : Ring.{u}} {G H : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]

/-- The profinite parameter of a product-bar column.
Source: paragraph (3) (blueprint: lem-sfb-condensed-product-bar-resolution-model). -/
abbrev productParameter (G H : Type u) [TopologicalSpace G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] [TopologicalSpace H] [CompactSpace H]
    [T2Space H] [TotallyDisconnectedSpace H] (a b : ℕ) : Profinite.{u} :=
  Profinite.of ((Fin a → G) × (Fin b → H))

/-- Evaluate the existing product diagram at one pair of group degrees.
Source: paragraph (3) (blueprint: lem-sfb-condensed-product-bar-resolution-model). -/
abbrev productColumn (B : ProductBar A.toMon G H) (a b : ℕ) :=
  B.cochains ⋙ productBarEvaluation A.toMon a b

/-- Every pair of simplex maps acts on the same coefficient functor.
Source: paragraph (3) (blueprint: lem-sfb-condensed-product-bar-resolution-model). -/
def productOperator (B : ProductBar A.toMon G H) {a b c d : ℕ}
    (θ : SimplexCategory.mk a ⟶ SimplexCategory.mk c)
    (ψ : SimplexCategory.mk b ⟶ SimplexCategory.mk d) :
    productColumn B a b ⟶ productColumn B c d where
  app N := ((B.cochains.obj N).map θ).app _ ≫
    ((B.cochains.obj N).obj (SimplexCategory.mk c)).map ψ
  naturality _ _ f := by cat_disch

/-- The product diagonal, retaining all cofaces and codegeneracies as simplex maps.
Source: paragraph (3) (blueprint: lem-sfb-condensed-product-bar-resolution-model). -/
abbrev productDiagonal (B : ProductBar A.toMon G H) :
    Equivariant A (G × H) ⥤ CosimplicialObject (Modules A) :=
  B.cochains ⋙ Functor.uncurry ⋙
    (Functor.whiskeringLeft _ _ _).obj (Functor.diag SimplexCategory)

/-- The graph used to evaluate a section of the represented product internal Hom.
Source: paragraph (3) (blueprint: lem-sfb-condensed-product-bar-resolution-model). -/
def productGraph {S T : Profinite.{u}} (f : T ⟶ S) {a b : ℕ}
    (g : Fin a → C(T, G)) (h : Fin b → C(T, H)) :
    T ⟶ productBarParameters G H S a b :=
  ConcreteCategory.ofHom
    (f.hom.hom.prodMk ((tupleMap g).prodMk (tupleMap h)))

/-- Pair continuous maps into the Cartesian product profinite parameter.
Source: paragraph (3) (blueprint: lem-sfb-condensed-product-bar-resolution-model). -/
def pairParameter {P Q T : Profinite.{u}} (g : C(T, P)) (h : C(T, Q)) :
    C(T, Profinite.of (P × Q)) := g.prodMk h

/-- A model with every term, coordinate change, derived column and augmentation fixed.
The bicosimplicial identities and commutation with the resolution differential are
encoded by the functor to two simplex categories, evaluated on the one complex I.
Source: paragraph (3), all product-resolution-model clauses
(blueprint: lem-sfb-condensed-product-bar-resolution-model). -/
structure ProductResolutionModel (F : InternalFunctions A)
    (V : Invariants A (G × H)) (B : ProductBar A.toMon G H)
    [HasDerivedCategory.{u + 2} (Modules A)]
    [HasDerivedCategory.{u + 2} (Equivariant A (G × H))]
    {N : Equivariant A (G × H)} (I : InjectiveResolution N) where
  /-- The free-product identification is natural in both parameters and generator normalized. -/
  freeProduct : ∀ P Q : Profinite.{u},
    freeParameter A (Profinite.of (P × Q)) ≅ freeParameter A P ⊗ freeParameter A Q
  /-- On every generalized generator the identification sends [(p,q)] to [p] tensor [q]. -/
  freeProduct_generator : ∀ (P Q S : Profinite.{u}) (p : S ⟶ P) (q : S ⟶ Q),
    ((freeProduct P Q).hom.hom.hom.app (op S))
        (parameterGenerator A (Profinite.of (P × Q)) S
          (ConcreteCategory.ofHom (p.hom.hom.prodMk q.hom.hom))) =
      Profinite.CondensedAction.InternalBar.pureTensor A.toMon _ _ S
        (parameterGenerator A P S p) (parameterGenerator A Q S q)
  /-- Currying is natural in the module variable. -/
  curryIso : ∀ P Q : Profinite.{u},
    F.functor (Profinite.of (P × Q)) ≅ F.functor Q ⋙ F.functor P
  /-- Currying has the specified evaluation on all base changes, not an arbitrary iso. -/
  curry_evaluate : ∀ (P Q S : Profinite.{u}) (M : Modules A)
    (x : sections A ((F.functor (Profinite.of (P × Q))).obj M) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : C(T, P))
    (W : Profinite.{u}) (k : W ⟶ T) (h : C(W, Q)),
    (F.evaluate Q T M
      ((F.evaluate P S ((F.functor Q).obj M)
        (((curryIso P Q).hom.app M).hom.hom.app (op S) x)).val T f g)).val W k h =
      (F.evaluate (Profinite.of (P × Q)) S M x).val W (k ≫ f)
        (pairParameter (g.comp k.hom.hom) h)
  /-- Each bidegree is the actual second-variable internal Hom functor. -/
  columnIso : ∀ a b : ℕ,
    productColumn B a b ≅ forgetAction ⋙ F.functor (productParameter G H a b)
  /-- The column identification agrees with the normalized represented-section formula. -/
  column_evaluate : ∀ (M : Equivariant A (G × H)) (a b : ℕ) (S : Profinite.{u})
    (x : sections A ((productColumn B a b).obj M) S)
    (T : Profinite.{u}) (f : T ⟶ S)
    (g : Fin a → C(T, G)) (h : Fin b → C(T, H)),
    (F.evaluate (productParameter G H a b) S M.module
      (((columnIso a b).hom.app M).hom.hom.app (op S) x)).val T f
        (pairParameter (tupleMap g) (tupleMap h)) =
      M.module.X.obj.map (productGraph f g h).op (B.sections M a b S x)
  /-- The product single-group bar, with all of its specified inhomogeneous operators. -/
  singleBar : BarDiagram (G := G × H) F
  /-- Coordinate reordering is an isomorphism of complete cosimplicial diagrams. -/
  diagonalIso : productDiagonal B ≅ singleBar.diagram
  /-- The diagonal identification is the coordinate reordering on internal functions. -/
  diagonal_evaluate : ∀ (M : Equivariant A (G × H)) (n : ℕ) (S : Profinite.{u})
    (x : sections A ((productColumn B n n).obj M) S)
    (T : Profinite.{u}) (f : T ⟶ S) (g : Fin n → C(T, G × H)),
    (F.evaluate (power (G × H) n) S M.module
      ((((diagonalIso.hom.app M).app (SimplexCategory.mk n) ≫
        (singleBar.term M n).hom).hom.hom.app (op S)) x)).val T f (tupleMap g) =
      M.module.X.obj.map (productGraph f
        (fun i ↦ ContinuousMap.fst.comp (g i))
        (fun i ↦ ContinuousMap.snd.comp (g i))).op (B.sections M n n S x)
  /-- The actual invariant inclusion supported in group degree zero. -/
  augmentation : (V.functor.mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
    B.diagonalTotal I.cocomplex
  /-- Every component is exactly the specified invariant inclusion and zero summand. -/
  augmentation_f : ∀ q : ℕ, augmentation.f q =
    V.inclusion.app (I.cocomplex.X q) ≫ B.augmentation.app (I.cocomplex.X q) ≫
      B.diagonalZero I.cocomplex q
  /-- Its actual chain map is a quasi-isomorphism. -/
  augmentation_quasiIso : QuasiIso augmentation
  /-- Every column comparison is simultaneously normalized by the same derived unit. -/
  column_unit : ∀ a b : ℕ, IsIso (barUnitAt (F.functor (productParameter G H a b))
    ((forgetAction.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex))
  /-- Derived columns for the whole equivariant coefficient functors. -/
  resolvedColumn : ∀ a b : ℕ,
    (barRightDerived (productColumn B a b)).obj (DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor (Equivariant A (G × H)) 0).obj N)) ≅
    DerivedCategory.Q.obj (((productColumn B a b).mapHomologicalComplex (.up ℤ)).obj
      I.cochainComplex)
  /-- The actual column comparisons use the localization of the given resolution map. -/
  resolvedColumn_normalization : ∀ a b : ℕ,
    (resolvedColumn a b).hom ≫ barUnitAt (productColumn B a b) I.cochainComplex =
      (barRightDerived (productColumn B a b)).map (DerivedCategory.Q.map I.ι')
  /-- Derived internal Hom is in its second variable, on the forgotten module N[0]. -/
  internalColumn : ∀ a b : ℕ,
    (barRightDerived (F.functor (productParameter G H a b))).obj
      (DerivedCategory.Q.obj ((forgetAction.mapHomologicalComplex (.up ℤ)).obj
        ((CochainComplex.singleFunctor (Equivariant A (G × H)) 0).obj N))) ≅
    DerivedCategory.Q.obj (((productColumn B a b).mapHomologicalComplex (.up ℤ)).obj
      I.cochainComplex)
  /-- The internal comparison is also the specified derived-unit comparison. -/
  internalColumn_normalization : ∀ a b : ℕ,
    (internalColumn a b).hom ≫ DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex (columnIso a b) (.up ℤ)).app I.cochainComplex).hom ≫
        barUnitAt (F.functor (productParameter G H a b))
          ((forgetAction.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) =
      (barRightDerived (F.functor (productParameter G H a b))).map (DerivedCategory.Q.map
        ((forgetAction.mapHomologicalComplex (.up ℤ)).map I.ι'))
  /-- All pairs of cosimplicial operators, including first faces, respect these comparisons. -/
  operator_compatibility : ∀ (a b c d : ℕ)
    (θ : SimplexCategory.mk a ⟶ SimplexCategory.mk c)
    (ψ : SimplexCategory.mk b ⟶ SimplexCategory.mk d),
    (barDerivedOperator (productOperator B θ ψ)).app (DerivedCategory.Q.obj
        ((CochainComplex.singleFunctor (Equivariant A (G × H)) 0).obj N)) ≫
        (resolvedColumn c d).hom =
      (resolvedColumn a b).hom ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (productOperator B θ ψ) (.up ℤ)).app
          I.cochainComplex)
  /-- The resolution computes ordinary derived invariants, including its augmentation. -/
  derivedIso : (barRightDerived V.functor).obj
      (productBarQ.obj ((CochainComplex.single₀ _).obj N)) ≅
    productBarQ.obj ((V.functor.mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  /-- The derived-unit normalization fixes this comparison on the given resolution. -/
  derived_normalization :
    barUnitAt V.functor I.cochainComplex ≫
      ((barRightDerived V.functor).mapIso (productBarResolutionIso N I)).inv ≫
        derivedIso.hom =
      DerivedCategory.Q.map
        (HomologicalComplex.mapExtendIso I.cocomplex ComplexShape.embeddingUpNat V.functor).hom

/-- One equivariant injective resolution models the entire product internal bar.

Source: current blueprint direct-image stability, paragraph (3), formal internal-bar
expansion (blueprint: lem-sfb-condensed-product-bar-resolution-model).

Proof (the seven steps of the node):
1. Apply lem-sfb-condensed-free-linearization-tensor to represented profinite parameters.
   The inverse maps on generators give the free-product isomorphism. Apply the closed
   adjunction of def-sfb-modobj-internal-hom twice; evaluation is successive evaluation
   on the two parameters, so it is natural in both parameters and the coefficient.
2. Construct the two nerves on this internal Hom. Associativity gives the face identities;
   the action law gives the two first-face identity, and the unit law gives degeneracies.
   All formulas are evaluated after arbitrary profinite base change.
3. Mixed operators change disjoint lists. The two first faces commute because (g,1)
   and (1,h) commute. Equivariant resolution differentials commute with every operator.
   Alternating sums square to zero; the total cross terms cancel with the specified signs.
   Nonnegative pairs and triples on each diagonal are finite.
4. By lem-sfb-condensed-action-injective-restriction the forgotten resolution is injective.
   By lem-weil-pbc-bounded-below-injectives-kinjective it is K-injective. Apply the unit
   comparisons of def-sfb-right-derived-functor to this same resolution for every column.
   Naturality and uniqueness of the derived unit give compatibility with every operator.
5. Reorder tuples of pairs into a pair of tuples. This preserves the two first faces
   because g h acts as (g,h), all adjacent products, final faces and identity insertions.
   Thus it identifies the entire diagonal cosimplicial diagram with the product-group bar.
6. The product action category is Grothendieck abelian by
   lem-sfb-condensed-product-action-inflation. Apply lem-sfb-condensed-injective-bar-rows
   to each injective term with group G times H, and then
   lem-sfb-condensed-bar-total-augmentation to its specified invariant augmentation.
   The resulting quasi-isomorphism has precisely the displayed degree-zero components.
7. Apply def-sfb-right-derived-functor to invariants on the original K-injective resolution.
   Its unit and the localization of the resolution determine the normalized derived iso.
   Invert the localized augmentation for Q(D) to Q(J). The same argument includes zero
   modules with arbitrary resolutions and trivial factors with their unnormalized nerves.
-/
theorem condensed_product_bar_resolution_model (A : Ring.{u})
    (G H : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    [HasDerivedCategory.{u + 2} (Modules A)]
    [HasDerivedCategory.{u + 2} (Equivariant A (G × H))]
    (F : InternalFunctions A) (V : Invariants A (G × H)) :
    ∃ B : ProductBar A.toMon G H, ∀ (N : Equivariant A (G × H))
      (I : InjectiveResolution N), Nonempty (ProductResolutionModel F V B I) := by
  classical
  obtain ⟨B, ⟨C⟩⟩ := exists_productBarCoordinates (G := G) (H := H) F
  refine ⟨B, ?_⟩
  intro N I
  obtain ⟨j, hj, hq⟩ := exists_productBarAugmentation B V I
  have hI : I.cochainComplex.IsKInjective := by
    dsimp only [InjectiveResolution.cochainComplex]
    infer_instance
  have hforget := forget_tensor_induction A (G × H)
  have : PreservesFiniteLimits (forgetAction (A := A) (G := G × H)) := hforget.2.1
  have : PreservesFiniteColimits (forgetAction (A := A) (G := G × H)) := hforget.2.2.1
  have : (forgetAction (A := A) (G := G × H)).PreservesInjectiveObjects :=
    hforget.2.2.2.2
  have hterms (n : ℤ) : Injective
      (((forgetAction (A := A) (G := G × H)).mapHomologicalComplex (.up ℤ)).obj
        I.cochainComplex |>.X n) := by
    change Injective (forgetAction.obj (I.cochainComplex.X n))
    exact Functor.injective_obj forgetAction _
  have hUI : CochainComplex.IsKInjective
      ((forgetAction.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex) :=
    CochainComplex.isKInjective_of_injective _ 0
  have hu (a b : ℕ) := barUnitAt_isIso
    (F.functor (productParameter G H a b))
      ((forgetAction.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)
  let e := fun a b ↦ barComparison (productColumn B a b) I.ι'
  let c := fun a b ↦ barComparison (F.functor (productParameter G H a b))
      ((forgetAction.mapHomologicalComplex (.up ℤ)).map I.ι') ≪≫
    (DerivedCategory.Q.mapIso
      ((NatIso.mapHomologicalComplex (C.columnIso a b) (.up ℤ)).app
        I.cochainComplex)).symm
  have hv := barUnitAt_isIso V.functor I.cochainComplex
  let d := (barRightDerived V.functor).mapIso (productBarResolutionIso N I) ≪≫
    (asIso (barUnitAt V.functor I.cochainComplex)).symm ≪≫
    DerivedCategory.Q.mapIso
      (HomologicalComplex.mapExtendIso I.cocomplex ComplexShape.embeddingUpNat V.functor)
  refine ⟨{
    freeProduct := C.freeProduct
    freeProduct_generator := C.freeProduct_generator
    curryIso := C.curryIso
    curry_evaluate := C.curry_evaluate
    columnIso := C.columnIso
    column_evaluate := C.column_evaluate
    singleBar := C.singleBar
    diagonalIso := C.diagonalIso
    diagonal_evaluate := C.diagonal_evaluate
    augmentation := j
    augmentation_f := hj
    augmentation_quasiIso := hq
    column_unit := hu
    resolvedColumn := e
    resolvedColumn_normalization := ?_
    internalColumn := c
    internalColumn_normalization := ?_
    operator_compatibility := ?_
    derivedIso := d
    derived_normalization := ?_ }⟩
  · intro a b
    have := barUnitAt_isIso (productColumn B a b) I.cochainComplex
    simp [e, barComparison, Category.assoc]
  · intro a b
    have := hu a b
    dsimp only [c, barComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv,
      Functor.mapIso_hom, asIso_inv, asIso_hom]
    rw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id]
    simp
  · intro a b c d θ ψ
    exact barComparison_operator (productOperator B θ ψ) I.ι'
  · simp [d]

end CategoryTheory.CondensedBar
