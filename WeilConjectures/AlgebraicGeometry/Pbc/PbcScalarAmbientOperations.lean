/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarStages
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarTensor
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarCompletedObjectComplete
import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRestrictionComplete

/-! # Ambient operation comparisons for finite scalar extension

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-ambient-operation-comparisons)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv
namespace AlgebraicGeometry.Scheme
section AmbientOperations

variable (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Field F] [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F] (i : E →ₐ[ℚ_[l]] F)
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarCompletedCoefficientMap_projection {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedCoefficientMap g d ≫ pbcAdicProjection X d n =
      (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map (pbcAdicProjection Y d n) ≫
        completedFiniteCoefficientMap g d n := by
  exact limit.lift_π _ (op n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarFiniteCoefficientMap_naturality {X Y : Scheme.{u}} (g : X ⟶ Y)
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (dA : AdicCoefficientDatum A) (dB : AdicCoefficientDatum B) (n : ℕ)
    (q : (A ⧸ dA.ideal ^ (n + 1)) →+* (B ⧸ dB.ideal ^ (n + 1))) :
    (proEtaleSheafInverseImage g CommRingCat.{u + 1}).map
        (AdicCoefficients.coefficientMap Y q) ≫ completedFiniteCoefficientMap g dB n =
      completedFiniteCoefficientMap g dA n ≫ AdicCoefficients.coefficientMap X q := by
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  have hinv : AdicCoefficients.coefficientMap Y q ≫
      (pbcLevelConstantComparison Y dB n).inv =
    (pbcLevelConstantComparison Y dA n).inv ≫
      (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).map (CommRingCat.ofHom q) := by
    apply (Iso.eq_inv_comp _).2
    rw [← Category.assoc]
    apply (Iso.comp_inv_eq _).2
    exact (scalarLevelConstantComparison_naturality Y dA dB n q).symm
  unfold completedFiniteCoefficientMap
  change L.map _ ≫ L.map _ ≫ _ ≫ _ = _
  rw [← L.map_comp_assoc, hinv, L.map_comp, Category.assoc]
  erw [reassoc_of% (proEtaleConstantInverseImageMap_naturality g (CommRingCat.ofHom q))]
  simp only [Category.assoc]
  rw [scalarLevelConstantComparison_naturality]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual completed coefficient inclusion commutes with the ringed structure map.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: apply every finite target projection. Both paths take a continuous residue
function, postcompose with the specified field inclusion and precompose with the
base-change map on connected components. Those operations commute. Joint monicity
of all coefficient limit projections gives the displayed completed equality. -/
theorem pbcScalarCoefficientStructureSquare :
    pbcActualCoefficientRingMap Y (pbcScalarCoefficientMap l E F i Y) ≫
        pbcActualStructureMap g (pbcIntegralDatum l F) =
      pbcActualStructureMap g (pbcIntegralDatum l E) ≫
        (proEtaleSheafDirectImage g RingCat.{u + 1}).map
          (pbcActualCoefficientRingMap X (pbcScalarCoefficientMap l E F i X)) := by
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let c (T : Scheme.{u}) := pbcScalarCoefficientMap l E F i T
  let L := proEtaleSheafInverseImage g CommRingCat.{u + 1}
  let R := proEtaleSheafDirectImage g CommRingCat.{u + 1}
  have hc (T : Scheme.{u}) (n : ℕ) :
      c T ≫ pbcAdicProjection T dF n = pbcAdicProjection T dE n ≫
        AdicCoefficients.coefficientMap T (pbcScalarQuotientMap l E F i n) :=
    (pbcScalarCoefficientMap_exists l E F i T).exists.choose_spec n
  have h : L.map (c Y) ≫ completedCoefficientMap g dF =
      completedCoefficientMap g dE ≫ c X := by
    apply limit.hom_ext
    intro n
    change (L.map (c Y) ≫ completedCoefficientMap g dF) ≫
        pbcAdicProjection X dF n.unop =
      (completedCoefficientMap g dE ≫ c X) ≫ pbcAdicProjection X dF n.unop
    simp only [Category.assoc, hc]
    rw [scalarCompletedCoefficientMap_projection]
    rw [← Category.assoc (completedCoefficientMap g dE), scalarCompletedCoefficientMap_projection]
    rw [← L.map_comp_assoc, hc, L.map_comp, Category.assoc]
    simpa only [Category.assoc] using congrArg
      (fun k ↦ L.map (pbcAdicProjection Y dE n.unop) ≫ k)
      (scalarFiniteCoefficientMap_naturality g dE dF n.unop
        (pbcScalarQuotientMap l E F i n.unop))
  have hd : c Y ≫ completedCoefficientDirectImageMap g dF =
      completedCoefficientDirectImageMap g dE ≫ R.map (c X) := by
    unfold completedCoefficientDirectImageMap
    have hn := (proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.naturality (c Y)
    change c Y ≫ (proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app _ =
      (proEtaleSheafAdjunction g CommRingCat.{u + 1}).unit.app _ ≫ R.map (L.map (c Y)) at hn
    rw [← Category.assoc]
    erw [hn]
    rw [Category.assoc, ← R.map_comp, h, R.map_comp, Category.assoc]
  exact congrArg
    (fun k ↦ (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map k) hd

/-- The ambient ordinary-pullback comparison is the normalized derived tensor comparison.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarOrdinaryPullIso :
    pbcEmbeddingAmbientTensor l E F i Y ⋙
        pbcActualDerivedPull g (pbcIntegralDatum l F) ≅
      pbcActualDerivedPull g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i X :=
  pbcActualScalarDerivedPullIso g (pbcIntegralDatum l E) (pbcIntegralDatum l F)
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcScalarCoefficientStructureSquare l E F i g)

/-- The direct-image comparison is the actual mate, rather than a selected isomorphism.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarDirectImageMap :
    pbcActualDerivedPush g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i Y ⟶
      pbcEmbeddingAmbientTensor l E F i X ⋙
        pbcActualDerivedPush g (pbcIntegralDatum l F) :=
  pbcActualScalarDirectImageMap g (pbcIntegralDatum l E) (pbcIntegralDatum l F)
    (pbcScalarCoefficientMap l E F i Y) (pbcScalarCoefficientMap l E F i X)
    (pbcScalarCoefficientStructureSquare l E F i g)

/-- The canonical scalar/direct-image mate is invertible for finite coefficient extensions.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: the target valuation ring is finite free over the source. Locally choose a
finite free basis. Scalar extension is then a finite sum, and derived direct image
commutes with finite sums. The resulting identification has the same ordinary
tensor formula as the mate, so descends independently of that basis. Equivalently
use the finite perfect projection formula and the tensor-unit normalization. -/
@[instance] theorem pbcScalarDirectImageMap_isIso :
    IsIso (pbcScalarDirectImageMap l E F i g) := by
  sorry

/-- The canonical invertible direct-image comparison, with its mate definition retained.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarDirectImageIso :
    pbcActualDerivedPush g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i Y ≅
      pbcEmbeddingAmbientTensor l E F i X ⋙
        pbcActualDerivedPush g (pbcIntegralDatum l F) :=
  asIso (pbcScalarDirectImageMap l E F i g)

private theorem pbcScalarDirectImageIso_hom :
    (pbcScalarDirectImageIso l E F i g).hom = pbcScalarDirectImageMap l E F i g := by
  unfold pbcScalarDirectImageIso
  rfl

-- Construct both arrows from the two reflection Hom bijections. Scalar restriction
-- lets the source reflection compute maps into complete target-coefficient objects.
private theorem scalar_reflector_transport
    {V Z : Type*} [Category V] [Category Z]
    (F : V ⥤ Z) (U : Z ⥤ V) (adj : F ⊣ U)
    (L : V ⥤ V) (M : Z ⥤ Z) (η : 𝟭 V ⟶ L) (ε : 𝟭 Z ⟶ M)
    (P : V → Prop) (Q : Z → Prop)
    (hd : ∀ X, Q (M.obj X))
    (hb : ∀ X Y, P Y → Function.Bijective (fun f : L.obj X ⟶ Y ↦ η.app X ≫ f))
    (he : ∀ X Y, Q Y → Function.Bijective (fun f : M.obj X ⟶ Y ↦ ε.app X ≫ f))
    (hF : ∀ X, Q (F.obj (L.obj X))) (hU : ∀ Y, Q Y → P (U.obj Y)) :
    ∃! e : F ⋙ M ≅ L ⋙ F,
      ∀ X, ε.app (F.obj X) ≫ e.hom.app X = F.map (η.app X) := by
  classical
  have hj (X : V) (Y : Z) (hY : Q Y) :
      Function.Bijective (fun f : F.obj (L.obj X) ⟶ Y ↦ F.map (η.app X) ≫ f) := by
    constructor
    · intro f g h
      apply (adj.homEquiv _ _).injective
      apply (hb X (U.obj Y) (hU Y hY)).1
      simpa only [← adj.homEquiv_naturality_left, Functor.id_obj] using
        congrArg (adj.homEquiv X Y) h
    · intro f
      obtain ⟨g, hg⟩ := (hb X (U.obj Y) (hU Y hY)).2 ((adj.homEquiv X Y) f)
      refine ⟨(adj.homEquiv (L.obj X) Y).symm g, ?_⟩
      apply (adj.homEquiv X Y).injective
      rw [adj.homEquiv_naturality_left, Equiv.apply_symm_apply]
      exact hg
  let f (X : V) := (he (F.obj X) (F.obj (L.obj X)) (hF X)).2
    (F.map (η.app X)) |>.choose
  have hf (X : V) : ε.app (F.obj X) ≫ f X = F.map (η.app X) :=
    (he (F.obj X) (F.obj (L.obj X)) (hF X)).2 (F.map (η.app X)) |>.choose_spec
  let g (X : V) := (hj X (M.obj (F.obj X)) (hd _)).2 (ε.app (F.obj X)) |>.choose
  have hg (X : V) : F.map (η.app X) ≫ g X = ε.app (F.obj X) :=
    (hj X (M.obj (F.obj X)) (hd _)).2 (ε.app (F.obj X)) |>.choose_spec
  let eX (X : V) : M.obj (F.obj X) ≅ F.obj (L.obj X) :=
    { hom := f X
      inv := g X
      hom_inv_id := by
        apply (he _ _ (hd (F.obj X))).1
        change ε.app (F.obj X) ≫ (f X ≫ g X) = ε.app (F.obj X) ≫ 𝟙 _
        rw [← Category.assoc, hf, hg, Category.comp_id]
      inv_hom_id := by
        apply (hj X _ (hF X)).1
        change F.map (η.app X) ≫ (g X ≫ f X) = F.map (η.app X) ≫ 𝟙 _
        rw [← Category.assoc, hg, hf, Category.comp_id] }
  let e : F ⋙ M ≅ L ⋙ F := NatIso.ofComponents eX (fun {X Y} h ↦ by
    apply (he _ _ (hF Y)).1
    change ε.app (F.obj X) ≫ (M.map (F.map h) ≫ f Y) =
      ε.app (F.obj X) ≫ (f X ≫ F.map (L.map h))
    rw [← Category.assoc, ← ε.naturality, Category.assoc, hf]
    rw [← Category.assoc, hf]
    simp only [Functor.id_map]
    rw [← F.map_comp, ← F.map_comp]
    simpa only [Functor.id_map] using congrArg F.map (η.naturality h))
  refine ⟨e, hf, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply (he _ _ (hF X)).1
  exact (he' X).trans (hf X).symm

private theorem scalar_completion_reflection
    (W : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K L : PbcCompletedDerived W d) (hL : PbcIsIntrinsicallyComplete W d L) :
    Function.Bijective (fun f : (pbcActualCompletion d W).obj K ⟶ L ↦
      (pbcActualCompletionUnit d W).app K ≫ f) := by
  let P : ObjectProperty (PbcCompletedDerived W d) := PbcIsIntrinsicallyComplete W d
  let adj := Adjunction.ofIsRightAdjoint P.ι
  exact ((ObjectProperty.fullyFaithfulι P).homEquiv.symm.trans
    (adj.homEquiv K ⟨L, hL⟩)).bijective

/-- Scalar extension commutes with completion through the actual quotient augmentation.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: scalar tensor of a source completion output is target-complete, and scalar
restriction preserves completeness. Transfer the source reflection Hom bijection
through the specified scalar adjunction. Together with the target reflection Hom
bijection, this constructs arrows in both directions. Cancel the respective units
to prove their inverse identities, naturality, and uniqueness. The forward arrow
is defined by its displayed unit equation, retaining the actual quotient unit. -/
theorem pbcScalarCompletionIso_exists (W : Scheme.{u}) :
    ∃! e : pbcEmbeddingAmbientTensor l E F i W ⋙
        pbcActualCompletion (pbcIntegralDatum l F) W ≅
      pbcActualCompletion (pbcIntegralDatum l E) W ⋙
        pbcEmbeddingAmbientTensor l E F i W,
      ∀ K : PbcCompletedDerived W (pbcIntegralDatum l E),
        (pbcActualCompletionUnit (pbcIntegralDatum l F) W).app
            ((pbcEmbeddingAmbientTensor l E F i W).obj K) ≫ e.hom.app K =
          (pbcEmbeddingAmbientTensor l E F i W).map
            ((pbcActualCompletionUnit (pbcIntegralDatum l E) W).app K) := by
  exact scalar_reflector_transport
    (pbcEmbeddingAmbientTensor l E F i W)
    (pbcDerivedRestrict (pbcScalarCoefficientMap l E F i W))
    (pbcDerivedScalarAdjunction (pbcScalarCoefficientMap l E F i W))
    (pbcActualCompletion (pbcIntegralDatum l E) W)
    (pbcActualCompletion (pbcIntegralDatum l F) W)
    (pbcActualCompletionUnit (pbcIntegralDatum l E) W)
    (pbcActualCompletionUnit (pbcIntegralDatum l F) W)
    (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E))
    (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F))
    (fun K ↦ ((ObjectProperty.ι
      (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F))).leftAdjoint.obj K).property)
    (scalar_completion_reflection W (pbcIntegralDatum l E))
    (scalar_completion_reflection W (pbcIntegralDatum l F))
    (pbcScalarCompletedObjectComplete l E F i W)
    (pbcScalarRestrictionComplete l E F i W)

/-- The unique completion comparison preserving the specified quotient unit.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarCompletionIso (W : Scheme.{u}) :
    pbcEmbeddingAmbientTensor l E F i W ⋙
        pbcActualCompletion (pbcIntegralDatum l F) W ≅
      pbcActualCompletion (pbcIntegralDatum l E) W ⋙
        pbcEmbeddingAmbientTensor l E F i W :=
  (pbcScalarCompletionIso_exists l E F i W).exists.choose

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcComplete_iso (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    ObjectProperty.IsClosedUnderIsomorphisms (PbcIsIntrinsicallyComplete W d) := by
  constructor
  intro K L e hK
  obtain ⟨r, f, hf, C, eC, hC⟩ := hK
  refine ⟨r, f, hf, C,
    eC ≪≫ (pbcDerivedExtend (pbcCompletedComparison W d).inv).mapIso e, ?_⟩
  change IsIso (eC.inv ≫ _) at hC
  have hu := (isIso_comp_left_iff eC.inv _).mp hC
  change IsIso ((_ ≫ eC.inv) ≫ _)
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite-free coefficient extension preserves ambient intrinsic completeness.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-ambient-operation-comparisons).
Proof: use the unit-normalized scalar/completion comparison. The completion unit
of the complete input is invertible, and tensor carries it to an invertible map.
The comparison's unit equation therefore makes the target completion unit
invertible. Its target is a reflected, intrinsically complete object; invariance
of intrinsic completeness under isomorphism gives the claim. -/
theorem pbcScalarPreservesComplete (W : Scheme.{u})
    (K : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete W (pbcIntegralDatum l E))) :
    PbcIsIntrinsicallyComplete W (pbcIntegralDatum l F)
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj) := by
  let dE := pbcIntegralDatum l E
  let dF := pbcIntegralDatum l F
  let I := ObjectProperty.ι (PbcIsIntrinsicallyComplete W dE)
  let adj := Adjunction.ofIsRightAdjoint I
  have hη : IsIso ((pbcActualCompletionUnit dE W).app K.obj) := by
    change IsIso (adj.unit.app (I.obj K))
    infer_instance
  obtain ⟨e, he, _⟩ := pbcScalarCompletionIso_exists l E F i W
  have hmap : IsIso ((pbcEmbeddingAmbientTensor l E F i W).map
      ((pbcActualCompletionUnit dE W).app K.obj)) := inferInstance
  have hcomp : IsIso ((pbcActualCompletionUnit dF W).app
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj) ≫ e.hom.app K.obj) := by
    rw [he K.obj]
    exact hmap
  have hunit : IsIso ((pbcActualCompletionUnit dF W).app
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj)) :=
    (isIso_comp_right_iff _ (e.hom.app K.obj)).mp hcomp
  have := pbcComplete_iso W dF
  exact ObjectProperty.prop_of_iso (PbcIsIntrinsicallyComplete W dF)
    (asIso ((pbcActualCompletionUnit dF W).app
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj))).symm
    ((ObjectProperty.ι (PbcIsIntrinsicallyComplete W dF)).leftAdjoint.obj
      ((pbcEmbeddingAmbientTensor l E F i W).obj K.obj)).property

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completed scalar/pullback is the ordinary comparison followed by the canonical
completion comparisons. Source: blueprint order 1307
(blueprint: lem-pbc-scalar-ambient-operation-comparisons). -/
@[irreducible] def pbcScalarCompletedPullIso :
    pbcEmbeddingAmbientTensor l E F i Y ⋙
        pbcActualCompletedPull g (pbcIntegralDatum l F) ≅
      pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i X :=
  NatIso.ofComponents
    (F := pbcEmbeddingAmbientTensor l E F i Y ⋙
      pbcActualCompletedPull g (pbcIntegralDatum l F))
    (G := pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙
      pbcEmbeddingAmbientTensor l E F i X) (fun K ↦
    (pbcActualCompletion (pbcIntegralDatum l F) X).mapIso
        ((pbcScalarOrdinaryPullIso l E F i g).app K) ≪≫
      (pbcScalarCompletionIso l E F i X).app
        ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K)) (fun {K L} f ↦ by
    have he := (pbcScalarOrdinaryPullIso l E F i g).hom.naturality f
    have hc := (pbcScalarCompletionIso l E F i X).hom.naturality
      ((pbcActualDerivedPull g (pbcIntegralDatum l E)).map f)
    dsimp only [CategoryTheory.Functor.comp_map] at he hc
    dsimp only [pbcActualCompletedPull, CategoryTheory.Functor.comp_map, Iso.trans_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.app_hom]
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, he,
      CategoryTheory.Functor.map_comp, Category.assoc, hc, Category.assoc])

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcScalarCompletedPullIso_hom
    (K : PbcCompletedDerived Y (pbcIntegralDatum l E)) :
    (pbcScalarCompletedPullIso l E F i g).hom.app K =
      (pbcActualCompletion (pbcIntegralDatum l F) X).map
          ((pbcScalarOrdinaryPullIso l E F i g).hom.app K) ≫
        (pbcScalarCompletionIso l E F i X).hom.app
          ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K) := by
  unfold pbcScalarCompletedPullIso
  rfl

variable {X' Y' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {a : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f a)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pbcCompletion_hom_ext (W : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (K L : PbcCompletedDerived W d) (hL : PbcIsIntrinsicallyComplete W d L)
    (f g : (pbcActualCompletion d W).obj K ⟶ L)
    (h : (pbcActualCompletionUnit d W).app K ≫ f =
      (pbcActualCompletionUnit d W).app K ≫ g) : f = g := by
  let I := ObjectProperty.ι (PbcIsIntrinsicallyComplete W d)
  let adj := Adjunction.ofIsRightAdjoint I
  let N : ObjectProperty.FullSubcategory (PbcIsIntrinsicallyComplete W d) := ⟨L, hL⟩
  let a : I.leftAdjoint.obj K ⟶ N := ObjectProperty.homMk f
  let b : I.leftAdjoint.obj K ⟶ N := ObjectProperty.homMk g
  have hab : adj.homEquiv K N a = adj.homEquiv K N b := by
    change adj.unit.app K ≫ I.map a = adj.unit.app K ≫ I.map b at h
    simpa only [Adjunction.homEquiv_unit] using h
  exact congrArg (fun z ↦ z.hom) ((adj.homEquiv K N).injective hab)

end AmbientOperations
end AlgebraicGeometry.Scheme
