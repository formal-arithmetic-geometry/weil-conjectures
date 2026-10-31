/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.GeneratorReduction.ShortWordCompletionIsomorphism
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SixFunctors.GeneratorReduction.CanonicalReductionPullComposition

/-! # Tensor, composition and adjunction reduction squares

Source: blueprint main-20261015, fix-prop-coherence.proof.md, the maps-used sentence
(blueprint: lem-sf-tensor-adjunction-reduction-squares).

The word evaluations, recursive coefficient arrows and independently normalized
ringed-site arrows are the published GeneratorReduction definitions. Only the
structural generators listed in this node are selected below.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u s i

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.GeneratorReduction

attribute [local irreducible] pullbackTensorCalculus
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard SheafOfModules.monoidalCategory

variable {S : Type s} {W : S → Scheme.{u}} {I : Type i} {location : I → S}

/-- Select precisely tensor associativity, scalar unitors, pullback/direct-image
composition and the two specified adjunctions' units and counits.
Source: blueprint fix-prop-coherence.proof.md, maps-used sentence
(blueprint: lem-sf-tensor-adjunction-reduction-squares). -/
def GeneratorKind.IsTensorAdjunction {a : S} {B C : Word W location a}
    (g : GeneratorKind W location B C) : Prop :=
  match g with
  | .tensorAssociator _ _ _ | .tensorLeftUnit _ | .tensorRightUnit _ => True
  | .pullComposition .. | .pushComposition .. => True
  | .pullPushUnit .. | .pullPushCounit .. | .openUnit .. | .openCounit .. => True
  | .openBaseChange .. | .openTensor .. | .properOpenInterchange .. |
      .properOpenLambda .. => False

/-- The invertible tensor and composition generators, for which the node also
asserts the square in the reverse direction. Adjunction units and counits are
not treated as invertible constraints.
Source: blueprint fix-prop-coherence.proof.md, maps-used sentence
(blueprint: lem-sf-tensor-adjunction-reduction-squares). -/
def GeneratorKind.IsTensorCompositionIso {a : S} {B C : Word W location a}
    (g : GeneratorKind W location B C) : Prop :=
  match g with
  | .tensorAssociator _ _ _ | .tensorLeftUnit _ | .tensorRightUnit _ => True
  | .pullComposition .. | .pushComposition .. => True
  | .pullPushUnit .. | .pullPushCounit .. | .openUnit .. | .openCounit .. |
      .openBaseChange .. | .openTensor .. | .properOpenInterchange .. |
      .properOpenLambda .. => False

/-- Functorial action of a system word on a morphism of all its input systems.
Source: blueprint fix-prop-coherence.proof.md, naturality in the maps-used sentence
(blueprint: lem-sf-tensor-adjunction-reduction-squares). -/
def Word.systemAction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    (M N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (f : ∀ k : I, M k ⟶ N k) : {a : S} → (B : Word W location a) →
      B.systemValue l E W location o M ⟶ B.systemValue l E W location o N
  | _, .input k => f k
  | _, .unit _ => 𝟙 _
  | a, .tensor B C => (IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.map
      (Prod.mkHom (B.systemAction l E o M N f) (C.systemAction l E o M N f))
  | _, .pull v _ _ _ B =>
      (IntegralSystemRealization.pull l E v).map (B.systemAction l E o M N f)
  | _, .push v _ _ _ _ B =>
      (IntegralSystemRealization.Operations.push l E o.system v).map (B.systemAction l E o M N f)
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.Operations.shriek l E o.system j).map
        (B.systemAction l E o M N f)

/-- Functorial action of an integral word, with the same completed operations as
its object evaluation. Source: blueprint fix-prop-coherence.proof.md, naturality
(blueprint: lem-sf-tensor-adjunction-reduction-squares). -/
def Word.integralAction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    (K L : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (f : ∀ k : I, K k ⟶ L k) : {a : S} → (B : Word W location a) →
      B.integralValue l E W location o K ⟶ B.integralValue l E W location o L
  | _, .input k => f k
  | _, .unit _ => 𝟙 _
  | a, .tensor B C => (integralCompletedTensor l E (W a)).map
      (Prod.mkHom (B.integralAction l E o K L f) (C.integralAction l E o K L f))
  | _, .pull v _ _ _ B =>
      (integralDerivedPullback l E v).map (B.integralAction l E o K L f)
  | _, .push v _ _ _ _ B =>
      (integralPush l E o v).map (B.integralAction l E o K L f)
  | _, .open j hj _ B => letI := hj
      (IntegralSystemRealization.ringedOpen l E j).map (B.integralAction l E o K L f)

private theorem closed_uncurry {A : Type*} [Category A]
    {H : Aᵒᵖ × A ⥤ A} (T : CoefficientClosedStructure H)
    {X Y Z : A} (f : X ⟶ H.obj (Opposite.op Y, Z)) :
    (T.transpose X Y Z).symm f =
      T.tensor.map (Prod.mkHom f (𝟙 Y)) ≫ T.evaluation Y Z := by
  let := T.monoidal
  simpa only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    CoefficientClosedStructure.evaluation, MonoidalCategory.tensorRight,
    MonoidalCategory.curriedTensor, Functor.flip,
    MonoidalCategory.tensor_map, MonoidalCategory.tensor_obj,
    MonoidalCategory.tensorHom_id] using!
      (T.adjunction Y).homEquiv_counit X Z f

private theorem closed_uncurry_pre {A : Type*} [Category A]
    {H : Aᵒᵖ × A ⥤ A} (T : CoefficientClosedStructure H)
    {X X' Y Z : A} (f : X ⟶ X') (g : X' ⟶ H.obj (Opposite.op Y, Z)) :
    (T.transpose X Y Z).symm (f ≫ g) =
      T.tensor.map (Prod.mkHom f (𝟙 Y)) ≫ (T.transpose X' Y Z).symm g := by
  let := T.monoidal
  simpa only [CoefficientClosedStructure.transpose, CoefficientClosedStructure.tensor,
    MonoidalCategory.tensorRight, MonoidalCategory.curriedTensor, Functor.flip,
    MonoidalCategory.tensor_map,
    MonoidalCategory.tensorHom_id, MonoidalCategory.tensor_obj] using!
      (T.adjunction Y).homEquiv_naturality_left_symm f g

private theorem closed_composition_beta {A : Type*} [Category A]
    {H : Aᵒᵖ × A ⥤ A} (T : CoefficientClosedStructure H)
    {X Y P Q V : A} (f : X ⟶ H.obj (Opposite.op Q, V))
    (g : Y ⟶ H.obj (Opposite.op P, Q)) :
    (T.transpose (T.tensor.obj (X, Y)) P V).symm
        (T.tensor.map (Prod.mkHom f g) ≫ T.composition P Q V) =
      (T.monoidal.associator X Y P).hom ≫
        T.tensor.map (Prod.mkHom (𝟙 X) ((T.transpose Y P Q).symm g)) ≫
        (T.transpose X Q V).symm f := by
  let := T.monoidal
  rw [closed_uncurry_pre, CoefficientClosedStructure.composition, Equiv.symm_apply_apply]
  have hn := MonoidalCategory.associator_naturality f g (𝟙 P)
  change T.tensor.map (Prod.mkHom (T.tensor.map (Prod.mkHom f g)) (𝟙 P)) ≫
      (T.monoidal.associator _ _ _).hom =
    (T.monoidal.associator X Y P).hom ≫
      T.tensor.map (Prod.mkHom f (T.tensor.map (Prod.mkHom g (𝟙 P)))) at hn
  rw [← Category.assoc, hn]
  simp only [closed_uncurry]
  simp only [Category.assoc, ← T.tensor.map_comp_assoc, prod_comp,
    Category.id_comp, Category.comp_id]

private theorem enriched_associativity {A N : Type*} [Category A] [Category N]
    {HA : Aᵒᵖ × A ⥤ A} {HN : Nᵒᵖ × N ⥤ N}
    (TA : CoefficientClosedStructure HA) (TN : CoefficientClosedStructure HN)
    (F : A ⥤ N) (μ : TA.tensor ⋙ F ≅ F.prod F ⋙ TN.tensor)
    (h : CoefficientEvaluationCompatible TA TN F μ) (X Y Z : A) :
    μ.hom.app (TA.tensor.obj (X, Y), Z) ≫
        TN.tensor.map (Prod.mkHom (μ.hom.app (X, Y)) (𝟙 (F.obj Z))) ≫
        (TN.monoidal.associator (F.obj X) (F.obj Y) (F.obj Z)).hom =
      F.map (TA.monoidal.associator X Y Z).hom ≫
        μ.hom.app (X, TA.tensor.obj (Y, Z)) ≫
        TN.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (μ.hom.app (Y, Z))) := by
  let Q := TA.tensor.obj (Y, Z)
  let V := TA.tensor.obj (X, Q)
  let f := TA.transpose X Q V (𝟙 V)
  let g := TA.transpose Y Z Q (𝟙 Q)
  have hf := h.transpose X Q V (𝟙 V)
  have hg := h.transpose Y Z Q (𝟙 Q)
  have hc := h.composition Z Q V
  have hab : TA.tensor.map (Prod.mkHom f g) ≫ TA.composition Z Q V =
      TA.transpose (TA.tensor.obj (X, Y)) Z V (TA.monoidal.associator X Y Z).hom := by
    apply (TA.transpose _ Z V).symm.injective
    rw [closed_composition_beta]
    simp only [f, g, Equiv.symm_apply_apply]
    rw [show Prod.mkHom (𝟙 X) (𝟙 Q) = 𝟙 (X, Q) from rfl,
      CategoryTheory.Functor.map_id]
    let := TA.monoidal
    simp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_obj, Q, V,
      Category.comp_id]
  have hp := h.transpose (TA.tensor.obj (X, Y)) Z V
    (TA.monoidal.associator X Y Z).hom
  rw [← hab, F.map_comp, Category.assoc, hc] at hp
  have hn := μ.hom.naturality (Prod.mkHom f g)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [← Category.assoc, ← Category.assoc, hn] at hp
  simp only [Category.assoc, ← TN.tensor.map_comp, prod_comp] at hp
  rw [hf, hg] at hp
  have hp := congrArg (TN.transpose (F.obj (TA.tensor.obj (X, Y)))
    (F.obj Z) (F.obj V)).symm hp
  dsimp only [Functor.comp_obj, Functor.prod_obj] at hp
  rw [closed_uncurry_pre, closed_composition_beta, Equiv.symm_apply_apply] at hp
  dsimp only [Q, V] at hp ⊢
  simp only [CategoryTheory.Functor.map_id, Category.comp_id,
    Equiv.symm_apply_apply] at hp
  apply (cancel_epi (μ.inv.app (TA.tensor.obj (X, Y), Z))).1
  have : IsIso (Prod.mkHom (𝟙 (F.obj X)) (μ.inv.app (Y, Z))) :=
    (Iso.prod (asIso _) (asIso _)).isIso_hom
  apply (cancel_mono (TN.tensor.map
    (Prod.mkHom (𝟙 (F.obj X)) (μ.inv.app (Y, Z))) ≫ μ.inv.app (X, Q))).1
  dsimp only [Functor.comp_obj, Functor.prod_obj, Q] at hp ⊢
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← TN.tensor.map_comp_assoc,
    prod_comp, Category.id_comp, Category.comp_id, Iso.hom_inv_id_app,
    ← prod_id, Functor.comp_obj,
    CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  exact hp

private theorem comparison_associator {A N : Type*} [Category A] [Category N]
    {HA : Aᵒᵖ × A ⥤ A} {HN : Nᵒᵖ × N ⥤ N}
    (TA : CoefficientClosedStructure HA) (TN : CoefficientClosedStructure HN)
    (F : A ⥤ N) (μ : TA.tensor ⋙ F ≅ F.prod F ⋙ TN.tensor)
    (h : CoefficientEvaluationCompatible TA TN F μ)
    (T : A × A ⥤ A) (e : T = TA.tensor)
    (X Y Z : A) (X' Y' Z' : N)
    (x : F.obj X ⟶ X') (y : F.obj Y ⟶ Y') (z : F.obj Z ⟶ Z') :
    let t := Functor.whiskerRight (eqToIso e).hom F ≫ μ.hom
    t.app (T.obj (X, Y), Z) ≫
        TN.tensor.map (Prod.mkHom (t.app (X, Y) ≫ TN.tensor.map (Prod.mkHom x y)) z) ≫
        (TN.monoidal.associator X' Y' Z').hom =
      F.map ((eqToIso (congrArg (fun U : A × A ⥤ A ↦
        U.obj (U.obj (X, Y), Z)) e)).hom ≫
          (TA.monoidal.associator X Y Z).hom ≫
            (eqToIso (congrArg (fun U : A × A ⥤ A ↦
              U.obj (X, U.obj (Y, Z))) e.symm)).hom) ≫
        t.app (X, T.obj (Y, Z)) ≫
        TN.tensor.map (Prod.mkHom x (t.app (Y, Z) ≫ TN.tensor.map (Prod.mkHom y z))) := by
  subst T
  simp only [eqToIso_refl, Iso.refl_hom, Functor.whiskerRight_app, NatTrans.comp_app,
    NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.prod_obj]
  simp only [Category.id_comp]
  let := TA.monoidal
  let := TN.monoidal
  dsimp only [CoefficientClosedStructure.tensor] at μ
  dsimp only [CoefficientClosedStructure.tensor] at *
  try simp only [Category.id_comp, Category.comp_id]
  have hn := MonoidalCategory.associator_naturality x y z
  change TN.tensor.map (Prod.mkHom (TN.tensor.map (Prod.mkHom x y)) z) ≫
      (TN.monoidal.associator X' Y' Z').hom =
    (TN.monoidal.associator (F.obj X) (F.obj Y) (F.obj Z)).hom ≫
      TN.tensor.map (Prod.mkHom x (TN.tensor.map (Prod.mkHom y z))) at hn
  erw [show TN.tensor.map
      (Prod.mkHom (μ.hom.app (X, Y) ≫ TN.tensor.map (Prod.mkHom x y)) z) =
    TN.tensor.map (Prod.mkHom (μ.hom.app (X, Y)) (𝟙 _)) ≫
      TN.tensor.map (Prod.mkHom (TN.tensor.map (Prod.mkHom x y)) z) by
        rw [← TN.tensor.map_comp]; simp only [prod_comp, Category.id_comp]]
  rw [Category.assoc, hn]
  erw [reassoc_of% (enriched_associativity TA TN F μ h X Y Z)]
  simp only [← TN.tensor.map_comp, prod_comp, Category.id_comp]
  erw [Category.comp_id]
  rfl

private theorem comparison_left_unitor {A N : Type*} [Category A] [Category N]
    {HA : Aᵒᵖ × A ⥤ A} {HN : Nᵒᵖ × N ⥤ N}
    (TA : CoefficientClosedStructure HA) (TN : CoefficientClosedStructure HN)
    (F : A ⥤ N) (μ : TA.tensor ⋙ F ≅ F.prod F ⋙ TN.tensor)
    (ι : F.obj TA.monoidal.tensorUnit ≅ TN.monoidal.tensorUnit)
    (hι : ∀ X : A,
      μ.inv.app (TA.monoidal.tensorUnit, X) ≫ F.map (TA.monoidal.leftUnitor X).hom =
        TN.tensor.map (Prod.mkHom ι.hom (𝟙 (F.obj X))) ≫
          (TN.monoidal.leftUnitor (F.obj X)).hom)
    (T : A × A ⥤ A) (e : T = TA.tensor) (X : A) (Y : N) (q : F.obj X ⟶ Y) :
    (Functor.whiskerRight (eqToIso e).hom F ≫ μ.hom).app
        (TA.monoidal.tensorUnit, X) ≫
        TN.tensor.map (Prod.mkHom ι.hom q) ≫ (TN.monoidal.leftUnitor Y).hom =
      F.map ((eqToIso (congrArg (fun U : A × A ⥤ A ↦
        U.obj (TA.monoidal.tensorUnit, X)) e)).hom ≫
          (TA.monoidal.leftUnitor X).hom) ≫ q := by
  subst T
  let := TA.monoidal
  let := TN.monoidal
  dsimp only [CoefficientClosedStructure.tensor] at μ
  dsimp only [CoefficientClosedStructure.tensor] at *
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have hl := hι X
  apply (cancel_epi (μ.inv.app (TA.monoidal.tensorUnit, X))).1
  simp only [Category.assoc]
  simp only [Functor.comp_obj, Functor.prod_obj, Category.id_comp,
    Iso.inv_hom_id_app_assoc]
  erw [reassoc_of% hl]
  have hn := MonoidalCategory.leftUnitor_naturality q
  rw [← MonoidalCategory.id_tensorHom] at hn
  change TN.tensor.map (Prod.mkHom (𝟙 TN.monoidal.tensorUnit) q) ≫
      (TN.monoidal.leftUnitor Y).hom =
    (TN.monoidal.leftUnitor (F.obj X)).hom ≫ q at hn
  erw [← hn]
  dsimp only [CoefficientClosedStructure.tensor] at *
  rw [← Category.assoc, ← (MonoidalCategory.tensor N).map_comp]
  simp only [prod_comp, Category.comp_id, Category.id_comp]

private def tensorOrdinaryR (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    (X : Scheme.{u}) :
    (o.ringed.tensor X).ordinary.tensor ⋙
        (IntegralSystemRealization.calculus l E X).reduction ⟶
      (IntegralSystemRealization.calculus l E X).reduction.prod
        (IntegralSystemRealization.calculus l E X).reduction ⋙
          (IntegralSystemRealization.calculus l E X).systemClosed.tensor :=
  Functor.whiskerRight (eqToIso (o.ringed.tensorClosed X)).hom
    (IntegralSystemRealization.calculus l E X).reduction ≫
      (IntegralSystemRealization.calculus l E X).reductionTensor.hom

private def pushOrdinaryR (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IntegralSystemRealization.ringedPush l E f ⋙
        (IntegralSystemRealization.calculus l E Y).reduction ⟶
      (IntegralSystemRealization.calculus l E X).reduction ⋙
        IntegralSystemRealization.Operations.push l E o.system f :=
  (mateEquiv (IntegralSystemRealization.ringedAdj l E f) (o.system.direct f).adj
    (o.realization.reductionPull f).inv).natTrans

private theorem mate_reconstruction
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {RA : A ⥤ C} {LA : C ⥤ A} {RB : B ⥤ D} {LB : D ⥤ B}
    {P : B ⥤ A} {Q : A ⥤ B} {F : D ⥤ C} {G : C ⥤ D}
    (aa : RA ⊣ LA) (ab : RB ⊣ LB) (ap : P ⊣ Q) (af : F ⊣ G)
    (χ : RB ⋙ F ≅ P ⋙ RA) (K : A) :
    RB.map (Q.map (aa.unit.app K) ≫
        (conjugateIsoEquiv (ap.comp aa) (ab.comp af) χ).hom.app (RA.obj K)) ≫
        ab.counit.app (G.obj (RA.obj K)) =
      (mateEquiv ap af χ.hom).natTrans.app K := by
  have hv := conjugateEquiv_counit (ap.comp aa) (ab.comp af) χ.hom (RA.obj K)
  have hn := χ.hom.naturality (Q.map (aa.unit.app K))
  have hε := ap.counit.naturality (aa.unit.app K)
  apply (af.homEquiv _ _).symm.injective
  change F.map _ ≫ af.counit.app _ = _
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc]
  change _ = F.map ((mateEquiv ap af χ.hom).natTrans.app K) ≫ af.counit.app _
  rw [mateEquiv_counit ap af χ.hom K]
  simp only [Adjunction.comp_counit_app, Functor.comp_map, Functor.comp_obj] at hv
  rw [CategoryTheory.Functor.map_comp, Category.assoc, conjugateIsoEquiv_apply_hom]
  change F.map (RB.map (Q.map (aa.unit.app K))) ≫
      F.map (RB.map ((conjugateEquiv (ap.comp aa) (ab.comp af) χ.hom).app
        (RA.obj K))) ≫ _ = _
  rw [hv]
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj, Functor.id_map] at hn hε
  rw [← Category.assoc, hn, Category.assoc, ← RA.map_comp_assoc, hε,
    RA.map_comp, Category.assoc, aa.left_triangle_components,
    Category.comp_id]

private theorem mate_unit_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (χ : R ⋙ F ≅ P ⋙ T) {X : A} {Y : C} (q : R.obj X ⟶ Y) :
    q ≫ b.unit.app Y = R.map (a.unit.app X) ≫
      (mateEquiv a b χ.hom).natTrans.app (P.obj X) ≫
      G.map (χ.inv.app X ≫ F.map q) := by
  have hm := unit_mateEquiv a b χ.hom X
  dsimp only [Functor.id_obj] at hm
  rw [G.map_comp, ← Category.assoc, ← Category.assoc, hm]
  simp only [Category.assoc, ← G.map_comp_assoc, Iso.hom_inv_id_app,
    Functor.comp_obj, G.map_id, Category.id_comp]
  exact b.unit.naturality q

private theorem mate_counit_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (χ : R ⋙ F ≅ P ⋙ T) {X : B} {Y : D} (q : T.obj X ⟶ Y) :
    χ.inv.app (Q.obj X) ≫
        F.map ((mateEquiv a b χ.hom).natTrans.app X ≫ G.map q) ≫ b.counit.app Y =
      T.map (a.counit.app X) ≫ q := by
  have hn := b.counit.naturality q
  have hm := mateEquiv_counit a b χ.hom X
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [F.map_comp, Category.assoc, hn]
  rw [reassoc_of% hm, Iso.inv_hom_id_app_assoc]

private theorem mate_compositor_square
    {A₀ A₁ A₂ N₀ N₁ N₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category N₀] [Category N₁] [Category N₂]
    {P : A₀ ⥤ A₁} {Q : A₁ ⥤ A₀} {P' : A₁ ⥤ A₂} {Q' : A₂ ⥤ A₁}
    {P'' : A₀ ⥤ A₂} {Q'' : A₂ ⥤ A₀}
    {F : N₀ ⥤ N₁} {G : N₁ ⥤ N₀} {F' : N₁ ⥤ N₂} {G' : N₂ ⥤ N₁}
    {F'' : N₀ ⥤ N₂} {G'' : N₂ ⥤ N₀}
    {R₀ : A₀ ⥤ N₀} {R₁ : A₁ ⥤ N₁} {R₂ : A₂ ⥤ N₂}
    (a : P ⊣ Q) (a' : P' ⊣ Q') (a'' : P'' ⊣ Q'')
    (b : F ⊣ G) (b' : F' ⊣ G') (b'' : F'' ⊣ G'')
    (χ : R₀ ⋙ F ⟶ P ⋙ R₁) (χ' : R₁ ⋙ F' ⟶ P' ⋙ R₂)
    (χ'' : R₀ ⋙ F'' ⟶ P'' ⋙ R₂)
    (α : P'' ⟶ P ⋙ P') (β : F'' ⟶ F ⋙ F')
    (h : (TwoSquare.vComp χ χ').whiskerRight β =
      (TwoSquare.mk _ _ _ _ χ'').whiskerLeft α) (X : A₂) :
    (mateEquiv a b χ).natTrans.app (Q'.obj X) ≫
        G.map ((mateEquiv a' b' χ').natTrans.app X) ≫
        (conjugateEquiv (b.comp b') b'' β).app (R₂.obj X) =
      R₀.map ((conjugateEquiv (a.comp a') a'' α).app X) ≫
        (mateEquiv a'' b'' χ'').natTrans.app X := by
  have hh := congrArg (mateEquiv (a.comp a') b'') h
  rw [mateEquiv_conjugateEquiv_vcomp (a.comp a') (b.comp b') b'',
    conjugateEquiv_mateEquiv_vcomp (a.comp a') a'' b'',
    mateEquiv_hcomp a b a' b'] at hh
  have hx := congrArg (fun t ↦ t.natTrans.app X) hh
  simpa only [TwoSquare.hComp, TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, Functor.comp_obj, Category.assoc] using hx

private theorem pushOrdinaryR_formula (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (scalarReductionSource l E X)) :
    (IntegralSystemRealization.calculus l E Y).reduction.map
        ((IntegralSystemRealization.ringedPush l E f).map
            ((IntegralSystemRealization.calculus l E X).adjunction.unit.app K) ≫
          (o.realization.push l E f).inv.app
            ((IntegralSystemRealization.calculus l E X).reduction.obj K)) ≫
        pushR l E o f K =
      (pushOrdinaryR l E o f).app K := by
  exact mate_reconstruction
    (IntegralSystemRealization.calculus l E X).adjunction
    (IntegralSystemRealization.calculus l E Y).adjunction
    (IntegralSystemRealization.ringedAdj l E f) (o.system.direct f).adj
    (o.realization.reductionPull f).symm K

private def Word.ordinaryR (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    {a : S} → (B : Word W location a) →
      (IntegralSystemRealization.calculus l E (W a)).reduction.obj
        (B.ringedValue l E W location o K) ⟶
      B.systemValue l E W location o (inputReduction l E W location K)
  | _, .input _ => 𝟙 _
  | a, .unit _ => (o.unitReduction (W a)).hom
  | a, .tensor B C => (tensorOrdinaryR l E o (W a)).app
      (B.ringedValue l E W location o K, C.ringedValue l E W location o K) ≫
        (IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.map
          (Prod.mkHom (B.ordinaryR l E o K) (C.ordinaryR l E o K))
  | _, .pull f _ _ _ B =>
      (o.realization.reductionPull f).hom.app (B.ringedValue l E W location o K) ≫
        (IntegralSystemRealization.pull l E f).map (B.ordinaryR l E o K)
  | _, .push f _ _ _ _ B =>
      (pushOrdinaryR l E o f).app (B.ringedValue l E W location o K) ≫
        (IntegralSystemRealization.Operations.push l E o.system f).map
          (B.ordinaryR l E o K)
  | _, .open j hj _ B => let := hj
      inverseOrZero ((o.realization.openReduction l E j).app
        (B.ringedValue l E W location o K)) ≫
      (IntegralSystemRealization.Operations.shriek l E o.system j).map
        (B.ordinaryR l E o K)


private theorem enriched_right_unitor {A N : Type*} [Category A] [Category N]
    {HA : Aᵒᵖ × A ⥤ A} {HN : Nᵒᵖ × N ⥤ N}
    (TA : CoefficientClosedStructure HA) (TN : CoefficientClosedStructure HN)
    (F : A ⥤ N) (μ : TA.tensor ⋙ F ≅ F.prod F ⋙ TN.tensor)
    (h : CoefficientEvaluationCompatible TA TN F μ)
    (ι : F.obj TA.monoidal.tensorUnit ≅ TN.monoidal.tensorUnit)
    (hι : ∀ X : A,
      μ.inv.app (TA.monoidal.tensorUnit, X) ≫ F.map (TA.monoidal.leftUnitor X).hom =
        TN.tensor.map (Prod.mkHom ι.hom (𝟙 (F.obj X))) ≫
          (TN.monoidal.leftUnitor (F.obj X)).hom) (X : A) :
    μ.hom.app (X, TA.monoidal.tensorUnit) ≫
        TN.tensor.map (Prod.mkHom (𝟙 (F.obj X)) ι.hom) ≫
        (TN.monoidal.rightUnitor (F.obj X)).hom =
      F.map (TA.monoidal.rightUnitor X).hom := by
  let := TA.monoidal
  let := TN.monoidal
  dsimp only [CoefficientClosedStructure.tensor] at μ
  dsimp only [CoefficientClosedStructure.tensor] at *
  let U := TA.monoidal.tensorUnit
  let V := F.obj U
  have ha := enriched_associativity TA TN F μ h X U U
  have hn := μ.hom.naturality (Prod.mkHom (𝟙 X) (TA.monoidal.leftUnitor U).hom)
  have hr := μ.hom.naturality (Prod.mkHom (TA.monoidal.rightUnitor X).hom (𝟙 U))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn hr
  simp only [CategoryTheory.Functor.map_id] at hn hr
  have hh := congrArg (fun z ↦ z ≫ TN.tensor.map
    (Prod.mkHom (𝟙 (F.obj X))
      (μ.inv.app (U, U) ≫ F.map (TA.monoidal.leftUnitor U).hom))) ha
  dsimp only [Functor.comp_obj, Functor.prod_obj] at ha hh
  dsimp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_obj,
    MonoidalCategory.tensor_map] at hh hn hr
  dsimp only [U] at hn hr
  simp only [Category.assoc] at hh
  simp only [MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id] at hh
  erw [Iso.hom_inv_id_app_assoc] at hh
  erw [← hn, ← F.map_comp_assoc] at hh
  have tr := MonoidalCategory.triangle X U
  rw [← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensorHom_id] at tr
  change (TA.monoidal.associator X U U).hom ≫
      TA.tensor.map (Prod.mkHom (𝟙 X) (TA.monoidal.leftUnitor U).hom) =
    TA.tensor.map (Prod.mkHom (TA.monoidal.rightUnitor X).hom (𝟙 U)) at tr
  dsimp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map] at tr
  erw [tr, hr, hι U] at hh
  have ht := MonoidalCategory.associator_naturality (𝟙 (F.obj X)) ι.hom (𝟙 V)
  have tt := MonoidalCategory.triangle (F.obj X) V
  rw [← MonoidalCategory.id_tensorHom, ← MonoidalCategory.tensorHom_id] at tt
  change TN.tensor.map (Prod.mkHom
      (TN.tensor.map (Prod.mkHom (𝟙 (F.obj X)) ι.hom)) (𝟙 V)) ≫
      (TN.monoidal.associator (F.obj X) TN.monoidal.tensorUnit V).hom =
    (TN.monoidal.associator (F.obj X) V V).hom ≫
      TN.tensor.map (Prod.mkHom (𝟙 (F.obj X))
        (TN.tensor.map (Prod.mkHom ι.hom (𝟙 V)))) at ht
  change (TN.monoidal.associator (F.obj X) TN.monoidal.tensorUnit V).hom ≫
      TN.tensor.map (Prod.mkHom (𝟙 (F.obj X)) (TN.monoidal.leftUnitor V).hom) =
    TN.tensor.map (Prod.mkHom (TN.monoidal.rightUnitor (F.obj X)).hom (𝟙 V)) at tt
  dsimp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map] at ht tt
  dsimp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map] at hh
  simp only [MonoidalCategory.id_tensorHom, MonoidalCategory.whiskerLeft_comp] at hh ht tt
  erw [← reassoc_of% ht, tt] at hh
  simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    Category.id_comp] at hh
  have hh := (cancel_epi (μ.hom.app (TA.tensor.obj (X, U), U))).1 hh
  let d := μ.hom.app (X, U) ≫
    MonoidalCategory.whiskerLeft (F.obj X) ι.hom ≫
      (TN.monoidal.rightUnitor (F.obj X)).hom
  simp only [MonoidalCategory.tensorHom_comp_tensorHom,
    Category.assoc] at hh
  erw [Category.id_comp] at hh
  change MonoidalCategory.tensorHom d (𝟙 V) =
    MonoidalCategory.tensorHom (F.map (TA.monoidal.rightUnitor X).hom) (𝟙 V) at hh
  have hw := congrArg (fun z ↦ z ≫ MonoidalCategory.tensorHom (𝟙 (F.obj X)) ι.hom ≫
      (TN.monoidal.rightUnitor (F.obj X)).hom) hh
  have nd := MonoidalCategory.rightUnitor_naturality d
  have nf := MonoidalCategory.rightUnitor_naturality (F.map (TA.monoidal.rightUnitor X).hom)
  simp only [MonoidalCategory.tensorHom_def', MonoidalCategory.whiskerLeft_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp, Category.comp_id] at hw
  simp only [← MonoidalCategory.whisker_exchange_assoc, nd, nf] at hw
  have hd := (cancel_epi
    (MonoidalCategory.whiskerLeft (F.obj (TA.tensor.obj (X, U))) ι.hom ≫
      (TN.monoidal.rightUnitor (F.obj (TA.tensor.obj (X, U)))).hom)).1
        (by simpa only [U, V, Functor.comp_obj, CoefficientClosedStructure.tensor,
          MonoidalCategory.tensor_obj, Category.assoc] using hw)
  dsimp only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map]
  erw [MonoidalCategory.id_tensorHom]
  exact hd

private theorem comparison_right_unitor {A N : Type*} [Category A] [Category N]
    {HA : Aᵒᵖ × A ⥤ A} {HN : Nᵒᵖ × N ⥤ N}
    (TA : CoefficientClosedStructure HA) (TN : CoefficientClosedStructure HN)
    (F : A ⥤ N) (μ : TA.tensor ⋙ F ≅ F.prod F ⋙ TN.tensor)
    (h : CoefficientEvaluationCompatible TA TN F μ)
    (ι : F.obj TA.monoidal.tensorUnit ≅ TN.monoidal.tensorUnit)
    (hι : ∀ X : A,
      μ.inv.app (TA.monoidal.tensorUnit, X) ≫ F.map (TA.monoidal.leftUnitor X).hom =
        TN.tensor.map (Prod.mkHom ι.hom (𝟙 (F.obj X))) ≫
          (TN.monoidal.leftUnitor (F.obj X)).hom)
    (T : A × A ⥤ A) (e : T = TA.tensor) (X : A) (Y : N) (q : F.obj X ⟶ Y) :
    (Functor.whiskerRight (eqToIso e).hom F ≫ μ.hom).app
        (X, TA.monoidal.tensorUnit) ≫
        TN.tensor.map (Prod.mkHom q ι.hom) ≫ (TN.monoidal.rightUnitor Y).hom =
      F.map ((eqToIso (congrArg (fun U : A × A ⥤ A ↦
        U.obj (X, TA.monoidal.tensorUnit)) e)).hom ≫
          (TA.monoidal.rightUnitor X).hom) ≫ q := by
  subst T
  let := TA.monoidal
  let := TN.monoidal
  dsimp only [CoefficientClosedStructure.tensor] at μ
  dsimp only [CoefficientClosedStructure.tensor] at *
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    NatTrans.id_app, Functor.comp_obj, CategoryTheory.Functor.map_id,
    Category.id_comp]
  have hr := enriched_right_unitor TA TN F μ h ι hι X
  rw [← hr]
  have hn := MonoidalCategory.rightUnitor_naturality q
  rw [← MonoidalCategory.tensorHom_id] at hn
  change TN.tensor.map (Prod.mkHom q (𝟙 _)) ≫ (TN.monoidal.rightUnitor Y).hom =
    (TN.monoidal.rightUnitor (F.obj X)).hom ≫ q at hn
  dsimp only [CoefficientClosedStructure.tensor] at *
  simp only [Category.assoc]
  erw [← hn]
  simp only [← Category.assoc, ← (MonoidalCategory.tensor N).map_comp, prod_comp,
    Category.id_comp, Category.comp_id]

private theorem inverseOrZero_eq_inv {A : Type*} [Category A] [HasZeroMorphisms A]
    {X Y : A} (f : X ⟶ Y) [IsIso f] : inverseOrZero f = inv f := by
  classical
  simp only [inverseOrZero, dif_pos (inferInstance : IsIso f)]

private theorem inverse_mate_unit_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasZeroMorphisms D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (χ : Q ⋙ R ⟶ T ⋙ G) {X : A} {Y : C} (q : R.obj X ⟶ Y)
    [IsIso (((mateEquiv a b).symm χ).natTrans.app X)] :
    q ≫ b.unit.app Y = R.map (a.unit.app X) ≫ χ.app (P.obj X) ≫
      G.map (inverseOrZero (((mateEquiv a b).symm χ).natTrans.app X) ≫ F.map q) := by
  have hm := unit_mateEquiv_symm a b χ X
  rw [inverseOrZero_eq_inv, G.map_comp, ← Category.assoc, ← Category.assoc, hm]
  simp only [Category.assoc, ← G.map_comp_assoc, Functor.comp_obj,
    Functor.id_obj, TwoSquare.natTrans, IsIso.hom_inv_id, G.map_id, Category.id_comp]
  exact b.unit.naturality q

private theorem inverse_mate_counit_square
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasZeroMorphisms D]
    {P : A ⥤ B} {Q : B ⥤ A} {F : C ⥤ D} {G : D ⥤ C}
    {R : A ⥤ C} {T : B ⥤ D} (a : P ⊣ Q) (b : F ⊣ G)
    (χ : Q ⋙ R ⟶ T ⋙ G) {X : B} {Y : D} (q : T.obj X ⟶ Y)
    [IsIso (((mateEquiv a b).symm χ).natTrans.app (Q.obj X))] :
    inverseOrZero (((mateEquiv a b).symm χ).natTrans.app (Q.obj X)) ≫
        F.map (χ.app X ≫ G.map q) ≫ b.counit.app Y =
      T.map (a.counit.app X) ≫ q := by
  have hm := mateEquiv_counit_symm a b χ X
  have hn := b.counit.naturality q
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [inverseOrZero_eq_inv, F.map_comp, Category.assoc, hn,
    reassoc_of% hm, IsIso.inv_hom_id_assoc]

private theorem isIso_of_inverseOrZero {A : Type*} [Category A] [HasZeroMorphisms A]
    {X Y : A} (f : X ⟶ Y) [IsIso (inverseOrZero f)] : IsIso f := by
  classical
  by_cases h : IsIso f
  · exact h
  · have hz : IsIso (0 : Y ⟶ X) := by
      simpa only [inverseOrZero, dif_neg h] using
        (inferInstance : IsIso (inverseOrZero f))
    obtain ⟨hY, hX⟩ := (Limits.isIsoZeroEquiv Y X) hz
    exact ⟨⟨0, by simp only [comp_zero, hX], by simp only [zero_comp, hY]⟩⟩

private theorem inverse_square {A : Type*} [Category A] [HasZeroMorphisms A]
    {X Y X' Y' : A} (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    [IsIso a] [IsIso b] (h : f ≫ b = a ≫ g) :
    g ≫ inverseOrZero b = inverseOrZero a ≫ f := by
  rw [inverseOrZero_eq_inv, inverseOrZero_eq_inv]
  apply (cancel_epi a).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem inverse_naturality {A N : Type*} [Category A] [Category N]
    [HasZeroMorphisms N] {F G : A ⥤ N} (α : F ⟶ G) {X Y : A} (f : X ⟶ Y)
    [IsIso (α.app X)] [IsIso (α.app Y)] :
    G.map f ≫ inverseOrZero (α.app Y) = inverseOrZero (α.app X) ≫ F.map f := by
  apply inverse_square
  exact α.naturality f

private theorem natTrans_isIso_at_iso {A N : Type*} [Category A] [Category N]
    {F G : A ⥤ N} (α : F ⟶ G) {X Y : A} (f : X ⟶ Y) [IsIso f]
    [IsIso (α.app X)] : IsIso (α.app Y) := by
  have hh : IsIso (F.map f ≫ α.app Y) := by
    rw [α.naturality f]
    infer_instance
  exact IsIso.of_isIso_comp_left (F.map f) _

private theorem inverseOrZero_naturality_iso {A N : Type*} [Category A] [Category N]
    [HasZeroMorphisms N] {F G : A ⥤ N} (α : F ⟶ G) {X Y : A}
    (f : X ⟶ Y) [IsIso f] :
    G.map f ≫ inverseOrZero (α.app Y) = inverseOrZero (α.app X) ≫ F.map f := by
  classical
  by_cases hx : IsIso (α.app X)
  · have := natTrans_isIso_at_iso α f
    exact inverse_naturality α f
  · have hy : ¬ IsIso (α.app Y) := by
      intro hY
      exact hx (natTrans_isIso_at_iso α (inv f))
    simp only [inverseOrZero, dif_neg hx, dif_neg hy, comp_zero, zero_comp]

private theorem partial_comparison_naturality {A N : Type*} [Category A] [Category N]
    [HasZeroMorphisms N] {F G H : A ⥤ N} (α : F ⟶ G) (β : F ⟶ H)
    {X Y : A} (f : X ⟶ Y) [IsIso (inverseOrZero (α.app X))]
    [IsIso (inverseOrZero (α.app Y))] :
    G.map f ≫ (inverseOrZero (α.app Y) ≫ β.app Y) =
      (inverseOrZero (α.app X) ≫ β.app X) ≫ H.map f := by
  have := isIso_of_inverseOrZero (α.app X)
  have := isIso_of_inverseOrZero (α.app Y)
  rw [← Category.assoc, inverse_naturality α f, Category.assoc, β.naturality,
    ← Category.assoc]

private theorem tensorR_naturality (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    (X : Scheme.{u})
    {K K' L L' : DerivedCategory (scalarReductionSource l E X)} (f : K ⟶ K') (g : L ⟶ L')
    [IsIso (tensorR l E o X K L)] [IsIso (tensorR l E o X K' L')] :
    (IntegralSystemRealization.calculus l E X).reduction.map
        ((integralCompletedTensor l E X).map (Prod.mkHom f g)) ≫
      tensorR l E o X K' L' = tensorR l E o X K L ≫
        (IntegralSystemRealization.calculus l E X).systemClosed.tensor.map
          (Prod.mkHom ((IntegralSystemRealization.calculus l E X).reduction.map f)
            ((IntegralSystemRealization.calculus l E X).reduction.map g)) := by
  let R := (IntegralSystemRealization.calculus l E X).reduction
  let α := Functor.whiskerRight (tensorCompletion l E o X) R
  let β := Functor.whiskerRight
    (eqToIso (o.ringed.tensorClosed X)).hom R ≫
      (IntegralSystemRealization.calculus l E X).reductionTensor.hom
  have hinv (P Q : DerivedCategory (scalarReductionSource l E X))
      [IsIso (tensorR l E o X P Q)] : IsIso (inverseOrZero (α.app (P, Q))) := by
    have : IsIso (inverseOrZero (α.app (P, Q)) ≫ β.app (P, Q)) :=
      by simpa only [α, β, NatTrans.comp_app, Functor.whiskerRight_app, eqToIso.hom,
        eqToHom_app, tensorR, Category.assoc] using
          (inferInstance : IsIso (tensorR l E o X P Q))
    have hβ : IsIso (β.app (P, Q)) := by
      dsimp only [β, NatTrans.comp_app, Functor.whiskerRight_app]
      infer_instance
    exact IsIso.of_isIso_comp_right (inverseOrZero (α.app (P, Q))) (β.app (P, Q))
  have := hinv K L
  have := hinv K' L'
  simpa only [α, β, NatTrans.comp_app, Functor.whiskerRight_app, eqToIso.hom,
    eqToHom_app, tensorR, Category.assoc, Functor.comp_map, Functor.prod_map, R] using
      partial_comparison_naturality α β (Prod.mkHom f g)

private theorem pullR_naturality (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    {X Y : Scheme.{u}} (v : X ⟶ Y)
    {K L : DerivedCategory (scalarReductionSource l E Y)} (f : K ⟶ L)
    [IsIso (pullR l E o v K)] [IsIso (pullR l E o v L)] :
    (IntegralSystemRealization.calculus l E X).reduction.map
        ((integralDerivedPullback l E v).map f) ≫ pullR l E o v L =
      pullR l E o v K ≫ (IntegralSystemRealization.pull l E v).map
        ((IntegralSystemRealization.calculus l E Y).reduction.map f) := by
  let α := Functor.whiskerRight ((o.ringed.pull v).unit l E)
    (IntegralSystemRealization.calculus l E X).reduction
  let β := (o.realization.reductionPull v).hom
  have hβ (P : DerivedCategory (scalarReductionSource l E Y)) : IsIso (β.app P) :=
    inferInstance
  have hinv (P : DerivedCategory (scalarReductionSource l E Y))
      [IsIso (pullR l E o v P)] : IsIso (inverseOrZero (α.app P)) := by
    have : IsIso (inverseOrZero (α.app P) ≫ β.app P) :=
      (inferInstance : IsIso (pullR l E o v P))
    exact IsIso.of_isIso_comp_right (inverseOrZero (α.app P)) (β.app P)
  have := hinv K
  have := hinv L
  exact partial_comparison_naturality α β f

private theorem openR_naturality (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    {K L : DerivedCategory (scalarReductionSource l E X)} (f : K ⟶ L)
    [IsIso (openR l E o j K)] [IsIso (openR l E o j L)] :
    (IntegralSystemRealization.calculus l E Y).reduction.map
        ((IntegralSystemRealization.ringedOpen l E j).map f) ≫ openR l E o j L =
      openR l E o j K ≫ (IntegralSystemRealization.Operations.shriek l E o.system j).map
        ((IntegralSystemRealization.calculus l E X).reduction.map f) := by
  have hK : IsIso (inverseOrZero ((o.realization.openReduction l E j).app K)) :=
    (inferInstance : IsIso (openR l E o j K))
  have hL : IsIso (inverseOrZero ((o.realization.openReduction l E j).app L)) :=
    (inferInstance : IsIso (openR l E o j L))
  have := isIso_of_inverseOrZero ((o.realization.openReduction l E j).app K)
  have := isIso_of_inverseOrZero ((o.realization.openReduction l E j).app L)
  exact inverse_naturality (o.realization.openReduction l E j) f

private theorem counit_iso_of_iso {A : Type*} [Category A] {N : Type*} [Category N]
    {R : A ⥤ N} {L : N ⥤ A} (adj : R ⊣ L) {X Y : N} (f : X ⟶ Y)
    [IsIso f] [IsIso (adj.counit.app Y)] : IsIso (adj.counit.app X) := by
  have : IsIso (adj.counit.app X ≫ f) := by
    have hn := adj.counit.naturality f
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ f


private theorem word_r_isIso (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (hc : ∀ (a : S) (N : coefficientSequenceDerived l E (W a)),
      IsNormalizedCoefficientSequence l E (W a) N →
        IsIso ((IntegralSystemRealization.calculus l E (W a)).adjunction.counit.app N))
    {a : S} (B : Word W location a) (lo hi torLo torHi : ℤ)
    (hB : B.admissible l E W location o K lo hi torLo torHi)
    (hp : B.primitiveFormulas l E W location o K) :
    IsIso (B.r l E W location o K) := by
  induction B with
  | input k => dsimp only [Word.r]; infer_instance
  | unit a => dsimp only [Word.r]; infer_instance
  | @tensor a B C ihB ihC =>
    have := ihB hB.2.1 hp.2.1
    have := ihC hB.2.2 hp.2.2
    have hε := hc a _ hB.1.1
    dsimp only [Word.systemValue] at hε
    have hmap : IsIso ((IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.map
        (Prod.mkHom (B.r l E W location o K) (C.r l E W location o K))) := by
      have : IsIso (Prod.mkHom (B.r l E W location o K)
          (C.r l E W location o K)) := (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
      infer_instance
    have := counit_iso_of_iso
      (IntegralSystemRealization.calculus l E (W a)).adjunction
      (f := (IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.map
        (Prod.mkHom (B.r l E W location o K) (C.r l E W location o K)))
    dsimp only [Word.r]
    rw [hp.1]
    infer_instance
  | @pull a b f hs ht hq B ih =>
    have := ih hB.2 hp.2
    have hε := hc a _ hB.1.1
    dsimp only [Word.systemValue] at hε
    have := counit_iso_of_iso
      (IntegralSystemRealization.calculus l E (W a)).adjunction
      ((IntegralSystemRealization.pull l E f).map (B.r l E W location o K))
    dsimp only [Word.r]
    rw [hp.1]
    infer_instance
  | @push a b f hs ht hq hproper B ih =>
    have := ih hB.2 hp.2
    have hε := hc b _ hB.1.1
    dsimp only [Word.systemValue] at hε
    have := counit_iso_of_iso
      (IntegralSystemRealization.calculus l E (W b)).adjunction
      ((IntegralSystemRealization.Operations.push l E o.system f).map
        (B.r l E W location o K))
    dsimp only [Word.r]
    rw [hp.1]
    infer_instance
  | @«open» a b j hj hq B ih =>
    let := hj
    have := ih hB.2 hp.2.2.2
    have hε := hc b _ hB.1.1
    dsimp only [Word.systemValue] at hε
    have := counit_iso_of_iso
      (IntegralSystemRealization.calculus l E (W b)).adjunction
      ((IntegralSystemRealization.Operations.shriek l E o.system j).map
        (B.r l E W location o K))
    have : IsIso (openDInv l E o j (B.integralValue l E W location o K)) :=
      ⟨⟨openD l E o j (B.integralValue l E W location o K), hp.2.2.1, hp.2.1⟩⟩
    dsimp only [Word.r]
    rw [hp.1]
    infer_instance


private theorem word_r_naturality (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (o : Operations l E)
    (K L : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (f : ∀ k : I, K k ⟶ L k)
    (hc : ∀ (a : S) (N : coefficientSequenceDerived l E (W a)),
      IsNormalizedCoefficientSequence l E (W a) N →
        IsIso ((IntegralSystemRealization.calculus l E (W a)).adjunction.counit.app N))
    {a : S} (B : Word W location a) (lo hi torLo torHi : ℤ)
    (hK : B.admissible l E W location o K lo hi torLo torHi)
    (hL : B.admissible l E W location o L lo hi torLo torHi)
    (hpK : B.primitiveFormulas l E W location o K)
    (hpL : B.primitiveFormulas l E W location o L) :
    (IntegralSystemRealization.calculus l E (W a)).reduction.map
        (B.integralAction l E o K L f) ≫ B.r l E W location o L =
      B.r l E W location o K ≫ B.systemAction l E o
        (inputReduction l E W location K) (inputReduction l E W location L)
        (fun k ↦ (IntegralSystemRealization.calculus l E (W (location k))).reduction.map
          (f k)) := by
  have hiso {a : S} (B : Word W location a)
      (M : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
      (ha : B.admissible l E W location o M lo hi torLo torHi)
      (hp : B.primitiveFormulas l E W location o M) :
      IsIso (B.r l E W location o M) := word_r_isIso l E o M hc B lo hi torLo torHi ha hp
  induction B with
  | input k =>
    dsimp only [Word.integralAction, Word.systemAction, Word.r]
    simp only [Category.id_comp, Category.comp_id]
  | unit a =>
    dsimp only [Word.integralAction, Word.integralValue, Word.systemAction, Word.r,
      Word.systemValue]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  | @tensor a B C ihB ihC =>
    have hBK := hiso B K hK.2.1 hpK.2.1
    have hCK := hiso C K hK.2.2 hpK.2.2
    have hBL := hiso B L hL.2.1 hpL.2.1
    have hCL := hiso C L hL.2.2 hpL.2.2
    have hTK := hiso (.tensor B C) K hK hpK
    have hTL := hiso (.tensor B C) L hL hpL
    have ht (M) (hB : IsIso (B.r l E W location o M))
        (hC : IsIso (C.r l E W location o M))
        (hT : IsIso ((Word.tensor B C).r l E W location o M)) :
        IsIso (tensorR l E o (W a) (B.integralValue l E W location o M)
          (C.integralValue l E W location o M)) := by
      dsimp only [Word.r] at hT
      have : IsIso (Prod.mkHom (B.r l E W location o M)
          (C.r l E W location o M)) := (isIso_prod_iff _ _).2 ⟨hB, hC⟩
      exact IsIso.of_isIso_comp_right _
        ((IntegralSystemRealization.calculus l E (W a)).systemClosed.tensor.map
          (Prod.mkHom (B.r l E W location o M) (C.r l E W location o M)))
    have := ht K hBK hCK hTK
    have := ht L hBL hCL hTL
    dsimp only [Word.integralAction, Word.systemAction, Word.r]
    rw [← Category.assoc, tensorR_naturality l E o]
    simp only [Category.assoc, ← Functor.map_comp, prod_comp]
    rw [ihB hK.2.1 hL.2.1 hpK.2.1 hpL.2.1,
      ihC hK.2.2 hL.2.2 hpK.2.2 hpL.2.2]
  | @pull a b v hs ht hq B ih =>
    have hBK := hiso B K hK.2 hpK.2
    have hBL := hiso B L hL.2 hpL.2
    have hPK := hiso (.pull v hs ht hq B) K hK hpK
    have hPL := hiso (.pull v hs ht hq B) L hL hpL
    have ht (M) (hB : IsIso (B.r l E W location o M))
        (hP : IsIso ((Word.pull v hs ht hq B).r l E W location o M)) :
        IsIso (pullR l E o v (B.integralValue l E W location o M)) := by
      dsimp only [Word.r] at hP
      exact IsIso.of_isIso_comp_right _
        ((IntegralSystemRealization.pull l E v).map (B.r l E W location o M))
    have := ht K hBK hPK
    have := ht L hBL hPL
    dsimp only [Word.integralAction, Word.systemAction, Word.r]
    rw [← Category.assoc, pullR_naturality l E o, Category.assoc, ← Functor.map_comp,
      ih hK.2 hL.2 hpK.2 hpL.2, Functor.map_comp, Category.assoc]
  | @push a b v hs ht hq hproper B ih =>
    dsimp only [Word.integralAction, Word.systemAction, Word.r]
    rw [← Category.assoc]
    have hn := (IntegralSystemRealization.calculus l E (W b)).adjunction.counit.naturality
      ((IntegralSystemRealization.Operations.push l E o.system v).map
        ((IntegralSystemRealization.calculus l E (W a)).reduction.map
          (B.integralAction l E o K L f)))
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [show (IntegralSystemRealization.calculus l E (W b)).reduction.map
        ((integralPush l E o v).map (B.integralAction l E o K L f)) ≫
        pushR l E o v (B.integralValue l E W location o L) = _ from hn,
      Category.assoc, ← Functor.map_comp, ih hK.2 hL.2 hpK.2 hpL.2,
      Functor.map_comp, Category.assoc]
    rfl
  | @«open» a b j hj hq B ih =>
    let := hj
    have hBK := hiso B K hK.2 hpK.2.2.2
    have hBL := hiso B L hL.2 hpL.2.2.2
    have hJK := hiso (.open j hj hq B) K hK hpK
    have hJL := hiso (.open j hj hq B) L hL hpL
    have ht (M) (hB : IsIso (B.r l E W location o M))
        (hJ : IsIso ((Word.open j hj hq B).r l E W location o M)) :
        IsIso (openR l E o j (B.integralValue l E W location o M)) := by
      dsimp only [Word.r] at hJ
      exact IsIso.of_isIso_comp_right _
        ((IntegralSystemRealization.Operations.shriek l E o.system j).map
          (B.r l E W location o M))
    have := ht K hBK hJK
    have := ht L hBL hJL
    dsimp only [Word.integralAction, Word.systemAction, Word.r]
    rw [← Category.assoc, openR_naturality l E o, Category.assoc, ← Functor.map_comp,
      ih hK.2 hL.2 hpK.2.2.2 hpL.2.2.2, Functor.map_comp, Category.assoc]


private theorem ordinary_tensor_associator (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) {a : S} (B C D : Word W location a)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    (Word.tensor (Word.tensor B C) D).ordinaryR l E o K ≫
        (GeneratorKind.tensorAssociator B C D).systemMap l E W location o
          (inputReduction l E W location K) =
      (IntegralSystemRealization.calculus l E (W a)).reduction.map
          ((GeneratorKind.tensorAssociator B C D).ringedMap l E W location o K) ≫
        (Word.tensor B (Word.tensor C D)).ordinaryR l E o K := by
  dsimp only [Word.ordinaryR, Word.ringedValue, GeneratorKind.systemMap,
    GeneratorKind.ringedMap, IntegralSystemRealization.ringedAssociator, Iso.trans_hom]
  simpa only [tensorOrdinaryR, Word.systemValue, Category.assoc] using
    comparison_associator
    (IntegralSystemRealization.calculus l E (W a)).integralClosed
    (IntegralSystemRealization.calculus l E (W a)).systemClosed
    (IntegralSystemRealization.calculus l E (W a)).reduction
    (IntegralSystemRealization.calculus l E (W a)).reductionTensor
    (IntegralSystemRealization.calculus l E (W a)).reduction_compatible
    (o.ringed.tensor (W a)).ordinary.tensor (o.ringed.tensorClosed (W a))
    (B.ringedValue l E W location o K) (C.ringedValue l E W location o K)
    (D.ringedValue l E W location o K) _ _ _
    (B.ordinaryR l E o K) (C.ordinaryR l E o K) (D.ordinaryR l E o K)

private theorem ordinary_tensor_left_unitor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) {a : S} (B : Word W location a)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    (Word.tensor (Word.unit a) B).ordinaryR l E o K ≫
        (GeneratorKind.tensorLeftUnit B).systemMap l E W location o
          (inputReduction l E W location K) =
      (IntegralSystemRealization.calculus l E (W a)).reduction.map
          ((GeneratorKind.tensorLeftUnit B).ringedMap l E W location o K) ≫
        B.ordinaryR l E o K := by
  dsimp only [Word.ordinaryR, Word.ringedValue, GeneratorKind.systemMap,
    GeneratorKind.ringedMap]
  simpa only [tensorOrdinaryR, Word.systemValue, Category.assoc] using
    comparison_left_unitor
    (IntegralSystemRealization.calculus l E (W a)).integralClosed
    (IntegralSystemRealization.calculus l E (W a)).systemClosed
    (IntegralSystemRealization.calculus l E (W a)).reduction
    (IntegralSystemRealization.calculus l E (W a)).reductionTensor
    (o.unitReduction (W a)) (o.unitNormalization (W a))
    (o.ringed.tensor (W a)).ordinary.tensor (o.ringed.tensorClosed (W a))
    (B.ringedValue l E W location o K) _ (B.ordinaryR l E o K)

private theorem ordinary_tensor_right_unitor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) {a : S} (B : Word W location a)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    (Word.tensor B (Word.unit a)).ordinaryR l E o K ≫
        (GeneratorKind.tensorRightUnit B).systemMap l E W location o
          (inputReduction l E W location K) =
      (IntegralSystemRealization.calculus l E (W a)).reduction.map
          ((GeneratorKind.tensorRightUnit B).ringedMap l E W location o K) ≫
        B.ordinaryR l E o K := by
  dsimp only [Word.ordinaryR, Word.ringedValue, GeneratorKind.systemMap,
    GeneratorKind.ringedMap]
  simpa only [tensorOrdinaryR, Word.systemValue, Category.assoc] using
    comparison_right_unitor
      (IntegralSystemRealization.calculus l E (W a)).integralClosed
      (IntegralSystemRealization.calculus l E (W a)).systemClosed
      (IntegralSystemRealization.calculus l E (W a)).reduction
      (IntegralSystemRealization.calculus l E (W a)).reductionTensor
      (IntegralSystemRealization.calculus l E (W a)).reduction_compatible
      (o.unitReduction (W a)) (o.unitNormalization (W a))
      (o.ringed.tensor (W a)).ordinary.tensor (o.ringed.tensorClosed (W a))
      (B.ringedValue l E W location o K) _ (B.ordinaryR l E o K)

private theorem ordinary_pull_composition (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) {a b c : S} (f : W a ⟶ W b) (g : W b ⟶ W c)
    (hsf : IsSeparated f) (htf : LocallyOfFiniteType f) (hqf : QuasiCompact f)
    (hsg : IsSeparated g) (htg : LocallyOfFiniteType g) (hqg : QuasiCompact g)
    (hs : IsSeparated (f ≫ g)) (ht : LocallyOfFiniteType (f ≫ g))
    (hq : QuasiCompact (f ≫ g)) (B : Word W location c)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    (Word.pull f hsf htf hqf (Word.pull g hsg htg hqg B)).ordinaryR l E o K ≫
        (GeneratorKind.pullComposition f g hsf htf hqf hsg htg hqg hs ht hq B).systemMap
          l E W location o (inputReduction l E W location K) =
      (IntegralSystemRealization.calculus l E (W a)).reduction.map
          ((GeneratorKind.pullComposition f g hsf htf hqf hsg htg hqg hs ht hq B).ringedMap
            l E W location o K) ≫
        (Word.pull (f ≫ g) hs ht hq B).ordinaryR l E o K := by
  let X := B.ringedValue l E W location o K
  have he := canonicalReductionPullComposition l E o.system o.realization o.composition f g X
  have hn := (o.composition.pullComp f g).inv.naturality (B.ordinaryR l E o K)
  dsimp only [Functor.comp_map] at hn
  dsimp only [Word.ordinaryR, Word.ringedValue, GeneratorKind.systemMap,
    GeneratorKind.ringedMap]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [hn]
  apply (cancel_epi ((IntegralSystemRealization.calculus l E (W a)).reduction.map
    ((IntegralSystemRealization.ringedPullComp l E f g).hom.app X))).1
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  erw [reassoc_of% he, Iso.hom_inv_id_app_assoc]
  dsimp only [X]
  simp only [Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]

private theorem ordinary_push_composition (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) {a b c : S} (f : W a ⟶ W b) (g : W b ⟶ W c)
    (hsf : IsSeparated f) (htf : LocallyOfFiniteType f) (hqf : QuasiCompact f)
    (hpf : IsProper f) (hsg : IsSeparated g) (htg : LocallyOfFiniteType g)
    (hqg : QuasiCompact g) (hpg : IsProper g) (hs : IsSeparated (f ≫ g))
    (ht : LocallyOfFiniteType (f ≫ g)) (hq : QuasiCompact (f ≫ g))
    (hp : IsProper (f ≫ g)) (B : Word W location a)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    (Word.push g hsg htg hqg hpg (Word.push f hsf htf hqf hpf B)).ordinaryR l E o K ≫
        (GeneratorKind.pushComposition f g hsf htf hqf hpf hsg htg hqg hpg
          hs ht hq hp B).systemMap l E W location o (inputReduction l E W location K) =
      (IntegralSystemRealization.calculus l E (W c)).reduction.map
          ((GeneratorKind.pushComposition f g hsf htf hqf hpf hsg htg hqg hpg
            hs ht hq hp B).ringedMap l E W location o K) ≫
        (Word.push (f ≫ g) hs ht hq hp B).ordinaryR l E o K := by
  have h :
      (TwoSquare.vComp (o.realization.reductionPull g).inv
        (o.realization.reductionPull f).inv).whiskerRight
          (o.composition.pullComp f g).hom =
      (TwoSquare.mk _ _ _ _ (o.realization.reductionPull (f ≫ g)).inv).whiskerLeft
        (IntegralSystemRealization.ringedPullComp l E f g).hom := by
    apply NatTrans.ext
    funext X
    dsimp only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
      TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
    simp only [Category.id_comp, Category.comp_id, Functor.comp_obj]
    apply (cancel_epi ((o.realization.reductionPull (f ≫ g)).hom.app X)).1
    simp only [Iso.hom_inv_id_app_assoc]
    erw [← reassoc_of% (canonicalReductionPullComposition l E
      o.system o.realization o.composition f g X)]
    simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]
    exact Category.comp_id _
  have hm := mate_compositor_square
    (IntegralSystemRealization.ringedAdj l E g) (IntegralSystemRealization.ringedAdj l E f)
    (IntegralSystemRealization.ringedAdj l E (f ≫ g))
    (o.system.direct g).adj (o.system.direct f).adj (o.system.direct (f ≫ g)).adj
    (o.realization.reductionPull g).inv (o.realization.reductionPull f).inv
    (o.realization.reductionPull (f ≫ g)).inv
    (IntegralSystemRealization.ringedPullComp l E f g).hom
    (o.composition.pullComp f g).hom h (B.ringedValue l E W location o K)
  have hn := (o.composition.pushComp l E f g).hom.naturality (B.ordinaryR l E o K)
  dsimp only [Functor.comp_map] at hn
  dsimp only [Word.ordinaryR, Word.ringedValue, GeneratorKind.systemMap,
    GeneratorKind.ringedMap]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [hn, reassoc_of% hm]
  rfl

private theorem ordinary_pullPush_unit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) {a b : S} (f : W a ⟶ W b)
    (hs : IsSeparated f) (ht : LocallyOfFiniteType f) (hq : QuasiCompact f)
    (hp : IsProper f) (B : Word W location b)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    B.ordinaryR l E o K ≫
        (GeneratorKind.pullPushUnit f hs ht hq hp B).systemMap l E W location o
          (inputReduction l E W location K) =
      (IntegralSystemRealization.calculus l E (W b)).reduction.map
          ((GeneratorKind.pullPushUnit f hs ht hq hp B).ringedMap l E W location o K) ≫
        (Word.push f hs ht hq hp (Word.pull f hs ht hq B)).ordinaryR l E o K := by
  exact mate_unit_square (IntegralSystemRealization.ringedAdj l E f)
    (o.system.direct f).adj (o.realization.reductionPull f).symm (B.ordinaryR l E o K)

private theorem ordinary_pullPush_counit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) {a b : S} (f : W a ⟶ W b)
    (hs : IsSeparated f) (ht : LocallyOfFiniteType f) (hq : QuasiCompact f)
    (hp : IsProper f) (B : Word W location a)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k)))) :
    (Word.pull f hs ht hq (Word.push f hs ht hq hp B)).ordinaryR l E o K ≫
        (GeneratorKind.pullPushCounit f hs ht hq hp B).systemMap l E W location o
          (inputReduction l E W location K) =
      (IntegralSystemRealization.calculus l E (W a)).reduction.map
          ((GeneratorKind.pullPushCounit f hs ht hq hp B).ringedMap l E W location o K) ≫
        B.ordinaryR l E o K := by
  dsimp only [Word.ordinaryR, GeneratorKind.systemMap, GeneratorKind.ringedMap,
    Word.ringedValue, pushOrdinaryR]
  simpa only [Category.assoc, Iso.symm_inv, Iso.symm_hom] using
    mate_counit_square (IntegralSystemRealization.ringedAdj l E f)
      (o.system.direct f).adj (o.realization.reductionPull f).symm (B.ordinaryR l E o K)


private theorem word_completion_reduction (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    {a : S} (B : Word W location a) (hlen : B.length ≤ 3)
    (ha : B.admissible l E W location o K lo hi torLo torHi) :
    (IntegralSystemRealization.calculus l E (W a)).reduction.map
        (B.completionMap l E W location o K) ≫ B.r l E W location o K =
      B.ordinaryR l E o K := by
  have hc {a : S} (B : Word W location a) (hl : B.length ≤ 3)
      (h : B.admissible l E W location o K lo hi torLo torHi) :
      IsIso (B.completionMap l E W location o K) :=
    completionMap_isIso l E W location o B hl K lo hi torLo torHi hAdm h
  induction B with
  | input k =>
    dsimp only [Word.completionMap, Word.r, Word.ordinaryR]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  | unit a =>
    dsimp only [Word.completionMap, Word.r, Word.ordinaryR]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  | @tensor a B C ihB ihC =>
    have hB : B.length ≤ 3 := by dsimp only [Word.length] at hlen; omega
    have hC : C.length ≤ 3 := by dsimp only [Word.length] at hlen; omega
    have := hc B hB ha.2.1
    have := hc C hC ha.2.2
    have ht := hc (.tensor B C) hlen ha
    have : IsIso (Prod.mkHom (B.completionMap l E W location o K)
        (C.completionMap l E W location o K)) :=
      (Iso.prod (asIso _) (asIso _)).isIso_hom
    dsimp only [Word.completionMap] at ht
    have : IsIso ((o.ringed.tensor (W a)).ordinary.tensor.map
        (Prod.mkHom (B.completionMap l E W location o K)
          (C.completionMap l E W location o K))) := by infer_instance
    have : IsIso ((tensorCompletion l E o (W a)).app
        (B.integralValue l E W location o K, C.integralValue l E W location o K)) := by
      exact IsIso.of_isIso_comp_left
        ((o.ringed.tensor (W a)).ordinary.tensor.map
          (Prod.mkHom (B.completionMap l E W location o K)
            (C.completionMap l E W location o K))) _
    dsimp only [Word.completionMap, Word.r, Word.ordinaryR, tensorR]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc,
      inverseOrZero_eq_inv, IsIso.hom_inv_id_assoc]
    have hn := (tensorOrdinaryR l E o (W a)).naturality
      (Prod.mkHom (B.completionMap l E W location o K)
        (C.completionMap l E W location o K))
    dsimp only [tensorOrdinaryR, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.comp_map, Functor.prod_map] at hn
    simp only [Category.assoc] at hn
    dsimp only [tensorOrdinaryR, NatTrans.comp_app, Functor.whiskerRight_app]
    simp only [eqToIso.hom, eqToHom_app] at hn ⊢
    erw [reassoc_of% hn, ← CategoryTheory.Functor.map_comp]
    simp only [prod_comp]
    erw [ihB hB ha.2.1, ihC hC ha.2.2]
    exact (Category.assoc _ _ _).symm
  | @pull a b v hs ht hq B ih =>
    have hB : B.length ≤ 3 := by dsimp only [Word.length] at hlen; omega
    have := hc B hB ha.2
    have hh := hc (.pull v hs ht hq B) hlen ha
    dsimp only [Word.completionMap] at hh
    have : IsIso (((o.ringed.pull v).unit l E).app
        (B.integralValue l E W location o K)) :=
      IsIso.of_isIso_comp_left
        ((IntegralSystemRealization.ringedPull l E v).map
          (B.completionMap l E W location o K)) _
    dsimp only [Word.completionMap, Word.r, Word.ordinaryR, pullR]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc,
      inverseOrZero_eq_inv, IsIso.hom_inv_id_assoc]
    erw [← Category.assoc, (o.realization.reductionPull v).hom.naturality,
      Category.assoc]
    simp only [Functor.comp_map]
    erw [← CategoryTheory.Functor.map_comp, ih hB ha.2]
  | @push a b v hs ht hq hp B ih =>
    have hB : B.length ≤ 3 := by dsimp only [Word.length] at hlen; omega
    dsimp only [Word.completionMap, Word.r, Word.ordinaryR]
    erw [CategoryTheory.Functor.map_comp, Category.assoc,
      reassoc_of% (pushOrdinaryR_formula l E o v
        (B.integralValue l E W location o K)),
      ]
    have hn := (pushOrdinaryR l E o v).naturality
      (B.completionMap l E W location o K)
    dsimp only [Functor.comp_map] at hn
    erw [reassoc_of% hn]
    erw [← CategoryTheory.Functor.map_comp, ih hB ha.2]
  | @«open» a b j hj hq B ih =>
    let := hj
    have hB : B.length ≤ 3 := by dsimp only [Word.length] at hlen; omega
    have := hc B hB ha.2
    dsimp only [Word.completionMap, Word.r, Word.ordinaryR, openR]
    erw [← Category.assoc,
      inverseOrZero_naturality_iso (o.realization.openReduction l E j)
        (B.completionMap l E W location o K),
      Category.assoc]
    simp only [Functor.comp_map]
    erw [← CategoryTheory.Functor.map_comp, ih hB ha.2]


private theorem word_ordinaryR_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E)
    (hc : ∀ (a : S) (N : coefficientSequenceDerived l E (W a)),
      IsNormalizedCoefficientSequence l E (W a) N →
        IsIso ((IntegralSystemRealization.calculus l E (W a)).adjunction.counit.app N))
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    {a : S} (B : Word W location a) (hB : B.length ≤ 3)
    (haB : B.admissible l E W location o K lo hi torLo torHi)
    (hpB : B.primitiveFormulas l E W location o K) :
    IsIso (B.ordinaryR l E o K) := by
  have := completionMap_isIso l E W location o B hB K
    lo hi torLo torHi hAdm haB
  have := word_r_isIso l E o K hc B lo hi torLo torHi haB hpB
  rw [← word_completion_reduction l E o K lo hi torLo torHi hAdm B hB haB]
  infer_instance

private theorem open_comparison_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) {a b : S} (j : W a ⟶ W b) (hj : IsOpenImmersion j)
    (hq : QuasiCompact j) (B : Word W location a)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    [IsIso (B.ordinaryR l E o K)]
    [IsIso ((Word.open j hj hq B).ordinaryR l E o K)] :
    IsIso ((o.realization.openReduction l E j).app
      (B.ringedValue l E W location o K)) := by
  let := hj
  have hJ : IsIso ((Word.open j hj hq B).ordinaryR l E o K) := inferInstance
  dsimp only [Word.ordinaryR] at hJ
  have hh : IsIso (inverseOrZero ((o.realization.openReduction l E j).app
      (B.ringedValue l E W location o K))) := by
    exact IsIso.of_isIso_comp_right _
      ((IntegralSystemRealization.Operations.shriek l E o.system j).map
        (B.ordinaryR l E o K))
  exact isIso_of_inverseOrZero _

private theorem ordinary_open_unit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) {a b : S} (j : W a ⟶ W b) (hj : IsOpenImmersion j)
    (hq : QuasiCompact j) (B : Word W location a)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    [hα : IsIso ((o.realization.openReduction l E j).app
      (B.ringedValue l E W location o K))] :
    B.ordinaryR l E o K ≫
        (GeneratorKind.openUnit j hj hq B).systemMap l E W location o
          (inputReduction l E W location K) =
      (IntegralSystemRealization.calculus l E (W a)).reduction.map
          ((GeneratorKind.openUnit j hj hq B).ringedMap l E W location o K) ≫
        (Word.pull j (by let := hj; infer_instance) (by let := hj; infer_instance)
          hq (Word.open j hj hq B)).ordinaryR l E o K := by
  let := hj
  have : IsIso (((mateEquiv (IntegralSystemRealization.ringedOpenAdj l E j)
    (o.system.extension j).adj).symm (o.realization.reductionPull j).hom).natTrans.app
      (B.ringedValue l E W location o K)) := hα
  exact inverse_mate_unit_square (IntegralSystemRealization.ringedOpenAdj l E j)
    (o.system.extension j).adj (o.realization.reductionPull j).hom
    (B.ordinaryR l E o K)

private theorem ordinary_open_counit (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E) {a b : S} (j : W a ⟶ W b) (hj : IsOpenImmersion j)
    (hq : QuasiCompact j) (B : Word W location b)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    [hα : IsIso ((o.realization.openReduction l E j).app
      ((IntegralSystemRealization.ringedPull l E j).obj
        (B.ringedValue l E W location o K)))] :
    (Word.open j hj hq (Word.pull j (by let := hj; infer_instance)
      (by let := hj; infer_instance) hq B)).ordinaryR l E o K ≫
        (GeneratorKind.openCounit j hj hq B).systemMap l E W location o
          (inputReduction l E W location K) =
      (IntegralSystemRealization.calculus l E (W b)).reduction.map
          ((GeneratorKind.openCounit j hj hq B).ringedMap l E W location o K) ≫
        B.ordinaryR l E o K := by
  let := hj
  have : IsIso (((mateEquiv (IntegralSystemRealization.ringedOpenAdj l E j)
    (o.system.extension j).adj).symm (o.realization.reductionPull j).hom).natTrans.app
      ((IntegralSystemRealization.ringedPull l E j).obj
        (B.ringedValue l E W location o K))) := hα
  dsimp only [Word.ordinaryR, GeneratorKind.systemMap, GeneratorKind.ringedMap,
    Word.ringedValue]
  simpa only [IntegralSystemRealization.RealizationModel.openReduction,
    IntegralSystemRealization.ringedOpenAdj, IntegralSystemRealization.Operations.shriek,
    TwoSquare.natTrans, Functor.comp_obj, Functor.id_obj, Category.assoc] using
    inverse_mate_counit_square (IntegralSystemRealization.ringedOpenAdj l E j)
      (o.system.extension j).adj (o.realization.reductionPull j).hom
      (B.ordinaryR l E o K)


private theorem assertion_of_ordinary_square (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C)
    (hB : B.length ≤ 3) (hC : C.length ≤ 3)
    (haB : B.admissible l E W location o K lo hi torLo torHi)
    (haC : C.admissible l E W location o K lo hi torLo torHi)
    (h : B.ordinaryR l E o K ≫
        g.systemMap l E W location o (inputReduction l E W location K) =
      (IntegralSystemRealization.calculus l E (W a)).reduction.map
        (g.ringedMap l E W location o K) ≫ C.ordinaryR l E o K) :
    Assertion l E W location o K g := by
  have := completionMap_isIso l E W location o B hB K
    lo hi torLo torHi hAdm haB
  unfold Assertion
  apply (cancel_epi ((IntegralSystemRealization.calculus l E (W a)).reduction.map
    (B.completionMap l E W location o K))).1
  dsimp only [GeneratorKind.integralMap]
  rw [inverseOrZero_eq_inv, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv]
  simp only [← Category.assoc]
  rw [word_completion_reduction l E o K lo hi torLo torHi hAdm B hB haB,
    h, Category.assoc,
    word_completion_reduction l E o K lo hi torLo torHi hAdm C hC haC]
  simp only [IsIso.hom_inv_id, Category.id_comp]


private theorem system_generator_naturality (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E)
    (M N : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    (f : ∀ k : I, M k ⟶ N k) {a : S} {B C : Word W location a}
    (g : GeneratorKind W location B C) (hg : g.IsTensorAdjunction) :
    B.systemAction l E o M N f ≫ g.systemMap l E W location o N =
      g.systemMap l E W location o M ≫ C.systemAction l E o M N f := by
  cases g with
  | @tensorAssociator a B C D =>
    let := (IntegralSystemRealization.calculus l E (W a)).systemClosed.monoidal
    exact MonoidalCategory.associator_naturality
      (B.systemAction l E o M N f) (C.systemAction l E o M N f)
      (D.systemAction l E o M N f)
  | @tensorLeftUnit a C =>
    let := (IntegralSystemRealization.calculus l E (W a)).systemClosed.monoidal
    dsimp only [Word.systemAction, GeneratorKind.systemMap, Word.systemValue]
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
      MonoidalCategory.id_tensorHom] using
      MonoidalCategory.leftUnitor_naturality (C.systemAction l E o M N f)
  | @tensorRightUnit a C =>
    let := (IntegralSystemRealization.calculus l E (W a)).systemClosed.monoidal
    dsimp only [Word.systemAction, GeneratorKind.systemMap, Word.systemValue]
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
      MonoidalCategory.tensorHom_id] using
      MonoidalCategory.rightUnitor_naturality (C.systemAction l E o M N f)
  | @pullComposition a b c v w _ _ _ _ _ _ _ _ _ B =>
    exact (o.composition.pullComp v w).inv.naturality (B.systemAction l E o M N f)
  | @pushComposition a b c v w _ _ _ _ _ _ _ _ _ _ _ _ B =>
    exact (o.composition.pushComp l E v w).hom.naturality (B.systemAction l E o M N f)
  | @pullPushUnit a b v _ _ _ _ B =>
    exact (o.system.direct v).adj.unit.naturality (B.systemAction l E o M N f)
  | @pullPushCounit a b v _ _ _ _ C =>
    exact (o.system.direct v).adj.counit.naturality (C.systemAction l E o M N f)
  | @openUnit a b j hj _ B =>
    let := hj
    exact (o.system.extension j).adj.unit.naturality (B.systemAction l E o M N f)
  | @openCounit a b j hj _ C =>
    let := hj
    exact (o.system.extension j).adj.counit.naturality (C.systemAction l E o M N f)
  | openBaseChange => exact hg.elim
  | openTensor => exact hg.elim
  | properOpenInterchange => exact hg.elim
  | properOpenLambda => exact hg.elim


private theorem system_generator_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E)
    (M : ∀ k : I, coefficientSequenceDerived l E (W (location k)))
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C)
    (hg : g.IsTensorCompositionIso) : IsIso (g.systemMap l E W location o M) := by
  cases g <;> first
  | exact hg.elim
  | (dsimp only [GeneratorKind.systemMap]; infer_instance)


private theorem ringed_generator_isIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C)
    (hg : g.IsTensorCompositionIso) : IsIso (g.ringedMap l E W location o K) := by
  cases g <;> first
  | exact hg.elim
  | (dsimp only [GeneratorKind.ringedMap]; infer_instance)


private theorem reverse_generator_square (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C)
    (hg : g.IsTensorCompositionIso)
    [IsIso (B.completionMap l E W location o K)]
    [IsIso (C.completionMap l E W location o K)]
    (h : Assertion l E W location o K g) :
    C.r l E W location o K ≫
        inverseOrZero (g.systemMap l E W location o (inputReduction l E W location K)) =
      (IntegralSystemRealization.calculus l E (W a)).reduction.map
          (inverseOrZero (g.integralMap l E W location o K)) ≫
        B.r l E W location o K := by
  have := system_generator_isIso l E o (inputReduction l E W location K) g hg
  have := ringed_generator_isIso l E o K g hg
  have : IsIso (g.integralMap l E W location o K) := by
    dsimp only [GeneratorKind.integralMap]
    rw [inverseOrZero_eq_inv]
    infer_instance
  rw [inverseOrZero_eq_inv]
  rw [inverseOrZero_eq_inv, CategoryTheory.Functor.map_inv]
  simpa only [inverseOrZero_eq_inv] using
    (inverse_square (B.r l E W location o K) (C.r l E W location o K)
    ((IntegralSystemRealization.calculus l E (W a)).reduction.map
      (g.integralMap l E W location o K))
    (g.systemMap l E W location o (inputReduction l E W location K)) h)


/-- Whole-system coefficient squares for the stated short structural generators,
including the reverse of each invertible constraint.
Source: blueprint main-20261015, sec-six-functors/sk-thm-sf-package/
fix-prop-coherence.proof.md, maps-used sentence
(blueprint: lem-sf-tensor-adjunction-reduction-squares).

Proof:
1. Define the ordinary word comparison q using the tensor reduction, canonical pullback
comparison, its proper right mate, and inverse open mate. Induction identifies q with
reduction of completionMap followed by the recursive r. The short-word completion
isomorphism permits cancellation of this transport.
2. Derive preservation of tensor associativity from compatibility with internal-Hom
composition, by uncurrying both sides. The specified left-unit normalization supplies
the left unitor; associativity, naturality and the triangle identity supply the right
unitor. Naturality inserts the comparisons of the children.
3. Apply canonicalReductionPullComposition to the pullback generator. Mathlib's pasting
identities for mateEquiv and conjugateEquiv give the proper direct-image compositor.
4. The unit and counit identities for mateEquiv give the proper adjunction squares.
The inverse mate identities give the open squares. The assumed primitive formulas and
normalized reconstruction prove recursive r invertible, hence the open mate is invertible
at the required ordinary input; no global invertibility of that mate is asserted.
5. Cancel reduction of completionMap to obtain the completed square. For invertible
constraints, multiply by the inverses to obtain the reverse square. Naturality of recursive
r follows by induction from naturality of the primitive comparisons, using the same
isomorphism argument for open comparisons. Naturality of the system structural maps
then gives the final input-naturality equation. All equalities concern whole systems.
-/
theorem tensorAdjunctionReductionSquares
    {D : FiniteFieldDatum.{u}} (coeff : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic coeff.l) E]
    [FiniteDimensional (Padic coeff.l) E]
    {S : Type s} (W : S → Scheme.{u}) (_hW : FiniteTypeFamily W D.k)
    {I : Type i} (location : I → S) (o : Operations coeff.l E)
    {a : S} {B C : Word W location a} (g : GeneratorKind W location B C)
    (_hKind : g.IsTensorAdjunction)
    (_hB : B.length ≤ 3) (_hC : C.length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource coeff.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, Admissible coeff.l E
      (IntegralSystemRealization.calculus coeff.l E (W (location k)))
        (K k) lo hi torLo torHi)
    (_hIntermediate : Word.admissible coeff.l E W location o K lo hi torLo torHi B ∧
      Word.admissible coeff.l E W location o K lo hi torLo torHi C)
    (_hPrimitiveB : B.primitiveFormulas coeff.l E W location o K)
    (_hPrimitiveC : C.primitiveFormulas coeff.l E W location o K) :
    Assertion coeff.l E W location o K g ∧
      (g.IsTensorCompositionIso →
        C.r coeff.l E W location o K ≫
            inverseOrZero (g.systemMap coeff.l E W location o
              (inputReduction coeff.l E W location K)) =
          (IntegralSystemRealization.calculus coeff.l E (W a)).reduction.map
              (inverseOrZero (g.integralMap coeff.l E W location o K)) ≫
            B.r coeff.l E W location o K) ∧
      (∀ (L : ∀ k : I,
          DerivedCategory (scalarReductionSource coeff.l E (W (location k))))
        (f : ∀ k : I, K k ⟶ L k),
        (∀ k : I, Admissible coeff.l E
          (IntegralSystemRealization.calculus coeff.l E (W (location k)))
            (L k) lo hi torLo torHi) →
        Word.admissible coeff.l E W location o L lo hi torLo torHi B →
        Word.admissible coeff.l E W location o L lo hi torLo torHi C →
        B.primitiveFormulas coeff.l E W location o L →
        C.primitiveFormulas coeff.l E W location o L →
        (IntegralSystemRealization.calculus coeff.l E (W a)).reduction.map
            (B.integralAction coeff.l E o K L f) ≫
          B.r coeff.l E W location o L ≫
          g.systemMap coeff.l E W location o (inputReduction coeff.l E W location L) =
        B.r coeff.l E W location o K ≫
          g.systemMap coeff.l E W location o (inputReduction coeff.l E W location K) ≫
          C.systemAction coeff.l E o
            (inputReduction coeff.l E W location K) (inputReduction coeff.l E W location L)
            (fun k ↦ (IntegralSystemRealization.calculus coeff.l E (W (location k))).reduction.map
              (f k))) := by
  have hk : IsUnit (coeff.l : D.k) := by
    let := Fintype.ofFinite D.k₀
    let : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
        (D.card_base.trans D.cardinality_eq))
    have : CharP D.k D.p :=
      charP_of_injective_algebraMap (algebraMap D.k₀ D.k).injective D.p
    exact (CharP.isUnit_natCast_iff (R := D.k) D.prime).2
      (fun h ↦ coeff.different
        ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : coeff.l.Prime)).1 h).symm)
  have hu (a : S) : IsUnit (coeff.l : Γ(W a, ⊤)) := by
    simpa only [map_natCast] using hk.map
      ((Scheme.ΓSpecIso (.of D.k)).inv ≫ (_hW.structureMap a).appTop).hom
  have hc (a : S) (N : coefficientSequenceDerived coeff.l E (W a))
      (hN : IsNormalizedCoefficientSequence coeff.l E (W a) N) :
      IsIso ((IntegralSystemRealization.calculus coeff.l E (W a)).adjunction.counit.app N) :=
    ((purNormalizedReconstruction coeff.l E (W a) (hu a)
      (IntegralSystemRealization.calculus coeff.l E (W a))).1 N hN).2
  have hforward : Assertion coeff.l E W location o K g := by
    apply assertion_of_ordinary_square coeff.l E o K lo hi torLo torHi _hAdm
      g _hB _hC _hIntermediate.1 _hIntermediate.2
    have qi {a : S} (U : Word W location a) (hU : U.length ≤ 3)
        (haU : U.admissible coeff.l E W location o K lo hi torLo torHi)
        (hpU : U.primitiveFormulas coeff.l E W location o K) :
        IsIso (U.ordinaryR coeff.l E o K) :=
      word_ordinaryR_isIso coeff.l E o hc K lo hi torLo torHi _hAdm U hU haU hpU
    cases g with
    | @tensorAssociator a U V T => exact ordinary_tensor_associator coeff.l E o U V T K
    | @tensorLeftUnit a U => exact ordinary_tensor_left_unitor coeff.l E o C K
    | @tensorRightUnit a U => exact ordinary_tensor_right_unitor coeff.l E o C K
    | @pullComposition a b c f g hsf htf hqf hsg htg hqg hs ht hq U =>
      exact ordinary_pull_composition coeff.l E o f g hsf htf hqf hsg htg hqg hs ht hq U K
    | @pushComposition a b c f g hsf htf hqf hpf hsg htg hqg hpg hs ht hq hp U =>
      exact ordinary_push_composition coeff.l E o f g hsf htf hqf hpf
        hsg htg hqg hpg hs ht hq hp U K
    | @pullPushUnit a b f hs ht hq hp U =>
      exact ordinary_pullPush_unit coeff.l E o f hs ht hq hp B K
    | @pullPushCounit a b f hs ht hq hp U =>
      exact ordinary_pullPush_counit coeff.l E o f hs ht hq hp C K
    | @openUnit a b j hj hq _ =>
      have := qi B _hB _hIntermediate.1 _hPrimitiveB
      have hU : (Word.open j hj hq B).length ≤ 3 := by
        dsimp only [Word.length] at _hC ⊢
        omega
      have := qi (.open j hj hq B) hU _hIntermediate.2.2 _hPrimitiveC.2
      have := open_comparison_isIso coeff.l E o j hj hq B K
      exact ordinary_open_unit coeff.l E o j hj hq B K
    | @openCounit a b j hj hq _ =>
      let := hj
      let V := Word.pull j (by infer_instance) (by infer_instance) hq C
      have hV : V.length ≤ 3 := by dsimp only [V, Word.length] at _hB ⊢; omega
      have := qi V hV _hIntermediate.1.2 _hPrimitiveB.2.2.2
      have := qi (.open j hj hq V) _hB _hIntermediate.1 _hPrimitiveB
      have hv := open_comparison_isIso coeff.l E o j hj hq V K
      have : IsIso ((o.realization.openReduction coeff.l E j).app
          ((IntegralSystemRealization.ringedPull coeff.l E j).obj
            (C.ringedValue coeff.l E W location o K))) := by
        exact hv
      exact ordinary_open_counit coeff.l E o j hj hq C K
    | openBaseChange => exact _hKind.elim
    | openTensor => exact _hKind.elim
    | properOpenInterchange => exact _hKind.elim
    | properOpenLambda => exact _hKind.elim
  refine ⟨hforward, ?_, ?_⟩
  · intro hg
    have := completionMap_isIso coeff.l E W location o B _hB K
      lo hi torLo torHi _hAdm _hIntermediate.1
    have := completionMap_isIso coeff.l E W location o C _hC K
      lo hi torLo torHi _hAdm _hIntermediate.2
    exact reverse_generator_square coeff.l E o K g hg hforward
  · intro L f _hL hBL hCL hpBL hpCL
    rw [← Category.assoc,
      word_r_naturality coeff.l E o K L f hc B lo hi torLo torHi
        _hIntermediate.1 hBL _hPrimitiveB hpBL, Category.assoc,
      system_generator_naturality coeff.l E o _ _ _ g _hKind]

end WeilConjectures.GeneratorReduction
