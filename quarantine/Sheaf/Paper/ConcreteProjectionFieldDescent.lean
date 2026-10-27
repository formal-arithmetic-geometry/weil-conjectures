/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Sheaf.Paper.ProjectionTensorCoefficientCocycles
public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.QcqsCompactSupportRealization
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfRationalizationKaroubi
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients

/-! # Localization and field descent of the specified projection component

Source: current blueprint, fix-prop-projection-formula.proof.md, field-stage sentence;
thm-sf-pf-field.proof.md, Compatibility and common finite coefficient field paragraphs
(blueprint: lem-sf-concrete-projection-field-descent).

The endpoint isomorphisms are composites of the recorded tensor, pullback and support
comparisons. All components are the existing proper-counit/open maps. The assertion
uses the operation datum, without projection invertibility, and retains arbitrary
rational arrows and all finite coefficient inclusions, including identity inclusions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u v w v' w'
open CategoryTheory AlgebraicGeometry
open CategoryTheory.SuppliedExchangeProjection
open scoped CategoryTheory.Functor
namespace WeilConjectures.ProjectionCoefficient

private abbrev ScalarCocycle :=
  @CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionScalarCocycle

section CoherenceCalculus
universe a b c ha hb hc i
variable {I : Type i} [Preorder I]
  {X : I → Type a} {Y : I → Type b} {Z : I → Type c}
  [∀ j, Category.{ha} (X j)] [∀ j, Category.{ha} (Y j)]
  [∀ j, Category.{ha} (Z j)]
  {F : ∀ j, X j ⥤ Y j} {G : ∀ j, Y j ⥤ Z j}
  {x : ∀ j k, j ≤ k → X j ⥤ X k}
  {y : ∀ j k, j ≤ k → Y j ⥤ Y k}
  {z : ∀ j k, j ≤ k → Z j ⥤ Z k}
  {xi : ∀ j, x j j le_rfl ≅ 𝟭 _}
  {yi : ∀ j, y j j le_rfl ≅ 𝟭 _}
  {zi : ∀ j, z j j le_rfl ≅ 𝟭 _}
  {xc : ∀ j k l (h : j ≤ k) (h' : k ≤ l), x j k h ⋙ x k l h' ≅ x j l (h.trans h')}
  {yc : ∀ j k l (h : j ≤ k) (h' : k ≤ l), y j k h ⋙ y k l h' ≅ y j l (h.trans h')}
  {zc : ∀ j k l (h : j ≤ k) (h' : k ≤ l), z j k h ⋙ z k l h' ≅ z j l (h.trans h')}
  {α : ∀ j k (h : j ≤ k), F j ⋙ y j k h ≅ x j k h ⋙ F k}
  {β : ∀ j k (h : j ≤ k), G j ⋙ z j k h ≅ y j k h ⋙ G k}

private theorem cocycle_comp
    (hF : ScalarCocycle X Y F x y xi yi xc yc α)
    (hG : ScalarCocycle Y Z G y z yi zi yc zc β) :
    ScalarCocycle X Z (fun j ↦ F j ⋙ G j) x z xi zi xc zc
      (fun j k h ↦ sixFunctorCompositeRealization (α j k h) (β j k h)) := by
  constructor
  · intro j M
    dsimp [sixFunctorCompositeRealization]
    simp only [Category.id_comp, Category.comp_id]
    rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hF.identity, hG.identity]
  · intro j k l h h' M
    dsimp [sixFunctorCompositeRealization]
    simp only [Category.id_comp, Category.comp_id]
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    have hn := (β k l h').hom.naturality ((α j k h).hom.app M)
    simp only [Functor.comp_map] at hn
    rw [reassoc_of% hn]
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hF.composition]
    simp only [CategoryTheory.Functor.map_comp]
    simpa only [Category.assoc] using congrArg
      (fun a ↦ a ≫ (G l).map ((α j l (h.trans h')).hom.app M))
      (hG.composition j k l h h' ((F j).obj M))

private theorem cocycle_id :
    ScalarCocycle X X (fun j ↦ 𝟭 (X j)) x x xi xi xc xc
      (fun j k h ↦ Iso.refl (x j k h)) := by
  constructor <;> intros <;> simp

end CoherenceCalculus

section ProductCoherence
universe a b c d ha hb hc hd i
variable {I : Type i} [Preorder I]
  {X : I → Type a} [∀ j, Category.{ha} (X j)]
  {Y : I → Type b} [∀ j, Category.{ha} (Y j)]
  {Z : I → Type c} [∀ j, Category.{ha} (Z j)]
  {W : I → Type d} [∀ j, Category.{ha} (W j)]
  {x : ∀ j k, j ≤ k → X j ⥤ X k}
  {xi : ∀ j, x j j le_rfl ≅ 𝟭 _}
  {xc : ∀ j k l (h : j ≤ k) (h' : k ≤ l),
    x j k h ⋙ x k l h' ≅ x j l (h.trans h')}
  {y : ∀ j k, j ≤ k → Y j ⥤ Y k}
  {yi : ∀ j, y j j le_rfl ≅ 𝟭 _}
  {yc : ∀ j k l (h : j ≤ k) (h' : k ≤ l),
    y j k h ⋙ y k l h' ≅ y j l (h.trans h')}
  {z : ∀ j k, j ≤ k → Z j ⥤ Z k}
  {zi : ∀ j, z j j le_rfl ≅ 𝟭 _}
  {zc : ∀ j k l (h : j ≤ k) (h' : k ≤ l),
    z j k h ⋙ z k l h' ≅ z j l (h.trans h')}
  {w : ∀ j k, j ≤ k → W j ⥤ W k}
  {wi : ∀ j, w j j le_rfl ≅ 𝟭 _}
  {wc : ∀ j k l (h : j ≤ k) (h' : k ≤ l),
    w j k h ⋙ w k l h' ≅ w j l (h.trans h')}
  {F : ∀ j, X j ⥤ Y j} {G : ∀ j, Z j ⥤ W j}
  {α : ∀ j k (h : j ≤ k), F j ⋙ y j k h ≅ x j k h ⋙ F k}
  {β : ∀ j k (h : j ≤ k), G j ⋙ w j k h ≅ z j k h ⋙ G k}

private theorem cocycle_prod
    (hF : ScalarCocycle X Y F x y xi yi xc yc α)
    (hG : ScalarCocycle Z W G z w zi wi zc wc β) :
    ScalarCocycle (fun j ↦ X j × Z j) (fun j ↦ Y j × W j)
      (fun j ↦ (F j).prod (G j))
      (fun j k h ↦ (x j k h).prod (z j k h))
      (fun j k h ↦ (y j k h).prod (w j k h))
      (fun j ↦ (NatIso.prod (xi j) (zi j))) (fun j ↦ (NatIso.prod (yi j) (wi j)))
      (fun j k l h h' ↦ (NatIso.prod (xc j k l h h') (zc j k l h h')))
      (fun j k l h h' ↦ (NatIso.prod (yc j k l h h') (wc j k l h h')))
      (fun j k h ↦ (NatIso.prod (α j k h) (β j k h))) := by
  constructor
  · intro j M
    exact Prod.ext (hF.identity j M.1) (hG.identity j M.2)
  · intro j k l h h' M
    exact Prod.ext (hF.composition j k l h h' M.1)
      (hG.composition j k l h h' M.2)

end ProductCoherence

section InclusionCalculus
universe a b c ha hb hc
variable {X₀ X₁ Xinf : Type a} {Y₀ Y₁ Yinf : Type b} {Z₀ Z₁ Zinf : Type c}
  [Category.{ha} X₀] [Category.{ha} X₁] [Category.{ha} Xinf]
  [Category.{ha} Y₀] [Category.{ha} Y₁] [Category.{ha} Yinf]
  [Category.{ha} Z₀] [Category.{ha} Z₁] [Category.{ha} Zinf]
  {F₀ : X₀ ⥤ Y₀} {F₁ : X₁ ⥤ Y₁} {Finf : Xinf ⥤ Yinf}
  {G₀ : Y₀ ⥤ Z₀} {G₁ : Y₁ ⥤ Z₁} {Ginf : Yinf ⥤ Zinf}
  {x : X₀ ⥤ X₁} {y : Y₀ ⥤ Y₁} {z : Z₀ ⥤ Z₁}
  {U₀ : X₀ ⥤ Xinf} {U₁ : X₁ ⥤ Xinf}
  {V₀ : Y₀ ⥤ Yinf} {V₁ : Y₁ ⥤ Yinf}
  {W₀ : Z₀ ⥤ Zinf} {W₁ : Z₁ ⥤ Zinf}
  {α : F₀ ⋙ y ≅ x ⋙ F₁} {β : G₀ ⋙ z ≅ y ⋙ G₁}
  {u : x ⋙ U₁ ≅ U₀} {v : y ⋙ V₁ ≅ V₀} {w : z ⋙ W₁ ≅ W₀}
  {γ₀ : F₀ ⋙ V₀ ≅ U₀ ⋙ Finf} {γ₁ : F₁ ⋙ V₁ ≅ U₁ ⋙ Finf}
  {δ₀ : G₀ ⋙ W₀ ≅ V₀ ⋙ Ginf} {δ₁ : G₁ ⋙ W₁ ≅ V₁ ⋙ Ginf}

private theorem inclusion_comp
    (hF : SixFunctorInclusionCoherence F₀ F₁ Finf x y U₀ U₁ V₀ V₁ α u v γ₀ γ₁)
    (hG : SixFunctorInclusionCoherence G₀ G₁ Ginf y z V₀ V₁ W₀ W₁ β v w δ₀ δ₁) :
    SixFunctorInclusionCoherence (F₀ ⋙ G₀) (F₁ ⋙ G₁) (Finf ⋙ Ginf)
      x z U₀ U₁ W₀ W₁ (sixFunctorCompositeRealization α β) u w
      (sixFunctorCompositeRealization γ₀ δ₀) (sixFunctorCompositeRealization γ₁ δ₁) := by
  intro M
  dsimp [sixFunctorCompositeRealization]
  simp only [Category.id_comp, Category.comp_id]
  simp only [← CategoryTheory.Functor.map_comp, ← Category.assoc]
  rw [hF M]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hG (F₀.obj M)]
  have hn := δ₁.inv.naturality (α.inv.app M)
  simp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

end InclusionCalculus

section ProductInclusion
universe a b c d ha hb hc hd
variable {X₀ X₁ Xinf : Type a}
  [Category.{ha} X₀] [Category.{ha} X₁] [Category.{ha} Xinf]
 {Y₀ Y₁ Yinf : Type b}
  [Category.{ha} Y₀] [Category.{ha} Y₁] [Category.{ha} Yinf]
 {Z₀ Z₁ Zinf : Type c}
  [Category.{ha} Z₀] [Category.{ha} Z₁] [Category.{ha} Zinf]
 {W₀ W₁ Winf : Type d}
  [Category.{ha} W₀] [Category.{ha} W₁] [Category.{ha} Winf]
  {x : X₀ ⥤ X₁} {x₀ : X₀ ⥤ Xinf} {x₁ : X₁ ⥤ Xinf}
  {xi : x ⋙ x₁ ≅ x₀}
  {y : Y₀ ⥤ Y₁} {y₀ : Y₀ ⥤ Yinf} {y₁ : Y₁ ⥤ Yinf}
  {yi : y ⋙ y₁ ≅ y₀}
  {z : Z₀ ⥤ Z₁} {z₀ : Z₀ ⥤ Zinf} {z₁ : Z₁ ⥤ Zinf}
  {zi : z ⋙ z₁ ≅ z₀}
  {w : W₀ ⥤ W₁} {w₀ : W₀ ⥤ Winf} {w₁ : W₁ ⥤ Winf}
  {wi : w ⋙ w₁ ≅ w₀}
  {F₀ : X₀ ⥤ Y₀}
  {F₁ : X₁ ⥤ Y₁}
  {Finf : Xinf ⥤ Yinf}
  {α : F₀ ⋙ y ≅ x ⋙ F₁}
  {γ₀ : F₀ ⋙ y₀ ≅ x₀ ⋙ Finf}
  {γ₁ : F₁ ⋙ y₁ ≅ x₁ ⋙ Finf}
  {G₀ : Z₀ ⥤ W₀}
  {G₁ : Z₁ ⥤ W₁}
  {Ginf : Zinf ⥤ Winf}
  {β : G₀ ⋙ w ≅ z ⋙ G₁}
  {δ₀ : G₀ ⋙ w₀ ≅ z₀ ⋙ Ginf}
  {δ₁ : G₁ ⋙ w₁ ≅ z₁ ⋙ Ginf}

private theorem inclusion_prod
    (hF : SixFunctorInclusionCoherence F₀ F₁ Finf x y x₀ x₁ y₀ y₁ α xi yi γ₀ γ₁)
    (hG : SixFunctorInclusionCoherence G₀ G₁ Ginf z w z₀ z₁ w₀ w₁ β zi wi δ₀ δ₁) :
    SixFunctorInclusionCoherence (F₀.prod G₀) (F₁.prod G₁) (Finf.prod Ginf)
      (x.prod z) (y.prod w) (x₀.prod z₀) (x₁.prod z₁) (y₀.prod w₀) (y₁.prod w₁)
      (NatIso.prod α β) (NatIso.prod xi zi) (NatIso.prod yi wi)
      (NatIso.prod γ₀ δ₀) (NatIso.prod γ₁ δ₁) := by
  intro M
  exact Prod.ext (hF M.1) (hG M.2)

private theorem inclusion_id :
    SixFunctorInclusionCoherence (𝟭 X₀) (𝟭 X₁) (𝟭 Xinf)
      x x x₀ x₁ x₀ x₁ (Iso.refl x) xi xi (Iso.refl x₀) (Iso.refl x₁) := by
  intro M
  simp

end ProductInclusion

section Components
variable {D : FiniteFieldDatum.{u}}
  {B : SixFunctorSpace D → Type v} [∀ X, Category.{w} (B X)]
  {B' : SixFunctorSpace D → Type v'} [∀ X, Category.{w'} (B' X)]
  {S : SixFunctorPushStage D B} {S' : SixFunctorPushStage D B'}
  {T : ∀ X, B X ⥤ B X ⥤ B X} {T' : ∀ X, B' X ⥤ B' X ⥤ B' X}
  {Q : SixFunctorCompactifiedSquare D}
  {A : SixFunctorExchangeData S T Q} {A' : SixFunctorExchangeData S' T' Q}
  {L : ∀ X, B X ⥤ B' X} {C : SixFunctorCoefficientComparison S S' L}

/-- The source bifunctor of the specified projection.
Source: def-exchange-projection, PF source (blueprint: lem-sf-concrete-projection-field-descent). -/
def source (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (Q : SixFunctorCompactifiedSquare D) : B Q.X × B Q.Y ⥤ B Q.Y :=
  (S.support Q.f Q.compactification).prod (𝟭 _) ⋙ Functor.uncurry.obj (T Q.Y)

/-- The target bifunctor of the specified projection.
Source: def-exchange-projection, PF target (blueprint: lem-sf-concrete-projection-field-descent). -/
def target (S : SixFunctorPushStage D B) (T : ∀ X, B X ⥤ B X ⥤ B X)
    (Q : SixFunctorCompactifiedSquare D) : B Q.X × B Q.Y ⥤ B Q.Y :=
  ((𝟭 _).prod (S.pull Q.f) ⋙ Functor.uncurry.obj (T Q.X)) ⋙
    S.support Q.f Q.compactification

/-- Source comparison: tensor comparison, then compact-support comparison in the first factor.
Source: def-exchange-projection, coefficient data
(blueprint: lem-sf-concrete-projection-field-descent). -/
def sourceIso (e : SixFunctorExchangeComparison A A' L C) (K : B Q.X) (N : B Q.Y) :
    (L Q.Y).obj ((source S T Q).obj (K, N)) ≅
      (source S' T' Q).obj ((L Q.X).obj K, (L Q.Y).obj N) :=
  (sixFunctorCompositeRealization
    (F := (S.support Q.f Q.compactification).prod (𝟭 (B Q.Y)))
    (F' := (S'.support Q.f Q.compactification).prod (𝟭 (B' Q.Y)))
    (LA := (L Q.X).prod (L Q.Y)) (LB := (L Q.Y).prod (L Q.Y))
    (NatIso.prod (C.supportAdjunction Q.f Q.compactification).left (Iso.refl (L Q.Y)))
    (e.tensor Q.Y)).app (K, N)

/-- Target comparison: compact support, tensor, then pullback in the second factor.
Source: def-exchange-projection, coefficient data
(blueprint: lem-sf-concrete-projection-field-descent). -/
def targetIso (e : SixFunctorExchangeComparison A A' L C) (K : B Q.X) (N : B Q.Y) :
    (L Q.Y).obj ((target S T Q).obj (K, N)) ≅
      (target S' T' Q).obj ((L Q.X).obj K, (L Q.Y).obj N) :=
  (sixFunctorCompositeRealization
    (sixFunctorCompositeRealization
      (F := (𝟭 (B Q.X)).prod (S.pull Q.f))
      (F' := (𝟭 (B' Q.X)).prod (S'.pull Q.f))
      (LA := (L Q.X).prod (L Q.Y)) (LB := (L Q.X).prod (L Q.X))
      (NatIso.prod (Iso.refl (L Q.X)) (C.directAdjunction Q.f).left) (e.tensor Q.X))
    (C.supportAdjunction Q.f Q.compactification).left).app (K, N)

private theorem sourceIso_formula (e : SixFunctorExchangeComparison A A' L C)
    (K : B Q.X) (N : B Q.Y) : sourceIso e K N =
  (e.tensor Q.Y).app ((S.support Q.f Q.compactification).obj K, N) ≪≫
    (Functor.uncurry.obj (T' Q.Y)).mapIso
      (Iso.prod ((C.supportAdjunction Q.f Q.compactification).left.app K) (Iso.refl _)) := by
  apply Iso.ext
  simp [sourceIso, source, sixFunctorCompositeRealization, NatIso.prod, NatTrans.prod,
    Iso.prod]

private theorem targetIso_formula (e : SixFunctorExchangeComparison A A' L C)
    (K : B Q.X) (N : B Q.Y) : targetIso e K N =
  (C.supportAdjunction Q.f Q.compactification).left.app
      (((T Q.X).obj K).obj ((S.pull Q.f).obj N)) ≪≫
    (S'.support Q.f Q.compactification).mapIso
      ((e.tensor Q.X).app (K, (S.pull Q.f).obj N) ≪≫
        (Functor.uncurry.obj (T' Q.X)).mapIso
          (Iso.prod (Iso.refl _) ((C.directAdjunction Q.f).left.app N))) := by
  apply Iso.ext
  simp [targetIso, target, sixFunctorCompositeRealization, NatIso.prod, NatTrans.prod,
    Iso.prod]

/-- The specified component after coefficient change, in the target operation coordinates.
Source: field-stage transport, ordered endpoint comparisons
(blueprint: lem-sf-concrete-projection-field-descent). -/
def transported (e : SixFunctorExchangeComparison A A' L C) (K : B Q.X) (N : B Q.Y) :=
  (sourceIso e K N).inv ≫ (L Q.Y).map (A.projectionComponent K N) ≫
    (targetIso e K N).hom

/-- The inverse representative uses the reverse ordered endpoint comparisons.
Source: field-stage transport, inverse paragraph
(blueprint: lem-sf-concrete-projection-field-descent). -/
def transportedInverse (e : SixFunctorExchangeComparison A A' L C)
    (K : B Q.X) (N : B Q.Y)
    (a : (target S T Q).obj (K, N) ⟶ (source S T Q).obj (K, N)) :=
  (targetIso e K N).inv ≫ (L Q.Y).map a ≫ (sourceIso e K N).hom

/-- Both inverse equations for every representative of the specified component.
Source: field-stage transport, final inverse paragraph
(blueprint: lem-sf-concrete-projection-field-descent). -/
def InverseLaw (e : SixFunctorExchangeComparison A A' L C) (K : B Q.X) (N : B Q.Y) :
    Prop :=
  ∀ a : (target S T Q).obj (K, N) ⟶ (source S T Q).obj (K, N),
    A.projectionComponent K N ≫ a = 𝟙 _ →
    a ≫ A.projectionComponent K N = 𝟙 _ →
    A'.projectionComponent ((L Q.X).obj K) ((L Q.Y).obj N) ≫
        transportedInverse e K N a = 𝟙 _ ∧
      transportedInverse e K N a ≫
        A'.projectionComponent ((L Q.X).obj K) ((L Q.Y).obj N) = 𝟙 _

/-- Naturality for arbitrary arrows in both input variables, in the given stage.
Source: field-stage transport, raw Hom tensor-linearity paragraph
(blueprint: lem-sf-concrete-projection-field-descent). -/
def Natural (A : SixFunctorExchangeData S T Q) : Prop :=
  ∀ (K K' : B Q.X) (N N' : B Q.Y) (a : K ⟶ K') (b : N ⟶ N'),
    (source S T Q).map (Prod.mkHom a b) ≫ A.projectionComponent K' N' =
      A.projectionComponent K N ≫ (target S T Q).map (Prod.mkHom a b)

/-- Forward transport of any equality of maps with the projection endpoints. This
includes every pair of specified composites and asserts no reflection of equality.
Source: field-stage transport, equality paragraph
(blueprint: lem-sf-concrete-projection-field-descent). -/
def EqualityLaw (e : SixFunctorExchangeComparison A A' L C) (K : B Q.X) (N : B Q.Y) :
    Prop :=
  ∀ a b : (source S T Q).obj (K, N) ⟶ (target S T Q).obj (K, N), a = b →
    (sourceIso e K N).inv ≫ (L Q.Y).map a ≫ (targetIso e K N).hom =
      (sourceIso e K N).inv ≫ (L Q.Y).map b ≫ (targetIso e K N).hom

private theorem transported_eq (e : SixFunctorExchangeComparison A A' L C)
    (K : B Q.X) (N : B Q.Y) :
    transported e K N = A'.projectionComponent ((L Q.X).obj K) ((L Q.Y).obj N) := by
  let c := (S'.support Q.f Q.compactification).mapIso
    ((e.tensor Q.X).app (K, (S.pull Q.f).obj N) ≪≫
      (Functor.uncurry.obj (T' Q.X)).mapIso
        (Iso.prod (Iso.refl _) ((C.directAdjunction Q.f).left.app N)))
  have h : (L Q.Y).map (A.projectionComponent K N) ≫
      (C.supportAdjunction Q.f Q.compactification).left.hom.app
        (((T Q.X).obj K).obj ((S.pull Q.f).obj N)) =
      (sourceIso e K N).hom ≫
        A'.projectionComponent ((L Q.X).obj K) ((L Q.Y).obj N) ≫ c.inv := by
    simpa only [sourceIso_formula, c, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Iso.prod_hom,
      Iso.prod_inv, Iso.refl_hom, Iso.refl_inv, Category.assoc]
      using eq_of_heq (e.projection K N)
  apply (cancel_epi (sourceIso e K N).hom).mp
  have h' := congrArg (fun a ↦ a ≫ c.hom) h
  simpa only [transported, targetIso_formula, c, Iso.trans_hom, Iso.app_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using h'

private theorem inverse_law (e : SixFunctorExchangeComparison A A' L C)
    (K : B Q.X) (N : B Q.Y) : InverseLaw e K N := by
  intro a ha hb
  rw [← transported_eq e K N]
  constructor
  · simp only [transported, transportedInverse, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc ((L Q.Y).map (A.projectionComponent K N)),
      ← CategoryTheory.Functor.map_comp, ha, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id]
  · simp only [transported, transportedInverse, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc ((L Q.Y).map a), ← CategoryTheory.Functor.map_comp, hb,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]

private theorem equality_law (e : SixFunctorExchangeComparison A A' L C)
    (K : B Q.X) (N : B Q.Y) : EqualityLaw e K N := by
  intro a b h
  cases h
  rfl

private theorem projection_natural (A : SixFunctorExchangeData S T Q) : Natural A := by
  intro K K' N N' a b
  let η := Functor.uncurry.map A.stage.projection
  have hs : source S T Q = Functor.uncurry.obj
      (A.stage.compactSupport ⋙ A.stage.tensorY) := by
    simp only [source, ← A.tensorY, ← A.compactSupport]
    rfl
  have ht : target S T Q = Functor.uncurry.obj
      ((Functor.postcompose₂.obj A.stage.compactSupport).obj
        ((((Functor.whiskeringLeft₂ (B Q.X)).obj (𝟭 (B Q.X))).obj
          A.stage.pull).obj A.stage.tensorX)) := by
    simp only [target, ← A.tensorX, ← A.compactSupport, ← A.pull]
    refine CategoryTheory.Functor.ext ?_ ?_
    · intro M
      rfl
    intro M M' f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    dsimp
    exact A.stage.compactSupport.map_comp _ _
  let η' : source S T Q ⟶ target S T Q :=
    (eqToHom hs) ≫ η ≫ (eqToHom ht.symm)
  have hc : ∀ K N, η'.app (K, N) = A.projectionComponent K N := by
    intro K N
    simp only [η', NatTrans.comp_app, eqToHom_app, η, Functor.uncurry_map_app,
      SixFunctorExchangeData.projectionComponent]
  simpa only [hc] using η'.naturality (Prod.mkHom a b)

end Components

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Coefficient)

/-- The stage source or target evaluated on a pair of finite-stage inputs.
Source: field-stage transport, S_H and T_H
(blueprint: lem-sf-concrete-projection-field-descent). -/
def endpoint {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) (b : Bool)
    (E : Padic.FiniteCoefficientFields C.l C.Qbar) :
    Stage C.l C.Qbar Q.X.obj.left E × Stage C.l C.Qbar Q.Y.obj.left E ⥤
      Stage C.l C.Qbar Q.Y.obj.left E :=
  match b with
  | true => source (sixFunctorCoefficientRational D C A.coefficientStages E)
      (sixFunctorCoefficientTensor D C A.coefficientStages E) Q
  | false => target (sixFunctorCoefficientRational D C A.coefficientStages E)
      (sixFunctorCoefficientTensor D C A.coefficientStages E) Q

/-- Endpoint comparisons are fixed composites, for source and target alike.
Source: field-stage transport, ordered endpoint comparisons
(blueprint: lem-sf-concrete-projection-field-descent). -/
def endpointIso {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) (b : Bool)
    {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F)
    (K : Stage C.l C.Qbar Q.X.obj.left E) (N : Stage C.l C.Qbar Q.Y.obj.left E) :
    ((stageSystem C.l C.Qbar Q.Y.obj.left).T h).obj ((endpoint A Q b E).obj (K, N)) ≅
      (endpoint A Q b F).obj
        (((stageSystem C.l C.Qbar Q.X.obj.left).T h).obj K,
          ((stageSystem C.l C.Qbar Q.Y.obj.left).T h).obj N) :=
  match b with
  | true => sourceIso (A.coefficientExchangeComparison h Q) K N
  | false => targetIso (A.coefficientExchangeComparison h Q) K N

/-- Identity and tower cocycles at the two actual projection endpoints.
Source: field-stage transport, identity and tower paragraph
(blueprint: lem-sf-concrete-projection-field-descent). -/
def EndpointCocycles {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) : Prop :=
  ExchangeProjectionScalarCocycle
      (fun E ↦ Stage C.l C.Qbar Q.X.obj.left E × Stage C.l C.Qbar Q.Y.obj.left E)
      (fun E ↦ Stage C.l C.Qbar Q.Y.obj.left E)
      (fun E ↦ source (sixFunctorCoefficientRational D C A.coefficientStages E)
        (sixFunctorCoefficientTensor D C A.coefficientStages E) Q)
      (fun _ _ h ↦ ((stageSystem C.l C.Qbar Q.X.obj.left).T h).prod
        ((stageSystem C.l C.Qbar Q.Y.obj.left).T h))
      (fun _ _ h ↦ (stageSystem C.l C.Qbar Q.Y.obj.left).T h)
      (fun E ↦ NatIso.prod (sixFunctorStageUnitor D C Q.X E)
        (sixFunctorStageUnitor D C Q.Y E))
      (sixFunctorStageUnitor D C Q.Y)
      (fun _ _ _ h h' ↦ NatIso.prod ((stageSystem C.l C.Qbar Q.X.obj.left).assoc h h')
        ((stageSystem C.l C.Qbar Q.Y.obj.left).assoc h h'))
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar Q.Y.obj.left).assoc h h')
      (fun _ _ h ↦ sixFunctorCompositeRealization
        (F := ((sixFunctorCoefficientRational D C A.coefficientStages _).support
          Q.f Q.compactification).prod (𝟭 _))
        (F' := ((sixFunctorCoefficientRational D C A.coefficientStages _).support
          Q.f Q.compactification).prod (𝟭 _))
        (LA := ((stageSystem C.l C.Qbar Q.X.obj.left).T h).prod
          ((stageSystem C.l C.Qbar Q.Y.obj.left).T h))
        (LB := ((stageSystem C.l C.Qbar Q.Y.obj.left).T h).prod
          ((stageSystem C.l C.Qbar Q.Y.obj.left).T h))
        (NatIso.prod ((A.coefficientTransition h).supportAdjunction
          Q.f Q.compactification).left
          (Iso.refl ((stageSystem C.l C.Qbar Q.Y.obj.left).T h)))
        ((A.coefficientExchangeComparison h Q).tensor Q.Y)) ∧
  ExchangeProjectionScalarCocycle
      (fun E ↦ Stage C.l C.Qbar Q.X.obj.left E × Stage C.l C.Qbar Q.Y.obj.left E)
      (fun E ↦ Stage C.l C.Qbar Q.Y.obj.left E)
      (fun E ↦ target (sixFunctorCoefficientRational D C A.coefficientStages E)
        (sixFunctorCoefficientTensor D C A.coefficientStages E) Q)
      (fun _ _ h ↦ ((stageSystem C.l C.Qbar Q.X.obj.left).T h).prod
        ((stageSystem C.l C.Qbar Q.Y.obj.left).T h))
      (fun _ _ h ↦ (stageSystem C.l C.Qbar Q.Y.obj.left).T h)
      (fun E ↦ NatIso.prod (sixFunctorStageUnitor D C Q.X E)
        (sixFunctorStageUnitor D C Q.Y E))
      (sixFunctorStageUnitor D C Q.Y)
      (fun _ _ _ h h' ↦ NatIso.prod ((stageSystem C.l C.Qbar Q.X.obj.left).assoc h h')
        ((stageSystem C.l C.Qbar Q.Y.obj.left).assoc h h'))
      (fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar Q.Y.obj.left).assoc h h')
      (fun _ _ h ↦ sixFunctorCompositeRealization
        (sixFunctorCompositeRealization
          (F := (𝟭 _).prod
            ((sixFunctorCoefficientRational D C A.coefficientStages _).pull Q.f))
          (F' := (𝟭 _).prod
            ((sixFunctorCoefficientRational D C A.coefficientStages _).pull Q.f))
          (LA := ((stageSystem C.l C.Qbar Q.X.obj.left).T h).prod
            ((stageSystem C.l C.Qbar Q.Y.obj.left).T h))
          (LB := ((stageSystem C.l C.Qbar Q.X.obj.left).T h).prod
            ((stageSystem C.l C.Qbar Q.X.obj.left).T h))
          (NatIso.prod (Iso.refl ((stageSystem C.l C.Qbar Q.X.obj.left).T h))
            ((A.coefficientTransition h).directAdjunction Q.f).left)
          ((A.coefficientExchangeComparison h Q).tensor Q.X))
        ((A.coefficientTransition h).supportAdjunction Q.f Q.compactification).left)

/-- Common-stage endpoints, using the supplied operation datum on literal pairs.
Source: field-stage transport, common-stage category
(blueprint: lem-sf-concrete-projection-field-descent). -/
def commonEndpoint {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) (b : Bool) :=
  match b with
  | true => source A.commonStage A.commonStageTensor Q
  | false => target A.commonStage A.commonStageTensor Q

/-- Inclusion endpoint comparison uses the same tensor/support/pullback composites.
Source: field-stage transport, common-stage representatives
(blueprint: lem-sf-concrete-projection-field-descent). -/
def inclusionEndpointIso {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) (b : Bool)
    (E : Padic.FiniteCoefficientFields C.l C.Qbar)
    (K : Stage C.l C.Qbar Q.X.obj.left E) (N : Stage C.l C.Qbar Q.Y.obj.left E) :
    (inclusion (l := C.l) (Ω := C.Qbar) (Y := Q.Y.obj.left) E).obj
        ((endpoint A Q b E).obj (K, N)) ≅
      (commonEndpoint A Q b).obj
        ((inclusion (l := C.l) (Ω := C.Qbar) (Y := Q.X.obj.left) E).obj K,
          (inclusion (l := C.l) (Ω := C.Qbar) (Y := Q.Y.obj.left) E).obj N) :=
  match b with
  | true => sourceIso (A.commonStageExchangeComparison E Q) K N
  | false => targetIso (A.commonStageExchangeComparison E Q) K N

/-- Enlarging the representative field agrees with the prescribed inclusion comparison
at both endpoints. This makes the projection classes independent of enlargement.
Source: field-stage transport, common-stage Hom colimit paragraph
(blueprint: lem-sf-concrete-projection-field-descent). -/
def InclusionCoherence {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) : Prop :=
  ∀ (b : Bool) (E F : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F)
    (K : Stage C.l C.Qbar Q.X.obj.left E) (N : Stage C.l C.Qbar Q.Y.obj.left E),
    (commonEndpoint A Q b).map
        (Prod.mkHom (((stageSystem C.l C.Qbar Q.X.obj.left).transIso h).hom.app K)
          (((stageSystem C.l C.Qbar Q.Y.obj.left).transIso h).hom.app N)) ≫
        (inclusionEndpointIso A Q b E K N).inv =
      (inclusionEndpointIso A Q b F
        (((stageSystem C.l C.Qbar Q.X.obj.left).T h).obj K)
        (((stageSystem C.l C.Qbar Q.Y.obj.left).T h).obj N)).inv ≫
        (inclusion (l := C.l) (Ω := C.Qbar) (Y := Q.Y.obj.left) F).map
          (endpointIso A Q b h K N).inv ≫
        ((stageSystem C.l C.Qbar Q.Y.obj.left).transIso h).hom.app
          ((endpoint A Q b E).obj (K, N))

/-- The literal equality of common-stage components represented before or after
finite field enlargement, conjugated only by the stage system's inclusion isomorphisms.
Source: field-stage transport, common-stage representative independence
(blueprint: lem-sf-concrete-projection-field-descent). -/
def EnlargementLaw {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) : Prop :=
  ∀ (E F : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E ≤ F)
    (K : Stage C.l C.Qbar Q.X.obj.left E) (N : Stage C.l C.Qbar Q.Y.obj.left E),
    transported (A.commonStageExchangeComparison F Q)
        (((stageSystem C.l C.Qbar Q.X.obj.left).T h).obj K)
        (((stageSystem C.l C.Qbar Q.Y.obj.left).T h).obj N) ≫
        (target A.commonStage A.commonStageTensor Q).map
          (Prod.mkHom (((stageSystem C.l C.Qbar Q.X.obj.left).transIso h).hom.app K)
            (((stageSystem C.l C.Qbar Q.Y.obj.left).transIso h).hom.app N)) =
      (source A.commonStage A.commonStageTensor Q).map
          (Prod.mkHom (((stageSystem C.l C.Qbar Q.X.obj.left).transIso h).hom.app K)
            (((stageSystem C.l C.Qbar Q.Y.obj.left).transIso h).hom.app N)) ≫
        transported (A.commonStageExchangeComparison E Q) K N

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option allowUnsafeReducibility true in
attribute [local reducible] endpoint commonEndpoint source target

set_option allowUnsafeReducibility true in
attribute [local irreducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
  sixFunctorStageUnitor

private theorem endpoint_cocycles {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (hA : SixFunctorCommonStageCoherence A)
    (hT : TensorCoherence A) (Q : SixFunctorCompactifiedSquare D) :
    EndpointCocycles A Q := by
  have hs := cocycle_comp
    (cocycle_prod (hA.2.2.2.2.1 Q.f Q.compactification)
      (cocycle_id (x := fun _ _ h ↦ (stageSystem C.l C.Qbar Q.Y.obj.left).T h)
        (xi := sixFunctorStageUnitor D C Q.Y)
        (xc := fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar Q.Y.obj.left).assoc h h')))
    (hT.1 Q Q.Y)
  have ht := cocycle_comp
    (cocycle_comp (cocycle_prod
      (cocycle_id (x := fun _ _ h ↦ (stageSystem C.l C.Qbar Q.X.obj.left).T h)
        (xi := sixFunctorStageUnitor D C Q.X)
        (xc := fun _ _ _ h h' ↦ (stageSystem C.l C.Qbar Q.X.obj.left).assoc h h'))
      (hA.2.2.1 Q.f))
      (hT.1 Q Q.X))
    (hA.2.2.2.2.1 Q.f Q.compactification)
  exact ⟨hs, ht⟩

private theorem tensor_inclusion {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (hA : TensorCoherence A)
    (Q : SixFunctorCompactifiedSquare D) (X : SixFunctorSpace D)
    {E F : Padic.FiniteCoefficientFields C.l C.Qbar} (h : E ≤ F) :
    SixFunctorInclusionCoherence
      (Functor.uncurry.obj (sixFunctorCoefficientTensor D C A.coefficientStages E X))
      (Functor.uncurry.obj (sixFunctorCoefficientTensor D C A.coefficientStages F X))
      (Functor.uncurry.obj (A.commonStageTensor X))
      (((stageSystem C.l C.Qbar X.obj.left).T h).prod
        ((stageSystem C.l C.Qbar X.obj.left).T h))
      ((stageSystem C.l C.Qbar X.obj.left).T h)
      ((inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E).prod
        (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E))
      ((inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F).prod
        (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F))
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) E)
      (inclusion (l := C.l) (Ω := C.Qbar) (Y := X.obj.left) F)
      ((A.coefficientExchangeComparison h Q).tensor X)
      (NatIso.prod ((stageSystem C.l C.Qbar X.obj.left).transIso h)
        ((stageSystem C.l C.Qbar X.obj.left).transIso h))
      ((stageSystem C.l C.Qbar X.obj.left).transIso h)
      ((A.commonStageExchangeComparison E Q).tensor X)
      ((A.commonStageExchangeComparison F Q).tensor X) :=
  fun M ↦ hA.2 Q X E F h M.1 M.2

private theorem inclusion_coherence {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (hA : SixFunctorCommonStageCoherence A)
    (hT : TensorCoherence A) (Q : SixFunctorCompactifiedSquare D) :
    InclusionCoherence A Q := by
  intro b E F h K N
  have hs := inclusion_comp
    (inclusion_prod (hA.2.2.2.2.2.1 Q.f Q.compactification h)
      (inclusion_id (x := (stageSystem C.l C.Qbar Q.Y.obj.left).T h)
        (x₀ := inclusion (l := C.l) (Ω := C.Qbar) (Y := Q.Y.obj.left) E)
        (x₁ := inclusion (l := C.l) (Ω := C.Qbar) (Y := Q.Y.obj.left) F)
        (xi := (stageSystem C.l C.Qbar Q.Y.obj.left).transIso h)))
    (tensor_inclusion A hT Q Q.Y h)
  have ht := inclusion_comp
    (inclusion_comp (inclusion_prod
      (inclusion_id (x := (stageSystem C.l C.Qbar Q.X.obj.left).T h)
        (x₀ := inclusion (l := C.l) (Ω := C.Qbar) (Y := Q.X.obj.left) E)
        (x₁ := inclusion (l := C.l) (Ω := C.Qbar) (Y := Q.X.obj.left) F)
        (xi := (stageSystem C.l C.Qbar Q.X.obj.left).transIso h))
      (hA.2.2.2.1 Q.f h))
      (tensor_inclusion A hT Q Q.X h))
    (hA.2.2.2.2.2.1 Q.f Q.compactification h)
  cases b
  · exact ht (K, N)
  · exact hs (K, N)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem enlargement_law {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    (A : SixFunctorCommonStages D C) (Q : SixFunctorCompactifiedSquare D) :
    EnlargementLaw A Q := by
  intro E F h K N
  rw [transported_eq, transported_eq]
  exact (projection_natural (A.commonStageExchange Q) _ _ _ _ _ _).symm

/-- Localization, finite coefficient towers, and common-stage descent of the very
specified projection component, with its inverse, naturality and forward equalities.
Source: fix-prop-projection-formula.proof.md, field-stage sentence, and
thm-sf-pf-field.proof.md, Compatibility and common-field paragraphs
(blueprint: lem-sf-concrete-projection-field-descent).

Proof: (1) retain one compactification. The concrete integral projection-cone lemma
puts every endpoint and tensor/pullback input in the complete constructible domains.
Use compactification-completed realization to conjugate the proper/open expression
by its normalized total-limit comparison. Neither structure morphism is separated.
(2) Apply raw rationalization factor by factor to the specified unit, mu, counit and
gamma composite; adjacent comparisons cancel. Rational arrows are finite sums of
integral arrows tensored with scalars, so integral naturality extends to all of them.
(3) Identify completed scalar extension with strict-tower extension by the canonical
finite-free comparison chi and preserve constructibility. (4) Apply scalar-tower
coherence to the simultaneous quotient-system tensor/pullback equations, then take
the stipulated total limits. This includes ramified and identity extensions.
(5) Ordinary-adjunction scalar compatibility identifies both unit and counit. Its
pullback comparison is the same limit of the quotient kappa maps. (6) Normalize the
open tensor comparison by open restriction and full faithfulness, then use its
completion-unit characterization. Pullback composition is preserved by the scalar
extension theorem, so the final Lj*Lp* comparison in gamma is preserved as well.
(7) Paste these primitive squares by coefficient-realization transport and conjugate
by the compactification realization: the result is precisely transported = PF.
(8) Paste primitive identity and tower equations for the two endpoints. Rationalize
these equations and extend naturality linearly on raw Hom tensors. Functoriality
carries every equality forward and cancels adjacent endpoint comparisons.
(9) Include the finite-stage arrow in the literal pair category. The inclusion
endpoint equation and its coherence show independence of enlargement; two common
fields admit a further compositum. Represent arbitrary input arrows at a common
stage to obtain naturality, including changes of presentation by rational isomorphisms.
(10) For an integral inverse v, apply Q to uv=1 and vu=1. Every further inverse is
obtained by transporting v with the reverse endpoint comparisons. The two products
are identities by functoriality; inclusion gives the same equations on classes.
No arbitrary rational object is reduced modulo a finite coefficient quotient. -/
theorem concreteProjectionFieldDescent
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn)
    (tensorCoherence : TensorCoherence S.closure)
    (Q : SixFunctorCompactifiedSquare D)
    [IsSeparated Q.f.hom.left] [LocallyOfFiniteType Q.f.hom.left] [QuasiCompact Q.f.hom.left] :
    (∀ (K : sfIntegralConstructibleCategory C.l E Q.X.obj.left)
      (N : sfIntegralConstructibleCategory C.l E Q.Y.obj.left),
      S.integralFiniteTorDomain Q.Y N →
      transported (S.higher.rationalExchangeComparison Q) K N =
        (S.higher.rationalExchange Q).projectionComponent
          ((sfRationalConstructibleLocalization C.l E Q.X.obj.left).obj K)
          ((sfRationalConstructibleLocalization C.l E Q.Y.obj.left).obj N)) ∧
    (∀ (E₀ F : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E₀ ≤ F)
      (K : Stage C.l C.Qbar Q.X.obj.left E₀) (N : Stage C.l C.Qbar Q.Y.obj.left E₀),
      transported (S.closure.coefficientExchangeComparison h Q) K N =
        ((S.closure.coefficientStages F).rationalExchange Q).projectionComponent
          (((stageSystem C.l C.Qbar Q.X.obj.left).T h).obj K)
          (((stageSystem C.l C.Qbar Q.Y.obj.left).T h).obj N)) ∧
    EndpointCocycles S.closure Q ∧
    InclusionCoherence S.closure Q ∧
    EnlargementLaw S.closure Q ∧
    (∀ (E₀ : Padic.FiniteCoefficientFields C.l C.Qbar)
      (K : Stage C.l C.Qbar Q.X.obj.left E₀) (N : Stage C.l C.Qbar Q.Y.obj.left E₀),
      transported (S.closure.commonStageExchangeComparison E₀ Q) K N =
        (S.closure.commonStageExchange Q).projectionComponent
          ((inclusion (l := C.l) (Ω := C.Qbar) (Y := Q.X.obj.left) E₀).obj K)
          ((inclusion (l := C.l) (Ω := C.Qbar) (Y := Q.Y.obj.left) E₀).obj N)) ∧
    (∀ (K : sfIntegralConstructibleCategory C.l E Q.X.obj.left)
      (N : sfIntegralConstructibleCategory C.l E Q.Y.obj.left),
      S.integralFiniteTorDomain Q.Y N →
      InverseLaw (S.higher.rationalExchangeComparison Q) K N ∧
        EqualityLaw (S.higher.rationalExchangeComparison Q) K N ∧
        ∀ a : (target S.higher.integral S.higher.integralTensor Q).obj (K, N) ⟶
          (source S.higher.integral S.higher.integralTensor Q).obj (K, N),
        (S.higher.integralExchange Q).projectionComponent K N ≫ a = 𝟙 _ →
        a ≫ (S.higher.integralExchange Q).projectionComponent K N = 𝟙 _ →
        (sfRationalConstructibleLocalization C.l E Q.Y.obj.left).map
            ((S.higher.integralExchange Q).projectionComponent K N) ≫
            (sfRationalConstructibleLocalization C.l E Q.Y.obj.left).map a = 𝟙 _ ∧
          (sfRationalConstructibleLocalization C.l E Q.Y.obj.left).map a ≫
            (sfRationalConstructibleLocalization C.l E Q.Y.obj.left).map
              ((S.higher.integralExchange Q).projectionComponent K N) = 𝟙 _) ∧
    Natural (S.higher.rationalExchange Q) ∧
    Natural (S.closure.commonStageExchange Q) ∧
    (∀ (E₀ F : Padic.FiniteCoefficientFields C.l C.Qbar) (h : E₀ ≤ F),
      Natural ((S.closure.coefficientStages E₀).rationalExchange Q) ∧
      ∀ (K : Stage C.l C.Qbar Q.X.obj.left E₀) (N : Stage C.l C.Qbar Q.Y.obj.left E₀),
      InverseLaw (S.closure.coefficientExchangeComparison h Q) K N ∧
      InverseLaw (S.closure.commonStageExchangeComparison E₀ Q) K N ∧
      EqualityLaw (S.closure.coefficientExchangeComparison h Q) K N ∧
      EqualityLaw (S.closure.commonStageExchangeComparison E₀ Q) K N) := by
  refine ⟨?_, ?_, endpoint_cocycles S.closure S.commonStageCoherence tensorCoherence Q,
    inclusion_coherence S.closure S.commonStageCoherence tensorCoherence Q,
    enlargement_law S.closure Q, ?_, ?_, projection_natural (S.higher.rationalExchange Q),
    projection_natural (S.closure.commonStageExchange Q), ?_⟩
  · intro K N _
    exact transported_eq (S.higher.rationalExchangeComparison Q) K N
  · intro E₀ F h K N
    exact transported_eq (S.closure.coefficientExchangeComparison h Q) K N
  · intro E₀ K N
    exact transported_eq (S.closure.commonStageExchangeComparison E₀ Q) K N
  · intro K N _
    refine ⟨inverse_law (S.higher.rationalExchangeComparison Q) K N,
      equality_law (S.higher.rationalExchangeComparison Q) K N, ?_⟩
    intro a ha hb
    constructor
    · rw [← CategoryTheory.Functor.map_comp, ha, CategoryTheory.Functor.map_id]
    · rw [← CategoryTheory.Functor.map_comp, hb, CategoryTheory.Functor.map_id]
  · intro E₀ F h
    refine ⟨projection_natural ((S.closure.coefficientStages E₀).rationalExchange Q), ?_⟩
    intro K N
    exact ⟨inverse_law (S.closure.coefficientExchangeComparison h Q) K N,
      inverse_law (S.closure.commonStageExchangeComparison E₀ Q) K N,
      equality_law (S.closure.coefficientExchangeComparison h Q) K N,
      equality_law (S.closure.commonStageExchangeComparison E₀ Q) K N⟩

end WeilConjectures.ProjectionCoefficient
