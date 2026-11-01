/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CompactSupportFiniteProjection.ConstructibleProjectionMates
import WeilConjectures.SixFunctors.Integral.IntegralReductionJointFaithfulness
import WeilConjectures.SixFunctors.Integral.IntegralProjectionReductionCoordinates
import WeilConjectures.SixFunctors.Compact.CompactSupportProjectionFiniteStages

/-! # Integral projection composition and proper-coincidence identities

Source: the coherence step of the compact-support projection formula
(blueprint: lem-sf-integral-stage-projection-structural-identities).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open CategoryTheory.SuppliedExchangeProjection

namespace WeilConjectures

attribute [local irreducible] CompactSupportFiniteProjection.partialTensor
  CompactSupportFiniteProjection.component
  compactSupportProjectionComponent compactSupportProperProjection

/-- The left projection-composition diagram, as a calculation in one category. -/
private theorem projection_left_path {A : Type*} [Category A]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ B₃ C₄ C₅ D₂ D₃ E₄ F₁ G₂ : A}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃}
    {d : A₃ ⟶ A₄} {e : A₄ ⟶ A₅} {f : A₅ ⟶ A₆}
    {d' : A₂ ⟶ B₃} {c' : B₃ ⟶ A₄}
    {x : B₃ ⟶ C₄} {y : C₄ ⟶ C₅} {z : C₅ ⟶ A₆}
    {w : A₁ ⟶ D₂} {v : D₂ ⟶ D₃} {p : D₃ ⟶ C₄}
    {r : D₃ ⟶ E₄} {s : E₄ ⟶ C₅}
    {t : A₀ ⟶ F₁} {h : F₁ ⟶ D₂} {j : F₁ ⟶ G₂} {q : G₂ ⟶ E₄}
    (h₁ : c ≫ d = d' ≫ c') (h₂ : c' ≫ e ≫ f = x ≫ y ≫ z)
    (h₃ : b ≫ d' ≫ x = w ≫ v ≫ p) (h₄ : p ≫ y = r ≫ s)
    (h₅ : a ≫ w = t ≫ h) (h₆ : h ≫ v ≫ r = j ≫ q) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f = t ≫ j ≫ q ≫ s ≫ z := by
  rw [reassoc_of% h₁, h₂, reassoc_of% h₃, reassoc_of% h₄,
    reassoc_of% h₅, reassoc_of% h₆]

/-- The right projection-composition diagram, with the same prescribed endpoint. -/
private theorem projection_right_path {A : Type*} [Category A]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ B₃ C₄ D₅ E₂ E₃ F₁ G₂ : A}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃}
    {d : A₃ ⟶ A₄} {e : A₄ ⟶ A₅} {f : A₅ ⟶ A₆}
    {d' : A₂ ⟶ B₃} {c' : B₃ ⟶ A₄}
    {e' : B₃ ⟶ C₄} {c'' : C₄ ⟶ A₅}
    {x : C₄ ⟶ D₅} {z : D₅ ⟶ A₆}
    {j : A₁ ⟶ E₂} {q : E₂ ⟶ C₄}
    {y : E₂ ⟶ E₃} {q' : E₃ ⟶ D₅}
    {t : A₀ ⟶ F₁} {v : F₁ ⟶ G₂} {p : G₂ ⟶ E₃}
    (h₁ : c ≫ d = d' ≫ c') (h₂ : c' ≫ e = e' ≫ c'')
    (h₃ : c'' ≫ f = x ≫ z) (h₄ : b ≫ d' ≫ e' = j ≫ q)
    (h₅ : q ≫ x = y ≫ q') (h₆ : a ≫ j ≫ y = t ≫ v ≫ p) :
    a ≫ b ≫ c ≫ d ≫ e ≫ f = t ≫ v ≫ p ≫ q' ≫ z := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃, reassoc_of% h₄,
    reassoc_of% h₅, reassoc_of% h₆]

private theorem support_transport
    {D : FiniteFieldDatum.{u}} {B : SixFunctorSpace D → Type*}
    [∀ X, Category (B X)] (S : SixFunctorPushStage D B)
    {X Y : SixFunctorSpace D} {f g : X ⟶ Y} (e : f = g)
    (c : Compactification f.hom.left) (K : B X) :
    (S.support f c).obj K =
      (S.support g (Eq.mp (congrArg (fun t : X ⟶ Y ↦
        Compactification t.hom.left) e) c)).obj K := by
  cases e
  rfl

private theorem comparison_transport
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) (m : ℕ)
    {X Y : SixFunctorSpace D} {f g : X ⟶ Y} (e : f = g)
    (c : Compactification f.hom.left)
    (K : sfIntegralConstructibleCategory C.l E X.obj.left) :
    HEq (((d.integralNormalization.reduction m).supportAdjunction f c).left.hom.app K)
      (((d.integralNormalization.reduction m).supportAdjunction g
        (Eq.mp (congrArg (fun t : X ⟶ Y ↦ Compactification t.hom.left) e) c)).left.hom.app
          K) := by
  cases e
  rfl

private theorem reductions_heq
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) (X : SixFunctorSpace D)
    {K K' M : sfIntegralConstructibleCategory C.l E X.obj.left} (e : K = K')
    (a : K ⟶ M) (b : K' ⟶ M)
    (h : ∀ m : ℕ, HEq ((IntegralProjectionReduction.reduction d m X).map a)
      ((IntegralProjectionReduction.reduction d m X).map b)) : HEq a b := by
  cases e
  exact heq_of_eq (integral_reductions_jointly_faithful d X a b
    (fun m ↦ eq_of_heq (h m)))

private theorem cancel_iso_heq {A : Type*} [Category A]
    {K K' M N : A} (e : K = K') (a : K ⟶ M) (b : K' ⟶ M) (i : M ≅ N)
    (h : HEq (a ≫ i.hom) (b ≫ i.hom)) : HEq a b := by
  cases e
  exact heq_of_eq ((cancel_mono i.hom).1 (eq_of_heq h))

private theorem coefficient_proper
    {D : FiniteFieldDatum.{u}} {B B' : SixFunctorSpace D → Type*}
    [∀ X, Category (B X)] [∀ X, Category (B' X)]
    {S : SixFunctorPushStage D B} {F : SixFunctorPushStage D B'}
    {R : ∀ X, B X ⥤ B' X} (a : SixFunctorCoefficientComparison S F R)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : B X) :
    (R Y).map ((S.properIdentification f c).hom.app K) ≫
        (a.directAdjunction f).right.hom.app K =
      (a.supportAdjunction f c).left.hom.app K ≫
        (F.properIdentification f c).hom.app ((R X).obj K) := by
  simp only [SixFunctorPushStage.properIdentification, Iso.trans_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [a.properIdentity f K, ← Category.assoc,
    a.compactification f c (.ofIsProper f.hom.left) K, Category.assoc]

set_option maxHeartbeats 2000000 in
-- Checking the operation-coordinate types requires more than the default heartbeat budget.
private theorem integral_composition
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) :
    let B := fun X : SixFunctorSpace D ↦ sfIntegralConstructibleCategory C.l E X.obj.left
    let S := d.higher.integral
    let T := d.higher.integralTensor
    let A := d.higher.integralExchange
    let P := d.integralFiniteTorDomain
    (∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : B X) (L : B Z), P Z L →
      ((T Z).map ((S.composition f g cf cg cfg).hom.app K)).app L ≫
          compactSupportProjectionComponent A g cg ((S.support f cf).obj K) L ≫
          (S.support g cg).map
            (compactSupportProjectionComponent A f cf K ((S.pull g).obj L)) =
        compactSupportProjectionComponent A (f ≫ g) cfg K L ≫
          (S.composition f g cf cg cfg).hom.app
            (((T X).obj K).obj ((S.pull (f ≫ g)).obj L)) ≫
          (S.support g cg).map ((S.support f cf).map
            (((T X).obj K).map ((S.pullComposition f g).hom.app L)))) := by
  dsimp only
  intro X Y Z f g _ _ _ _ _ _ cf cg cfg K L _
  let : IsSeparated (f ≫ g).hom.left := by
    change IsSeparated (f.hom.left ≫ g.hom.left)
    infer_instance
  let : LocallyOfFiniteType (f ≫ g).hom.left := by
    change LocallyOfFiniteType (f.hom.left ≫ g.hom.left)
    infer_instance
  let : QuasiCompact (f ≫ g).hom.left := by
    change QuasiCompact (f.hom.left ≫ g.hom.left)
    infer_instance
  apply integral_reductions_jointly_faithful d Z
  intro m
  obtain ⟨t, hn₁, hn₂, hpf, _⟩ := integralProjection_reduction_coordinates d m
  let R := IntegralProjectionReduction.reduction d m
  let J := IntegralProjectionReduction.torReduction d m
  let S := d.higher.integral
  let F := (IntegralProjectionReduction.stage d m).finite
  let V := CompactSupportFiniteProjection.partialTensor
    (IntegralProjectionReduction.stage d m)
  let G := fun {U V : SixFunctorSpace D} (q : U ⟶ V) ↦
    CompactSupportFiniteProjection.torPull (IntegralProjectionReduction.stage d m) q
  let a := d.integralNormalization.reduction m
  let k := (R X).obj K
  let l := (J Z).obj L
  let φg := IntegralProjectionReduction.pullIso d m g L
  let N := ((d.higher.integralTensor X).obj K).obj
    ((S.pull f).obj ((S.pull g).obj L))
  let N₀ := ((d.higher.integralTensor X).obj K).obj ((S.pull (f ≫ g)).obj L)
  let ex := IntegralProjectionReduction.tensorPullIso d m t f K ((S.pull g).obj L) ≪≫
    ((V X).obj k).mapIso ((G f).mapIso φg)
  let e := (a.supportAdjunction g cg).left.app ((S.support f cf).obj N) ≪≫
    (F.support g cg).mapIso ((a.supportAdjunction f cf).left.app N) ≪≫
    (F.support g cg).mapIso ((F.support f cf).mapIso ex)
  let p := fun {U V : SixFunctorSpace D} (q : U ⟶ V)
    (c : Compactification q.hom.left) (M : sfIntegralConstructibleCategory C.l E U.obj.left)
    (N : sfIntegralConstructibleCategory C.l E V.obj.left) ↦
    compactSupportProjectionComponent d.higher.integralExchange q c M N
  let pm := fun {U V : SixFunctorSpace D} (q : U ⟶ V)
    (c : Compactification q.hom.left) (M : sixFunctorFiniteCategory D C E
      (m + 1) (Nat.le_add_left 1 m) U)
    (N : finiteTorConstructibleCategory C.l E (m + 1) (Nat.le_add_left 1 m) V.obj.left) ↦
    CompactSupportFiniteProjection.component (IntegralProjectionReduction.stage d m) q c M N
  have laws := (compactSupportProjectionFormula_finiteStages d).2.1 m
  have hf :
      ((V Y).obj ((F.support f cf).obj k)).map φg.hom ≫ pm f cf k ((G g).obj l) =
      pm f cf k ((J Y).obj ((S.pull g).obj L)) ≫
        (F.support f cf).map (((V X).obj k).map ((G f).map φg.hom)) := by
    simpa only [R, S, F, V, G, J, k, l, IntegralProjectionReduction.stage,
      IntegralProjectionReduction.reduction, Functor.comp_obj,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp, Category.comp_id]
      using laws.naturality f cf (𝟙 k) φg.hom
  have hg :
      ((V Z).map ((F.support g cg).map
        ((a.supportAdjunction f cf).left.hom.app K))).app l ≫
        pm g cg ((F.support f cf).obj k) l =
      pm g cg ((R Y).obj ((S.support f cf).obj K)) l ≫
        (F.support g cg).map
          (((V Y).map ((a.supportAdjunction f cf).left.hom.app K)).app ((G g).obj l)) := by
    simpa only [R, S, F, V, G, J, k, l, IntegralProjectionReduction.stage,
      IntegralProjectionReduction.reduction, Functor.comp_obj,
      CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
      using laws.naturality g cg ((a.supportAdjunction f cf).left.hom.app K) (𝟙 l)
  have htn := ((V Y).map ((a.supportAdjunction f cf).left.hom.app K)).naturality φg.hom
  have hpf₁ := hpf f cf K ((S.pull g).obj L)
  have hpf₂ := hpf g cg ((S.support f cf).obj K) L
  have hpf₃ := hpf (f ≫ g) cfg K L
  dsimp only [IntegralProjectionReduction.sourceIso,
    IntegralProjectionReduction.targetIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom] at hpf₁ hpf₂ hpf₃
  simp only [Category.assoc] at hpf₁ hpf₂ hpf₃
  have inner :
      (R Y).map (p f cf K ((S.pull g).obj L)) ≫
        (a.supportAdjunction f cf).left.hom.app N ≫ (F.support f cf).map ex.hom =
      (IntegralProjectionReduction.tensorPullIso d m t g ((S.support f cf).obj K) L).hom ≫
        ((V Y).map ((a.supportAdjunction f cf).left.hom.app K)).app ((G g).obj l) ≫
        pm f cf k ((G g).obj l) := by
    dsimp only [ex, Iso.trans_hom, Functor.mapIso_hom]
    simp only [Functor.map_comp]
    rw [reassoc_of% hpf₁, ← hf, ← reassoc_of% htn]
    simp only [IntegralProjectionReduction.tensorPullIso, Iso.trans_hom,
      Functor.mapIso_hom, Category.assoc]
    rfl
  have innerg := congrArg (F.support g cg).map inner
  simp only [Functor.map_comp] at innerg
  have natg := (a.supportAdjunction g cg).left.hom.naturality
    (p f cf K ((S.pull g).obj L))
  dsimp only [Functor.comp_map] at natg
  have hnt := hn₁ Z _ _ L ((S.composition f g cf cg cfg).hom.app K)
  dsimp only [Functor.comp_obj] at hnt
  have hc := congrArg (fun z ↦ ((V Z).map z).app l)
    (a.composition f g cf cg cfg K)
  simp only [Functor.map_comp, NatTrans.comp_app, Functor.comp_obj] at hc
  have hleft :
      (R Z).map
        (((d.higher.integralTensor Z).map ((S.composition f g cf cg cfg).hom.app K)).app L ≫
          p g cg ((S.support f cf).obj K) L ≫
          (S.support g cg).map (p f cf K ((S.pull g).obj L))) ≫ e.hom =
      (IntegralProjectionReduction.sourceIso d m t (f ≫ g) cfg K L).hom ≫
        ((V Z).map ((F.composition f g cf cg cfg).hom.app k)).app l ≫
        pm g cg ((F.support f cf).obj k) l ≫
        (F.support g cg).map (pm f cf k ((G g).obj l)) := by
    dsimp only [e, IntegralProjectionReduction.sourceIso, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom]
    simp only [Functor.map_comp, Category.assoc]
    exact projection_left_path natg innerg hpf₂ hg.symm hnt hc
  have hpull :
      (J X).map ((S.pullComposition f g).hom.app L) ≫
        (IntegralProjectionReduction.pullIso d m f ((S.pull g).obj L)).hom ≫
        (G f).map φg.hom =
      (IntegralProjectionReduction.pullIso d m (f ≫ g) L).hom ≫
        (CompactSupportFiniteProjection.torPullComposition
          (IntegralProjectionReduction.stage d m) f g l).hom := by
    apply (finiteTorConstructible C.l E (m + 1) (Nat.le_add_left 1 m) X.obj.left).ι.map_injective
    exact congrArg (fun z ↦ z.hom) (a.pullComposition f g L)
  have hpt := congrArg ((V X).obj k).map hpull
  simp only [Functor.map_comp] at hpt
  have htensor :
      (R X).map (((d.higher.integralTensor X).obj K).map
        ((S.pullComposition f g).hom.app L)) ≫ ex.hom =
      (IntegralProjectionReduction.tensorPullIso d m t (f ≫ g) K L).hom ≫
        ((V X).obj k).map (CompactSupportFiniteProjection.torPullComposition
          (IntegralProjectionReduction.stage d m) f g l).hom := by
    dsimp only [ex, IntegralProjectionReduction.tensorPullIso, Iso.trans_hom,
      Functor.mapIso_hom]
    simp only [Category.assoc]
    rw [reassoc_of% (hn₂ X K _ _ ((S.pullComposition f g).hom.app L)),
      hpt]
  have htensorf := congrArg (F.support f cf).map htensor
  simp only [Functor.map_comp] at htensorf
  have htensorg := congrArg (F.support g cg).map htensorf
  simp only [Functor.map_comp] at htensorg
  have natf := (a.supportAdjunction f cf).left.hom.naturality
    (((d.higher.integralTensor X).obj K).map ((S.pullComposition f g).hom.app L))
  dsimp only [Functor.comp_map] at natf
  have natfg := congrArg (F.support g cg).map natf
  simp only [Functor.map_comp] at natfg
  have natg' := (a.supportAdjunction g cg).left.hom.naturality
    ((S.support f cf).map
      (((d.higher.integralTensor X).obj K).map ((S.pullComposition f g).hom.app L)))
  dsimp only [Functor.comp_map] at natg'
  have natc := (F.composition f g cf cg cfg).hom.naturality
    (IntegralProjectionReduction.tensorPullIso d m t (f ≫ g) K L).hom
  dsimp only [Functor.comp_map] at natc
  have hright :
      (R Z).map
        (p (f ≫ g) cfg K L ≫ (S.composition f g cf cg cfg).hom.app N₀ ≫
          (S.support g cg).map ((S.support f cf).map
            (((d.higher.integralTensor X).obj K).map
              ((S.pullComposition f g).hom.app L)))) ≫ e.hom =
      (IntegralProjectionReduction.sourceIso d m t (f ≫ g) cfg K L).hom ≫
        pm (f ≫ g) cfg k l ≫ (F.composition f g cf cg cfg).hom.app
          (((V X).obj k).obj ((G (f ≫ g)).obj l)) ≫
        (F.support g cg).map ((F.support f cf).map (((V X).obj k).map
          (CompactSupportFiniteProjection.torPullComposition
            (IntegralProjectionReduction.stage d m) f g l).hom)) := by
    dsimp only [e, IntegralProjectionReduction.sourceIso, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom]
    simp only [Functor.map_comp, Category.assoc]
    exact projection_right_path natg' natfg htensorg
      (a.composition f g cf cg cfg N₀) natc.symm hpf₃
  apply (cancel_mono e.hom).1
  rw [hleft, hright]
  exact congrArg (fun z ↦
    (IntegralProjectionReduction.sourceIso d m t (f ≫ g) cfg K L).hom ≫ z)
      (laws.composition f g cf cg cfg k l)

set_option maxHeartbeats 2000000 in
-- Checking the operation-coordinate types requires more than the default heartbeat budget.
private theorem integral_pentagon
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) :
    let B := fun X : SixFunctorSpace D ↦ sfIntegralConstructibleCategory C.l E X.obj.left
    let S := d.higher.integral
    (∀ {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated h.hom.left] [LocallyOfFiniteType h.hom.left] [QuasiCompact h.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : B X),
    HEq ((S.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.support h ch).map ((S.composition f g cf cg cfg).hom.app K))
      ((S.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app K ≫
        (S.composition g h cg ch cgh).hom.app ((S.support f cf).obj K))) := by
  dsimp only
  intro X Y Z W f g h _ _ _ _ _ _ _ _ _ cf cg ch cfg cgh cfgh K
  have hs := support_transport d.higher.integral (Category.assoc f g h) cfgh K
  apply reductions_heq d W hs
  intro m
  let R := IntegralProjectionReduction.reduction d m
  let S := d.higher.integral
  let F := (IntegralProjectionReduction.stage d m).finite
  let c := d.integralNormalization.reduction m
  let e := (c.supportAdjunction h ch).left.app ((S.support g cg).obj
      ((S.support f cf).obj K)) ≪≫
    (F.support h ch).mapIso ((c.supportAdjunction g cg).left.app
      ((S.support f cf).obj K)) ≪≫
    (F.support h ch).mapIso ((F.support g cg).mapIso
      ((c.supportAdjunction f cf).left.app K))
  have hleft :
      (R W).map ((S.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
        (S.support h ch).map ((S.composition f g cf cg cfg).hom.app K)) ≫ e.hom =
      (c.supportAdjunction ((f ≫ g) ≫ h) cfgh).left.hom.app K ≫
        (F.composition (f ≫ g) h cfg ch cfgh).hom.app ((R X).obj K) ≫
        (F.support h ch).map ((F.composition f g cf cg cfg).hom.app ((R X).obj K)) := by
    have hn := (c.supportAdjunction h ch).left.hom.naturality
      ((S.composition f g cf cg cfg).hom.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    have hf := congrArg (F.support h ch).map (c.composition f g cf cg cfg K)
    simp only [Functor.map_comp] at hf
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hn, hf, reassoc_of% (c.composition (f ≫ g) h cfg ch cfgh K)]
  let c' := Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
    (Category.assoc f g h)) cfgh
  have hright :
      (R W).map ((S.composition f (g ≫ h) cf cgh c').hom.app K ≫
        (S.composition g h cg ch cgh).hom.app ((S.support f cf).obj K)) ≫ e.hom =
      (c.supportAdjunction (f ≫ (g ≫ h)) c').left.hom.app K ≫
        (F.composition f (g ≫ h) cf cgh c').hom.app ((R X).obj K) ≫
        (F.composition g h cg ch cgh).hom.app ((F.support f cf).obj ((R X).obj K)) := by
    have hn := (F.composition g h cg ch cgh).hom.naturality
      ((c.supportAdjunction f cf).left.hom.app K)
    dsimp only [Functor.comp_map, Functor.comp_obj] at hn
    dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (c.composition g h cg ch cgh ((S.support f cf).obj K))]
    rw [← hn, reassoc_of% (c.composition f (g ≫ h) cf cgh c' K)]
  apply cancel_iso_heq (congrArg (R W).obj hs) _ _ e
  rw [hleft, hright]
  exact heq_comp (congrArg (R W).obj hs)
    (support_transport F (Category.assoc f g h) cfgh ((R X).obj K)) rfl
    (comparison_transport d m (Category.assoc f g h) cfgh K)
    (((compactSupportProjectionFormula_finiteStages d).2.1 m).pentagon
      f g h cf cg ch cfg cgh cfgh ((R X).obj K))

set_option maxHeartbeats 2000000 in
-- Checking the operation-coordinate types requires more than the default heartbeat budget.
private theorem integral_proper
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) :
    let B := fun X : SixFunctorSpace D ↦ sfIntegralConstructibleCategory C.l E X.obj.left
    let S := d.higher.integral
    let T := d.higher.integralTensor
    let A := d.higher.integralExchange
    let P := d.integralFiniteTorDomain
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : B X) (L : B Y), P Y L →
      ((T Y).map ((S.properIdentification f c).hom.app K)).app L ≫
          compactSupportProperProjection A f K L =
        compactSupportProjectionComponent A f c K L ≫
          (S.properIdentification f c).hom.app
            (((T X).obj K).obj ((S.pull f).obj L))) := by
  dsimp only
  intro X Y f _ c K L _
  apply integral_reductions_jointly_faithful d Y
  intro m
  obtain ⟨t, hn₁, _, hpf, hproper⟩ := integralProjection_reduction_coordinates d m
  let R := IntegralProjectionReduction.reduction d m
  let F := (IntegralProjectionReduction.stage d m).finite
  let T := CompactSupportFiniteProjection.partialTensor
    (IntegralProjectionReduction.stage d m)
  let a := d.integralNormalization.reduction m
  let N := ((d.higher.integralTensor X).obj K).obj ((d.higher.integral.pull f).obj L)
  let eT := IntegralProjectionReduction.tensorPullIso d m t f K L
  let Lm := (IntegralProjectionReduction.torReduction d m Y).obj L
  have ht := congrArg (fun z ↦ ((T Y).map z).app Lm)
    (coefficient_proper a f c K)
  simp only [Functor.map_comp, NatTrans.comp_app] at ht
  have hfin := ((compactSupportProjectionFormula_finiteStages d).2.1 m).proper
    f c ((R X).obj K) Lm
  have hn := (F.properIdentification f c).hom.naturality eT.hom
  have hp := hpf f c K L
  dsimp only [IntegralProjectionReduction.sourceIso,
    IntegralProjectionReduction.targetIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom] at hp
  apply (cancel_mono (IntegralProjectionReduction.properTargetIso d m t f K L).hom).1
  have hleft :
      (R Y).map
        (((d.higher.integralTensor Y).map
          ((d.higher.integral.properIdentification f c).hom.app K)).app L ≫
            compactSupportProperProjection d.higher.integralExchange f K L) ≫
        (IntegralProjectionReduction.properTargetIso d m t f K L).hom =
      (IntegralProjectionReduction.sourceIso d m t f c K L).hom ≫
        CompactSupportFiniteProjection.component (IntegralProjectionReduction.stage d m)
          f c ((R X).obj K) Lm ≫
        (F.properIdentification f c).hom.app _ := by
    simp only [Functor.map_comp, Category.assoc]
    rw [hproper f K L]
    dsimp only [IntegralProjectionReduction.properSourceIso,
      IntegralProjectionReduction.sourceIso, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom]
    simp only [Category.assoc]
    rw [reassoc_of% (hn₁ Y _ _ L
      ((d.higher.integral.properIdentification f c).hom.app K))]
    rw [reassoc_of% ht, hfin]
  have hright :
      (R Y).map
        (compactSupportProjectionComponent d.higher.integralExchange f c K L ≫
          (d.higher.integral.properIdentification f c).hom.app N) ≫
        (IntegralProjectionReduction.properTargetIso d m t f K L).hom =
      (IntegralProjectionReduction.sourceIso d m t f c K L).hom ≫
        CompactSupportFiniteProjection.component (IntegralProjectionReduction.stage d m)
          f c ((R X).obj K) Lm ≫
        (F.properIdentification f c).hom.app _ := by
    dsimp only [IntegralProjectionReduction.properTargetIso,
      IntegralProjectionReduction.sourceIso, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom]
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% (coefficient_proper a f c N), ← hn,
      reassoc_of% hp]
  exact hleft.trans hright.symm

/-- Composition, its pentagon, and proper coincidence for the normalized integral
projection. These are equalities of the actual recorded operation maps and make no
assertion that projection is invertible.
Source: fix-prop-projection-formula.proof.md, the coherence sentence, and
lem-sf-projection-integral-stage-laws, proof step 2.
(blueprint: lem-sf-integral-stage-projection-structural-identities).

Proof: integral residue Tor lifts every reduced input to the full finite-Tor category.
Use normalized tensor coordinates and the individual proper/open projection reduction
squares. The coefficient datum already preserves support composition, pullback composition,
compactification comparison and proper identification. For composition, move the inner
projection past the support comparison by naturality, use the two single-projection squares,
and move the finite tensor and pullback comparisons using finite projection naturality.
The remaining equation is exactly finite projection composition. For the pentagon, normalize
the two compositor paths with the coefficient composition equation and naturality, apply the
finite pentagon, and retain the equality transport along Category.assoc. For proper
coincidence, combine tensor naturality, the two projection squares and coefficient
compatibility of properIdentification; the finite proper equation finishes the square.
Cancel the endpoint isomorphisms. Equality of all finite reductions implies equality of the
integral arrows by the proved constructible Milnor injection: finite shifted Hom groups make
the lim-one term vanish. Its qcqs finiteness input is the finite-coefficient Hom theorem,
which does not assume separated structure maps. No faithfulness of unrestricted derived
evaluation or invertibility of a projection component is assumed. -/
theorem integralStageProjection_structuralIdentities
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (d : SixFunctorOperationDatum D C E n hn) :
    let B := fun X : SixFunctorSpace D ↦ sfIntegralConstructibleCategory C.l E X.obj.left
    let S := d.higher.integral
    let T := d.higher.integralTensor
    let A := d.higher.integralExchange
    let P := d.integralFiniteTorDomain
    (∀ {X Y Z : SixFunctorSpace D} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cfg : Compactification (f ≫ g).hom.left) (K : B X) (L : B Z), P Z L →
      ((T Z).map ((S.composition f g cf cg cfg).hom.app K)).app L ≫
          compactSupportProjectionComponent A g cg ((S.support f cf).obj K) L ≫
          (S.support g cg).map
            (compactSupportProjectionComponent A f cf K ((S.pull g).obj L)) =
        compactSupportProjectionComponent A (f ≫ g) cfg K L ≫
          (S.composition f g cf cg cfg).hom.app
            (((T X).obj K).obj ((S.pull (f ≫ g)).obj L)) ≫
          (S.support g cg).map ((S.support f cf).map
            (((T X).obj K).map ((S.pullComposition f g).hom.app L)))) ∧
    (∀ {X Y Z W : SixFunctorSpace D}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    [IsSeparated g.hom.left] [LocallyOfFiniteType g.hom.left] [QuasiCompact g.hom.left]
    [IsSeparated h.hom.left] [LocallyOfFiniteType h.hom.left] [QuasiCompact h.hom.left]
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch : Compactification h.hom.left) (cfg : Compactification (f ≫ g).hom.left)
    (cgh : Compactification (g ≫ h).hom.left)
    (cfgh : Compactification ((f ≫ g) ≫ h).hom.left) (K : B X),
    HEq ((S.composition (f ≫ g) h cfg ch cfgh).hom.app K ≫
      (S.support h ch).map ((S.composition f g cf cg cfg).hom.app K))
      ((S.composition f (g ≫ h) cf cgh
        (Eq.mp (congrArg (fun t : X ⟶ W ↦ Compactification t.hom.left)
          (Category.assoc f g h)) cfgh)).hom.app K ≫
        (S.composition g h cg ch cgh).hom.app ((S.support f cf).obj K))) ∧
    (∀ {X Y : SixFunctorSpace D} (f : X ⟶ Y) [IsProper f.hom.left]
    (c : Compactification f.hom.left) (K : B X) (L : B Y), P Y L →
      ((T Y).map ((S.properIdentification f c).hom.app K)).app L ≫
          compactSupportProperProjection A f K L =
        compactSupportProjectionComponent A f c K L ≫
          (S.properIdentification f c).hom.app
            (((T X).obj K).obj ((S.pull f).obj L))) := by
  exact ⟨integral_composition d, integral_pentagon d, integral_proper d⟩

end WeilConjectures
