/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerCore
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorUnitRepresentatives
import all WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceScalarUnit
import all WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerComparisonData
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems

/-! # Scalar extension of coherent systems is unital and associative

The whole-system scalar tensorator `ScalarExtensionTower.derivedSigma` is compatible with the
associators and unitors of the published coherent system monoidal structures.

Source: Stacks Project, Tags 03EL and 07A4.
(blueprint: lem-pur-system-scalar-tensor-braiding).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MonoidalCategory
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard pullbackTensorCalculus
  Functor.leftAdjoint Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  integralComparisonSequenceScalarModel
attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall

variable (l : ℕ) [Fact l.Prime]
  (E L : Type u) [Field E] [Field L]
  [Algebra (Padic l) E] [Algebra (Padic l) L]
  [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (W : Scheme.{u})

/-- Paste a cochain square through an adjunction unit. -/
private theorem scalarAssoc_adjunction_paste {B D : Type*} [Category B] [Category D]
    {F : B ⥤ D} {G : D ⥤ B} (adj : F ⊣ G)
    {P Q : B} {T V T' V' : D} (a : P ⟶ Q)
    (b : F.obj Q ⟶ T) (c : T ⟶ V)
    (b' : F.obj P ⟶ T') (c' : T' ⟶ V') (d : V' ⟶ V)
    (h : a ≫ adj.unit.app Q ≫ G.map b ≫ G.map c =
      adj.unit.app P ≫ G.map b' ≫ G.map c' ≫ G.map d) :
    F.map a ≫ b ≫ c = b' ≫ c' ≫ d := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  have hu := adj.unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← hu]
  simpa only [Category.assoc] using h

/-- Pasting the six pure-section equations requires only function congruence. -/
private theorem scalarAssoc_sectionSquare
    {A B C D E F G H : Type*}
    (σ : A → B) (ηB : B → C) (κB : C → D) (tB : D → H)
    (ηA : A → E) (κA : E → F) (tA : F → G) (τ : G → H)
    (x : A) (b : B) (d : D) (h : H) (f : F) (g : G)
    (hσ : σ x = b) (hκB : κB (ηB b) = d) (htB : tB d = h)
    (hκA : κA (ηA x) = f) (htA : tA f = g) (hτ : τ g = h) :
    tB (κB (ηB (σ x))) = τ (tA (κA (ηA x))) := by
  rw [hσ, hκB, htB, hκA, htA, hτ]

set_option maxHeartbeats 800000 in
-- Elaborating the nested total-complex comparison uses extra heartbeats.
/-- The strict scalar tensorator commutes with cochain reassociation.
Source: Stacks 07A4, with the unsigned reassociation of Tag 06YN.
(blueprint: lem-pur-system-scalar-tensor-braiding).

Proof: transpose both chain maps by the scalar-extension adjunction; detect equality on
local pure triples. Both routes send `x ⊗ y ⊗ z` to the tensor of the three unit images, with
the right parenthesization. -/
theorem scalarSigma_cochain_associativity (P Q N : ScalarExtensionTower.Complex l E W)
    (aY : (ScalarExtensionTower.tensor l E W).obj
        ((ScalarExtensionTower.tensor l E W).obj (P, Q), N) ≅
      (ScalarExtensionTower.tensor l E W).obj (P, (ScalarExtensionTower.tensor l E W).obj (Q, N)))
    (aX : (ScalarExtensionTower.tensor l L W).obj
        ((ScalarExtensionTower.tensor l L W).obj ((ScalarExtensionTower.scalar l E L ι W).obj P,
          (ScalarExtensionTower.scalar l E L ι W).obj Q),
          (ScalarExtensionTower.scalar l E L ι W).obj N) ≅
      (ScalarExtensionTower.tensor l L W).obj ((ScalarExtensionTower.scalar l E L ι W).obj P,
        (ScalarExtensionTower.tensor l L W).obj ((ScalarExtensionTower.scalar l E L ι W).obj Q,
          (ScalarExtensionTower.scalar l E L ι W).obj N)))
    (haY : ∀ (p q r pq qr k : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
      (hn : pq + r = k) (hn' : p + qr = k) (U : (ℕ × W.ProEt)ᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (N.X r).val.obj U),
      (aY.hom.f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf.{u, u} l E W)
          ((ScalarExtensionTower.tensor l E W).obj (P, Q)) N pq r k hn U
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf.{u, u} l E W) P Q p q pq hpq U x y) z) =
      coefficientTensorGenerator.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf.{u, u} l E W) P
        ((ScalarExtensionTower.tensor l E W).obj (Q, N)) p qr k hn' U x
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf.{u, u} l E W) Q N q r qr hqr U y z))
    (haX : ∀ (p q r pq qr k : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
      (hn : pq + r = k) (hn' : p + qr = k) (U : (ℕ × W.ProEt)ᵒᵖ)
      (x : (((ScalarExtensionTower.scalar l E L ι W).obj P).X p).val.obj U)
      (y : (((ScalarExtensionTower.scalar l E L ι W).obj Q).X q).val.obj U)
      (z : (((ScalarExtensionTower.scalar l E L ι W).obj N).X r).val.obj U),
      (aX.hom.f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf.{u, u} l L W)
          ((ScalarExtensionTower.tensor l L W).obj ((ScalarExtensionTower.scalar l E L ι W).obj P,
            (ScalarExtensionTower.scalar l E L ι W).obj Q))
          ((ScalarExtensionTower.scalar l E L ι W).obj N) pq r k hn U
          (coefficientTensorGenerator.{u, u + 1, u}
            (coefficientSequenceTopology (ProEt.topology W))
            (coefficientSequenceCommRingSheaf.{u, u} l L W)
            ((ScalarExtensionTower.scalar l E L ι W).obj P)
            ((ScalarExtensionTower.scalar l E L ι W).obj Q) p q pq hpq U x y) z) =
      coefficientTensorGenerator.{u, u + 1, u} (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf.{u, u} l L W)
        ((ScalarExtensionTower.scalar l E L ι W).obj P)
        ((ScalarExtensionTower.tensor l L W).obj ((ScalarExtensionTower.scalar l E L ι W).obj Q,
          (ScalarExtensionTower.scalar l E L ι W).obj N)) p qr k hn' U x
        (coefficientTensorGenerator.{u, u + 1, u}
          (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf.{u, u} l L W)
          ((ScalarExtensionTower.scalar l E L ι W).obj Q)
          ((ScalarExtensionTower.scalar l E L ι W).obj N) q r qr hqr U y z)) :
    (ScalarExtensionTower.scalar l E L ι W).map aY.hom ≫
        ((ScalarExtensionTower.comparisons l).sigma E L ι W).hom.app
          (P, (ScalarExtensionTower.tensor l E W).obj (Q, N)) ≫
        (ScalarExtensionTower.tensor l L W).map (Prod.mkHom
          (𝟙 ((ScalarExtensionTower.scalar l E L ι W).obj P))
          (((ScalarExtensionTower.comparisons l).sigma E L ι W).hom.app (Q, N))) =
      ((ScalarExtensionTower.comparisons l).sigma E L ι W).hom.app
          ((ScalarExtensionTower.tensor l E W).obj (P, Q), N) ≫
        (ScalarExtensionTower.tensor l L W).map (Prod.mkHom
          (((ScalarExtensionTower.comparisons l).sigma E L ι W).hom.app (P, Q))
          (𝟙 ((ScalarExtensionTower.scalar l E L ι W).obj N))) ≫ aX.hom := by
  let JW := coefficientSequenceTopology (ProEt.topology W)
  let RE := coefficientSequenceCommRingSheaf.{u, u} l E W
  let RL := coefficientSequenceCommRingSheaf.{u, u} l L W
  let V := ScalarExtensionTower.scalar l E L ι W
  let TY := ScalarExtensionTower.tensor l E W
  let T := ScalarExtensionTower.tensor l L W
  let κ := (ScalarExtensionTower.comparisons l).sigma E L ι W
  let adj := ScalarExtensionTower.scalar_adj l E L ι W
  apply scalarAssoc_adjunction_paste (adj.mapHomologicalComplex (.up ℤ))
  apply CategoryTheory.tensorGenerator_ext₃.{u + 1, u, u} JW RE P Q N
  intro p q r pq k hpq hn U x y z
  have hqr : q + r = q + r := rfl
  have hn' : p + (q + r) = k := by omega
  change ((T.map (Prod.mkHom (𝟙 (V.obj P)) (κ.hom.app (Q, N)))).f k).val.app U
      (((κ.hom.app (P, TY.obj (Q, N))).f k).val.app U
        ((adj.unit.app _).val.app U
          ((aY.hom.f k).val.app U
            (coefficientTensorGenerator.{u, u + 1, u} JW RE (TY.obj (P, Q)) N pq r k hn U
              (coefficientTensorGenerator.{u, u + 1, u} JW RE P Q p q pq hpq U x y) z)))) =
    (aX.hom.f k).val.app U
      (((T.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (V.obj N)))).f k).val.app U
        (((κ.hom.app (TY.obj (P, Q), N)).f k).val.app U
          ((adj.unit.app _).val.app U
            (coefficientTensorGenerator.{u, u + 1, u} JW RE (TY.obj (P, Q)) N pq r k hn U
              (coefficientTensorGenerator.{u, u + 1, u} JW RE P Q p q pq hpq U x y) z))))
  let xp := (adj.unit.app (P.X p)).val.app U x
  let yq := (adj.unit.app (Q.X q)).val.app U y
  let zr := (adj.unit.app (N.X r)).val.app U z
  let gPQ := coefficientTensorGenerator.{u, u + 1, u} JW RE P Q p q pq hpq U x y
  let gQN := coefficientTensorGenerator.{u, u + 1, u} JW RE Q N q r (q + r) hqr U y z
  let gY' := coefficientTensorGenerator.{u, u + 1, u} JW RE P (TY.obj (Q, N))
    p (q + r) k hn' U x gQN
  let gR := coefficientTensorGenerator.{u, u + 1, u} JW RL (V.obj P) (V.obj (TY.obj (Q, N)))
    p (q + r) k hn' U xp ((adj.unit.app ((TY.obj (Q, N)).X (q + r))).val.app U gQN)
  let gL := coefficientTensorGenerator.{u, u + 1, u} JW RL (V.obj (TY.obj (P, Q))) (V.obj N)
    pq r k hn U ((adj.unit.app ((TY.obj (P, Q)).X pq)).val.app U gPQ) zr
  let gPQ' := coefficientTensorGenerator.{u, u + 1, u} JW RL
    (V.obj P) (V.obj Q) p q pq hpq U xp yq
  let gQN' := coefficientTensorGenerator.{u, u + 1, u} JW RL
    (V.obj Q) (V.obj N) q r (q + r) hqr U yq zr
  let gL' := coefficientTensorGenerator.{u, u + 1, u} JW RL
    (T.obj (V.obj P, V.obj Q)) (V.obj N) pq r k hn U gPQ' zr
  let gR' := coefficientTensorGenerator.{u, u + 1, u} JW RL
    (V.obj P) (T.obj (V.obj Q, V.obj N)) p (q + r) k hn' U xp gQN'
  have hκ' : ∀ (A B : ScalarExtensionTower.Complex l E W) (p q k : ℤ) (h : p + q = k)
      (U : (ℕ × W.ProEt)ᵒᵖ) (x : (A.X p).val.obj U) (y : (B.X q).val.obj U),
      ((κ.hom.app (A, B)).f k).val.app U
        ((adj.unit.app _).val.app U
          (coefficientTensorGenerator.{u, u + 1, u} JW RE A B p q k h U x y)) =
      coefficientTensorGenerator.{u, u + 1, u} JW RL (V.obj A) (V.obj B) p q k h U
        ((adj.unit.app (A.X p)).val.app U x)
        ((adj.unit.app (B.X q)).val.app U y) := by
    intro A B p q k h U x y
    subst h
    have h := (ScalarExtensionTower.comparisons l).sigma_formula E L ι W A B p q U 1 x y
    rw [← sequenceScalarAdjunction_unit l E L ι W, ← sequenceScalarAdjunction_unit l E L ι W,
      ← sequenceScalarAdjunction_unit l E L ι W] at h
    exact h
  refine scalarAssoc_sectionSquare
    ((aY.hom.f k).val.app U)
    ((adj.unit.app ((TY.obj (P, TY.obj (Q, N))).X k)).val.app U)
    (((κ.hom.app (P, TY.obj (Q, N))).f k).val.app U)
    (((T.map (Prod.mkHom (𝟙 (V.obj P)) (κ.hom.app (Q, N)))).f k).val.app U)
    ((adj.unit.app ((TY.obj (TY.obj (P, Q), N)).X k)).val.app U)
    (((κ.hom.app (TY.obj (P, Q), N)).f k).val.app U)
    (((T.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (V.obj N)))).f k).val.app U)
    ((aX.hom.f k).val.app U)
    _ gY' gR gR' gL gL' ?_ ?_ ?_ ?_ ?_ ?_
  · exact haY p q r pq (q + r) k hpq hqr hn hn' U x y z
  · exact hκ' P (TY.obj (Q, N)) p (q + r) k hn' U x gQN
  · have hm := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
      (𝟙 (V.obj P)) (κ.hom.app (Q, N)) p (q + r) k hn' U xp
      ((adj.unit.app ((TY.obj (Q, N)).X (q + r))).val.app U gQN)
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app] at hm
    exact hm.trans (congrArg (fun w ↦ coefficientTensorGenerator.{u, u + 1, u}
      JW RL (V.obj P) (T.obj (V.obj Q, V.obj N)) p (q + r) k hn' U xp w)
      (hκ' Q N q r (q + r) hqr U y z))
  · exact hκ' (TY.obj (P, Q)) N pq r k hn U gPQ z
  · have hm := CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}
      (κ.hom.app (P, Q)) (𝟙 (V.obj N)) pq r k hn U
      ((adj.unit.app ((TY.obj (P, Q)).X pq)).val.app U gPQ) zr
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app] at hm
    exact hm.trans (congrArg (fun w ↦ coefficientTensorGenerator.{u, u + 1, u}
      JW RL (T.obj (V.obj P, V.obj Q)) (V.obj N) pq r k hn U w zr)
      (hκ' P Q p q pq hpq U x y))
  · exact haX p q r pq (q + r) k hpq hqr hn hn' U xp yq zr

/-- The normalized whole-system scalar tensorator is associative.

Source: Stacks 07A4, total tensor construction; the scalar calculation of
lem-pur-system-scalar-tensor-braiding.
(blueprint: lem-pur-system-scalar-tensor-braiding).

Proof plan: take simultaneous flat-term K-flat representatives. By `DerivedSigmaModel` the
derived scalar tensorator is the localization of the strict scalar tensorator, conjugated by
the fixed tensor models and scalar counits; the system associators are the localizations of the
total reassociation maps with the same models. On a homogeneous local tensor both strict routes
send `c ⊗ ((x ⊗ y) ⊗ z)` to `(c x) ⊗ (y ⊗ z)` without a sign. These generators span the
sheafified total tensors, so the chain maps agree; localize and extend by naturality. -/
theorem systemScalarTensorAssociativity
    (M N P : coefficientSequenceDerived l E W) :
    let H := integralComparisonDerivedSequenceScalar l E L ι W
    let σ := ScalarExtensionTower.derivedSigma l E L ι W
      (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)
    H.map ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator M N P).hom ≫
      σ.hom.app (M, (pullbackTensorCalculus l E W).systemClosed.tensor.obj (N, P)) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom (𝟙 _) (σ.hom.app (N, P))) =
    σ.hom.app ((pullbackTensorCalculus l E W).systemClosed.tensor.obj (M, N), P) ≫
      (pullbackTensorCalculus l L W).systemClosed.tensor.map
        (Prod.mkHom (σ.hom.app (M, N)) (𝟙 _)) ≫
      ((pullbackTensorCalculus l L W).systemClosed.monoidal.associator
        (H.obj M) (H.obj N) (H.obj P)).hom := by
  sorry

/-- The selected calculus retains the system normalization from its resolution model.
Source: Stacks 07A4 and 0941 (blueprint: lem-pur-system-scalar-tensor-braiding). -/
private theorem scalar_systemTensorCoherence (D : Type u) [Field D] [Algebra (Padic l) D]
    [FiniteDimensional (Padic l) D] (W : Scheme.{u}) :
    ∃ β : @SymmetricCategory (coefficientSequenceDerived l D W) _
      (pullbackTensorCalculus l D W).systemClosed.monoidal,
      Nonempty (RingedDerivedTensorCoherence
        (coefficientSequenceTopology (ProEt.topology W))
        (coefficientSequenceCommRingSheaf l D W)
        (pullbackTensorCalculus l D W).systemClosed
        (pullbackTensorCalculus l D W).systemTensorModel β) := by
  unfold pullbackTensorCalculus
  exact (coefficientDerivedSystemEvaluationCalculus l D W).choose_spec.some.systemTensorCoherence

/-- Scalar extension of coherent systems sends the coefficient-ring unit to the
coefficient-ring unit.

Source: Stacks 03EL; extension of scalars of a free module of rank one.
(blueprint: lem-pur-system-scalar-tensor-braiding).

Proof: the coherent unit is the degree-zero single complex on the structure sheaf; it is
flat-term K-flat, so the scalar model computes its derived extension by the underived one, and
extension of scalars of the structure sheaf is the structure sheaf. -/
theorem systemScalarTensorUnitObject :
    Nonempty ((integralComparisonDerivedSequenceScalar l E L ι W).obj
        (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit ≅
      (pullbackTensorCalculus l L W).systemClosed.monoidal.tensorUnit) := by
  obtain ⟨_, ⟨cE⟩⟩ := scalar_systemTensorCoherence l E W
  obtain ⟨_, ⟨cL⟩⟩ := scalar_systemTensorCoherence l L W
  let δ := integralComparisonSequenceScalarModel.{u, u} l E L ι W
  let J := coefficientSequenceTopology (ProEt.topology W)
  let RE := coefficientSequenceCommRingSheaf.{u, u} l E W
  let RL := coefficientSequenceCommRingSheaf.{u, u} l L W
  have hk := unit_kflat.{u + 1, u, u} J RE
  have hiso : IsIso (δ.ε.app (ringedTensorUnitComplex.{u + 1, u, u} J RE)) := δ.computes _ hk
  let φ : (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RE ⟶
      ((𝟭 _).sheafPushforwardContinuous RingCat.{u + 1} J J).obj
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RL) :=
    ⟨Functor.whiskerRight (integralComparisonSequenceScalarMap.{u, u} l E L ι W).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let adj : δ.E ⊣ SheafOfModules.pushforward φ := ScalarExtensionTower.scalar_adj l E L ι W
  letI : (SheafOfModules.pushforward φ).IsRightAdjoint := adj.isRightAdjoint
  let e₀ : δ.E.obj (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RE)) ≅
      SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RL) :=
    (adj.leftAdjointUniq (SheafOfModules.pullbackPushforwardAdjunction φ)).app _ ≪≫
      asIso (SheafOfModules.pullbackObjUnitToUnit φ)
  let c : (δ.E.mapHomologicalComplex (.up ℤ)).obj (ringedTensorUnitComplex.{u + 1, u, u} J RE) ≅
      ringedTensorUnitComplex.{u + 1, u, u} J RL :=
    (HomologicalComplex.singleMapHomologicalComplex δ.E (.up ℤ) 0).app _ ≪≫
      (HomologicalComplex.single _ (.up ℤ) 0).mapIso e₀
  exact ⟨(integralComparisonDerivedSequenceScalar l E L ι W).mapIso cE.unitIso ≪≫
    @asIso _ _ _ _ (δ.ε.app (ringedTensorUnitComplex.{u + 1, u, u} J RE)) hiso ≪≫
    DerivedCategory.Q.mapIso c ≪≫ cL.unitIso.symm⟩

universe a b c d in
private theorem scalarAssociativity_from_tensorHom
    {C : Type a} [Category.{b} C] [MonoidalCategory C]
    {D : Type c} [Category.{d} D] [MonoidalCategory D]
    (F : C ⥤ D) (μ : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (h : ∀ A B M : C,
      F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
          (𝟙 (F.obj A) ⊗ₘ (μ.app (B, M)).hom) =
        (μ.app (A ⊗ B, M)).hom ≫ ((μ.app (A, B)).hom ⊗ₘ 𝟙 (F.obj M)) ≫
          (α_ (F.obj A) (F.obj B) (F.obj M)).hom) (A B M : C) :
    F.map (α_ A B M).hom ≫ (μ.app (A, B ⊗ M)).hom ≫
        F.obj A ◁ (μ.app (B, M)).hom =
      (μ.app (A ⊗ B, M)).hom ≫ (μ.app (A, B)).hom ▷ F.obj M ≫
        (α_ (F.obj A) (F.obj B) (F.obj M)).hom := by
  have h' := h A B M
  dsimp only [Functor.comp_obj, tensor_obj, Functor.prod_obj] at h' ⊢
  simpa only [MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_id] using h'

/-- Both unit equations for the normalized whole-system scalar tensorator.

Source: Stacks 03EL and 07A4.
(blueprint: lem-pur-system-scalar-tensor-braiding).

Proof: the associativity equation and any identification of the scalar extension of the unit
are combined by the monoidal unit extraction lemma. -/
theorem systemScalarTensorUnit :
    let H := integralComparisonDerivedSequenceScalar l E L ι W
    let σ := ScalarExtensionTower.derivedSigma l E L ι W
      (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)
    ∃ ε : H.obj (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit ≅
      (pullbackTensorCalculus l L W).systemClosed.monoidal.tensorUnit,
      ∀ M : coefficientSequenceDerived l E W,
        (σ.hom.app ((pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit, M) ≫
          (pullbackTensorCalculus l L W).systemClosed.tensor.map
            (Prod.mkHom ε.hom (𝟙 _)) ≫
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.leftUnitor (H.obj M)).hom =
        H.map ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor M).hom) ∧
        (σ.hom.app (M, (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit) ≫
          (pullbackTensorCalculus l L W).systemClosed.tensor.map
            (Prod.mkHom (𝟙 _) ε.hom) ≫
          ((pullbackTensorCalculus l L W).systemClosed.monoidal.rightUnitor (H.obj M)).hom =
        H.map ((pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor M).hom) := by
  letI : MonoidalCategory (coefficientSequenceDerived l E W) :=
    (pullbackTensorCalculus l E W).systemClosed.monoidal
  letI : MonoidalCategory (coefficientSequenceDerived l L W) :=
    (pullbackTensorCalculus l L W).systemClosed.monoidal
  let H := integralComparisonDerivedSequenceScalar l E L ι W
  let σ := ScalarExtensionTower.derivedSigma l E L ι W
    (pullbackTensorCalculus l E W) (pullbackTensorCalculus l L W)
  obtain ⟨e⟩ := systemScalarTensorUnitObject l E L ι W
  have hAssoc := scalarAssociativity_from_tensorHom H σ
    (systemScalarTensorAssociativity l E L ι W)
  obtain ⟨ε, hL, hR⟩ := unit_from_tensor H σ e hAssoc
  exact ⟨ε, fun M ↦ ⟨hL M, hR M⟩⟩

end WeilConjectures
