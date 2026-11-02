/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonSequenceSystems
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.UnitNormalizedCochainTensor
public import WeilConjectures.AlgebraicGeometry.SixFunctors.SitePullbackTensorGenerators
import all WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorConstraintCompletion
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteDualityMaps

/-! # The normalized tensor comparison of strict sequence pullback

Source: Stacks 07A4 (blueprint: stage3-pur-strict-pullback-comparisons).

For every morphism of schemes, the termwise sequence-site inverse image of strict
quotient cochain systems has a unique tensor comparison which is the adjunction-unit
generator formula on every pure total tensor. Universes of schemes and coefficients
are independent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite

namespace WeilConjectures.IntegralCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The unit-normalized cochain tensor comparison of the strict sequence pullback.
Source: Stacks 07A4 (blueprint: stage3-pur-strict-pullback-comparisons).
Proof: the sequence base change is representably flat, being the product of the
identity of the index poset with the left exact pro-etale base change. Apply the
normalized ordinary tensor comparison and its unique cochain extension. -/
theorem seqTensor_existsUnique {X Y : Scheme.{t}} (f : X ⟶ Y) :
    ∃! e : coefficientTotalTensor.{u, t + 1, t}
        (coefficientSequenceTopology (ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) ⋙
        (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ) ≅
      (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).prod
        ((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{u, t + 1, t}
          (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X),
      ∀ (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
        (p q k : ℤ) (h : p + q = k) (V : ℕ × Y.ProEt)
        (x : (P.X p).val.obj (op V)) (y : (Q.X q).val.obj (op V)),
        ((e.hom.app (P,Q)).f k).val.app
          (op ((integralComparisonSequenceBaseChange f).obj V))
          (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)).unit.app
            (((coefficientTotalTensor.{u, t + 1, t}
              (coefficientSequenceTopology (ProEt.topology Y))
              (coefficientSequenceCommRingSheaf l E Y)).obj (P,Q)).X k)).val.app (op V)
            (coefficientTensorGenerator.{u, t + 1, t}
              (coefficientSequenceTopology (ProEt.topology Y))
              (coefficientSequenceCommRingSheaf l E Y) P Q p q k h (op V) x y)) =
        coefficientTensorGenerator.{u, t + 1, t}
          (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj P)
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj Q)
          p q k h (op ((integralComparisonSequenceBaseChange f).obj V))
          (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)).unit.app
            (P.X p)).val.app (op V) x)
          (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)).unit.app
            (Q.X q)).val.app (op V) y) := by
  letI : RepresentablyFlat (proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  letI : RepresentablyFlat (integralComparisonSequenceBaseChange f) := by
    refine ⟨fun W ↦ ?_⟩
    exact IsCofiltered.of_equivalence
      (StructuredArrow.prodEquivalence W.1 W.2 (𝟭 ℕ) (proEtaleBaseChange f)).symm
  exact SemilinearSections.unitNormalizedCochainTensor.{t + 1, t, u}
    (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceTopology (ProEt.topology X)) (integralComparisonSequenceBaseChange f)
    (coefficientSequenceCommRingSheaf l E Y) (coefficientSequenceCommRingSheaf l E X)
    (integralComparisonSequenceRingMap l E f) (integralComparisonSequencePullback l E f)
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f))
    (SemilinearSections.sitePullbackTensorGenerators
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceTopology (ProEt.topology X)) (integralComparisonSequenceBaseChange f)
      (coefficientSequenceCommRingSheaf l E Y) (coefficientSequenceCommRingSheaf l E X)
      (integralComparisonSequenceRingMap l E f) (integralComparisonSequencePullback l E f)
      (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f))).exists.choose

/-- The chosen normalized tensor comparison of strict sequence pullback.
Source: Stacks 07A4 (blueprint: stage3-pur-strict-pullback-comparisons). -/
def seqTensor {X Y : Scheme.{t}} (f : X ⟶ Y) :=
  (seqTensor_existsUnique l E f).exists.choose

/-- The generator formula of `seqTensor`.
Source: Stacks 07A4 (blueprint: stage3-pur-strict-pullback-comparisons). -/
theorem seqTensor_generator {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (p q k : ℤ) (h : p + q = k) (V : (ℕ × Y.ProEt)ᵒᵖ)
    (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V) :
    (((seqTensor l E f).hom.app (P,Q)).f k).val.app
        (op ((integralComparisonSequenceBaseChange f).obj V.unop))
        (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)).unit.app
          (((coefficientTotalTensor.{u, t + 1, t}
            (coefficientSequenceTopology (ProEt.topology Y))
            (coefficientSequenceCommRingSheaf l E Y)).obj (P,Q)).X k)).val.app V
          (coefficientTensorGenerator.{u, t + 1, t}
            (coefficientSequenceTopology (ProEt.topology Y))
            (coefficientSequenceCommRingSheaf l E Y) P Q p q k h V x y)) =
      coefficientTensorGenerator.{u, t + 1, t}
        (coefficientSequenceTopology (ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X)
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj P)
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj Q)
        p q k h (op ((integralComparisonSequenceBaseChange f).obj V.unop))
        (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)).unit.app
          (P.X p)).val.app V x)
        (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)).unit.app
          (Q.X q)).val.app V y) :=
  (seqTensor_existsUnique l E f).exists.choose_spec P Q p q k h V.unop x y

/-- Paste a cochain square through an adjunction unit.
Source: naturality of the adjunction unit
(blueprint: stage3-pur-strict-pullback-comparisons). -/
private theorem adjunction_comparison_paste {B D : Type*} [Category B] [Category D]
    {L : B ⥤ D} {R : D ⥤ B} (adj : L ⊣ R)
    {P Q : B} {T V T' V' : D} (a : P ⟶ Q)
    (b : L.obj Q ⟶ T) (c : T ⟶ V)
    (b' : L.obj P ⟶ T') (c' : T' ⟶ V') (d : V' ⟶ V)
    (h : a ≫ adj.unit.app Q ≫ R.map b ≫ R.map c =
      adj.unit.app P ≫ R.map b' ≫ R.map c' ≫ R.map d) :
    L.map a ≫ b ≫ c = b' ≫ c' ≫ d := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp]
  have hu := adj.unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← hu]
  simpa only [Category.assoc] using h

/-- Pasting six pure-section equations requires only function congruence.
Source: the pure-tensor calculation of Stacks 07A4
(blueprint: stage3-pur-strict-pullback-comparisons). -/
private theorem associativitySectionSquare
    {A B C D E F G H : Type*}
    (σ : A → B) (ηB : B → C) (κB : C → D) (tB : D → H)
    (ηA : A → E) (κA : E → F) (tA : F → G) (τ : G → H)
    (x : A) (b : B) (d : D) (h : H) (f : F) (g : G)
    (hσ : σ x = b) (hκB : κB (ηB b) = d) (htB : tB d = h)
    (hκA : κA (ηA x) = f) (htA : tA f = g) (hτ : τ g = h) :
    tB (κB (ηB (σ x))) = τ (tA (κA (ηA x))) := by
  rw [hσ, hκB, htB, hκA, htA, hτ]

attribute [local irreducible] seqTensor
  SheafOfModules.monoidalCategory HomologicalComplex₂.total
  CategoryTheory.Functor.mapBifunctorHomologicalComplex
attribute [local implicit_reducible] integralComparisonSequenceDirectImage
  Functor.mapHomologicalComplex

set_option maxHeartbeats 800000 in
-- Elaborating the nested total-complex comparison uses extra heartbeats.
/-- The normalized sequence pullback commutes with cochain reassociation, for any
two associators given by the unsigned rebracketing of pure triples.
Source: Stacks 07A4, Tag 06YN (blueprint: stage3-pur-strict-pullback-comparisons).
Proof: transpose by the inverse-image adjunction, detect equality on local pure
triples of each triple total summand, and apply the generator formula twice on
each side together with its naturality on tensor generators. -/
theorem seqTensor_associativity {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P Q N : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    let JY := coefficientSequenceTopology (ProEt.topology Y)
    let JX := coefficientSequenceTopology (ProEt.topology X)
    let RY := coefficientSequenceCommRingSheaf l E Y
    let RX := coefficientSequenceCommRingSheaf l E X
    let V := (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)
    let TY := coefficientTotalTensor.{u, t + 1, t} JY RY
    let T := coefficientTotalTensor.{u, t + 1, t} JX RX
    let κ := seqTensor l E f
    ∀ (aY : TY.obj (TY.obj (P, Q), N) ≅ TY.obj (P, TY.obj (Q, N)))
      (aX : T.obj (T.obj (V.obj P, V.obj Q), V.obj N) ≅
        T.obj (V.obj P, T.obj (V.obj Q, V.obj N))),
    (∀ (p q r pq qr k : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
      (hn : pq + r = k) (hn' : p + qr = k) (U : (ℕ × Y.ProEt)ᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) (z : (N.X r).val.obj U),
      (aY.hom.f k).val.app U
        (coefficientTensorGenerator.{u, t + 1, t} JY RY (TY.obj (P, Q)) N pq r k hn U
          (coefficientTensorGenerator.{u, t + 1, t} JY RY P Q p q pq hpq U x y) z) =
      coefficientTensorGenerator.{u, t + 1, t} JY RY P (TY.obj (Q, N)) p qr k hn' U x
        (coefficientTensorGenerator.{u, t + 1, t} JY RY Q N q r qr hqr U y z)) →
    (∀ (p q r pq qr k : ℤ) (hpq : p + q = pq) (hqr : q + r = qr)
      (hn : pq + r = k) (hn' : p + qr = k) (U : (ℕ × X.ProEt)ᵒᵖ)
      (x : ((V.obj P).X p).val.obj U) (y : ((V.obj Q).X q).val.obj U)
      (z : ((V.obj N).X r).val.obj U),
      (aX.hom.f k).val.app U
        (coefficientTensorGenerator.{u, t + 1, t} JX RX
          (T.obj (V.obj P, V.obj Q)) (V.obj N) pq r k hn U
          (coefficientTensorGenerator.{u, t + 1, t} JX RX
            (V.obj P) (V.obj Q) p q pq hpq U x y) z) =
      coefficientTensorGenerator.{u, t + 1, t} JX RX
        (V.obj P) (T.obj (V.obj Q, V.obj N)) p qr k hn' U x
        (coefficientTensorGenerator.{u, t + 1, t} JX RX
          (V.obj Q) (V.obj N) q r qr hqr U y z)) →
    V.map aY.hom ≫ κ.hom.app (P, TY.obj (Q, N)) ≫
        T.map (Prod.mkHom (𝟙 (V.obj P)) (κ.hom.app (Q, N))) =
      κ.hom.app (TY.obj (P, Q), N) ≫
        T.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (V.obj N))) ≫ aX.hom := by
  let RY := coefficientSequenceCommRingSheaf l E Y
  let RX := coefficientSequenceCommRingSheaf l E X
  let JY := coefficientSequenceTopology (ProEt.topology Y)
  let JX := coefficientSequenceTopology (ProEt.topology X)
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{t + 1, t, max u (t + 1)} RY
  let := SheafOfModules.monoidalCategory RY
  let := SheafOfModules.isMonoidal_W_independentCoefficients.{t + 1, t, max u (t + 1)} RX
  let := SheafOfModules.monoidalCategory RX
  let L := integralComparisonSequencePullback l E f
  let adj : integralComparisonSequencePullback l E f ⊣ integralComparisonSequenceDirectImage l E f :=
    Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)
  let V := L.mapHomologicalComplex (.up ℤ)
  let κ := seqTensor l E f
  let TY := coefficientTotalTensor.{u, t + 1, t} JY RY
  let T := coefficientTotalTensor.{u, t + 1, t} JX RX
  dsimp only
  intro aY aX haY haX
  let : (integralComparisonSequenceDirectImage l E f).Additive :=
    { map_add := by intros; rfl }
  apply adjunction_comparison_paste (adj.mapHomologicalComplex (.up ℤ))
  apply CategoryTheory.tensorGenerator_ext₃.{t + 1, t, u} JY RY P Q N
  intro p q r pq k hpq hn U x y z
  have hqr : q + r = q + r := rfl
  have hn' : p + (q + r) = k := by omega
  change ((T.map (Prod.mkHom (𝟙 (V.obj P)) (κ.hom.app (Q, N)))).f k).val.app
      (op ((integralComparisonSequenceBaseChange f).obj U.unop))
      (((κ.hom.app (P, TY.obj (Q, N))).f k).val.app
        (op ((integralComparisonSequenceBaseChange f).obj U.unop))
        ((adj.unit.app _).val.app U
          ((aY.hom.f k).val.app U
            (coefficientTensorGenerator.{u, t + 1, t} JY RY (TY.obj (P, Q)) N pq r k hn U
              (coefficientTensorGenerator.{u, t + 1, t} JY RY P Q p q pq hpq U x y) z)))) =
    (aX.hom.f k).val.app
      (op ((integralComparisonSequenceBaseChange f).obj U.unop))
      (((T.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (V.obj N)))).f k).val.app
        (op ((integralComparisonSequenceBaseChange f).obj U.unop))
        (((κ.hom.app (TY.obj (P, Q), N)).f k).val.app
          (op ((integralComparisonSequenceBaseChange f).obj U.unop))
          ((adj.unit.app _).val.app U
            (coefficientTensorGenerator.{u, t + 1, t} JY RY (TY.obj (P, Q)) N pq r k hn U
              (coefficientTensorGenerator.{u, t + 1, t} JY RY P Q p q pq hpq U x y) z))))
  let U' := op ((integralComparisonSequenceBaseChange f).obj U.unop)
  let xp := (adj.unit.app (P.X p)).val.app U x
  let yq := (adj.unit.app (Q.X q)).val.app U y
  let zr := (adj.unit.app (N.X r)).val.app U z
  let gPQ := coefficientTensorGenerator.{u, t + 1, t} JY RY P Q p q pq hpq U x y
  let gQN := coefficientTensorGenerator.{u, t + 1, t} JY RY Q N q r (q + r) hqr U y z
  let gY' := coefficientTensorGenerator.{u, t + 1, t} JY RY P (TY.obj (Q, N))
    p (q + r) k hn' U x gQN
  let gR := coefficientTensorGenerator.{u, t + 1, t} JX RX (V.obj P) (V.obj (TY.obj (Q, N)))
    p (q + r) k hn' U' xp ((adj.unit.app ((TY.obj (Q, N)).X (q + r))).val.app U gQN)
  let gL := coefficientTensorGenerator.{u, t + 1, t} JX RX (V.obj (TY.obj (P, Q))) (V.obj N)
    pq r k hn U' ((adj.unit.app ((TY.obj (P, Q)).X pq)).val.app U gPQ) zr
  let gPQ' := coefficientTensorGenerator.{u, t + 1, t} JX RX
    (V.obj P) (V.obj Q) p q pq hpq U' xp yq
  let gQN' := coefficientTensorGenerator.{u, t + 1, t} JX RX
    (V.obj Q) (V.obj N) q r (q + r) hqr U' yq zr
  let gL' := coefficientTensorGenerator.{u, t + 1, t} JX RX
    (T.obj (V.obj P, V.obj Q)) (V.obj N) pq r k hn U' gPQ' zr
  let gR' := coefficientTensorGenerator.{u, t + 1, t} JX RX
    (V.obj P) (T.obj (V.obj Q, V.obj N)) p (q + r) k hn' U' xp gQN'
  have hκ' : ∀ A B p q k h U x y,
      ((κ.hom.app (A, B)).f k).val.app
          (op ((integralComparisonSequenceBaseChange f).obj (unop U)))
        ((adj.unit.app _).val.app U
          (coefficientTensorGenerator.{u, t + 1, t} JY RY A B p q k h U x y)) =
      coefficientTensorGenerator.{u, t + 1, t} JX RX (V.obj A) (V.obj B) p q k h
        (op ((integralComparisonSequenceBaseChange f).obj (unop U)))
        ((adj.unit.app (A.X p)).val.app U x)
        ((adj.unit.app (B.X q)).val.app U y) := by
    intro A B p q k h U x y
    exact seqTensor_generator l E f A B p q k h U x y
  refine associativitySectionSquare
    ((aY.hom.f k).val.app U)
    ((adj.unit.app ((TY.obj (P, TY.obj (Q, N))).X k)).val.app U)
    (((κ.hom.app (P, TY.obj (Q, N))).f k).val.app U')
    (((T.map (Prod.mkHom (𝟙 (V.obj P)) (κ.hom.app (Q, N)))).f k).val.app U')
    ((adj.unit.app ((TY.obj (TY.obj (P, Q), N)).X k)).val.app U)
    (((κ.hom.app (TY.obj (P, Q), N)).f k).val.app U')
    (((T.map (Prod.mkHom (κ.hom.app (P, Q)) (𝟙 (V.obj N)))).f k).val.app U')
    ((aX.hom.f k).val.app U')
    _ gY' gR gR' gL gL' ?_ ?_ ?_ ?_ ?_ ?_
  · exact haY p q r pq (q + r) k hpq hqr hn hn' U x y z
  · exact hκ' P (TY.obj (Q, N)) p (q + r) k hn' U x gQN
  · have hm := CategoryTheory.ScalarHomTensor.tensor_generator_map.{t + 1, t, u}
      (𝟙 (V.obj P)) (κ.hom.app (Q, N)) p (q + r) k hn' U' xp
      ((adj.unit.app ((TY.obj (Q, N)).X (q + r))).val.app U gQN)
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app] at hm
    exact hm.trans (congrArg (fun w ↦ coefficientTensorGenerator.{u, t + 1, t}
      JX RX (V.obj P) (T.obj (V.obj Q, V.obj N)) p (q + r) k hn' U' xp w)
      (hκ' Q N q r (q + r) hqr U y z))
  · exact hκ' (TY.obj (P, Q)) N pq r k hn U gPQ z
  · have hm := CategoryTheory.ScalarHomTensor.tensor_generator_map.{t + 1, t, u}
      (κ.hom.app (P, Q)) (𝟙 (V.obj N)) pq r k hn U'
      ((adj.unit.app ((TY.obj (P, Q)).X pq)).val.app U gPQ) zr
    simp only [HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app] at hm
    exact hm.trans (congrArg (fun w ↦ coefficientTensorGenerator.{u, t + 1, t}
      JX RX (T.obj (V.obj P, V.obj Q)) (V.obj N) pq r k hn U' w zr)
      (hκ' P Q p q pq hpq U x y))
  · exact haX p q r pq (q + r) k hpq hqr hn hn' U' xp yq zr

private theorem signedSectionSquare
    {A B C D E F : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup D] [AddCommGroup E] [AddCommGroup F]
    (σ : A →+ B) (η : B →+ D) (κ' : D →+ F)
    (η' : A →+ C) (κ : C →+ E) (τ : E →+ F)
    (x : A) (x' : B) (y : E) (y' : F) (ε : ℤˣ)
    (hσ : σ x = ε • x') (hκ' : κ' (η x') = y')
    (hκ : κ (η' x) = y) (hτ : τ y = ε • y') :
    κ' (η (σ x)) = τ (κ (η' x)) := by
  rw [hσ]
  simp only [Units.smul_def, map_zsmul]
  rw [hκ', hκ, hτ]
  rfl

set_option maxHeartbeats 800000 in
-- The section calculation elaborates the tensor sheafification and adjunction models.
/-- The normalized sequence pullback commutes with any two signed symmetries of the
total tensor given by the Koszul sign on pure tensors.
Source: Stacks 07A4, 0FNG (blueprint: stage3-pur-strict-pullback-comparisons).
Proof: transpose by the inverse-image adjunction and compare on pure tensors of
each total summand: both sides give the sign times the tensor of the unit sections. -/
theorem seqTensor_braiding {X Y : Scheme.{t}} (f : X ⟶ Y)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    let JY := coefficientSequenceTopology (ProEt.topology Y)
    let JX := coefficientSequenceTopology (ProEt.topology X)
    let RY := coefficientSequenceCommRingSheaf l E Y
    let RX := coefficientSequenceCommRingSheaf l E X
    let V := (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)
    let TY := coefficientTotalTensor.{u, t + 1, t} JY RY
    let T := coefficientTotalTensor.{u, t + 1, t} JX RX
    ∀ (σY : TY.obj (P, Q) ≅ TY.obj (Q, P)) (σX : T.obj (V.obj P, V.obj Q) ≅ T.obj (V.obj Q, V.obj P)),
    (∀ (p q k : ℤ) (h : p + q = k) (U : (ℕ × Y.ProEt)ᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      (σY.hom.f k).val.app U (coefficientTensorGenerator.{u, t + 1, t} JY RY P Q p q k h U x y) =
        (p*q).negOnePow • coefficientTensorGenerator.{u, t + 1, t}
          JY RY Q P q p k ((add_comm q p).trans h) U y x) →
    (∀ (p q k : ℤ) (h : p + q = k) (U : (ℕ × X.ProEt)ᵒᵖ)
      (x : ((V.obj P).X p).val.obj U) (y : ((V.obj Q).X q).val.obj U),
      (σX.hom.f k).val.app U
        (coefficientTensorGenerator.{u, t + 1, t} JX RX (V.obj P) (V.obj Q) p q k h U x y) =
        (p*q).negOnePow • coefficientTensorGenerator.{u, t + 1, t}
          JX RX (V.obj Q) (V.obj P) q p k ((add_comm q p).trans h) U y x) →
    V.map σY.hom ≫ (seqTensor l E f).hom.app (Q,P) =
      (seqTensor l E f).hom.app (P,Q) ≫ σX.hom := by
  dsimp only
  intro σY σX hσY hσX
  let L := integralComparisonSequencePullback l E f
  let adj : integralComparisonSequencePullback l E f ⊣ integralComparisonSequenceDirectImage l E f :=
    Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)
  let κ := seqTensor l E f
  apply HomologicalComplex.hom_ext
  intro k
  change L.map (σY.hom.f k) ≫ (κ.hom.app (Q,P)).f k =
    (κ.hom.app (P,Q)).f k ≫ σX.hom.f k
  apply (adj.homEquiv _ _).injective
  change adj.unit.app _ ≫ (integralComparisonSequenceDirectImage l E f).map
      (L.map (σY.hom.f k) ≫ (κ.hom.app (Q,P)).f k) =
    adj.unit.app _ ≫ (integralComparisonSequenceDirectImage l E f).map
      ((κ.hom.app (P,Q)).f k ≫ σX.hom.f k)
  simp only [Functor.map_comp]
  have hu := adj.unit.naturality (σY.hom.f k)
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← hu]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (P.X p) (Q.X q)).inv).1
  apply (PresheafOfModules.sheafificationAdjunction.{max u (t + 1)} (𝟙 _)).homEquiv _ _ |>.injective
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change ((κ.hom.app (Q,P)).f k).val.app
      (op ((integralComparisonSequenceBaseChange f).obj U.unop))
      ((adj.unit.app _).val.app U
        ((σY.hom.f k).val.app U
          (coefficientTensorGenerator.{u, t + 1, t}
            (coefficientSequenceTopology (ProEt.topology Y))
            (coefficientSequenceCommRingSheaf l E Y) P Q p q k hpq U x y))) =
    (σX.hom.f k).val.app (op ((integralComparisonSequenceBaseChange f).obj U.unop))
      (((κ.hom.app (P,Q)).f k).val.app
        (op ((integralComparisonSequenceBaseChange f).obj U.unop))
        ((adj.unit.app _).val.app U
          (coefficientTensorGenerator.{u, t + 1, t}
            (coefficientSequenceTopology (ProEt.topology Y))
            (coefficientSequenceCommRingSheaf l E Y) P Q p q k hpq U x y)))
  let P' := (L.mapHomologicalComplex (.up ℤ)).obj P
  let Q' := (L.mapHomologicalComplex (.up ℤ)).obj Q
  let U' := op ((integralComparisonSequenceBaseChange f).obj U.unop)
  let xp := ((adj.unit.app (P.X p)).val.app U) x
  let yq := ((adj.unit.app (Q.X q)).val.app U) y
  let gY := coefficientTensorGenerator.{u, t + 1, t}
    (coefficientSequenceTopology (ProEt.topology Y))
    (coefficientSequenceCommRingSheaf l E Y) Q P q p k ((add_comm q p).trans hpq) U y x
  let gX := coefficientTensorGenerator.{u, t + 1, t}
    (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X) P' Q' p q k hpq U' xp yq
  let gX' := coefficientTensorGenerator.{u, t + 1, t}
    (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X) Q' P' q p k
    ((add_comm q p).trans hpq) U' yq xp
  refine signedSectionSquare
    ((σY.hom.f k).val.app U).hom.toAddMonoidHom
    ((adj.unit.app (((coefficientTotalTensor.{u, t + 1, t}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y)).obj (Q,P)).X k)).val.app U).hom.toAddMonoidHom
    (((κ.hom.app (Q,P)).f k).val.app U').hom.toAddMonoidHom
    ((adj.unit.app (((coefficientTotalTensor.{u, t + 1, t}
      (coefficientSequenceTopology (ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y)).obj (P,Q)).X k)).val.app U).hom.toAddMonoidHom
    (((κ.hom.app (P,Q)).f k).val.app U').hom.toAddMonoidHom
    ((σX.hom.f k).val.app U').hom.toAddMonoidHom
    _ gY gX gX' (p*q).negOnePow ?_ ?_ ?_ ?_
  · exact hσY p q k hpq U x y
  · exact seqTensor_generator l E f Q P q p k ((add_comm q p).trans hpq) U y x
  · exact seqTensor_generator l E f P Q p q k hpq U x y
  · exact hσX p q k hpq _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The prescribed compositor sends the composite adjunction unit to the pasted
restriction of the two successive units.
Source: Stacks 0D6D (blueprint: stage3-pur-strict-pullback-comparisons).
Proof: the compositor is the conjugate of the sectionwise fibre-product pasting map;
the unit equation of conjugate transformations evaluated on sections gives the claim. -/
theorem sequenceComposition_unit {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (M : coefficientSequenceModules l E Y) (n : ℕ) (U : Y.ProEt) (x : M.val.obj (op (n, U))) :
    ((integralComparisonSequenceComposition l E h f).hom.app M).val.app
        (op (n, (proEtaleBaseChange (h ≫ f)).obj U))
        (((Adjunction.ofIsRightAdjoint
          (integralComparisonSequenceDirectImage l E (h ≫ f))).unit.app M).val.app
          (op (n, U)) x) =
      ((integralComparisonSequencePullback l E h).obj
          ((integralComparisonSequencePullback l E f).obj M)).val.map
        (CategoryTheory.Prod.mkHom (𝟙 n)
          ((MorphismProperty.Over.pullbackComp h f).hom.app U)).op
        (((Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)).unit.app
            ((integralComparisonSequencePullback l E f).obj M)).val.app
          (op (n, (proEtaleBaseChange f).obj U))
          (((Adjunction.ofIsRightAdjoint
            (integralComparisonSequenceDirectImage l E f)).unit.app M).val.app
            (op (n, U)) x)) := by
  obtain ⟨d, hd, hsec⟩ :=
    (integralComparisonSequenceComposition_existsUnique l E h f).exists.choose_spec
  let adj₁ := (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)).comp
    (Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h))
  let adj₂ := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ f))
  have hc := unit_conjugateEquiv adj₁ adj₂
    (integralComparisonSequenceComposition l E h f).hom M
  have hd' : conjugateEquiv adj₁ adj₂ (integralComparisonSequenceComposition l E h f).hom =
      d.hom := congrArg Iso.hom hd
  rw [hd'] at hc
  have he := congrArg (fun g ↦ g.val.app (op (n, U)) x) hc
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply] at he
  refine he.symm.trans ?_
  exact hsec _ n U _

private theorem sectionMap_naturality {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{max u (t + 1)}} {M N : SheafOfModules.{max u (t + 1)} R}
    (φ : M ⟶ N) {A B : Cᵒᵖ} (g : A ⟶ B) (w : M.val.obj A) :
    φ.val.app B (M.val.map g w) = N.val.map g (φ.val.app A w) :=
  PresheafOfModules.naturality_apply φ.val g w

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in
-- The pure-section calculation elaborates three pullbacks and their tensor models.
/-- The normalized tensor comparisons are compatible with the prescribed compositor.
Source: Stacks 07A4, 0D6D (blueprint: stage3-pur-strict-pullback-comparisons).
Proof: transpose by the composite adjunction and compare on pure total tensors.
Both sides give the pasted restriction of the tensor of the successive unit sections:
use the compositor unit formula, the generator formulas of the three comparisons,
naturality of units and of restrictions, and restriction of tensor generators. -/
theorem seqTensor_composition {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    let TY := coefficientTotalTensor.{u, t + 1, t}
      (coefficientSequenceTopology (ProEt.topology Y)) (coefficientSequenceCommRingSheaf l E Y)
    let TZ := coefficientTotalTensor.{u, t + 1, t}
      (coefficientSequenceTopology (ProEt.topology Z)) (coefficientSequenceCommRingSheaf l E Z)
    let Vf := (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)
    let Vh := (integralComparisonSequencePullback l E h).mapHomologicalComplex (.up ℤ)
    let comp := (Functor.mapHomologicalComplexCompIso
      (integralComparisonSequenceComposition l E h f).symm (.up ℤ)).symm
    (seqTensor l E (h ≫ f)).hom.app (P,Q) ≫
        TZ.map (Prod.mkHom (comp.hom.app P) (comp.hom.app Q)) =
      comp.hom.app (TY.obj (P,Q)) ≫ Vh.map ((seqTensor l E f).hom.app (P,Q)) ≫
        (seqTensor l E h).hom.app (Vf.obj P, Vf.obj Q) := by
  dsimp only
  let JY := coefficientSequenceTopology (ProEt.topology Y)
  let JX := coefficientSequenceTopology (ProEt.topology X)
  let JZ := coefficientSequenceTopology (ProEt.topology Z)
  let RY := coefficientSequenceCommRingSheaf l E Y
  let RX := coefficientSequenceCommRingSheaf l E X
  let RZ := coefficientSequenceCommRingSheaf l E Z
  let Lf := integralComparisonSequencePullback l E f
  let Lh := integralComparisonSequencePullback l E h
  let a := integralComparisonSequenceComposition l E h f
  let adjf : Lf ⊣ integralComparisonSequenceDirectImage l E f :=
    Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E f)
  let adjh : Lh ⊣ integralComparisonSequenceDirectImage l E h :=
    Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)
  let adj : integralComparisonSequencePullback l E (h ≫ f) ⊣
      integralComparisonSequenceDirectImage l E (h ≫ f) :=
    Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ f))
  let Vf := Lf.mapHomologicalComplex (.up ℤ)
  let κf := seqTensor l E f
  let κh := seqTensor l E h
  let κ := seqTensor l E (h ≫ f)
  apply HomologicalComplex.hom_ext
  intro k
  simp only [HomologicalComplex.comp_f]
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{t + 1, t, u} (J := JY) (R := RY) P Q k
  intro p q hpq V x y
  obtain ⟨⟨n, U⟩⟩ := V
  let g := coefficientTensorGenerator.{u, t + 1, t} JY RY P Q p q k hpq (op (n, U)) x y
  let W : (ℕ × Z.ProEt)ᵒᵖ := op ((integralComparisonSequenceBaseChange (h ≫ f)).obj (n, U))
  let Wf : (ℕ × X.ProEt)ᵒᵖ := op ((integralComparisonSequenceBaseChange f).obj (n, U))
  let Wh : (ℕ × Z.ProEt)ᵒᵖ := op ((integralComparisonSequenceBaseChange h).obj
    ((integralComparisonSequenceBaseChange f).obj (n, U)))
  let ρ : Wh ⟶ W := (CategoryTheory.Prod.mkHom (𝟙 n)
    ((MorphismProperty.Over.pullbackComp h f).hom.app U)).op
  let comp := (Functor.mapHomologicalComplexCompIso a.symm (.up ℤ)).symm
  change (((coefficientTotalTensor.{u, t + 1, t} JZ RZ).map
      (Prod.mkHom (comp.hom.app P) (comp.hom.app Q))).f k).val.app W
      (((κ.hom.app (P,Q)).f k).val.app W ((adj.unit.app _).val.app (op (n, U)) g)) =
    ((κh.hom.app (Vf.obj P, Vf.obj Q)).f k).val.app W
      ((((Lh.mapHomologicalComplex (.up ℤ)).map (κf.hom.app (P,Q))).f k).val.app W
        (((comp.hom.app ((coefficientTotalTensor.{u, t + 1, t} JY RY).obj (P,Q))).f k).val.app W
          ((adj.unit.app _).val.app (op (n, U)) g)))
  sorry

end WeilConjectures.IntegralCoherence
