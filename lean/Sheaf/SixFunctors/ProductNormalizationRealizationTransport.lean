/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.SixFunctors.ProductCompactificationIdentity
public import Sheaf.Paper.NormalizedTensorConstraintTransport
public import Sheaf.Paper.CompletedPrimitiveCounitComparison
public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge
public import Sheaf.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenArrows
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Sheaf.Paper.ProperOpenTowerComparison
public import Sheaf.Paper.BasicOperationsCoefficientReduction
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.ExchangeFunctoriality
import Sheaf.CategoryTheory.ExpressionContextualIntertwining
import Sheaf.SixFunctors.OpenTensorNormalization
public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus

/-! # Product normalization through completed realization

Source: Stacks sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok, and the
proper-reduction sentence of the current blueprint, lem-sf-kunneth-coherence.proof.md
(blueprint: lem-sf-product-normalization-realization-transport).

## Main definitions

* `Word`: ordered specified generator pairs and their expression contexts.
* `ProductDiagram`: the two product squares of the compactification calculation.
* `transport`: conjugation by the specified completed realization comparisons.

## Main statements

* `productNormalizationRealizationTransport`: the product normalization transport laws.

Finite words retain the existing expression syntax and the actual specified arrows.
The coefficient-square constructor includes tensor constraints in that same calculus;
it is a whole-system square, never a collection of evaluated equations.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w v₂ w₂
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization.ProductNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {D : FiniteFieldDatum.{u}} {o : Operations l E} (r : Realizations l E D o)
  {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}

/-- The specified component c_V, on its full normalized bounded etale-origin domain.
Source: Stacks 0941 (blueprint: lem-sf-product-normalization-realization-transport). -/
def comparison {W : Over (Spec (CommRingCat.of D.k))}
    (e : Expression _ I X W) (g : e.geometric)
    (K : ∀ i, Integral l E (X i).left) (h : e.domain l E o K) :
    (coefficientSequenceLimit l E W.left).obj
        (e.systemObj l E o ((inputReduction l E X).obj K)) ≅
      (e.evaluate (integralInterpretation l E)).obj K :=
  (r.comparison e g).app ⟨K, h⟩

/-- The arrow c_V L(m) c_S inverse, in Lean's left-to-right composition convention.
Source: Stacks 0941, transport formula
(blueprint: lem-sf-product-normalization-realization-transport). -/
def transport {W : Over (Spec (CommRingCat.of D.k))}
    (e t : Expression _ I X W) (ge : e.geometric) (gt : t.geometric)
    (K : ∀ i, Integral l E (X i).left)
    (he : e.domain l E o K) (ht : t.domain l E o K)
    (m : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K)) :
    (e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K :=
  (comparison l E r e ge K he).inv ≫
    (coefficientSequenceLimit l E W.left).map m ≫ (comparison l E r t gt K ht).hom

/-- Finite ordered canonical words, including inverses. `coefficient` records the
whole-system coefficient square of the actual quotient-model constraints; it does not
assert that finite evaluations detect arrows. The canonical constructor reuses the
published generator list, its outer contexts, and the independently specified integral
arrows. Both endpoint comparisons are always the prescribed expression comparisons.
Source: node proof steps 1--2, Stacks 0941
(blueprint: lem-sf-product-normalization-realization-transport). -/
inductive Word
    (K : ∀ i, Integral l E (X i).left) :
    {W : Over (Spec (CommRingCat.of D.k))} → (e t : Expression _ I X W) →
    (e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K)) →
    ((e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K) → Prop where
  | canonical {W : Over (Spec (CommRingCat.of D.k))} {e t : Expression _ I X W}
      {m : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.systemObj l E o ((inputReduction l E X).obj K)}
      {q : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      (p : CanonicalPair l E o r.compositors r.openComparisons r.canonicalBridge r.properOpen
        r.ringedModels r.ringedOpenComparisons r.ringedProperOpen
        ((inputReduction l E X).obj K) K e t m q) : Word K e t m q
  | coefficient {W : Over (Spec (CommRingCat.of D.k))} {e t : Expression _ I X W}
      (ge : e.geometric) (gt : t.geometric) (he : e.domain l E o K)
      (ht : t.domain l E o K)
      (m : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.systemObj l E o ((inputReduction l E X).obj K))
      (q : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K)
      (square : (r.reduction e ge).inv.app ⟨K, he⟩ ≫ m =
        (calculus l E W.left).reduction.map q ≫ (r.reduction t gt).inv.app ⟨K, ht⟩) :
      Word K e t m q
  | comp {W : Over (Spec (CommRingCat.of D.k))} {e t z : Expression _ I X W}
      (gt : t.geometric) (ht : t.domain l E o K)
      {a : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.systemObj l E o ((inputReduction l E X).obj K)}
      {b : t.systemObj l E o ((inputReduction l E X).obj K) ⟶
        z.systemObj l E o ((inputReduction l E X).obj K)}
      {qa : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {qb : (t.evaluate (integralInterpretation l E)).obj K ⟶
        (z.evaluate (integralInterpretation l E)).obj K} :
      Word K e t a qa → Word K t z b qb → Word K e z (a ≫ b) (qa ≫ qb)
  | inverse {W : Over (Spec (CommRingCat.of D.k))} {e t : Expression _ I X W}
      (a : e.systemObj l E o ((inputReduction l E X).obj K) ≅
        t.systemObj l E o ((inputReduction l E X).obj K))
      (b : (e.evaluate (integralInterpretation l E)).obj K ≅
        (t.evaluate (integralInterpretation l E)).obj K) :
      Word K e t a.hom b.hom → Word K t e a.inv b.inv
  | push {U V : Over (Spec (CommRingCat.of D.k))} (f : U ⟶ V)
      (hf : IsProper f.left) {e t : Expression _ I X U}
      {a : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.systemObj l E o ((inputReduction l E X).obj K)}
      {b : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K} :
      Word K e t a b → Word K (.push f hf e) (.push f hf t)
        ((Operations.push l E o f.left).map a) ((ringedPush l E f.left).map b)
  | pull {U V : Over (Spec (CommRingCat.of D.k))} (f : U ⟶ V)
      {e t : Expression _ I X V}
      {a : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.systemObj l E o ((inputReduction l E X).obj K)}
      {b : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K} :
      Word K e t a b → Word K (.pull f e) (.pull f t)
        ((pull l E f.left).map a) ((integralDerivedPullback l E f.left).map b)
  | shriek {U V : Over (Spec (CommRingCat.of D.k))} (j : U ⟶ V)
      [hj : IsOpenImmersion j.left] (hq : QuasiCompact j.left)
      {e t : Expression _ I X U}
      {a : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.systemObj l E o ((inputReduction l E X).obj K)}
      {b : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K} :
      Word K e t a b → Word K (.shriek j hj hq e) (.shriek j hj hq t)
        ((Operations.shriek l E o j.left).map a) ((ringedOpen l E j.left).map b)
  | tensor {W : Over (Spec (CommRingCat.of D.k))} {e t z v : Expression _ I X W}
      {a : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
        t.systemObj l E o ((inputReduction l E X).obj K)}
      {b : z.systemObj l E o ((inputReduction l E X).obj K) ⟶
        v.systemObj l E o ((inputReduction l E X).obj K)}
      {qa : (e.evaluate (integralInterpretation l E)).obj K ⟶
        (t.evaluate (integralInterpretation l E)).obj K}
      {qb : (z.evaluate (integralInterpretation l E)).obj K ⟶
        (v.evaluate (integralInterpretation l E)).obj K} :
      Word K e t a qa → Word K z v b qb → Word K (.tensor e z) (.tensor t v)
        ((calculus l E W.left).systemClosed.tensor.map (Prod.mkHom a b))
        ((integralCompletedTensor l E W.left).map (Prod.mkHom qa qb))
  | symmetry {W : Over (Spec (CommRingCat.of D.k))} (e t : Expression _ I X W)
      (σ : @SymmetricCategory (System l E W.left) _
        (calculus l E W.left).systemClosed.monoidal)
      (_C : RingedDerivedTensorCoherence
        (coefficientSequenceTopology (ProEt.topology W.left))
        (coefficientSequenceCommRingSheaf l E W.left)
        (calculus l E W.left).systemClosed (calculus l E W.left).systemTensorModel σ)
      (v : integralCompletedTensor l E W.left ≅
        (calculus l E W.left).reduction.prod (calculus l E W.left).reduction ⋙
          (calculus l E W.left).systemClosed.tensor ⋙ coefficientSequenceLimit l E W.left)
      (ρ : PrimitiveCounit.RoosRealization l E W.left)
      (_hv : PrimitiveCounit.TensorModel l E W.left 
        (calculus l E W.left).toCoefficientDerivedSystemReduction ρ v) :
      Word K (.tensor e t) (.tensor t e)
        (σ.braiding (e.systemObj l E o ((inputReduction l E X).obj K))
          (t.systemObj l E o ((inputReduction l E X).obj K))).hom
        (v.hom.app ((e.evaluate (integralInterpretation l E)).obj K,
            (t.evaluate (integralInterpretation l E)).obj K) ≫
          (coefficientSequenceLimit l E W.left).map
            (σ.braiding
              ((calculus l E W.left).reduction.obj
                ((e.evaluate (integralInterpretation l E)).obj K))
              ((calculus l E W.left).reduction.obj
                ((t.evaluate (integralInterpretation l E)).obj K))).hom ≫
          v.inv.app ((t.evaluate (integralInterpretation l E)).obj K,
            (e.evaluate (integralInterpretation l E)).obj K))
  | associator {W : Over (Spec (CommRingCat.of D.k))}
      (e t z : Expression _ I X W)
      (v : integralCompletedTensor l E W.left ≅
        (calculus l E W.left).reduction.prod (calculus l E W.left).reduction ⋙
          (calculus l E W.left).systemClosed.tensor ⋙ coefficientSequenceLimit l E W.left)
      (ρ : PrimitiveCounit.RoosRealization l E W.left)
      (_hv : PrimitiveCounit.TensorModel l E W.left 
        (calculus l E W.left).toCoefficientDerivedSystemReduction ρ v)
      [IsIso (NormalizedTensorTransport.contraction l E W.left
        (calculus l E W.left).toCoefficientDerivedSystemReduction v
        ((t.evaluate (integralInterpretation l E)).obj K)
        ((z.evaluate (integralInterpretation l E)).obj K))] :
      Word K (.tensor (.tensor e t) z) (.tensor e (.tensor t z))
        ((calculus l E W.left).systemClosed.monoidal.associator
          (e.systemObj l E o ((inputReduction l E X).obj K))
          (t.systemObj l E o ((inputReduction l E X).obj K))
          (z.systemObj l E o ((inputReduction l E X).obj K))).hom
        (NormalizedTensorTransport.quotientAssociator l E W.left
        (calculus l E W.left).toCoefficientDerivedSystemReduction v
          ((e.evaluate (integralInterpretation l E)).obj K)
          ((t.evaluate (integralInterpretation l E)).obj K)
          ((z.evaluate (integralInterpretation l E)).obj K))

/-- The intertwining and conjugation equations for a specified word.
Source: node proof steps 1--2 (blueprint: lem-sf-product-normalization-realization-transport). -/
def Intertwines {W : Over (Spec (CommRingCat.of D.k))}
    (e t : Expression _ I X W) (ge : e.geometric) (gt : t.geometric)
    (K : ∀ i, Integral l E (X i).left)
    (he : e.domain l E o K) (ht : t.domain l E o K)
    (m : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K))
    (q : (e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K) : Prop :=
  (coefficientSequenceLimit l E W.left).map m ≫ (comparison l E r t gt K ht).hom =
    (comparison l E r e ge K he).hom ≫ q

/-- All words in the calculation intertwine, invertible words stay invertible, equal
paths give equal completed paths, and every assumed compactification identity transports.
The equal-path clause applies to the open restriction identity and to the two routes
in the signed-symmetry and triple-associativity diagrams, with their parentheses retained.
The final clause is lambda_aj,bk = Rc_*(e^c) lambda_a,b, where the third word is the
proper-image context of the open product word.
Source: node proof steps 1--6 (blueprint: lem-sf-product-normalization-realization-transport). -/
def WordLaws : Prop :=
  ∀ {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))} (e t : Expression _ I X W)
    (ge : e.geometric) (gt : t.geometric) (K : ∀ i, Integral l E (X i).left)
    (he : e.domain l E o K) (ht : t.domain l E o K)
    (m : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K))
    (q : (e.evaluate (integralInterpretation l E)).obj K ⟶
      (t.evaluate (integralInterpretation l E)).obj K),
    Word l E r K e t m q →
      Intertwines l E r e t ge gt K he ht m q ∧
      q = transport l E r e t ge gt K he ht m ∧
      (IsIso m → IsIso q) ∧
      (∀ (m' : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
          t.systemObj l E o ((inputReduction l E X).obj K))
        (q' : (e.evaluate (integralInterpretation l E)).obj K ⟶
          (t.evaluate (integralInterpretation l E)).obj K),
        Word l E r K e t m' q' → m = m' → q = q') ∧
      (∀ (z : Expression _ I X W) (_gz : z.geometric) (_hz : z.domain l E o K)
        (a : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
          z.systemObj l E o ((inputReduction l E X).obj K))
        (b : z.systemObj l E o ((inputReduction l E X).obj K) ⟶
          t.systemObj l E o ((inputReduction l E X).obj K))
        (qa : (e.evaluate (integralInterpretation l E)).obj K ⟶
          (z.evaluate (integralInterpretation l E)).obj K)
        (qb : (z.evaluate (integralInterpretation l E)).obj K ⟶
          (t.evaluate (integralInterpretation l E)).obj K),
        Word l E r K e z a qa → Word l E r K z t b qb → m = a ≫ b → q = qa ≫ qb)

/-- Naturality of transported actual system words. Morphisms of the input family use the
existing evaluation functors; the hypothesis is precisely naturality of e_bullet on the
whole system domain. Its completed map is the same `transport`, not an unrelated iso.
Source: node proof step 3 (blueprint: lem-sf-product-normalization-realization-transport). -/
def NaturalityLaws : Prop :=
  ∀ {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))} (e t : Expression _ I X W)
    (ge : e.geometric) (gt : t.geometric)
    (K L : ∀ i, Integral l E (X i).left)
    (heK : e.domain l E o K) (htK : t.domain l E o K)
    (heL : e.domain l E o L) (htL : t.domain l E o L) (f : K ⟶ L)
    (a : e.systemObj l E o ((inputReduction l E X).obj K) ⟶
      t.systemObj l E o ((inputReduction l E X).obj K))
    (b : e.systemObj l E o ((inputReduction l E X).obj L) ⟶
      t.systemObj l E o ((inputReduction l E X).obj L)),
    (e.evaluate (systemInterpretation l E o)).map ((inputReduction l E X).map f) ≫ b =
      a ≫ (t.evaluate (systemInterpretation l E o)).map ((inputReduction l E X).map f) →
    (e.evaluate (integralInterpretation l E)).map f ≫
        transport l E r e t ge gt L heL htL b =
      transport l E r e t ge gt K heK htK a ≫
        (t.evaluate (integralInterpretation l E)).map f

/-- Scalar transport of a prescribed arrow. These are the supplied comparison functors
at E and at a common finite coefficient field; arbitrary target universes allow both.
The second equation is independence of enlarging the common field, with its stipulated
endpoint composition cocycle. Identity comparisons are included by identity functors.
Source: node proof step 7, def-exchange-projection
(blueprint: lem-sf-product-normalization-realization-transport). -/
def ScalarLaws : Prop :=
  ∀ (W : Scheme.{u}) (C : Type v) [Category.{w} C] (F : Integral l E W ⥤ C)
    (A B : Integral l E W) (A' B' : C) (cA : F.obj A ≅ A') (cB : F.obj B ≅ B')
    (m n : A ⟶ B),
    (m = n →
      SuppliedExchangeProjection.exchangeProjectionCoefficientRepresentative F cA.symm cB m =
        SuppliedExchangeProjection.exchangeProjectionCoefficientRepresentative F cA.symm cB n) ∧
    ∀ (C₂ : Type v₂) [Category.{w₂} C₂] (H : C ⥤ C₂) (A'' B'' : C₂)
      (dA : H.obj A' ≅ A'') (dB : H.obj B' ≅ B'')
      (eA : (F ⋙ H).obj A ≅ A'') (eB : (F ⋙ H).obj B ≅ B'')
      (_hcA : eA.hom = H.map cA.hom ≫ dA.hom)
      (_hcB : eB.hom = H.map cB.hom ≫ dB.hom),
      SuppliedExchangeProjection.exchangeProjectionCoefficientRepresentative (F ⋙ H)
          eA.symm eB m =
        SuppliedExchangeProjection.exchangeProjectionCoefficientRepresentative H dA.symm dB
          (SuppliedExchangeProjection.exchangeProjectionCoefficientRepresentative F cA.symm cB m)

/-- The prescribed integer ring in the published constant-tower universe. This is
only the canonical universe lift of O_E, with its inherited ring operations.
Source: Stacks 0941 (blueprint: lem-sf-product-normalization-realization-transport). -/
abbrev constantIntegers := ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)

/-- The actual positive quotient of O_E, lifted on both sides of its quotient map.
Source: Stacks 0941 (blueprint: lem-sf-product-normalization-realization-transport). -/
def constantCoefficient (n : ℕ) : constantIntegers l E →+* scalarRings l E n :=
  (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))).ulift

/-- Termwise restriction along the actual O_E quotient maps. The compatibility proof
is the defining quotient-factor equation, so no new scalar map is selected.
Source: Stacks 03CZ, 0941
(blueprint: lem-sf-product-normalization-realization-transport). -/
def constantRestriction (W : Scheme.{u}) :=
  ProEtale.SemilinearProperOpen.rho (scalarRings l E) (scalarTransitions l E)
    (constantIntegers l E) (constantCoefficient l E)
    (fun _n ↦ RingHom.ext (fun _x ↦ rfl)) W

/-- The normalized direct-image comparison after restriction to O_E towers.
Source: Stacks 07A7 (blueprint: lem-sf-product-normalization-realization-transport). -/
def constantPush {U V : Scheme.{u}} (f : U ⟶ V) :=
  ProEtale.SemilinearProperOpen.rhoR (scalarRings l E) (scalarTransitions l E)
    (constantIntegers l E) (constantCoefficient l E)
    (fun _n ↦ RingHom.ext (fun _x ↦ rfl)) f

/-- The open-unit-normalized comparison after restriction to O_E towers.
Source: Stacks 03DI (blueprint: lem-sf-product-normalization-realization-transport). -/
def constantOpen {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :=
  ProEtale.SemilinearProperOpen.rhoJ (scalarRings l E) (scalarTransitions l E)
    (constantIntegers l E) (constantCoefficient l E)
    (fun _n ↦ RingHom.ext (fun _x ↦ rfl)) j

/-- The actual proper/open letter in the calculation, compared to the constant-O_E
strict-tower Gamma_Q, and then to its completed realization. Finite evaluation is
on the supplied etale-origin witness at the actual quotient coefficient ring.
Every occurrence is on the same expression domain as the word theorem.
Source: node proof step 5; properOpenTowerComparison and gamma_scalarRestriction
(blueprint: lem-sf-product-normalization-realization-transport). -/
def ProperOpenLaws : Prop :=
  ∀ {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {U V W Z : Over (Spec (CommRingCat.of D.k))}
    (k : U ⟶ V) (s : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [hk : IsOpenImmersion k.left] [hi : IsOpenImmersion i.left]
    [qk : QuasiCompact k.left] [qi : QuasiCompact i.left]
    [hs : IsProper s.left] [hp : IsProper p.left]
    (h : k.left ≫ p.left = s.left ≫ i.left)
    (e : Expression _ I X U)
    (gs : (Expression.shriek i hi qi (.push s hs e)).geometric)
    (gt : (Expression.push p hp (.shriek k hk qk e)).geometric)
    (K : ∀ a, Integral l E (X a).left)
    (hsrc : (Expression.shriek i hi qi (.push s hs e)).domain l E o K)
    (htgt : (Expression.push p hp (.shriek k hk qk e)).domain l E o K),
    let M := e.systemObj l E o ((inputReduction l E X).obj K)
    let N := (constantRestriction l E U.left).obj M
    ∃ lam : (ProEtale.StrictTower.J (constantIntegers l E) k.left ⋙
          ProEtale.StrictTower.R (constantIntegers l E) p.left) ⋙
          ProEtale.StrictTower.G (constantIntegers l E) i.left ≅
        ProEtale.StrictTower.R (constantIntegers l E) s.left,
      lam.hom = ProEtale.StrictTower.properOpenRestrictionMap
        (constantIntegers l E) k.left s.left p.left i.left h ∧
      ProEtale.StrictTower.properOpenOpenAdjunct
          (constantIntegers l E) k.left s.left p.left i.left lam =
        ProEtale.StrictTower.gamma (constantIntegers l E) k.left s.left p.left i.left h ∧
      (constantRestriction l E Z.left).map
          ((r.properOpen.gamma k.left s.left p.left i.left h).app M) ≫
        (constantRestriction l E Z.left).map
          ((r.canonicalBridge.push l E p.left).hom.app
            ((Operations.shriek l E o k.left).obj M)) ≫
        (constantPush l E p.left).app ((Operations.shriek l E o k.left).obj M) ≫
        (ProEtale.StrictTower.R (constantIntegers l E) p.left).map
          ((constantRestriction l E V.left).map
              ((r.canonicalBridge.shriek l E k.left).hom.app M) ≫
            (constantOpen l E k.left).hom.app M) =
      (constantRestriction l E Z.left).map
          ((r.canonicalBridge.shriek l E i.left).hom.app
            ((Operations.push l E o s.left).obj M)) ≫
        (constantOpen l E i.left).hom.app ((Operations.push l E o s.left).obj M) ≫
        (ProEtale.StrictTower.J (constantIntegers l E) i.left).map
          ((constantRestriction l E W.left).map
              ((r.canonicalBridge.push l E s.left).hom.app M) ≫
            (constantPush l E s.left).app M) ≫
        (ProEtale.StrictTower.properOpenOpenAdjunct
          (constantIntegers l E) k.left s.left p.left i.left lam).app N ∧
      ((Expression.shriek i hi qi (.push s hs e)).completionMap l E r.ringedModels K ≫
          transport l E r _ _ gs gt K hsrc htgt
            ((r.properOpen.gamma k.left s.left p.left i.left h).app M) =
        (r.ringedProperOpen.gamma k.left s.left p.left i.left h).app
            (e.ringedObj l E r.ringedModels K) ≫
          (Expression.push p hp (.shriek k hk qk e)).completionMap l E r.ringedModels K) ∧
      ∀ (n : ℕ)
        (w : ProEtale.StrictTower.ScalarEtaleOrigin (constantIntegers l E) U.left
          ((ProEtale.StrictTower.ev (constantIntegers l E) U.left n).obj N))
        (_hC : w.Λ = scalarRings l E n)
        (_hscalar : HEq w.φ (constantCoefficient l E n)),
        (ProEtale.StrictTower.finiteSource (constantIntegers l E) s.left i.left N n w).hom ≫
          (ProEtale.StrictTower.ev (constantIntegers l E) Z.left n).map
            ((ProEtale.StrictTower.properOpenOpenAdjunct
              (constantIntegers l E) k.left s.left p.left i.left lam).app N) =
        (ProEtale.StrictTower.HD (constantIntegers l E) Z.left w.Λ w.φ).map
            ((ProEtale.StrictTower.finiteGamma w.Λ k.left s.left p.left i.left h).hom.app
              w.origin.L) ≫
          (ProEtale.StrictTower.finiteTarget (constantIntegers l E) k.left p.left N n w).hom

/-- Product compactification geometry over the fixed finite-field base. The two pullback
squares and two projection equations specify u=j times_B k; no arbitrary product map is
introduced. Source: node first paragraph
(blueprint: lem-sf-product-normalization-realization-transport). -/
structure ProductDiagram (D : FiniteFieldDatum.{u}) where
  B : Over (Spec (CommRingCat.of D.k))
  X : Over (Spec (CommRingCat.of D.k))
  Y : Over (Spec (CommRingCat.of D.k))
  Xb : Over (Spec (CommRingCat.of D.k))
  Yb : Over (Spec (CommRingCat.of D.k))
  T : Over (Spec (CommRingCat.of D.k))
  Tb : Over (Spec (CommRingCat.of D.k))
  j : X ⟶ Xb
  k : Y ⟶ Yb
  a : Xb ⟶ B
  b : Yb ⟶ B
  p : T ⟶ X
  q : T ⟶ Y
  pb : Tb ⟶ Xb
  qb : Tb ⟶ Yb
  u : T ⟶ Tb
  [openJ : IsOpenImmersion j.left]
  [openK : IsOpenImmersion k.left]
  [openU : IsOpenImmersion u.left]
  [properA : IsProper a.left]
  [properB : IsProper b.left]
  [qcJ : QuasiCompact j.left]
  [qcK : QuasiCompact k.left]
  [qcU : QuasiCompact u.left]
  square : IsPullback p.left q.left (j ≫ a).left (k ≫ b).left
  barSquare : IsPullback pb.left qb.left a.left b.left
  left : u.left ≫ pb.left = p.left ≫ j.left
  right : u.left ≫ qb.left = q.left ≫ k.left
  finiteType : ∀ V ∈ [B, X, Y, Xb, Yb, T, Tb], LocallyOfFiniteType V.hom
  quasiCompact : ∀ V ∈ [B, X, Y, Xb, Yb, T, Tb], QuasiCompact V.hom
  separated : ∀ V ∈ [B, X, Y, Xb, Yb, T, Tb], IsSeparated V.hom

attribute [instance] ProductDiagram.openJ ProductDiagram.openK ProductDiagram.openU
  ProductDiagram.properA ProductDiagram.properB
  ProductDiagram.qcJ ProductDiagram.qcK ProductDiagram.qcU

/-- The actual external product of the two open extensions, retaining parentheses.
Source: node e_bullet source (blueprint: lem-sf-product-normalization-realization-transport). -/
def ProductDiagram.ambient (d : ProductDiagram D) (e : Expression _ I X d.X)
    (t : Expression _ I X d.Y) : Expression _ I X d.Tb :=
  .tensor (.pull d.pb (.shriek d.j inferInstance inferInstance e))
    (.pull d.qb (.shriek d.k inferInstance inferInstance t))

/-- The actual external product on the open fiber product.
Source: node e_bullet target (blueprint: lem-sf-product-normalization-realization-transport). -/
def ProductDiagram.inside (d : ProductDiagram D) (e : Expression _ I X d.X)
    (t : Expression _ I X d.Y) : Expression _ I X d.T :=
  .tensor (.pull d.p e) (.pull d.q t)

/-- Open extension of the inside product.
Source: node e_bullet target (blueprint: lem-sf-product-normalization-realization-transport). -/
def ProductDiagram.extended (d : ProductDiagram D) (e : Expression _ I X d.X)
    (t : Expression _ I X d.Y) : Expression _ I X d.Tb :=
  .shriek d.u inferInstance inferInstance (d.inside e t)

/-- Canonical restriction comparison on systems: the two normalized open units,
projection-composition squares, then inverse tensor/pullback comparison. Its adjunct
is the inverse of the ordered open base-change/tensor word.
Source: node proof step 3; openTensorNormalization
(blueprint: lem-sf-product-normalization-realization-transport). -/
def ProductDiagram.systemRestriction (d : ProductDiagram D)
    (K : System l E d.X.left) (L : System l E d.Y.left) :=
  (calculus l E d.T.left).systemClosed.tensor.map
    (Prod.mkHom
      ((pull l E d.p.left).map ((o.extension d.j.left).adj.unit.app K) ≫
        (r.compositors.square l E d.p.left d.u.left d.j.left d.pb.left d.left.symm).inv.app
          ((Operations.shriek l E o d.j.left).obj K))
      ((pull l E d.q.left).map ((o.extension d.k.left).adj.unit.app L) ≫
        (r.compositors.square l E d.q.left d.u.left d.k.left d.qb.left d.right.symm).inv.app
          ((Operations.shriek l E o d.k.left).obj L))) ≫
    (pullbackTensorSystemComparison l E d.u.left).inv.app
      ((pull l E d.pb.left).obj ((Operations.shriek l E o d.j.left).obj K),
        (pull l E d.qb.left).obj ((Operations.shriek l E o d.k.left).obj L))

/-- The localized completed-ring open restriction identification, using the two actual
open units, the projection squares and inverse tensor comparison.
Source: node proof step 3 (blueprint: lem-sf-product-normalization-realization-transport). -/
def ProductDiagram.ringedRestriction (d : ProductDiagram D)
    (K : Integral l E d.X.left) (L : Integral l E d.Y.left) :=
  (r.ringedModels.tensor d.T.left).ordinary.tensor.map
    (Prod.mkHom
      ((ringedPull.{u} l E d.p.left).map ((ringedOpenAdj.{u} l E d.j.left).unit.app K) ≫
        (ringedSquare.{u} l E d.p.left d.u.left d.j.left d.pb.left d.left.symm).inv.app
          ((ringedOpen.{u} l E d.j.left).obj K))
      ((ringedPull.{u} l E d.q.left).map ((ringedOpenAdj.{u} l E d.k.left).unit.app L) ≫
        (ringedSquare.{u} l E d.q.left d.u.left d.k.left d.qb.left d.right.symm).inv.app
          ((ringedOpen.{u} l E d.k.left).obj L))) ≫
    (ringedTensorPull.{u} l E r.ringedModels d.u.left).inv.app
      ((ringedPull.{u} l E d.pb.left).obj ((ringedOpen.{u} l E d.j.left).obj K),
        (ringedPull.{u} l E d.qb.left).obj ((ringedOpen.{u} l E d.k.left).obj L))

/-- Canonical completed open product: inverse open adjunct fixes the localized map,
its completion equals conjugation of the actual system word, and its restriction is
the identity under the specified open unit.
Source: node proof step 3 (blueprint: lem-sf-product-normalization-realization-transport). -/
def OpenLaws : Prop :=
  ∀ {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    (d : ProductDiagram D) (e : Expression _ I X d.X) (t : Expression _ I X d.Y)
    (ga : (d.ambient e t).geometric) (gb : (d.extended e t).geometric)
    (K : ∀ i, Integral l E (X i).left)
    (ha : (d.ambient e t).domain l E o K) (hb : (d.extended e t).domain l E o K),
    ∃ es : (d.ambient e t).systemObj l E o ((inputReduction l E X).obj K) ≅
        (d.extended e t).systemObj l E o ((inputReduction l E X).obj K),
      ∃ er : (d.ambient e t).ringedObj l E r.ringedModels K ≅
          (d.extended e t).ringedObj l E r.ringedModels K,
        ∃ ec : ((d.ambient e t).evaluate (integralInterpretation l E)).obj K ≅
            ((d.extended e t).evaluate (integralInterpretation l E)).obj K,
          es.inv = ((o.extension d.u.left).adj.homEquiv _ _).symm
            (d.systemRestriction l E r
              (e.systemObj l E o ((inputReduction l E X).obj K))
              (t.systemObj l E o ((inputReduction l E X).obj K))) ∧
          er.inv = ((ringedOpenAdj.{u} l E d.u.left).homEquiv _ _).symm
            (d.ringedRestriction l E r
              (e.ringedObj l E r.ringedModels K) (t.ringedObj l E r.ringedModels K)) ∧
          ec.hom = transport l E r (d.ambient e t) (d.extended e t) ga gb K ha hb es.hom ∧
          (d.ambient e t).completionMap l E r.ringedModels K ≫ ec.hom =
            er.hom ≫ (d.extended e t).completionMap l E r.ringedModels K ∧
          d.ringedRestriction l E r
              (e.ringedObj l E r.ringedModels K) (t.ringedObj l E r.ringedModels K) ≫
            (ringedPull.{u} l E d.u.left).map er.hom =
              (ringedOpenAdj.{u} l E d.u.left).unit.app
                ((d.inside e t).ringedObj l E r.ringedModels K) ∧
          Word l E r K (d.ambient e t) (d.extended e t) es.hom ec.hom

/-- The compactification identity is an implication from the assumed whole-system
identity, with the actual proper-image functor on the normalized completed open map.
Here the two lambda arrows are the specified ordered exchange/projection words in
`Word`; their endpoints retain the compactification identifications. In particular
no finite-level compactification theorem is assumed at integral coefficients.
Source: node proof step 6 (blueprint: lem-sf-product-normalization-realization-transport). -/
def ProductIdentityLaws : Prop :=
  ∀ {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    (d : ProductDiagram D) (e : Expression _ I X d.X) (t : Expression _ I X d.Y)
    (c : d.Tb ⟶ d.B) (hc : IsProper c.left) (_hcomp : c = d.qb ≫ d.b)
    (S : Expression _ I X d.B)
    (_gS : S.geometric) (ga : (d.ambient e t).geometric) (gb : (d.extended e t).geometric)
    (_gPa : (Expression.push c hc (d.ambient e t)).geometric)
    (_gPb : (Expression.push c hc (d.extended e t)).geometric)
    (K : ∀ i, Integral l E (X i).left)
    (_hS : S.domain l E o K)
    (ha : (d.ambient e t).domain l E o K) (hb : (d.extended e t).domain l E o K)
    (_hPa : (Expression.push c hc (d.ambient e t)).domain l E o K)
    (_hPb : (Expression.push c hc (d.extended e t)).domain l E o K)
    (es : (d.ambient e t).systemObj l E o ((inputReduction l E X).obj K) ≅
      (d.extended e t).systemObj l E o ((inputReduction l E X).obj K))
    (ec : ((d.ambient e t).evaluate (integralInterpretation l E)).obj K ≅
      ((d.extended e t).evaluate (integralInterpretation l E)).obj K)
    (lam : S.systemObj l E o ((inputReduction l E X).obj K) ⟶
      (Expression.push c hc (d.extended e t)).systemObj l E o ((inputReduction l E X).obj K))
    (lamProper : S.systemObj l E o ((inputReduction l E X).obj K) ⟶
      (Expression.push c hc (d.ambient e t)).systemObj l E o ((inputReduction l E X).obj K))
    (lamC : (S.evaluate (integralInterpretation l E)).obj K ⟶
      ((Expression.push c hc (d.extended e t)).evaluate (integralInterpretation l E)).obj K)
    (lamProperC : (S.evaluate (integralInterpretation l E)).obj K ⟶
      ((Expression.push c hc (d.ambient e t)).evaluate (integralInterpretation l E)).obj K),
    Word l E r K (d.ambient e t) (d.extended e t) es.hom ec.hom →
    Word l E r K S (.push c hc (d.extended e t)) lam lamC →
    Word l E r K S (.push c hc (d.ambient e t)) lamProper lamProperC →
    lam = lamProper ≫ (Operations.push l E o c.left).map es.hom →
      ec.hom = transport l E r (d.ambient e t) (d.extended e t) ga gb K ha hb es.hom ∧
      lamC = lamProperC ≫ (ringedPush l E c.left).map ec.hom

/-- Transport of the specified product normalization through completed realization.
Source: Stacks sites-cohomology.tex, Tag 0941, lemma-derived-limit-is-ok, and current
blueprint lem-sf-kunneth-coherence.proof.md, proper-reduction sentence
(blueprint: lem-sf-product-normalization-realization-transport).

Proof: (1) Apply integralCompactificationSystemRealization to each canonical generator
and each outer expression context. The coefficient square for signed symmetry and
associativity is normalizedTensorConstraintTransport; expression_contextual_intertwining
converts that whole-system square to the same realization equation.
(2) Induct on ordered words: functoriality handles the empty word; at composition cancel
the intermediate comparison; at an inverse multiply by both inverse isomorphisms.
(3) For the normalized open base-change/tensor word, the conjugation formula is therefore
the canonical completed open comparison. Its inverse and naturality follow by the same
cancellation. openTensorNormalization identifies its restriction word with the identity.
(4) Apply the equal-path clause to the assumed system signed-symmetry and triple-
associativity equations, retaining every actual constraint letter.
(5) Paste r.properOpen.canonical with gamma_scalarRestriction using the canonical
bridge and the actual lifted O_E quotient maps; this identifies restriction of the
word generator itself with the constant-R mate. Open-adjunction uniqueness identifies it
with properOpenOpenAdjunct of the specified
restriction map. properOpenTowerComparison and StrictTower.gamma_evaluation supply its bounded
etale-origin finite normalization at the actual quotient coefficients. The canonical
properOpen word gives its total-limit realization equation.
(6) Apply the word-composition clause to the assumed lambda_aj,bk = S_c(e) lambda_a,b.
Here lambda is the ordered alpha, projection, exchange and two-symmetry composite of
product_compactification_identity; its proper-image context is retained by CanonicalPair.
(7) Apply the rational or common-stage coefficient functor to each equation. The supplied
comparisons preserve the generators by basicOperationsCoefficientReduction. On composites
all intermediate endpoint comparisons cancel; for E subset F subset H substitute the
stipulated scalar-extension cocycle at both endpoints. No reduction of rational objects,
faithfulness of finite reduction, or faithfulness of evaluation is used. -/
theorem productNormalizationRealizationTransport
    (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p) (o : Operations l E)
    (r : Realizations l E D o) :
    WordLaws l E r ∧ NaturalityLaws l E r ∧ OpenLaws l E r ∧
      ProductIdentityLaws l E r ∧ ProperOpenLaws l E r ∧
      ScalarLaws.{u, v, w, v₂, w₂} l E := by
  sorry

end WeilConjectures.IntegralSystemRealization.ProductNormalization

attribute [instance] WeilConjectures.IntegralHom.derivedCategory
