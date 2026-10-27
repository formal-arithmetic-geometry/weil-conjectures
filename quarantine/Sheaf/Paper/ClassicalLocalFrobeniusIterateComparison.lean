/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.Paper.CompletedLocalFibreComparisonData
import Sheaf.Paper.LisseRationalRealization
import Sheaf.TraceFormula.PointTransportComposition

/-! # Classical realization and every local Frobenius period

Source: Bhatt--Scholze, Proposition 6.8.4(1),(4), Remark 6.8.15;
blueprint real-mixed-by-curves, first paragraph
(blueprint: lem-zl-classical-local-frobenius-iterate-comparison).

The classical factors use the existing finite-etale paths and the actual
inverse-limit/rationalized automorphism fibre comparison. Positive exponents are
indexed by n+1, as in the published local Frobenius construction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open Opposite
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures.ClassicalLocalFrobenius

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type (u + 1)) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]
  [hUnits : Fact (∀ x : (D.geometricFiber Y₀).left,
    IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x))]
  (R : ZlClassicalRealization D l hl Ω Y₀)

/-- The return equation in the new Frobenius generators follows by regrouping powers.
Source: blueprint constant-field clause
(blueprint: lem-zl-classical-local-frobenius-iterate-comparison).
Proof: use positivePower_blocks on both schemes, substitute the given return equation,
and reverse the point-side power equation. -/
theorem blockReturnEquation
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom
        ((m + 1) * (n + 1) - 1) =
      localPositivePower (frobeniusPointIso D).hom ((m + 1) * (n + 1) - 1) ≫ x) :
    x ≫ localPositivePower (localPositivePower (D.geometricFrobenius Y₀).hom m) n =
      localPositivePower (localPositivePower (frobeniusPointIso D).hom m) n ≫ x := by
  sorry

/-- The new middle factor is formed from the two new pullback factorizations.
Source: BS 6.8.15; blueprint constant-field clause
(blueprint: lem-zl-classical-local-frobenius-iterate-comparison). -/
def blockReturn
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom
        ((m + 1) * (n + 1) - 1) =
      localPositivePower (frobeniusPointIso D).hom ((m + 1) * (n + 1) - 1) ≫ x) :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  (LocalFrobeniusLarge.composition l Ω
    (localPositivePower (localPositivePower (frobeniusPointIso D).hom m) n) x K).symm ≪≫
  eqToIso (congrArg (fun f ↦ (commonStageDerivedPullback l Ω f).obj K)
    (blockReturnEquation D Y₀ x m n h).symm) ≪≫
  LocalFrobeniusLarge.composition l Ω x
    (localPositivePower (localPositivePower (D.geometricFrobenius Y₀).hom m) n) K

/-- The local operator after constant extension, with the new generator and Weil map.
Source: Weil II (1.1.10); blueprint constant-field clause
(blueprint: lem-zl-classical-local-frobenius-iterate-comparison). -/
def blockOperator (K : sfCommonStageWeilComplex D l hl Y₀ Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom
        ((m + 1) * (n + 1) - 1) =
      localPositivePower (frobeniusPointIso D).hom ((m + 1) * (n + 1) - 1) ≫ x) :
    (LocalFrobeniusLarge.stalk D l hl Ω Y₀ x).obj K.carrier ⟶
      (LocalFrobeniusLarge.stalk D l hl Ω Y₀ x).obj K.carrier :=
  letI := frobeniusPointPrimeInvertible D l hl
  letI := sfWeilPrimeInvertible D l hl Y₀
  transportBlocks l Ω D hl m ((commonStageDerivedPullback l Ω x).obj K.carrier) n ≫
  (LocalFrobeniusLarge.pointFibre D l hl Ω).map
    (blockReturn l Ω D hl Y₀ K.carrier x m n h).hom ≫
  (LocalFrobeniusLarge.stalk D l hl Ω Y₀ x).map
    (sfWeilAlong l Ω D hl Y₀ (localPositivePower (D.geometricFrobenius Y₀).hom m) K.carrier
      (LocalFrobeniusLarge.weilIterate D l hl Ω Y₀ K m) n).hom

/-- The same return written using the block powers of scheme isomorphisms.
Source: blueprint constant-field clause
(blueprint: lem-zl-classical-local-frobenius-iterate-comparison).
Proof: expand the hom of each positiveIso using positiveIso_hom, apply
positivePower_blocks, and substitute the given product-period semilinear return. -/
theorem blockIsoReturnEquation
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom
        ((m + 1) * (n + 1) - 1) =
      localPositivePower (frobeniusPointIso D).hom ((m + 1) * (n + 1) - 1) ≫ x) :
    x ≫ (positiveIso (positiveIso (D.geometricFrobenius Y₀) m) n).hom =
      (positiveIso (positiveIso (frobeniusPointIso D) m) n).hom ≫ x := by
  sorry

/-- The classical middle factor for the new generator, on its literal endpoints.
Source: BS 6.8.15; blueprint constant-field clause
(blueprint: lem-zl-classical-local-frobenius-iterate-comparison). -/
def classicalBlockReturn
    (M : LisseAlgebraicSheaf l (D.geometricFiber Y₀).left Ω)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom
        ((m + 1) * (n + 1) - 1) =
      localPositivePower (frobeniusPointIso D).hom ((m + 1) * (n + 1) - 1) ≫ x) :=
  eqToIso (congrArg (fun y ↦ lisseAlgebraicFiber l (D.geometricFiber Y₀).left Ω y M)
    (blockIsoReturnEquation D Y₀ x m n h).symm) ≪≫
  (lisseAlgebraicAutomorphismFiberIso
    (positiveIso (positiveIso (D.geometricFrobenius Y₀) m) n) l Ω x M).symm

/-- The block construction retains its literal underlying classical sheaf.
Source: blueprint constant-field clause
(blueprint: lem-zl-classical-local-frobenius-iterate-comparison).
Proof: unfold classicalBlock and IsoAlgebra.mk; its carrier is M.carrier. -/
theorem classicalBlockCarrier (M : ZlClassicalWeil D l Ω Y₀) (m : ℕ) :
    (classicalBlock l Ω D Y₀ M m).carrier = M.carrier := by
  sorry

/-- The new classical operator before the literal carrier equality is transported.
Source: Weil II (1.1.10); BS 6.8.15
(blueprint: lem-zl-classical-local-frobenius-iterate-comparison). -/
def classicalBlockOperatorRaw (M : ZlClassicalWeil D l Ω Y₀)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom
        ((m + 1) * (n + 1) - 1) =
      localPositivePower (frobeniusPointIso D).hom ((m + 1) * (n + 1) - 1) ≫ x) :=
  (etaleAlgebraicPathIso l Ω (classicalBlock l Ω D Y₀ M m).carrier
    (FiniteEtale.fiberReparamIso
      (positiveIso (positiveIso (frobeniusPointIso D) m) n) x).symm).hom ≫
  (classicalBlockReturn l Ω D Y₀ (classicalBlock l Ω D Y₀ M m).carrier x m n h).hom ≫
  (fibre l Ω x).map
    (classicalWeilIterate l Ω (positiveIso (D.geometricFrobenius Y₀) m)
      (classicalBlock l Ω D Y₀ M m) n).hom

/-- Constant-extension classical local operator with the literal underlying carrier restored.
Source: Weil II (1.1.10); BS 6.8.15
(blueprint: lem-zl-classical-local-frobenius-iterate-comparison). -/
def classicalBlockOperator (M : ZlClassicalWeil D l Ω Y₀)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom
        ((m + 1) * (n + 1) - 1) =
      localPositivePower (frobeniusPointIso D).hom ((m + 1) * (n + 1) - 1) ≫ x) :=
  (fibre l Ω x).map (eqToHom (classicalBlockCarrier l Ω D Y₀ M m).symm) ≫
    classicalBlockOperatorRaw l Ω D Y₀ M x m n h ≫
      (fibre l Ω x).map (eqToHom (classicalBlockCarrier l Ω D Y₀ M m))

/-- Constant-field extension preserves both local operators at the product period.
Source: Weil II (1.1.10); BS 6.8.15; blueprint proof step 8
(blueprint: lem-zl-classical-local-frobenius-iterate-comparison).
Proof: expand each new transport using transport_blocks and each Weil map using
sfWeil_blocks and classicalWeil_blocks. The composition pentagon, followed by the
equality transports of positivePower_blocks, identifies the middle factors. The
finite-etale reparametrization for a composite is its composite path, so classical
transports obey the same identity. Cancel inverse endpoint transports in WBI. -/
theorem constantExtension_operators
    (M : ZlClassicalWeil D l Ω Y₀)
    (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m n : ℕ)
    (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom
        ((m + 1) * (n + 1) - 1) =
      localPositivePower (frobeniusPointIso D).hom ((m + 1) * (n + 1) - 1) ≫ x) :
    blockOperator l Ω D hl Y₀ ((R.weil.obj M).obj) x m n h =
      LocalFrobeniusLarge.operator D l hl Ω Y₀ ((R.weil.obj M).obj) x
        ((m + 1) * (n + 1) - 1) h ∧
    HEq (classicalBlockOperator l Ω D Y₀ M x m n h)
      (classicalOperator l Ω D Y₀ M x ((m + 1) * (n + 1) - 1) h) := by
  sorry

/-- All clauses of the normalized comparison on the actual classical and sf fibres.
Positive periods are n+1; the return equality is semilinear and is quantified for
all geometric lifts satisfying it, hence in particular every extension-field point.
Source: BS 6.8.4(1),(4), 6.8.15; blueprint real-mixed-by-curves paragraph 1
(blueprint: lem-zl-classical-local-frobenius-iterate-comparison). -/
def ComparisonAssertions : Prop :=
  ∃! c : ∀ x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left,
      R.functor ⋙ LocalFrobeniusLarge.stalk D l hl Ω Y₀ x ≅ fibre l Ω x,
    CompletedNormalization l Ω D hl Y₀ R c ∧
    FactorSquares l Ω D hl Y₀ R c ∧
    (∀ (M : ZlClassicalWeil D l Ω Y₀)
      (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (n : ℕ)
      (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom n =
        localPositivePower (frobeniusPointIso D).hom n ≫ x),
      LocalFrobeniusLarge.operator D l hl Ω Y₀ ((R.weil.obj M).obj) x n h ≫
          (c x).hom.app M.carrier =
        (c x).hom.app M.carrier ≫ classicalOperator l Ω D Y₀ M x n h) ∧
    (∀ (M N : ZlClassicalWeil D l Ω Y₀) (f : M ⟶ N)
      (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
      (LocalFrobeniusLarge.stalk D l hl Ω Y₀ x).map (R.functor.map f.hom.f) ≫
        (c x).hom.app N.carrier = (c x).hom.app M.carrier ≫
          (fibre l Ω x).map f.hom.f) ∧
    (∀ (P Q : LisseCoefficientPairs l (D.geometricFiber Y₀).left Ω) (f : P ⟶ Q)
      (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left),
      (LocalFrobeniusLarge.stalk D l hl Ω Y₀ x).map
          (R.functor.map ((lisseCoefficientCocartesian l
            (D.geometricFiber Y₀).left Ω).Q.map f)) ≫
        (c x).hom.app ((lisseCoefficientCocartesian l
          (D.geometricFiber Y₀).left Ω).Q.obj Q) =
      (c x).hom.app ((lisseCoefficientCocartesian l
          (D.geometricFiber Y₀).left Ω).Q.obj P) ≫
        (fibre l Ω x).map ((lisseCoefficientCocartesian l
          (D.geometricFiber Y₀).left Ω).Q.map f)) ∧
    (∀ (M : ZlClassicalWeil D l Ω Y₀)
      (x : Spec (.of D.k) ⟶ (D.geometricFiber Y₀).left) (m n : ℕ)
      (h : x ≫ localPositivePower (D.geometricFrobenius Y₀).hom
          ((m + 1) * (n + 1) - 1) =
        localPositivePower (frobeniusPointIso D).hom ((m + 1) * (n + 1) - 1) ≫ x),
      blockOperator l Ω D hl Y₀ ((R.weil.obj M).obj) x m n h ≫
          (c x).hom.app M.carrier =
        (c x).hom.app M.carrier ≫
          classicalBlockOperator l Ω D Y₀ M x m n h)

include hl in
/-- The stalk-unit convention follows from the finite-field coefficient hypothesis.
Source: BS 6.8.4 hypotheses, finite-field base convention
(blueprint: lem-zl-classical-local-frobenius-iterate-comparison).
Proof: zlClassicalStalkInvertible gives an inverse of l at each stalk; apply
isUnit_of_invertible at each point and package the resulting proposition in Fact. -/
theorem stalkPrimeUnits : Fact (∀ x : (D.geometricFiber Y₀).left,
    IsUnit (l : (D.geometricFiber Y₀).left.presheaf.stalk x)) := by
  sorry

/-- Normalized classical realization intertwines local Frobenius at every period.
Source: BS 6.8.4(1),(4), 6.8.15; blueprint real-mixed-by-curves paragraph 1
(blueprint: lem-zl-classical-local-frobenius-iterate-comparison).
Proof:
1. At each finite E take the SAME stage isomorphism occurring in R.pullback_pinning.
Its inverse on fibres, followed by completed-system reduction/limit and rationalization,
is c. Point sections agree with the actual inverse limit of the etale quotient stalks.
The formula in CompletedNormalization determines it on these generators.
2. The ordinary unit sends u to 1 tensor u. The pinned unit square and its finite
reduction square identify it with literal classical reindexing, keeping every germ.
Linearity extends from generators to sections, sheafification and finite sums.
3. Compose with every completed-fibre projection. Both paths have the same finite
germ image, so the inverse-limit maps agree. Tensor with E and Ω. The same calculation
with two pullbacks identifies the actual composition comparisons.
4. The restriction/coprojection formula for point transport preserves each section
and its lifted point. Apply the preceding unit square, then induct on the number of
transports with the specified composition comparisons. This gives the first factor square.
5. By definition vartheta=R(theta)d_1. Naturality of d_r on theta and the two
composition comparisons imply vartheta^[r]=R(theta^[r])d_r by induction. This
is in the rational categories and requires no invariant lattice for theta or its inverse.
6. At the actual semilinear return, the composition square gives the middle factor
square; step 5 gives the Weil factor square. Substitute these three equations in WBI
to obtain the displayed operator intertwining equation.
7. Every construction is natural in all sheaf maps, hence in Weil maps, without
invertibility of the map. Finite scalar extension acts on tensors by multiplication
and commutes with every finite reduction. Identity and tower scalar comparisons
therefore descend through the common-stage Hom quotient, including arbitrary lifts.
8. For q replaced by q^(m+1), use gs^(m+1), gY^(m+1) and theta^[m+1].
The block recursions transport_blocks, sfWeil_blocks and classicalWeil_blocks expand
the new n+1-fold maps to the old (m+1)(n+1)-fold maps. Pullback associativity identifies
their middle factors. Apply the same three squares at each product-period return.
9. Nothing uses positive rank or a k-linear Frobenius. Empty schemes are vacuous;
zero fibres and rank zero obey the same tensor, projection and morphism formulas.
Uniqueness follows from the normalized section formula: these local sections generate
the ordinary point inverse image after sheafification, and rational tensors generate
its Ω extension. Finite free models and isomorphisms cover the classical category. -/
theorem classical_local_frobenius_iterate_comparison
    (S : @ZlClassicalRealization D l _ hl Ω _ _ _ Y₀ _ _ _
      (stalkPrimeUnits l D hl Y₀)) :
    @ComparisonAssertions l _ Ω _ _ _ D hl Y₀ _ _ _ (stalkPrimeUnits l D hl Y₀) S := by
  sorry

end WeilConjectures.ClassicalLocalFrobenius
