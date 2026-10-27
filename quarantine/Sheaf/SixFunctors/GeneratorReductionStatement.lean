/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.SixFunctors.GeneratorReductionData
public import Sheaf.SixFunctors.ShortWordCompletionIsomorphism
import Sheaf.SixFunctors.ShortWordIntegralDomain
import Sheaf.SixFunctors.PrimitiveQuotientAugmentations
import Sheaf.SixFunctors.OpenReconstructionEffectivity
import Sheaf.SixFunctors.TensorAdjunctionReductionSquares
import Sheaf.SixFunctors.StructuralReductionWordSubstitution
import Sheaf.SixFunctors.OpenBaseChangeReductionSquare
import Sheaf.SixFunctors.OpenTensorReductionSquare
import Sheaf.SixFunctors.ProperOpenLambdaReductionSquare
import Sheaf.SixFunctors.ProperOpenInterchangeReductionSquare
/-! # Canonical coefficient squares for the basic six-functor generators

Source: blueprint fix-prop-coherence, basic structural maps
(blueprint: lem-sf-generator-reduction-coherence).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u s i v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable {S : Type s} (W : S → Scheme.{u}) {I : Type i} (location : I → S)

private theorem inverseOrZero_eq_inv {A : Type v} [Category.{w} A] [HasZeroMorphisms A]
    {X Y : A} (f : X ⟶ Y) [IsIso f] : inverseOrZero f = inv f := by
  simp only [inverseOrZero, dif_pos (inferInstance : IsIso f)]

private theorem transpose_augmentation
    {A : Type*} {B : Type*} [Category A] [Category B]
    {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G)
    {X Y : A} {N : B} (χ : X ⟶ Y) (d : Y ⟶ G.obj N) (r : F.obj X ⟶ N)
    [IsIso (F.map χ)] (h : χ ≫ d = adj.unit.app X ≫ G.map r) :
    inv (F.map χ) ≫ r = F.map d ≫ adj.counit.app N := by
  apply (cancel_epi (F.map χ)).1
  rw [IsIso.hom_inv_id_assoc, ← Category.assoc, ← F.map_comp, h, F.map_comp,
    Category.assoc, adj.counit_naturality, adj.left_triangle_components_assoc]

private theorem tensor_transpose (o : Operations l E) (X : Scheme.{u})
    (K L : DerivedCategory (scalarReductionSource l E X)) :
    tensorR l E o X K L =
      (IntegralSystemRealization.calculus l E X).reduction.map
        ((tensorD l E X).inv.app (K, L)) ≫
      (IntegralSystemRealization.calculus l E X).adjunction.counit.app
        ((IntegralSystemRealization.calculus l E X).systemClosed.tensor.obj
          ((IntegralSystemRealization.calculus l E X).reduction.obj K,
            (IntegralSystemRealization.calculus l E X).reduction.obj L)) := by
  obtain ⟨hiso, h⟩ := (primitiveQuotientAugmentations l E o.ringed o.system o.realization).1 X K L
  let := hiso
  dsimp only [tensorR, tensorCompletion]
  rw [inverseOrZero_eq_inv]
  exact transpose_augmentation
    (IntegralSystemRealization.calculus l E X).adjunction _ _ _ h

private theorem pull_transpose (o : Operations l E) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (K : DerivedCategory (scalarReductionSource l E Y)) :
    pullR l E o f K =
      (IntegralSystemRealization.calculus l E X).reduction.map
        ((pullD l E f).inv.app K) ≫
      (IntegralSystemRealization.calculus l E X).adjunction.counit.app
        ((IntegralSystemRealization.pull l E f).obj
          ((IntegralSystemRealization.calculus l E Y).reduction.obj K)) := by
  obtain ⟨hiso, h⟩ := (primitiveQuotientAugmentations l E o.ringed o.system o.realization).2 f K
  let := hiso
  dsimp only [pullR]
  rw [inverseOrZero_eq_inv]
  exact transpose_augmentation
    (IntegralSystemRealization.calculus l E X).adjunction _ _ _ h

private theorem open_transpose (o : Operations l E) {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (K : DerivedCategory (scalarReductionSource l E X)) :
    openR l E o j K =
      (IntegralSystemRealization.calculus l E Y).reduction.map (openDInv l E o j K) ≫
        (IntegralSystemRealization.calculus l E Y).adjunction.counit.app
          ((IntegralSystemRealization.Operations.shriek l E o.system j).obj
            ((IntegralSystemRealization.calculus l E X).reduction.obj K)) := by
  exact ((IntegralSystemRealization.calculus l E Y).adjunction.homEquiv _ _).symm_apply_apply
    (openR l E o j K) |>.symm

private theorem open_inverse_laws (o : Operations l E) {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (K : DerivedCategory (scalarReductionSource l E X))
    [IsIso ((o.realization.openReduction l E j).app K)]
    [IsIso ((IntegralSystemRealization.calculus l E Y).adjunction.unit.app
      ((IntegralSystemRealization.ringedOpen l E j).obj K))] :
    (openD l E o j K ≫ openDInv l E o j K = 𝟙 _) ∧
      (openDInv l E o j K ≫ openD l E o j K = 𝟙 _) := by
  simp only [openD, openDInv, openR, inverseOrZero_eq_inv]
  constructor
  · simp only [Category.assoc, IsIso.inv_hom_id_assoc, ← Functor.map_comp,
      IsIso.hom_inv_id]
    exact CategoryTheory.Functor.map_id _ _
  · simp only [Category.assoc, ← Functor.map_comp_assoc, IsIso.inv_hom_id]
    rw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp, IsIso.hom_inv_id]

private theorem length_zero_formulas (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    {a : S} (B : Word W location a) (h : B.length = 0) :
    B.primitiveFormulas l E W location o K := by
  cases B <;> simp_all [Word.length, Word.primitiveFormulas]

private theorem length_zero_domain (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    {a : S} (B : Word W location a) (hzero : B.length = 0) :
    finiteTorConstructibleIntegral l E (W a) (B.integralValue l E W location o K) ∨
      B.integralValue l E W location o K =
        (IntegralSystemRealization.calculus l E (W a)).integralClosed.monoidal.tensorUnit := by
  cases B <;> simp_all only [Word.length, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, Word.integralValue]
  · exact Or.inl (hAdm _).1
  · exact Or.inr trivial

/-- Primitive comparison formula on the stated one-operation domain.
Source: blueprint coherence proof, steps 1--2
(blueprint: lem-sf-generator-reduction-coherence).

Proof: use simultaneous flat-term K-flat quotient representatives. Tensor and
pullback use the same quotient augmentation in their defining Roos towers and
completion units. The actual counit's evaluated transpose is the limit projection,
so their independent coefficient maps equal R(d inverse) followed by that counit.
Proper image is its defining L S R tower and d is identity. For open extension,
the canonical mate is the inverse of the specified r_j on complete inputs by
lem-sf-integral-open-reduction-comparison; apply L and the inverse reconstruction
unit to obtain d_j. Naturality of the counit and the two triangle identities give
the asserted transpose formula and both inverse laws. No evaluation faithfulness
is used. -/
theorem primitiveReductionTranspose (o : Operations l E)
    {a : S} (B : Word W location a)
    (_hLength : B.length ≤ 1)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    (_hIntermediate : Word.admissible l E W location o K lo hi torLo torHi B) :
    B.primitiveFormulas l E W location o K := by
  cases B with
  | input k => trivial
  | unit a => trivial
  | tensor B C =>
    refine ⟨?_, length_zero_formulas l E W location o K B ?_,
      length_zero_formulas l E W location o K C ?_⟩
    · exact tensor_transpose l E o _ _ _
    · simp only [Word.length] at _hLength
      omega
    · simp only [Word.length] at _hLength
      omega
  | pull f hs ht hq B =>
    refine ⟨?_, length_zero_formulas l E W location o K B ?_⟩
    · exact pull_transpose l E o _ _
    · simp only [Word.length] at _hLength
      omega
  | push f hs ht hq hp B =>
    refine ⟨?_, length_zero_formulas l E W location o K B ?_⟩
    · dsimp only [pushR]
      rw [CategoryTheory.Functor.map_id, Category.id_comp]
    · simp only [Word.length] at _hLength
      omega
  | «open» j hj hq B =>
    let := hj
    let := hq
    have hzero : B.length = 0 := by
      simp only [Word.length] at _hLength
      omega
    obtain ⟨hiso, hunit⟩ := openReconstructionEffectivity l E o.system o.realization j _
      (length_zero_domain l E W location o K lo hi torLo torHi _hAdm B hzero)
    let := hiso
    let := hunit
    exact ⟨open_transpose l E o j _, (open_inverse_laws l E o j _).1,
      (open_inverse_laws l E o j _).2,
      length_zero_formulas l E W location o K B hzero⟩

private theorem short_word_formulas (o : Operations l E)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (hAdm : ∀ k : I, Admissible l E
      (IntegralSystemRealization.calculus l E (W (location k))) (K k) lo hi torLo torHi)
    {a : S} (B : Word W location a) (hLength : B.length ≤ 3)
    (hIntermediate : B.admissible l E W location o K lo hi torLo torHi) :
    B.primitiveFormulas l E W location o K := by
  revert hLength hIntermediate
  induction B with
  | input k => intro _ _; trivial
  | unit a => intro _ _; trivial
  | tensor B C ihB ihC =>
    intro hLength hIntermediate
    obtain ⟨hB, hC⟩ := hIntermediate.2
    have hlenB : B.length ≤ 3 := by simp only [Word.length] at hLength; omega
    have hlenC : C.length ≤ 3 := by simp only [Word.length] at hLength; omega
    exact ⟨tensor_transpose l E o _ _ _, ihB hlenB hB, ihC hlenC hC⟩
  | pull f hs ht hq B ih =>
    intro hLength hIntermediate
    have hlen : B.length ≤ 3 := by simp only [Word.length] at hLength; omega
    exact ⟨pull_transpose l E o _ _, ih hlen hIntermediate.2⟩
  | push f hs ht hq hp B ih =>
    intro hLength hIntermediate
    have hlen : B.length ≤ 3 := by simp only [Word.length] at hLength; omega
    refine ⟨?_, ih hlen hIntermediate.2⟩
    dsimp only [pushR]
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  | «open» j hj hq B ih =>
    intro hLength hIntermediate
    let := hj
    let := hq
    have hlen : B.length ≤ 2 := by simp only [Word.length] at hLength; omega
    obtain ⟨hiso, hunit⟩ := openReconstructionEffectivity l E o.system o.realization j _
      (shortWordIntegralDomain l E W location o B hlen K lo hi torLo torHi
        hAdm hIntermediate.2)
    let := hiso
    let := hunit
    exact ⟨open_transpose l E o j _, (open_inverse_laws l E o j _).1,
      (open_inverse_laws l E o j _).2, ih (by omega) hIntermediate.2⟩

/-- Coefficient transposes and squares for the canonical basic generators.
Source: blueprint fix-prop-coherence.proof.md, the maps-used sentence
(blueprint: lem-sf-generator-reduction-coherence).

Proof, step 1: use lem-coef-semilinear-derived-sections to choose simultaneous
flat-term K-flat and K-injective models of the actual strict systems. The retained
FixedEtaleOriginWitness at every level, adjacent transition squares, normalization,
constructibility and common finite intervals put precisely the inputs and every
intermediate in the stated domain. All comparisons are maps of whole systems.

Step 2: the specified d_tensor and d_pull are the quotient/Roos identifications
of def-pur-integral-derived-operations and its completed tower substitution theorem.
The integral proper image is L S R by def-weil-derived-direct-image, so d_push is
identity in these coordinates. The actual counit projection at level n is the
adjunct of the total-limit projection, by lem-coef-derived-system-evaluation-calculus.
Consequently the independently constructed completion/reduction comparisons equal
R(d_A inverse) followed by the actual counit. For the open map use the mate of the
fixed reduction/pullback square, transported from
lem-sf-integral-open-reduction-comparison. Substitute d_j inverse = u followed by
L(r_j), apply counit naturality, and cancel e_(R X) R(u_X) by the triangle identity.
This proves the displayed primitive equations and the inverse laws for d_j.

Step 3: tensor and pullback on K-flat quotient complexes preserve reassociation,
scalar unit multiplication, and the canonical pullback compositor, by
lem-pur-completed-operation-tower-substitution. The section models of
lem-coef-semilinear-derived-sections preserve adjunction transposition. Thus the
actual geometric/open units and counits and the direct-image compositor, defined
as the right-adjoint conjugate of the pullback compositor, have commuting squares.
Use lem-weil-pbc-ringed-exchange-tensor-coherence for the canonical ringed tensor
and square identifications. Completing the independently constructed ringed maps
by the recursive actual quotient units gives the specified integral maps.

Step 4: inverse open base change and inverse open tensor are adjuncts of pullback
and tensor of the open unit, by lem-sf-open-tensor-normalization. Paste their
unit, tensor/pullback and counit squares. For proper/open lambda, first conjugate
the cartesian open base-change map by the actual adjunctions, then restrict the
k-extension through the clopen lift s:U -> V ×_Z W, use J_s = S_s fixed by the
inverse open unit, and compose direct images. The recorded properOpenLambda and
ringedProperOpenLambda perform exactly these four factors, independently on the
two sides. Apply the preceding squares to every intermediate listed in
lambdaAdmissible, including the internal length-four terms. Paste to get the
lambda square. Its inverse, transposed under J_i adjoint to P_i, is the actual
proper/open interchange; paste the open-counit square to get its square.

Step 5: substitute these one-factor equations successively into the recursive r_B
and r_C. In tensor apply the child comparisons in both slots and use
bifunctoriality; in each unary operation apply its functor to the child comparison.
Associativity and counit naturality give the asserted equality before any finite
evaluation. Only the generator endpoints have the length-three bound. No assertion
of equality detection by evaluated arrows or of arbitrary context realization is
used. Identity arrows, the empty open and zero inputs use the same units and maps. -/
theorem generatorReductionCoherence
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E]
    {S : Type s} (W : S → Scheme.{u}) (_hW : FiniteTypeFamily W D.k)
    {I : Type i} (location : I → S) (o : Operations C.l E)
    {a : S} {B Cw : Word W location a} (g : GeneratorKind W location B Cw)
    (_hB : B.length ≤ 3)
    (_hC : Cw.length ≤ 3)
    (K : ∀ k : I, DerivedCategory (scalarReductionSource C.l E (W (location k))))
    (lo hi torLo torHi : ℤ)
    (_hAdm : ∀ k : I, Admissible C.l E
      (IntegralSystemRealization.calculus C.l E (W (location k))) (K k) lo hi torLo torHi)
    (_hIntermediate : Word.admissible C.l E W location o K lo hi torLo torHi B ∧
      Word.admissible C.l E W location o K lo hi torLo torHi Cw)
    (_hGenerator : g.admissible C.l E W location o K lo hi torLo torHi) :
    B.primitiveFormulas C.l E W location o K ∧
      Cw.primitiveFormulas C.l E W location o K ∧ Assertion C.l E W location o K g := by
  have hpB := short_word_formulas C.l E W location o K lo hi torLo torHi
    _hAdm B _hB _hIntermediate.1
  have hpC := short_word_formulas C.l E W location o K lo hi torLo torHi
    _hAdm Cw _hC _hIntermediate.2
  refine ⟨hpB, hpC, ?_⟩
  have hShort : ∀ {S : Type s} (W : S → Scheme.{u})
      (hW : FiniteTypeFamily W D.k) {I : Type i} (location : I → S)
      {a : S} {B Cw : Word W location a} (g : GeneratorKind W location B Cw),
      OpenInterchangeReduction.Structural g → B.length ≤ 3 → Cw.length ≤ 3 →
      ∀ (K : ∀ k : I, DerivedCategory (scalarReductionSource C.l E (W (location k))))
        (lo hi torLo torHi : ℤ),
        (∀ k : I, Admissible C.l E
          (IntegralSystemRealization.calculus C.l E (W (location k))) (K k)
          lo hi torLo torHi) →
        B.admissible C.l E W location o K lo hi torLo torHi →
        Cw.admissible C.l E W location o K lo hi torLo torHi →
        Assertion C.l E W location o K g := by
    intro S W hW I location a B Cw g hg hB hC K lo hi torLo torHi hAdm hAB hAC
    have hKind : g.IsTensorAdjunction := by cases g <;> exact hg
    exact (tensorAdjunctionReductionSquares C E W hW location o g hKind hB hC K
      lo hi torLo torHi hAdm ⟨hAB, hAC⟩
      (short_word_formulas C.l E W location o K lo hi torLo torHi hAdm B hB hAB)
      (short_word_formulas C.l E W location o K lo hi torLo torHi hAdm Cw hC hAC)).1
  classical
  by_cases hg : OpenInterchangeReduction.Structural g
  · exact hShort W _hW location g hg _hB _hC K lo hi torLo torHi
      _hAdm _hIntermediate.1 _hIntermediate.2
  · have hOpen : OpenInterchangeReduction.OpenGenerator g := by
      cases g <;> trivial
    have hStructural : OpenInterchangeReduction.StructuralSquares.{u, s, i} C.l E D o :=
      OpenInterchangeReduction.structuralReductionWordSubstitution C E o hShort
    cases g <;> simp only [OpenInterchangeReduction.OpenGenerator] at hOpen
    case openBaseChange =>
      apply OpenInterchangeReduction.openBaseChangeReductionSquare C E o
        hStructural W _hW location
      all_goals first | assumption | exact _hIntermediate.1 | exact _hIntermediate.2
    case openTensor =>
      apply OpenInterchangeReduction.openTensorReductionSquare C E o
        hStructural W _hW location
      all_goals first | assumption | exact _hIntermediate.1 | exact _hIntermediate.2
    case properOpenLambda =>
      apply OpenInterchangeReduction.properOpenLambdaReductionSquare C E o
        hStructural W _hW location
      all_goals first | assumption | exact _hIntermediate.1 | exact _hIntermediate.2
    case properOpenInterchange =>
      apply OpenInterchangeReduction.properOpenInterchangeReductionSquare C E o
        hStructural W _hW location
      all_goals first | assumption | exact _hIntermediate.1 | exact _hIntermediate.2


end WeilConjectures.GeneratorReduction
