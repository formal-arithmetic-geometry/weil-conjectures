/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.SixFunctors.GeneratorReductionStatement
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.NormalizedDVREffectivity

/-! # Recursive characterization of integral realization

Source: blueprint main-20261015, fix-prop-coherence.proof.md, coefficient transport;
the seven proof steps of lem-pur-integral-realization-recursion
(blueprint: lem-pur-integral-realization-recursion).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
namespace Recursion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The proper single-operation identification, transporting the defining strict
system tower to the recorded integral proper image by its canonical adjoint conjugate.
The final factor identifies L R K with K using the actual unit. Source: blueprint
fix-prop-coherence, realization proof step 3; generator-reduction proof step 2
(blueprint: lem-pur-integral-realization-recursion). -/
def properD {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (r : Realizations l E D o) {X Y : Scheme.{u}} (p : X ⟶ Y) (K : Integral l E X) :=
  (r.realizationModel.push l E p).hom.app ((calculus l E X).reduction.obj K) ≫
    (PurCompactSupport.push (PurCompactSupport.completed l E) p).map
      (GeneratorReduction.inverseOrZero ((calculus l E X).adjunction.unit.app K))

/-- The specified localized open identification: L of the inverse open coefficient
map, followed by the inverse actual reconstruction unit. This is exactly the formula
for GeneratorReduction.openD with the same realization model, without requiring its
unrelated tensor-unit data. Source: blueprint fix-prop-coherence, realization step 3
(blueprint: lem-pur-integral-realization-recursion). -/
def openD {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (r : Realizations l E D o) {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (K : Integral l E X) :=
  (coefficientSequenceLimit l E Y).map ((r.realizationModel.openReduction l E j).app K) ≫
    GeneratorReduction.inverseOrZero ((calculus l E Y).adjunction.unit.app
      ((ringedOpen l E j).obj K))

/-- a_P(M) is the inverse of L P(e_M), followed by exactly the recorded pullback d.
Source: blueprint fix-prop-coherence, coefficient transport, recursion step 4
(blueprint: lem-pur-integral-realization-recursion). -/
def pullA {X Y : Scheme.{u}} (f : X ⟶ Y) (M : System l E Y) :=
  GeneratorReduction.inverseOrZero ((coefficientSequenceLimit l E X).map
    ((pull l E f).map ((calculus l E Y).adjunction.counit.app M))) ≫
  (GeneratorReduction.pullD l E f).hom.app ((coefficientSequenceLimit l E Y).obj M)

/-- a_S(M) uses the same proper-tower d and the actual counit e_M.
Source: blueprint fix-prop-coherence, coefficient transport, recursion step 4
(blueprint: lem-pur-integral-realization-recursion). -/
def properA {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (r : Realizations l E D o) {X Y : Scheme.{u}} (p : X ⟶ Y) (M : System l E X) :=
  GeneratorReduction.inverseOrZero ((coefficientSequenceLimit l E Y).map
    ((Operations.push l E o p).map ((calculus l E X).adjunction.counit.app M))) ≫
  properD l E r p ((coefficientSequenceLimit l E X).obj M)

/-- a_J(M) uses the prescribed localized open d, rather than an arbitrary comparison.
Source: blueprint fix-prop-coherence, coefficient transport, recursion step 4
(blueprint: lem-pur-integral-realization-recursion). -/
def openA {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (r : Realizations l E D o) {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (M : System l E X) :=
  GeneratorReduction.inverseOrZero ((coefficientSequenceLimit l E Y).map
    ((Operations.shriek l E o j).map ((calculus l E X).adjunction.counit.app M))) ≫
  openD l E r j ((coefficientSequenceLimit l E X).obj M)

/-- a_tensor(M,N) is the inverse of L(e_M tensor e_N), followed by precisely the
published two-input strict-tower identification. Source: blueprint fix-prop-coherence,
coefficient transport, recursion step 5
(blueprint: lem-pur-integral-realization-recursion). -/
def tensorA (X : Scheme.{u}) (M N : System l E X) :=
  GeneratorReduction.inverseOrZero ((coefficientSequenceLimit l E X).map
    ((calculus l E X).systemClosed.tensor.map
      (Prod.mkHom ((calculus l E X).adjunction.counit.app M)
        ((calculus l E X).adjunction.counit.app N)))) ≫
  (GeneratorReduction.tensorD l E X).hom.app
    ((coefficientSequenceLimit l E X).obj M, (coefficientSequenceLimit l E X).obj N)

/-- The expression language of this node has just variables, P, S, J and binary tensor.
The compact-support abbreviation in the dependency's larger language is expanded as
S J before using this predicate. Source: blueprint fix-prop-coherence, recursion step 6
(blueprint: lem-pur-integral-realization-recursion). -/
def BasicTree {B : Scheme.{u}} {I : Type u} {X : I → Over B} :
    {W : Over B} → Expression B I X W → Prop
  | _, .var _ => True
  | _, .pull _ e | _, .push _ _ e | _, .shriek _ _ _ e => BasicTree e
  | _, .tensor e t => BasicTree e ∧ BasicTree t
  | _, .compactSupport _ _ _ => False

/-- A family of natural comparisons on precisely the dependency's geometric and
admissible full input domains. Arbitrarily many independent slots can be used, and
the two tensor subtrees may use disjoint slots. Source: blueprint fix-prop-coherence,
recursion steps 5--7 (blueprint: lem-pur-integral-realization-recursion). -/
abbrev ComparisonFamily (D : FiniteFieldDatum.{u}) (o : Operations l E) :=
  ∀ {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))}
    (e : Expression _ I X W) (_g : e.geometric),
    e.realizationSource l E o ≅ e.realizationTarget l E o

/-- The displayed recursion equations, including the actual inverse-unit leaf
normalization, at every vertex of a tree. `inverseOrZero` is used only to give a
real ambient map; the theorem below asserts invertibility on the stipulated domains.
Source: blueprint fix-prop-coherence, recursion steps 3--6
(blueprint: lem-pur-integral-realization-recursion). -/
def Equations {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (r : Realizations l E D o) (c : ComparisonFamily l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))} :
    {W : Over (Spec (CommRingCat.of D.k))} → (e : Expression _ I X W) →
    (g : e.geometric) → (K : (e.domain l E o).FullSubcategory) → Prop
  | _, .var i, g, K =>
      (c (.var i) g).hom.app K =
        GeneratorReduction.inverseOrZero ((calculus l E (X i).left).adjunction.unit.app (K.obj i))
  | _, .pull f e, g, K =>
      (c (.pull f e) g).hom.app K =
        pullA l E f.left (e.systemObj l E o ((inputReduction l E X).obj K.obj)) ≫
        (integralDerivedPullback l E f.left).map
          ((c e g.2.2.2.2.2).hom.app ⟨K.obj, K.property.1, K.property.2.2⟩) ∧
      Equations r c e g.2.2.2.2.2 ⟨K.obj, K.property.1, K.property.2.2⟩
  | _, .push p hp e, g, K =>
      (c (.push p hp e) g).hom.app K =
        properA l E r p.left (e.systemObj l E o ((inputReduction l E X).obj K.obj)) ≫
        (PurCompactSupport.push (PurCompactSupport.completed l E) p.left).map
          ((c e g.2.2).hom.app ⟨K.obj, K.property.1, K.property.2.2⟩) ∧
      Equations r c e g.2.2 ⟨K.obj, K.property.1, K.property.2.2⟩
  | _, .shriek j hj hq e, g, K =>
      letI := hj
      (c (.shriek j hj hq e) g).hom.app K =
        openA l E r j.left (e.systemObj l E o ((inputReduction l E X).obj K.obj)) ≫
        (ringedOpen l E j.left).map
          ((c e g.2.2).hom.app ⟨K.obj, K.property.1, K.property.2.2⟩) ∧
      Equations r c e g.2.2 ⟨K.obj, K.property.1, K.property.2.2⟩
  | W, .tensor e t, g, K =>
      (c (.tensor e t) g).hom.app K =
        tensorA l E W.left
          (e.systemObj l E o ((inputReduction l E X).obj K.obj))
          (t.systemObj l E o ((inputReduction l E X).obj K.obj)) ≫
        (integralCompletedTensor l E W.left).map
          (Prod.mkHom
            ((c e g.2.2.1).hom.app ⟨K.obj, K.property.1, K.property.2.2.1⟩)
            ((c t g.2.2.2).hom.app ⟨K.obj, K.property.1, K.property.2.2.2⟩)) ∧
      Equations r c e g.2.2.1 ⟨K.obj, K.property.1, K.property.2.2.1⟩ ∧
      Equations r c t g.2.2.2 ⟨K.obj, K.property.1, K.property.2.2.2⟩
  | _, .compactSupport _ _ _, _, _ => True

/-- Invertibility and naturality of the specified operation comparisons on the
normalized common-bound domain. Naturality is equality of actual integral maps.
Source: blueprint fix-prop-coherence, recursion steps 1, 4, 5 and 7
(blueprint: lem-pur-integral-realization-recursion). -/
structure OperationLaws (D : FiniteFieldDatum.{u}) {o : Operations l E}
    (r : Realizations l E D o) : Prop where
  unit : ∀ (X : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (K : Integral l E X.left),
    sfIntegralConstructible l E X.left K →
    Good l E X.left ((calculus l E X.left).reduction.obj K) →
    IsIso ((calculus l E X.left).adjunction.unit.app K)
  counit : ∀ (X : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (M : System l E X.left),
    Good l E X.left M → IsIso ((calculus l E X.left).adjunction.counit.app M)
  pull_iso : ∀ {X Y : Over (Spec (CommRingCat.of D.k))} (f : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsSeparated f.left] [LocallyOfFiniteType f.left] [QuasiCompact f.left]
    (M : System l E Y.left), Good l E Y.left M →
    Good l E X.left ((pull l E f.left).obj M) → IsIso (pullA l E f.left M)
  proper_iso : ∀ {X Y : Over (Spec (CommRingCat.of D.k))} (p : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsProper p.left]
    (M : System l E X.left), Good l E X.left M →
    Good l E Y.left ((Operations.push l E o p.left).obj M) → IsIso (properA l E r p.left M)
  open_iso : ∀ {X Y : Over (Spec (CommRingCat.of D.k))} (j : X ⟶ Y)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    [IsOpenImmersion j.left] [QuasiCompact j.left] (M : System l E X.left),
    Good l E X.left M → Good l E Y.left ((Operations.shriek l E o j.left).obj M) →
    IsIso (openA l E r j.left M)
  tensor_iso : ∀ (X : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (M N : System l E X.left),
    Good l E X.left M → Good l E X.left N →
    Good l E X.left ((calculus l E X.left).systemClosed.tensor.obj (M, N)) →
    IsIso (tensorA l E X.left M N)

/-- The specified comparisons obey the leaf, unary and binary recursion, and these
identities characterize that family among natural isomorphisms. No shift law occurs.
Source: blueprint main-20261015, fix-prop-coherence.proof.md, coefficient transport
(blueprint: lem-pur-integral-realization-recursion).

Proof:
1. Normalized DVR effectivity identifies each evaluated actual counit with an
isomorphism. Derived evaluation detects isomorphisms, so e_M is invertible; its
levels give completeness, constructibility and the same common cohomological and
Tor bounds for L M. No equality detection by evaluation is used.
2. The right triangle gives L(e_M) u_(L M) = 1, hence u_(L M) is invertible.
The variable case of integralCompactificationSystemRealization gives an isomorphism
L R K to K. Naturality of the actual unit transports invertibility to u_K.
3. Start the canonical coefficient comparison at identity on R K. At a unary
vertex compose r_A with A of the child's comparison; at a tensor vertex use both
independent slots. Generator reduction coherence gives r_A = R(d_A inverse) e.
Transposing by the actual adjunction gives b_V = u_(I_V) L(q_V), and the inverse
transpose is q_V = R(b_V) e_M. The triangle identity identifies a single transpose
with d_A inverse, including the specified localized open comparison. At a leaf
b is the actual unit, so c is its inverse.
4. Substitute the inverse transposition in the unary coefficient composite.
Naturality of d gives b_AV = A_int(b_V) d_A(L M) inverse L A(e_M), in diagrammatic
order. Invert all factors to obtain exactly pullA, properA or openA followed by
A_int(c_V). The canonical proper adjoint conjugate transports its strict-tower
identification to the recorded integral proper image.
5. In the tensor calculation bifunctoriality factors the tensor of the two counit
composites. Naturality of the specified two-input d gives the same formula with
L(e_M tensor e_N); invert it to obtain tensorA followed by tensor(c_V,c_T).
6. Induct on the finite tree: the preceding calculations identify the specified
comparisons themselves, and determine any other family with the same recursion.
Use extensionality of natural transformations to obtain equality of natural isos.
7. Counit naturality, followed by functoriality and naturality of d, proves the
unary and binary comparison squares. Inverse-unit naturality starts the induction,
and pasting proves naturality in every independent input slot. -/
theorem integralRealizationRecursion (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    (o : Operations l E) (r : Realizations l E D o) :
    OperationLaws l E D r ∧
    (∀ {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
      {W : Over (Spec (CommRingCat.of D.k))} (e : Expression _ I X W)
      (g : e.geometric) (K : (e.domain l E o).FullSubcategory),
      BasicTree e → Equations l E r r.comparison e g K) ∧
    (∀ (c : ComparisonFamily l E D o),
      (∀ {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
        {W : Over (Spec (CommRingCat.of D.k))} (e : Expression _ I X W)
        (g : e.geometric) (K : (e.domain l E o).FullSubcategory),
        BasicTree e → Equations l E r c e g K) →
      ∀ {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
        {W : Over (Spec (CommRingCat.of D.k))} (e : Expression _ I X W)
        (g : e.geometric), BasicTree e → c e g = r.comparison e g) := by
  sorry

end Recursion
end WeilConjectures.IntegralSystemRealization
