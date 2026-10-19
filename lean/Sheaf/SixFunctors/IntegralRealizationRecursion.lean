/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization
public import Sheaf.SixFunctors.GeneratorReductionStatement
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.PurNormalizedReconstructionAdjunctionCalculus
import Mathlib.Algebra.CharP.CharAndCard

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

private theorem inverseOrZero_eq_inv {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {A B : C} (f : A ⟶ B) [IsIso f] : GeneratorReduction.inverseOrZero f = inv f := by
  classical
  simp only [GeneratorReduction.inverseOrZero, dif_pos (inferInstance : IsIso f)]

private theorem prime_isUnit (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X : Over (Spec (CommRingCat.of D.k))) : IsUnit (l : Γ(X.left, ⊤)) := by
  let := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, D.card_base, D.cardinality_eq])
  have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
  have h : IsUnit (l : D.k) := (CharP.isUnit_natCast_iff D.prime).2
    (fun h ↦ hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 h).symm)
  let f := (Scheme.ΓSpecIso (CommRingCat.of D.k)).inv ≫ X.hom.appTop
  simpa only [map_natCast] using h.map f.hom

private theorem counit_isIso (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X : Over (Spec (CommRingCat.of D.k))) (M : System l E X.left)
    (hM : Good l E X.left M) : IsIso ((calculus l E X.left).adjunction.counit.app M) := by
  exact ((purNormalizedReconstruction l E X.left (prime_isUnit l D hl X)
    (calculus l E X.left)).1 M hM.1).2

private theorem unit_limit_isIso (X : Scheme.{u}) (M : System l E X)
    [IsIso ((calculus l E X).adjunction.counit.app M)] :
    IsIso ((calculus l E X).adjunction.unit.app ((coefficientSequenceLimit l E X).obj M)) := by
  exact isIso_of_comp_hom_eq_id _ ((calculus l E X).adjunction.right_triangle_components M)

private theorem unit_isIso {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (r : Realizations l E D o) (X : Over (Spec (CommRingCat.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (K : Integral l E X.left)
    (hK : sfIntegralConstructible l E X.left K)
    (hR : Good l E X.left ((calculus l E X.left).reduction.obj K)) :
    IsIso ((calculus l E X.left).adjunction.unit.app K) := by
  let inputs : ULift.{u} Unit → Over (Spec (CommRingCat.of D.k)) := fun _ ↦ X
  let e : Expression _ (ULift.{u} Unit) inputs X := .var ⟨()⟩
  have g : e.geometric := ⟨inferInstance, inferInstance, trivial⟩
  let A : (e.domain l E o).FullSubcategory :=
    ⟨fun _ ↦ K, (fun _ ↦ ⟨hK, hR⟩), hR, trivial⟩
  exact isIso_of_comp_hom_eq_id ((r.comparison e g).hom.app A)
    (r.inputNormalization (X := inputs) ⟨()⟩ g A)

private theorem openA_eq {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (r : Realizations l E D o) (hl : l ≠ D.p)
    {X Y : Over (Spec (CommRingCat.of D.k))} (j : X ⟶ Y)
    [IsOpenImmersion j.left] [QuasiCompact j.left] (M : System l E X.left)
    (hM : Good l E X.left M)
    (hJ : Good l E Y.left ((Operations.shriek l E o j.left).obj M)) :
    openA l E r j.left M = (r.openRealization j.left inferInstance M hM hJ).hom := by
  have := counit_isIso l E D hl X M hM
  have := counit_isIso l E D hl Y _ hJ
  have := unit_limit_isIso l E Y.left ((Operations.shriek l E o j.left).obj M)
  let h := r.openRealization j.left inferInstance M hM hJ
  have hu : IsIso ((calculus l E Y.left).adjunction.unit.app
      ((ringedOpen l E j.left).obj ((coefficientSequenceLimit l E X.left).obj M))) :=
    (NatTrans.isIso_app_iff_of_iso (calculus l E Y.left).adjunction.unit h).mp
      inferInstance
  dsimp only [openA, openD]
  rw [inverseOrZero_eq_inv, inverseOrZero_eq_inv]
  rw [← r.openNormalization j.left M hM hJ]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id,
    IsIso.inv_hom_id_assoc]

private theorem properA_eq {D : FiniteFieldDatum.{u}} {o : Operations l E}
    (r : Realizations l E D o) (hl : l ≠ D.p)
    {X Y : Over (Spec (CommRingCat.of D.k))} (p : X ⟶ Y)
    (M : System l E X.left) (hM : Good l E X.left M) :
    properA l E r p.left M = (r.realizationModel.push l E p.left).hom.app M := by
  have := counit_isIso l E D hl X M hM
  have := unit_limit_isIso l E X.left M
  have hi : GeneratorReduction.inverseOrZero
      ((calculus l E X.left).adjunction.unit.app
        ((coefficientSequenceLimit l E X.left).obj M)) =
      (coefficientSequenceLimit l E X.left).map
        ((calculus l E X.left).adjunction.counit.app M) := by
    rw [inverseOrZero_eq_inv]
    apply (cancel_epi ((calculus l E X.left).adjunction.unit.app
      ((coefficientSequenceLimit l E X.left).obj M))).1
    rw [IsIso.hom_inv_id]
    exact ((calculus l E X.left).adjunction.right_triangle_components M).symm
  dsimp only [properA, properD]
  rw [inverseOrZero_eq_inv, hi]
  have hn := (r.realizationModel.push l E p.left).hom.naturality
    ((calculus l E X.left).adjunction.counit.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  erw [← hn]
  simp only [IsIso.inv_hom_id_assoc, Functor.id_obj]

private theorem tensor_counit_isIso (X : Scheme.{u}) (M N : System l E X)
    [IsIso ((calculus l E X).adjunction.counit.app M)]
    [IsIso ((calculus l E X).adjunction.counit.app N)] :
    IsIso ((calculus l E X).systemClosed.tensor.map
      (Prod.mkHom ((calculus l E X).adjunction.counit.app M)
        ((calculus l E X).adjunction.counit.app N))) := by
  have : IsIso (Prod.mkHom ((calculus l E X).adjunction.counit.app M)
      ((calculus l E X).adjunction.counit.app N)) :=
    (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
  infer_instance

private theorem comparison_equations {D : FiniteFieldDatum.{u}} (hl : l ≠ D.p)
    {o : Operations l E} (r : Realizations l E D o)
    {I : Type u} [Finite I] {X : I → Over (Spec (CommRingCat.of D.k))}
    {W : Over (Spec (CommRingCat.of D.k))} (e : Expression _ I X W)
    (g : e.geometric) (K : (e.domain l E o).FullSubcategory) (hb : BasicTree e) :
    Equations l E r r.comparison e g K := by
  revert g K
  induction e with
  | var i =>
      intro g K
      have := isIso_of_comp_hom_eq_id ((r.comparison (.var i) g).hom.app K)
        (r.inputNormalization i g K)
      dsimp only [Equations]
      rw [inverseOrZero_eq_inv]
      exact IsIso.eq_inv_of_hom_inv_id (r.inputNormalization i g K)
  | @pull U V f e ih =>
      intro g K
      have hM := e.admissibleGood l E o _ K.property.2.2
      have := counit_isIso l E D hl V _ hM
      constructor
      · dsimp only [pullA]
        rw [inverseOrZero_eq_inv]
        apply (cancel_epi ((coefficientSequenceLimit l E U.left).map
          ((pull l E f.left).map ((calculus l E V.left).adjunction.counit.app
            (e.systemObj l E o ((inputReduction l E X).obj K.obj)))))).1
        rw [Category.assoc, IsIso.hom_inv_id_assoc]
        exact r.pull f e g.2.2.2.2.2 g K
      · exact ih hb g.2.2.2.2.2 _
  | @push U V p hp e ih =>
      intro g K
      constructor
      · rw [properA_eq l E r hl p _ (e.admissibleGood l E o _ K.property.2.2)]
        exact r.push p hp e g.2.2 g K
      · exact ih hb g.2.2 _
  | @shriek U V j hj hq e ih =>
      intro g K
      have := hj
      have := hq
      constructor
      · rw [openA_eq l E r hl j _ (e.admissibleGood l E o _ K.property.2.2)
          K.property.2.1]
        exact r.shriek j e g.2.2 g K
      · exact ih hb g.2.2 _
  | @tensor W e t ihe iht =>
      intro g K
      have := counit_isIso l E D hl W _
        (e.admissibleGood l E o _ K.property.2.2.1)
      have := counit_isIso l E D hl W _
        (t.admissibleGood l E o _ K.property.2.2.2)
      have := tensor_counit_isIso l E W.left
        (e.systemObj l E o ((inputReduction l E X).obj K.obj))
        (t.systemObj l E o ((inputReduction l E X).obj K.obj))
      refine ⟨?_, ihe hb.1 g.2.2.1 _, iht hb.2 g.2.2.2 _⟩
      dsimp only [tensorA]
      rw [inverseOrZero_eq_inv]
      apply (cancel_epi ((coefficientSequenceLimit l E W.left).map
        ((calculus l E W.left).systemClosed.tensor.map
          (Prod.mkHom
            ((calculus l E W.left).adjunction.counit.app
              (e.systemObj l E o ((inputReduction l E X).obj K.obj)))
            ((calculus l E W.left).adjunction.counit.app
              (t.systemObj l E o ((inputReduction l E X).obj K.obj))))))).1
      rw [Category.assoc, IsIso.hom_inv_id_assoc]
      exact r.tensor e t g.2.2.1 g.2.2.2 g K
  | compactSupport f c e ih => exact hb.elim

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
  classical
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro X _ _ K hK hR
      exact unit_isIso l E r X K hK hR
    · intro X _ _ M hM
      exact counit_isIso l E D _hl X M hM
    · intro X Y f _ _ _ _ _ _ _ M hM _
      have := counit_isIso l E D _hl Y M hM
      dsimp only [pullA]
      rw [inverseOrZero_eq_inv]
      infer_instance
    · intro X Y p _ _ _ _ _ M hM _
      rw [properA_eq l E r _hl p M hM]
      infer_instance
    · intro X Y j _ _ _ _ _ _ M hM hJ
      rw [openA_eq l E r _hl j M hM hJ]
      infer_instance
    · intro X _ _ M N hM hN _
      have := counit_isIso l E D _hl X M hM
      have := counit_isIso l E D _hl X N hN
      have := tensor_counit_isIso l E X.left M N
      dsimp only [tensorA]
      rw [inverseOrZero_eq_inv]
      infer_instance
  · intro I _ X W e g K hb
    exact comparison_equations l E _hl r e g K hb
  · intro c hc I _ X W e
    induction e with
    | var i =>
        intro g hb
        apply Iso.ext
        apply NatTrans.ext
        funext K
        exact (hc (.var i) g K hb).trans
          (comparison_equations l E _hl r (.var i) g K hb).symm
    | pull f e ih =>
        intro g hb
        apply Iso.ext
        apply NatTrans.ext
        funext K
        have hchild := congrArg (fun q => q.hom.app
          ⟨K.obj, K.property.1, K.property.2.2⟩)
          (ih g.2.2.2.2.2 hb)
        rw [(hc (.pull f e) g K hb).1,
          (comparison_equations l E _hl r (.pull f e) g K hb).1, hchild]
    | push p hp e ih =>
        intro g hb
        apply Iso.ext
        apply NatTrans.ext
        funext K
        have hchild := congrArg (fun q => q.hom.app
          ⟨K.obj, K.property.1, K.property.2.2⟩)
          (ih g.2.2 hb)
        rw [(hc (.push p hp e) g K hb).1,
          (comparison_equations l E _hl r (.push p hp e) g K hb).1, hchild]
    | shriek j hj hq e ih =>
        intro g hb
        apply Iso.ext
        apply NatTrans.ext
        funext K
        have hchild := congrArg (fun q => q.hom.app
          ⟨K.obj, K.property.1, K.property.2.2⟩)
          (ih g.2.2 hb)
        rw [(hc (.shriek j hj hq e) g K hb).1,
          (comparison_equations l E _hl r (.shriek j hj hq e) g K hb).1, hchild]
    | tensor e t ihe iht =>
        intro g hb
        apply Iso.ext
        apply NatTrans.ext
        funext K
        have he := congrArg (fun q => q.hom.app
          ⟨K.obj, K.property.1, K.property.2.2.1⟩)
          (ihe g.2.2.1 hb.1)
        have ht := congrArg (fun q => q.hom.app
          ⟨K.obj, K.property.1, K.property.2.2.2⟩)
          (iht g.2.2.2 hb.2)
        rw [(hc (.tensor e t) g K hb).1,
          (comparison_equations l E _hl r (.tensor e t) g K hb).1,
          he, ht]
    | compactSupport f cf e ih =>
        intro _ hb
        exact hb.elim

end Recursion
end WeilConjectures.IntegralSystemRealization
