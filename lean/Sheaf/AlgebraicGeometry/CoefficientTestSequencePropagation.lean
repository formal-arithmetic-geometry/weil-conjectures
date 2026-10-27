/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelPresentation
public import Sheaf.AlgebraicGeometry.RegularHilbertCoefficientDatum
public import Sheaf.AlgebraicGeometry.CommonPowerHilbertMarking
public import Sheaf.AlgebraicGeometry.EtaleCoordinateFlag
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Field.ULift

import Sheaf.AlgebraicGeometry.FormalCoefficientTransformCriterion
import Sheaf.AlgebraicGeometry.ImplicitTaylorCoordinateCalculus
import Sheaf.AlgebraicGeometry.JetDiagramHilbertControl
import Sheaf.AlgebraicGeometry.MarkedControlledBlowupCharts
import Sheaf.AlgebraicGeometry.PermissibleCoordinateChart
import Sheaf.AlgebraicGeometry.EtaleLocalNormalForm

/-! # Propagation of regular Hilbert coefficients through finite tests

Source: ILO VIII 2.3.11--2.3.13, pp. 93--94; BM 1997, Definition 6.2, (6.1),
Theorems 7.20--7.21 and proof of Theorem 9.4; BMT 5.2 and 6.2--6.3
(blueprint: lem-trf-coefficient-test-sequence-propagation).

Coefficient functions can acquire exceptional unit transition factors. Their principal
ideal sheaves therefore record the global transforms, while local regular Taylor data
record the five division and Jacobian conditions. No global choice of exceptional equation
or of a Taylor chart is made. All geometric tests use the existing `HilbertSamuel.Step`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.HilbertCoefficient

/-- Initial coefficient charts, identified with the supplied objects by isomorphisms over
one open restriction of that chart. The source and support are its actual cartesian
pullbacks, and the ideal is the restriction of the supplied common-power ideal.
Source: BM 1997, Definition 6.2 and (6.1)
(blueprint: lem-trf-coefficient-test-sequence-propagation). -/
structure InitialCoefficientTestModel
    {X Z : Scheme.{u}} {p : Z ⟶ Spec (.of (ULift.{u} ℚ))} {i : X ⟶ Z}
    {a : X} {m n s Q : ℕ} {α : Fin s → Fin n →₀ ℕ}
    (D : RegularHilbertCoefficientDatum p i a m n s α Q) (V : D.U.Opens) (b : ℕ) where
  ambient : HilbertSamuel.Embedded (ULift.{u} ℚ)
  marked : HilbertSamuel.Marked ambient
  ambientIso : ambient.Z ≅ V.toScheme
  sourceIso : ambient.X ≅ pullback i (V.ι ≫ D.e)
  supportIso : marked.N ≅ (D.j ⁻¹ᵁ V).toScheme
  base : ambient.p = ambientIso.hom ≫ V.ι ≫ D.e ≫ p
  embedding : ambient.i ≫ ambientIso.hom = sourceIso.hom ≫ pullback.snd i (V.ι ≫ D.e)
  support : marked.j ≫ ambientIso.hom = supportIso.hom ≫ (D.j ∣_ V)
  level : ambient.level = HilbertSamuel.function (i ≫ p) a
  boundary : ambient.boundary = []
  marking : marked.marking = b
  ideal : marked.ideal = (commonPowerIdeal α D.coeff b).comap
    (supportIso.hom ≫ (D.j ⁻¹ᵁ V).ι)

/-- Principal coefficient ideals of the initial model, pulled through its specified support
isomorphism. This does not define a second marked coefficient ideal.
Source: BM 1997, (6.1), Theorem 7.20
(blueprint: lem-trf-coefficient-test-sequence-propagation). -/
def InitialCoefficientTestModel.coefficients
    {X Z : Scheme.{u}} {p : Z ⟶ Spec (.of (ULift.{u} ℚ))} {i : X ⟶ Z}
    {a : X} {m n s Q : ℕ} {α : Fin s → Fin n →₀ ℕ}
    {D : RegularHilbertCoefficientDatum p i a m n s α Q} {V : D.U.Opens} {b : ℕ}
    (A : InitialCoefficientTestModel D V b) (l : Fin s) (γ : Fin n →₀ ℕ) :
    A.marked.N.IdealSheafData :=
  (Scheme.IdealSheafData.ofIdealTop (Ideal.span {D.coeff l γ})).comap
    (A.supportIso.hom ≫ (D.j ⁻¹ᵁ V).ι)

/-- The five conditions at every retaining-level point are supplied on an actual pointed
étale chart of that point. The coefficient scheme is the cartesian inverse image of the
current support. Its coefficient ideals are the current ones, with the same vertices and
jet bound. The labelled boundary consists of distinct coefficient-coordinate hyperplanes;
a label absent from the chart is represented by the unit ideal.
Source: BM 1997, Theorems 7.20--7.21 and proof of Theorem 9.4
(blueprint: lem-trf-coefficient-test-sequence-propagation). -/
def HasRetainedCoefficientCharts {n s : ℕ} (α : Fin s → Fin n →₀ ℕ) (Q : ℕ)
    (S : HilbertSamuel.Embedded (ULift.{u} ℚ)) (M : HilbertSamuel.Marked S)
    (C : Fin s → (Fin n →₀ ℕ) → M.N.IdealSheafData) : Prop :=
  ∀ x : S.X, HilbertSamuel.function (S.i ≫ S.p) x = S.level →
    ∃ (m : ℕ) (D : RegularHilbertCoefficientDatum S.p S.i x m n s α Q)
      (q : D.N ⟶ M.N) (labels : Fin S.boundary.length → Option (Fin m)),
      IsPullback q D.j M.j D.e ∧
      (∀ (l : Fin s) (γ : Fin n →₀ ℕ),
        (C l γ).comap q = Scheme.IdealSheafData.ofIdealTop (Ideal.span {D.coeff l γ})) ∧
      (∀ j : Fin S.boundary.length, (S.boundary.get j).comap D.e = match labels j with
        | none => ⊤
        | some h => Scheme.IdealSheafData.ofIdealTop
            (Ideal.span {D.coord (MvPolynomial.X (Sum.inl h))})) ∧
      (∀ (j k : Fin S.boundary.length) (h : Fin m),
        labels j = some h → labels k = some h → j = k)

/-- Exact coefficient transformation across a geometric test. The commuting support map
is the unique map induced by the closed embeddings. For a smooth-center blowup, positive
weights divide by the exceptional power; nonpositive weights multiply. For the other two
tests every coefficient ideal is an ordinary pullback.
Source: BM 1997, (6.1), Theorems 7.20--7.21
(blueprint: lem-trf-coefficient-test-sequence-propagation). -/
def CoefficientsTransform {n s : ℕ} (α : Fin s → Fin n →₀ ℕ)
    {S T : HilbertSamuel.Embedded (ULift.{u} ℚ)} (t : HilbertSamuel.Step S T)
    (M : HilbertSamuel.Marked S) (M' : HilbertSamuel.Marked T)
    (C : Fin s → (Fin n →₀ ℕ) → M.N.IdealSheafData)
    (C' : Fin s → (Fin n →₀ ℕ) → M'.N.IdealSheafData) : Prop :=
  t.Transforms M M' ∧ ∃ q : M'.N ⟶ M.N, q ≫ M.j = M'.j ≫ t.π ∧
    ∀ (l : Fin s) (γ : Fin n →₀ ℕ),
      if t.kind = .admissibleBlowup then
        if γ.degree < (α l).degree then
          C' l γ * (t.center.comap (M'.j ≫ t.π)) ^ ((α l).degree - γ.degree) =
            (C l γ).comap q
        else C' l γ = (C l γ).comap q *
          (t.center.comap (M'.j ≫ t.π)) ^ (γ.degree - (α l).degree)
      else C' l γ = (C l γ).comap q

/-- Finite-test propagation, including the existence of each next transform and all choices
of such transforms. Depth zero already includes ambient cosupport equality, the global
upper bound, the common-power identity, boundary transversality everywhere, and the five
conditions at retaining points. Recursion uses precisely the existing three test types.
Source: BM 1997, Definition 6.2; BMT 5.2 and 6.2
(blueprint: lem-trf-coefficient-test-sequence-propagation). -/
def CoefficientTestsThrough {n s : ℕ} (α : Fin s → Fin n →₀ ℕ) (Q : ℕ) :
    ℕ → (S : HilbertSamuel.Embedded (ULift.{u} ℚ)) → (M : HilbertSamuel.Marked S) →
      (Fin s → (Fin n →₀ ℕ) → M.N.IdealSheafData) → Prop
  | d, S, M, C =>
    M.cosupport = S.locus ∧
    (∀ (T : HilbertSamuel.Embedded (ULift.{u} ℚ)) (t : HilbertSamuel.Step S T),
      t.Admissible S.locus ↔ t.Admissible M.cosupport) ∧
    (∀ x : S.X, HilbertSamuel.le (HilbertSamuel.function (S.i ≫ S.p) x) S.level) ∧
    M.ideal = ⨆ (l : Fin s) (γ : Fin n →₀ ℕ) (_ : γ.degree < (α l).degree),
      C l γ ^ (M.marking / ((α l).degree - γ.degree)) ∧
    HasEtaleCoordinateFlag S.p M.j.ker M.j.ker S.boundary ∧
    HasRetainedCoefficientCharts α Q S M C ∧
    match d with
    | 0 => True
    | d + 1 => ∀ (T : HilbertSamuel.Embedded (ULift.{u} ℚ)) (t : HilbertSamuel.Step S T),
        t.Admissible S.locus →
        (∃ (M' : HilbertSamuel.Marked T)
          (C' : Fin s → (Fin n →₀ ℕ) → M'.N.IdealSheafData),
          CoefficientsTransform α t M M' C C') ∧
        ∀ (M' : HilbertSamuel.Marked T)
          (C' : Fin s → (Fin n →₀ ℕ) → M'.N.IdealSheafData),
          CoefficientsTransform α t M M' C C' → CoefficientTestsThrough α Q d T M' C'

/-- Complete finite-test propagation of the supplied regular coefficient data, and its
compatibility with every smooth pullback on every constant-relative-dimension piece.
Choose one open V containing the supplied center, as in commonPowerHilbertMarking.
All models, ideals, finite tests and smooth pullbacks start on this same restriction.
Further open restriction is the relative-dimension-zero case, including identity maps.
Source: ILO VIII 2.3.11--2.3.13; BM 1997, Definition 6.2, (6.1), Theorems 7.20--7.21;
BMT 5.2 and 6.2--6.3 (blueprint: lem-trf-coefficient-test-sequence-propagation).

Proof:
1. Start with L = H_X(a), the supplied upper bound and five conditions. The jet bound
   Q >= d_i - 1 is the hypothesis of common-power-hilbert-marking. That node identifies
   initial cosupport on one open V containing D.center and proves coherence, also for
   the empty list and marking one. Restrict X, N and all coefficient ideals to V once.
2. Homogeneous-continuous-formal-division gives block triangular division matrices in
   coefficient-variable degree. Store pure-transverse initial forms, supported identities
   for every Z^beta f_i, and conditions (4),(5) as identities of series at the source point.
3. For a permissible blowup, marked-controlled-blowup-charts supplies smooth transforms,
   the labelled boundary and controlled ideal. Common-power-hilbert-marking gives the
   equality locus, upper bound and exclusion of equality on charts missing N'.
4. Coordinate-blowup-division-generators generates the actual saturated ideal by
   e^(-d_i) sigma*f_i on the entire exceptional fibre. Its filtration bounds make every
   stored supported multiplication identity regular, retaining the same quotient supports.
5. Implicit-Taylor-coordinate-calculus transports (4),(5); saturation by e contracts (5).
   The pure-transverse initial forms on e = 0 are the stored source forms, even below L.
6. For a line product, formal-coefficient-transform-criterion and jet-diagram-hilbert-control
   adjoin a free relative Taylor variable at every point and sum H once. Coefficients pull
   back and the new zero-section equation is an independent coefficient coordinate.
7. Trace boundary germs backwards: either their charts are free-coordinate products over
   an earlier X, or they lie over the last relevant permissible center. In the second case
   retain the identities of steps 4--5 on the whole fibre, not only its equality locus.
8. Permissible-coordinate-chart describes a boundary blowup by W_1=e, W_2=eu and its
   other chart. Pull back X,N and coefficients ordinarily. Stored pure-transverse forms
   give prefix division (1),(2), while the identities (4),(5) persist.
9. Supported polynomial multiples remain supported sums. Closedness from homogeneous
   continuous formal division extends this to formal multipliers, proving (3) at every
   new order point, including one above an intermediate lower-level point.
10. At a point outside the new order locus, the first dropping block has a nonzero
    degree-m remainder independent of all earlier prefix columns by (5) and Q >= m.
    Thus H drops lexicographically. Away from N' use the first nonzero transverse row.
11. The current common-power identity equates its order locus with marked cosupport.
    Steps 9--10 identify this with the retaining locus and make the datum available
    before any next permissible blowup, including when the cosupport is empty.
12. This proves every finite depth and equality of all allowed next smooth centers;
    the existing PresentsThrough predicate then gives Presents for the marked datum.
13. The first differing index and its sign survive inclusive summation; induction proves
    preservation and reflection of equality and both lexicographic inequalities for r sums.
14. Etale-local-normal-form factors any smooth map through affine r-space and an etale
    map. Jet-diagram-hilbert-control and implicit Taylor calculus give the numerical
    formula and pull back the actual coefficient identities, retaining all relative variables.
15. Run the finite-test induction on each relative-dimension piece; the same cartesian
    and exceptional-power identities restrict to every open, with no unsummed identification.
-/
theorem coefficient_test_sequence_propagation {X Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of (ULift.{u} ℚ))) (i : X ⟶ Z)
    [Smooth p] [IsClosedImmersion i] [IsReduced X]
    [LocallyOfFiniteType (i ≫ p)] [QuasiCompact (i ≫ p)] (a : X)
    {m n s Q : ℕ} (α : Fin s → Fin n →₀ ℕ) (hα : orderedVertices α)
    (hQ : ∀ l : Fin s, (α l).degree - 1 ≤ Q)
    (hbound : ∀ x : X, HilbertSamuel.le (HilbertSamuel.function (i ≫ p) x)
      (HilbertSamuel.function (i ≫ p) a))
    (D : RegularHilbertCoefficientDatum p i a m n s α Q)
    (b : ℕ) (hb : 0 < b) (hempty : s = 0 → b = 1)
    (hcommon : ∀ (l : Fin s) (γ : Fin n →₀ ℕ), γ.degree < (α l).degree →
      (α l).degree - γ.degree ∣ b) :
    (∃ V : D.U.Opens, D.center ∈ V ∧
      Nonempty (InitialCoefficientTestModel D V b) ∧
      (∀ A : InitialCoefficientTestModel D V b,
        (∀ d : ℕ, CoefficientTestsThrough α Q d A.ambient A.marked A.coefficients) ∧
        HilbertSamuel.Presents A.marked ∧
        ∀ (T : HilbertSamuel.Embedded (ULift.{u} ℚ)) (f : T.Z ⟶ A.ambient.Z) (r : ℕ),
          HilbertSamuel.Pullback f r →
          (∀ (g : T.X ⟶ A.ambient.X), IsPullback g T.i A.ambient.i f →
            ∀ y : T.X, HilbertSamuel.function (T.i ≫ T.p) y =
              (HilbertSamuel.summation^[r])
                (HilbertSamuel.function (A.ambient.i ≫ A.ambient.p) (g y))) ∧
          (∃ (P : HilbertSamuel.Marked T) (q : P.N ⟶ A.marked.N),
            HilbertSamuel.MarkedPullback f A.marked P ∧ IsPullback q P.j A.marked.j f) ∧
          ∀ (P : HilbertSamuel.Marked T) (q : P.N ⟶ A.marked.N),
            HilbertSamuel.MarkedPullback f A.marked P → IsPullback q P.j A.marked.j f →
            HilbertSamuel.Presents P ∧
            ∀ d : ℕ, CoefficientTestsThrough α Q d T P
              (fun l γ ↦ (A.coefficients l γ).comap q))) ∧
    (∀ (r : ℕ) (F G : ℕ → ℕ),
      ((HilbertSamuel.summation^[r]) F = (HilbertSamuel.summation^[r]) G ↔ F = G) ∧
      (HilbertSamuel.lt ((HilbertSamuel.summation^[r]) F)
        ((HilbertSamuel.summation^[r]) G) ↔ HilbertSamuel.lt F G) ∧
      (HilbertSamuel.le ((HilbertSamuel.summation^[r]) F)
        ((HilbertSamuel.summation^[r]) G) ↔ HilbertSamuel.le F G)) := by
  sorry

end AlgebraicGeometry.HilbertCoefficient
