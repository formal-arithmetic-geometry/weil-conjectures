/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.Paper.A1LisseSectionEvaluation
public import Sheaf.Paper.LisseIntegralSmallCoefficients
public import Sheaf.Paper.CommonStageLocallyFree
import WeilConjectures.Mathlib.Topology.NoetherianSpace
import Sheaf.AlgebraicGeometry.ClosedPointField
import Sheaf.Paper.GaloisLisseRepresentations
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.Paper.LisseCompletedSystemComparison
import Sheaf.SixFunctors.FrobeniusPointTransportNatural
import WeilConjectures.SixFunctors.Etale.Derived.Adjunctions
import Sheaf.SixFunctors.FrobeniusPointTransport
import Sheaf.Paper.FrobeniusGeometricExchange
import Sheaf.SixFunctors.FrobeniusCohomologyTransport
import Sheaf.SixFunctors.FrobeniusCohomologyTransportIso
import Sheaf.Paper.CommonStageCompactWeilCohomology

/-! # Finite stalk detection and Frobenius compatibility of lisse sections

Source: Deligne, Weil II (1.1.6)--(1.1.14), pp. 150--153; blueprint
sec-deligne-laumon-a1/sk-l-dl-a1-endpoints/lem-a1-geometric-coinvariants-pure.proof.md,
second paragraph (blueprint: lem-a1-lisse-sections-stalk-evaluation).
The family may repeat a closed point with different residue-field embeddings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] A1SectionEvaluation.evaluation
  globalGeometricFrobeniusQbarOnCohomology

/-- Finite closed-point evaluation detects ordinary sections of a lisse Weil sheaf,
and every degree-d local Frobenius intertwines evaluation with T^d.
Source: Deligne, Weil II (1.1.6)--(1.1.14), pp. 150--153; the blueprint endpoint
proof, second paragraph (blueprint: lem-a1-lisse-sections-stalk-evaluation).
Proof:
1. Separated finite type is preserved by geometric base change
(lem-pod-separated-finite-type-base-change). The geometric scheme is Noetherian
(lem-weil-pbc-finite-type-over-noetherian), hence has Noetherian space
(lem-weil-pbc-noetherian-scheme-closed-subsets-minimal), and finitely many clopen
connected components (lem-sfb-noetherian-connected-components-open).
2. Each nonempty component has a closed point
(lem-sc-quasi-compact-kolmogorov-closed-point). Its residue field is k, and its image
in Y0 is closed by lem-kun-closed-point-field. Choose one lift per component;
different lifts may have the same image. On the empty scheme choose no points.
3. The system realization lem-per-lisse-completed-system-comparison and
lem-tw-lisse-rational-realization identify the lisse adic fibres with the actual
point fibres. A section is a morphism from the coefficient unit. On each component,
cor-galois-lisse-representations makes the fibre functor faithful. A section with
zero chosen evaluations is therefore zero on each component, hence zero globally.
4. The chosen stalks are finite dimensional by that same fibre equivalence.
The finite product is finite dimensional, so its injective section subspace is too.
5. The point-fibre equivalence, the ordinary pullback/direct-image adjunction
(fix-prop-adjunctions), and the pullback unit identify H^0 with ordinary sections.
Naturality of point transport (lem-weil-frobenius-point-transport-natural) and its
constant-unit normalization identify its effect on a section with pullback.
6. Expand the specified exchange mate into unit, square comparison and counit.
The triangular identities cancel the adjacent unit and counit, so ordinary global
transport is section pullback. This is a whole-system identity by
lem-coef-semilinear-derived-sections, preserved by localization and common-stage
realization (lem-tw-lisse-rational-realization). Thus T(v)=theta composed with g*v.
7. Induction gives T^r(v)=theta^[r] composed with (g^r)*v for every r>=1,
using the composition comparisons in def-weil-local-frobenius-trace.
8. Transport is invertible by lem-weil-frobenius-cohomology-transport-iso and the
Weil structure is an isomorphism; hence their composite T is a linear automorphism.
9. At a closed point of degree d, use the semilinear return g^d z=z h^d.
Naturality and preservation of 1 under iterated point transport identify the
pulled-back evaluation with I^[d], followed by the return comparison. Applying
theta^[d] gives precisely the defining local operator F_y, hence ev(T^d a)=F_y(ev a).
No Frobenius-stable integral lattice or connectedness is assumed. -/
theorem a1LisseSectionsStalkEvaluation
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    [IsSeparated Y₀.hom]
    (Ω : Type u) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    (c₀ : Compactification Y₀.hom) (G : sfCommonStageWeilSheaf D l hl Y₀ Ω)
    (_hG : @IsCommonStageLisse l _ Ω _ _ _ (D.geometricFiber Y₀).left
      (sfWeilPrimeInvertible D l hl Y₀) G.obj.carrier) :
    (∃ (m : ℕ) (y : Fin m → {y : Y₀.left // y ∈ closedPoints Y₀.left})
      (ι : ∀ i : Fin m, Y₀.left.residueField (y i).val →+* D.k)
      (hι : ∀ i : Fin m,
        (ι i).comp (Y₀.hom.residueFieldAlgebraMap (y i).val) = algebraMap D.k₀ D.k),
      Function.Injective (fun a : A1SectionEvaluation.sections D l hl Y₀ Ω c₀ G.obj ↦
        fun i : Fin m ↦
          A1SectionEvaluation.evaluation D l hl Y₀ Ω c₀ G.obj
            (localClosedPoint D Y₀ (y i) (ι i) (hι i))
            (pullback.lift_snd _ _ _) a)) ∧
    FiniteDimensional Ω (A1SectionEvaluation.sections D l hl Y₀ Ω c₀ G.obj) ∧
    IsIso (globalGeometricFrobeniusQbarOnCohomology D l hl Y₀ Ω c₀ G.obj false 0) ∧
    (∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
      (ι : Y₀.left.residueField y.val →+* D.k)
      (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k)
      (a : A1SectionEvaluation.sections D l hl Y₀ Ω c₀ G.obj),
      A1SectionEvaluation.evaluation D l hl Y₀ Ω c₀ G.obj
        (localClosedPoint D Y₀ y ι hι) (pullback.lift_snd _ _ _)
        (((globalGeometricFrobeniusQbarOnCohomology D l hl Y₀ Ω c₀ G.obj false 0).hom ^
          localClosedPointDegree D Y₀ y) a) =
      localQbarClosedFrobeniusStalk l Ω D hl Y₀ G.obj y ι hι
        (A1SectionEvaluation.evaluation D l hl Y₀ Ω c₀ G.obj
          (localClosedPoint D Y₀ y ι hι) (pullback.lift_snd _ _ _) a)) := by
  sorry

end WeilConjectures
