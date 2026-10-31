/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientFamilyPullback
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedPullbackCompatibility
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackCompatibility

/-! # Base change before taking uniformizer quotients

Source: coefficient changes, paragraphs (3a)--(3c).
(blueprint: lem-diagonal-nontorsion-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

private theorem residue_isUnit (l : ℕ) {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : IsUnit (l : Γ(S, ⊤))) (x : X) : IsUnit (l : X.residueField x) := by
  simpa only [map_natCast] using hS.map (f.appTop ≫ X.Γevaluation x).hom

/-- The non-torsion stages of base change, before any quotient assertion.
Source: blueprint paragraphs (3a)--(3c).
(blueprint: lem-diagonal-nontorsion-base-change). -/
structure NonTorsionPullback (l : ℕ) [Fact l.Prime] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y'] (family : Family l Y) (family' : Family l Y') where
  [invertibleP : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
  [invertibleP' : ∀ x : ProjectiveLine Y', Invertible (l : (ProjectiveLine Y').residueField x)]
  [invertibleW : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
  [invertibleW' : ∀ x : diagonalSurface Y', Invertible (l : (diagonalSurface Y').residueField x)]
  rootsP : CartesianAdicComparison l (baseP g)
  rootsW : CartesianAdicComparison l (baseW g)
  zl : PullbackCompatibility (Profinite.continuousMapRingObj.{u} ℤ_[l]) g
    (zlLine l) family.zl family'.zl
    (spIntegralComparison (baseP g) l (bottomField l))
    (spIntegralComparison (baseW g) l (bottomField l))
  integral : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    PullbackCompatibility (Profinite.padicIntegersRingObj.{u} l E.1) g
      (fun X ↦ spIntegralTwist X l E) (family.integral E) (family'.integral E)
      (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E)
  rational : ∀ E : PadicAlgCl.FiniteIntermediateField l,
    PullbackCompatibility (Profinite.continuousMapRingObj.{u} E.1) g
      (fun X ↦ spRationalTwist X l E) (family.rational E) (family'.rational E)
      (rootsP.rational E) (rootsW.rational E)
  closure : PullbackCompatibility (Profinite.padicAlgClRingObj.{u} l) g
    (fun X ↦ spQbarTwist X l) family.closure family'.closure rootsP.qbar rootsW.qbar

/-- Base change of the completed class and its trace splitting, followed by
the three non-torsion coefficient constructions. No uniformizer quotient
comparison is asserted.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraphs (3a)--(3c).
(blueprint: lem-diagonal-nontorsion-base-change).

Proof: The displayed BaseSquares give the three geometric diagrams. Pull the
Cartier two-term roof by the units map u to g*u and generator t^-1 to (g*t)^-1.
The diagonal equations a-b and the section equation t stay nonzerodivisors
over every base ring. The positive quotient generator remains +1. Exact inverse
image and the canonical tensor comparison therefore give one commuting diagram
of entire Kummer systems, retaining transitions ell in degree -1 and identity
in degree zero. Closed-support base change gives the supported-source endpoint.
For this source system and the root-line system, the normalized limit maps
are isomorphisms by their explicit limits. Apply naturality to the entire
Cartier diagram to compare the completed arrows. At finite levels the unit/Chern
splitting is natural. Its whole-system diagram passes through the derived
limit, and its coefficient and twist comparisons are isomorphisms. Invert the
splitting and project onto its trace summand; this proves all three completed
trace equations. References transport these equations to the fixed Z_ell
components. Finite-free extension, localization, and the filtered finite-field
colimit preserve these diagrams and give the integral, rational and closure
comparisons, with the roots fixed by CartesianAdicComparison. This only uses
the specified source and line systems, not arbitrary inverse-limit preservation. -/
theorem diagonalCoefficient_nonTorsionBaseChange (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)
    (Y Y' : Scheme.{u}) [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [IsNoetherian Y'] [IsNoetherian (ProjectiveLine Y')] [IsNoetherian (diagonalSurface Y')]
    (g : Y' ⟶ Y) [g.IsOver (Spec (.of k))]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y']
    [DiagonalTraceLocalizations l (ProjectiveLine Y')]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (_hcompletion : DiagonalCompletionSpec l (diagonalSurface Y) D)
    (_hsystem : DiagonalCycleSystemSpec l Y hY D)
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y')))
    (_hcompletion' : DiagonalCompletionSpec l (diagonalSurface Y') D')
    (_hsystem' : DiagonalCycleSystemSpec l Y' hY' D')
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (δ' : diagonalCompletedDomain l Y' ⟶ diagonalCompletedCodomain l Y')
    (_hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (_hδ' : DiagonalTrace.IsDiagonalLimit l Y' hY' D' δ')
    (geometry : BaseSquares g)
    (family : Family l Y) (family' : Family l Y')
    (_reference : Reference l Y δ family) (_reference' : Reference l Y' δ' family') :
    Nonempty (NonTorsionPullback l g family family') := by
  classical
  let : ∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x) :=
    fun x ↦ (residue_isUnit l (ProjectiveLine Y ↘ Y) hY x).invertible
  let : ∀ x : ProjectiveLine Y', Invertible (l : (ProjectiveLine Y').residueField x) :=
    fun x ↦ (residue_isUnit l (ProjectiveLine Y' ↘ Y') hY' x).invertible
  let : ∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x) :=
    fun x ↦ (residue_isUnit l
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y) ≫
        (ProjectiveLine Y ↘ Y)) hY x).invertible
  let : ∀ x : diagonalSurface Y', Invertible (l : (diagonalSurface Y').residueField x) :=
    fun x ↦ (residue_isUnit l
      (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y') ≫
        (ProjectiveLine Y' ↘ Y')) hY' x).invertible
  obtain ⟨rootsP⟩ :=
    ((cartesianCoefficients l (baseP g)).2.1 inferInstance inferInstance).2.2
  obtain ⟨rootsW⟩ :=
    ((cartesianCoefficients l (baseW g)).2.1 inferInstance inferInstance).2.2
  obtain ⟨zl⟩ := diagonalCoefficient_completedPullback l k p _hpl Y Y' g hY hY'
    D _hcompletion _hsystem D' _hcompletion' _hsystem' δ δ' _hδ _hδ'
    geometry family family' _reference _reference'
  obtain ⟨integral, rational, closure⟩ :=
    diagonalCoefficient_scalarPullback l g family family' rootsP rootsW zl
  exact ⟨{
    invertibleP := inferInstance
    invertibleP' := inferInstance
    invertibleW := inferInstance
    invertibleW' := inferInstance
    rootsP := rootsP
    rootsW := rootsW
    zl := zl
    integral := fun E ↦ (integral E).some
    rational := fun E ↦ (rational E).some
    closure := closure.some }⟩

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
