/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W6
-/
module

public import Sheaf.Paper.DiagonalCoefficientDiagrams
public import Sheaf.Paper.DiagonalCoefficientPullback

/-! # Propagation of diagonal pullback through scalar extensions

Source: diagonal coefficient changes, paragraphs (1)--(3).
(blueprint: lem-diagonal-scalar-pullback-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Scalar-compatible families inherit geometric pullback from their Z_l
member, using the fixed Cartesian root comparisons at every coefficient stage.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraphs (1), (2) and the last
sentence of (3). (blueprint: lem-diagonal-scalar-pullback-compatibility).

Proof: For each finite E extend the Z_l pullback square to O_E. This is a
finite free extension: tensoring is exact and commutes with the relevant
products, derived limits and direct images. Paste with Family.toIntegral on
the two bases. The canonical scalar/pullback compositor and uniqueness of
adjoints identify the resulting endpoints with the coefficient unit and the
projection-normalized spIntegralComparison. The integral_inclusion equation
of the Cartesian comparisons, specialized from the bottom field, fixes the
root map. Uniqueness of adjunction mates identifies the three direct-image
comparisons with modelExchange, giving integral PullbackCompatibility.
Next use Family.toRational and localization at ell. Localization is a filtered
colimit on complexes with a common lower bound here, so bounded continuity
commutes it with the three direct images; inverse image preserves this
colimit. The rational_scalar equations of rootsP and rootsW fix the line maps.
Paste the scalar and geometric squares to obtain the rational comparisons and
their invertible mates. Finally use Family.toClosure and the filtered diagram
of finite intermediate fields. Family.rationalTransitions makes the diagrams
coherent. Exact filtered colimits and bounded continuity pass both the class
and all trace squares to the colimit. The qbar_coprojection equations identify
the resulting maps with rootsP.qbar and rootsW.qbar. All supported-source maps
are the canonical closed-support mates: their scalar and geometric pastings
agree by the adjunction units. No completed reference or choice of Cartier
boundary enters this scalar propagation argument. -/
theorem diagonalCoefficient_scalarPullback
    (l : ℕ) [Fact l.Prime] {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsNoetherian Y] [IsNoetherian Y']
    [∀ x : ProjectiveLine Y, Invertible (l : (ProjectiveLine Y).residueField x)]
    [∀ x : ProjectiveLine Y', Invertible (l : (ProjectiveLine Y').residueField x)]
    [∀ x : diagonalSurface Y, Invertible (l : (diagonalSurface Y).residueField x)]
    [∀ x : diagonalSurface Y', Invertible (l : (diagonalSurface Y').residueField x)]
    (family : Family l Y) (family' : Family l Y')
    (rootsP : CartesianAdicComparison l (baseP g))
    (rootsW : CartesianAdicComparison l (baseW g))
    (zl : PullbackCompatibility (Profinite.continuousMapRingObj.{u} ℤ_[l]) g
      (zlLine l) family.zl family'.zl
      (spIntegralComparison (baseP g) l (bottomField l))
      (spIntegralComparison (baseW g) l (bottomField l))) :
    (∀ E : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (PullbackCompatibility (Profinite.padicIntegersRingObj.{u} l E.1) g
        (fun X ↦ spIntegralTwist X l E) (family.integral E) (family'.integral E)
        (spIntegralComparison (baseP g) l E) (spIntegralComparison (baseW g) l E))) ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (PullbackCompatibility (Profinite.continuousMapRingObj.{u} E.1) g
        (fun X ↦ spRationalTwist X l E) (family.rational E) (family'.rational E)
        (rootsP.rational E) (rootsW.rational E))) ∧
    Nonempty (PullbackCompatibility (Profinite.padicAlgClRingObj.{u} l) g
      (fun X ↦ spQbarTwist X l) family.closure family'.closure rootsP.qbar rootsW.qbar) := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
