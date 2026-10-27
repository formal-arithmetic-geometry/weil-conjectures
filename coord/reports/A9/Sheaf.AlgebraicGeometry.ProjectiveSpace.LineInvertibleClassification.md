## What changed

Replaced the hole in `Sheaf.AlgebraicGeometry.ProjectiveSpace.LineInvertibleClassification`
by an explicit proof, with the original signature unchanged. The proof chooses chart frames,
compares their restrictions by a unit, rescales the first frame, constructs `TwistData`, and
uses the already proved source `TwistData.existsUnique_iso` to obtain the global isomorphism.
For uniqueness it pulls generators back through an arbitrary isomorphism, compares them with
unit multiples of the source generators, and uses naturality and free-generator injectivity
to derive the transition equation. No chosen data are defined using an unproved existence
statement.

Added four modules under `Sheaf.AlgebraicGeometry.ProjectiveSpace`:

- `StandardChartFrames`: proves `exists_standardChart_frames` using `polyEquivChart`, the
  polynomial PID instances, `invertible_sections_of_isAffineOpen`, `CommRing.Pic.mk_eq_one_iff`,
  and `isFreeGenerator_of_bijective_smul`. No hole.
- `OverlapUnitNormalization`: proves `exists_normalized_overlap_unit` from the concrete
  overlap coordinate lemma and the existing Laurent-unit theorem. It explicitly cancels the
  etale-section type tags and the GammaSpec unit map, then rescales by the inverse scalar.
- `TransitionDegreeSeparation`: proves `eq_degree_of_chart_units`. Polynomial chart units
  are constant; injective overlap evaluation reduces the relation to Laurent monomials;
  `degree_C_mul_T` proves equality of exponents. No hole.
- `OverlapLaurentCoordinates`: isolates the geometric coordinate identification as
  `bijective_overlap_laurent`. Its map is the actual `LaurentPolynomial.eval₂` at
  `ratioUnit 0 1`, with structural constants `chartConst`; it asserts no line-bundle
  classification, frame existence, or gluing.

The source read is Stacks `divisors.tex`, Tag 0BXJ,
`divisors-lemma-Pic-projective-space-UFD`, specialized to dimension one over a field.
The new coordinate lemma records the explicit degree-zero monomial argument, including
negative exponents. The unit record `sk-thm-sf-ctf-stability` and its route are unchanged.
The item is below that route; no unit-level statement or step is bypassed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProjectiveLine.existsUnique_degree_of_isInvertible`.

Added one hole, the entire proof of
`AlgebraicGeometry.ProjectiveLine.bijective_overlap_laurent`, in
`Sheaf.AlgebraicGeometry.ProjectiveSpace.OverlapLaurentCoordinates`, node
`lem-sfb-projective-line-overlap-laurent-coordinates`.

Thus this delivery is a decomposition: one upper hole closed and one strictly narrower
coordinate-ring hole added, for net zero direct holes. The other three new public theorems
and both private assembly lemmas are proved. The item module has zero textual holes.

Validation: lcompile.py --all compiled all five delivered modules successfully. Their
individual compilation times were 0.4, 3.2, 4.4, 4.1 and 4.9 seconds respectively
(coordinates, frames, normalization, degree separation, classification). All Lean lines
are at most 100 characters; node dependency lists equal the unions of proof-step uses.

Edge cases checked in the statements and arguments: arbitrary fields (including F_2),
zero and negative transition exponents, arbitrary invertible modules and choices of twists,
and nonunique module isomorphisms. Laurent evaluation uses z=x_0/x_1=t^-1, so its
exponent n is exactly the twist degree; the original convention g_0=t^-d g_1 is preserved.
The coordinate lemma concerns only a specified ring map, so it cannot supply an arbitrary
witness or a classification theorem by another name.

## No longer needed

Removed these direct proof imports from the item:
`Sheaf.AlgebraicGeometry.AffinePuncturedLineAlgebra`,
`WeilConjectures.AlgebraicGeometry.PicardFunctor`,
`WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator`,
`WeilConjectures.Topology.GlueSheavesOfModules`, and
`Mathlib.Algebra.Polynomial.Laurent`.
The affine unit theorem and Laurent algebra remain needed through the new lower modules;
free-generator operations remain needed through their source imports. This does not claim
these modules are globally unreachable.

The direct DAG dependencies `lem-pur-affine-punctured-line-algebra`,
`def-sc-picard-group`, `lem-weil-pbc-glue-sheaves-of-modules`, and
`def-weil-laurent-polynomial-ring` are replaced by the explicit helper nodes and the
proved source twist-comparison theorem. The affine-unit and Laurent nodes remain needed
below the helpers. The separate sheaf-gluing theorem is not used by this proof:
`TwistData.existsUnique_iso` already glues the maps and inverses via `glueHom`.
The original tool-use approvals are retained as inherited metadata. No existing module is
withdrawn and no global pruning count is claimed.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and transition sign were correct. The DAG plan did not expose
the Lean-level compatibility of the Laurent coordinate identification with `ratioUnit`
and structural scalar maps. This is now the precise remaining hole, rather than an
unnamed identification hidden inside a classification proof. Its explicit map distinguishes
it from the abstract Laurent unit computation already available in the library.

The general gluing step was already implemented by the proved source theorem
`TwistData.existsUnique_iso`; repeating sheaf morphism descent was unnecessary.
The chart Picard step can also be shortened: apply PID triviality directly to the section
module, then use the source affine free-generator theorem, without transporting the scheme
Picard group through a chart isomorphism.

## New nodes

`lem-sfb-projective-line-standard-chart-frames`, module `StandardChartFrames`, records the
proved affine-chart generator argument using the section-module Picard group of a PID.

`lem-sfb-projective-line-overlap-unit-normalization`, module `OverlapUnitNormalization`,
records the proved Laurent unit lifting and inverse-scalar rescaling.

`lem-sfb-projective-line-transition-degree-separation`, module `TransitionDegreeSeparation`,
records the proved reduction to equal Laurent degrees after proving chart units constant.

`lem-sfb-projective-line-overlap-laurent-coordinates`, module `OverlapLaurentCoordinates`,
is the sole split-off hole. Its proof identifies a degree-zero monomial with exponent vector
(m,-m) with z^m and gives the inverse on homogeneous fractions. This is strictly part of the
original node's chart computation; it has no sheaf-module or invertibility parameter.

All new nodes inherit the item's chapter and unit and retain its absent imported blueprint
ancestor. Searches used LeanSearch, LeanFinder/Loogle and grep; the returned Mathlib Laurent
localization results do not identify this concrete projective-space overlap map. No change
record is needed because no existing public signature, definition, instance, attribute or
public import was changed.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
