## What changed

Replaced the sole partial `sorry` in
`AlgebraicGeometry.WeilSheaf.IsReal.isMixed` with a compiling proof from
`Sheaf.DeligneLaumon.SmoothAffineConstituentPurity`, imported privately.
All existing source-library signatures, attributes, public imports, definitions,
and proved declarations are preserved verbatim.

The proof applies the existing Noetherian induction. On a reduced nonempty base,
it intersects the dense lisse open with the dense smooth locus, chooses an affine
neighborhood, and proves smoothness and lissity of the restriction. It constructs
an actual Jordan--Hölder filtration using the already proved source-library
`IsLisse.exists_filtration_isIrreducibleLisse`, maps its terms monomorphically into
the restricted sheaf using `exists_mono_of_chain`, and applies the new purity lemma
to each quotient. The sum of the absolute values of their weights is a common
upper bound, including a zero-length filtration. The proved Noetherian induction
then performs open--closed gluing and reduction recovery.

The new statement isolates one irreducible subquotient on a smooth affine base.
Its proof plan follows the current blueprint's geometric-constituent and anchored
curve argument, adds the Frobenius-orbit argument identifying the constituent
weights for a simple Weil object, and descends punctual purity by residue powers.
This is strictly a part of the full theorem: it neither constructs a filtration
of a general constructible sheaf nor handles singular strata or gluing.

Validation: both delivered Lean modules compiled through lcompile.py. The main
module's revised proof compiled without warnings. Edge cases checked: zero sheaf
(empty Jordan--Hölder filtration, upper bound zero); empty base (handled by the
existing induction, and incompatible with the lower lemma's nonzero irreducible
quotient); disconnected smooth affine base (a simple lisse quotient is supported
on one connected component); dimension zero (a Frobenius eigenline over a finite
field); nonsemisimple ambient sheaf (the existing filtration and exact stalks do
not assume semisimplicity); nilpotents (the existing reduced-closed induction).

## Proved and sorry left

Original item: 1 hole. Current item: 0 holes.

Closed, by decomposition:
`AlgebraicGeometry.WeilSheaf.IsReal.isMixed`
(node `thm-zl-real-mixed-by-curves`). Its combination proof is complete.

Added and remaining: 1 hole,
`AlgebraicGeometry.WeilSheaf.IsReal.exists_isPunctuallyPureOfWeight_cokernel_of_smooth_affine`
(node `lem-zl-smooth-affine-constituent-purity`), in the new module
`Sheaf.DeligneLaumon.SmoothAffineConstituentPurity`.

Thus this delivery closes one upper hole and adds one strictly smaller lower
hole: it is a decomposition, with net hole reduction zero, not a completed proof
of the geometric constituent argument. No sorry is left in a definition, local
have, anonymous function or private declaration.

## No longer needed

No imports removed, no modules withdrawn, and no pruning claimed. In particular,
`Sheaf.DeligneLaumon.ProEtaleIrreducibilityDetector` remains needed by the already
proved curve-testing declaration in this same source module.

For the outer assembly, the raw-heart generic-stratification, finite-frontier,
and gluing declarations
`lem-zl-raw-heart-adic-lisse-stratification`,
`lem-zl-smooth-affine-frontier-stratification`, and
`lem-zl-reduced-frontier-mixed-gluing` are not directly invoked: the source
category already has generic lissity and the entire Noetherian gluing induction
proved. Their unit-level mathematical steps are retained by these source proofs;
this is not a withdrawal of those declarations or modules. No conclusion about
their use by other targets is made. The finite constant-extension comparison,
classical filtration transport, geometric constituents, anchored two-point
purity and point flags remain in the lower constituent lemma's proof plan and
are not claimed pruned. No dependency of the proved curve-testing declaration
is removed.

## Where the brief, the DAG or earlier work was wrong

The remaining hole was embedded in the function argument to the already proved
Noetherian induction, rather than being a whole named theorem proof. The
replacement removes that partial-proof hole.

The node's dependency records now describe the newer raw/common-stage
`WeilConjectures.sfCommonStageWeilSheaf` formalism. For example,
`zl_classical_weil_filtration_heart_transport`, `constantExtensionMixedDescent`,
`twoPointCurveConstituentPurity`, `raw_heart_adic_lisse_stratification`,
`zl_point_weil_heart_flag`, and `zlReducedFrontierMixedGluing` take that category,
whereas this source module takes `AlgebraicGeometry.WeilSheaf` with pro-etale
carriers over `PadicAlgCl l`. They are not definitionally interchangeable.
I read their signatures and did not apply them to objects of another category
or identify the models without a theorem. The source-category constituent step
is therefore explicit as a lower statement. Its future proof must implement
the comparison, or prove the same anchored argument directly for source sheaves.
The raw model's normalization and finite-stage transport work is not silently
asserted by the current assembly.

The binding unit's lisse restriction, finite Weil filtration, geometric
constituents, curve purity with a common weight, descent, dimension-zero case,
and open--closed induction remain the mathematical route. Already proved source
lemmas implement the outer portions; the lower statement records the geometric
portions still pending. Existing module docstrings describing TODOs are preserved
as required by the source-library boundary; this report records the new state.

## New nodes

`lem-zl-smooth-affine-constituent-purity`, in
`dag/nodes/sec-deligne-laumon-general/`, states punctual purity of one irreducible
lisse subquotient of a real lisse sheaf on a smooth affine finite-type base. Its
source is the current blueprint real-mixed-by-curves proof, paragraphs 1--5 and
the point case in paragraph 7. It has a complete proof in words both in the node
and in its Lean docstring, and actual logged LeanSearch, LeanFinder and grep
searches. Whole-blueprint searches found no arbitrary-dimensional version of
this source-category statement; the curve version is already proved and is
cited. No existing signature or definition changed, so no adaptation or change
record is required.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
