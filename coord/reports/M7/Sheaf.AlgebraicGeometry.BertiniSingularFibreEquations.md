## What changed

Replaced the hole in `AlgebraicGeometry.bertini_singular_fibre_equations` by a proof
from two separate geometric steps, without changing its signature or public imports.
`BertiniLocalFirstJets` defines the actual cotangent fibre and the value/differential
of an actual local regular function, and states the local spanning-and-rank step.
`BertiniSingularFibrePolynomialEquations` states the affine polynomial presentation
and its value/differential relations for an arbitrary finite family and arbitrary
local frame; it has no generation, immersion, or rank hypothesis.

The item constructs evaluation as the finite linear-combination map followed by
the cotangent basis equivalence, proves its surjectivity from the span, transports
the polynomial quotient using the symmetric algebra of the dual standard basis,
and expands dual vectors to prove the required equations. Its coordinate generators
agree with those of the polynomial quotient, so the original coefficient morphism
is preserved. The real constructions use no choice of data from an unproved
existence theorem: local frames and affine presentations are bound inside the
proof, and the public definitions are explicit germs and tensor differential germs.

Validation: both new modules compile on the project server (3.5 s and 3.9 s),
and the revised item compiles without errors or warnings (6.3 s). A direct text
comparison confirms the original theorem signature and all public imports are
unchanged. Node dependency unions, referenced ids, and the 100-character line
limit were checked.

## Proved and sorry left

One original hole closed: `AlgebraicGeometry.bertini_singular_fibre_equations`
(node `lem-zl-bertini-singular-fibre-equations`). The item module has zero holes.

Two holes added, each exactly a named public theorem in its own new module:

- `AlgebraicGeometry.exists_bertiniLocalFirstJets`
  (`lem-zl-bertini-local-first-jets`): local trivialization, cotangent rank and spanning.
- `AlgebraicGeometry.bertini_singular_fibre_polynomial_equations`
  (`lem-zl-bertini-singular-fibre-polynomial-equations`): affine fibre presentation
  and vanishing of the local polynomial equations on the reduced singular scheme.

This is a decomposition, not a completed geometric proof: one original hole is
replaced by two strictly separate geometric steps. Neither statement repeats the
original conclusion: the first contains no universal family or singular fibre;
the second contains no evaluation surjectivity, projective immersion, generation,
specified relative dimension, or symmetric algebra. The algebraic construction
combining them is proved in the item.

## No longer needed

Removed these direct proof imports from the item:

- `Sheaf.AlgebraicGeometry.ConormalSequenceSmoothImmersion`
- `Sheaf.AlgebraicGeometry.HypersurfaceNonzeroRelativeDifferential`
- `Sheaf.AlgebraicGeometry.SmoothDifferentialsFreeRankFibreDimension`
- `WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre`
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`
- `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`

Their mathematical roles are retained in the proof plans of the new geometric
steps. The item now uses the two new nodes directly; its old direct dependencies
are accounted for below these nodes. The symmetric-algebra identification also
cites the existing Mathlib leaf
`lem-weil-pbc-symmetric-algebra-free-module-polynomial`. No existing node or module is globally
pruned, and no source-library declaration is removed or changed. All original
public imports stay verbatim.

## Where the brief, the DAG or earlier work was wrong

The plan did not supply the bridge from the conormal and smooth-local-differential
APIs to actual coefficients of a local frame, nor the passage from pointwise
hypersurface smoothness to polynomial relations in the singular fibre ring.
Those are genuine geometric steps, now stated separately with actual coefficients
and full source-based proof descriptions. The existing
`immersiveSystem_source_first_jets` applies to closed points over an algebraically
closed field; this item needs arbitrary residue-field points and relative
cotangent fibres, so that theorem cannot be substituted directly.

The smoothness implication used here is one-way and does not assume flatness of
the universal zero scheme. The local-rank statement covers d=0. The quotient
statement allows an empty family and empty singular fibres (zero coordinate
ring), and it does not incorrectly assert that scheme-theoretic fibres of the
reduced singular scheme are themselves reduced. No target or existing definition
has changed. The unit's realized route is untouched.

## New nodes

`lem-zl-bertini-local-first-jets` realizes the local-frame, conormal spanning,
and cotangent-rank part of the existing plan (steps 1 and 2). Its explicit jet
construction uses the existing relative differential stalk fibre and universal
derivation, rather than unspecified first-order data.

`lem-zl-bertini-singular-fibre-polynomial-equations` realizes the affine
presentation and reduced-singular-scheme vanishing part (steps 3 and 4), with
polynomial equations in the original coefficient variables. Its assumptions are
strictly independent of the immersion and rank part.

No change records are required: only the item module, its proof node, and the two
new modules and their nodes are changed.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
