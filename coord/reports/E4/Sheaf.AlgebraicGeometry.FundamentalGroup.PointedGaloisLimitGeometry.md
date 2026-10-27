## What changed

Proved `AlgebraicGeometry.Scheme.UniversalCover.exists_pointedGaloisLimitGeometry`
in the assigned module, with its signature and public imports unchanged. The two
published section-diagram definitions are unchanged. All helpers are private and
proved; no additional public API or module is introduced.

The proof constructs the stabilizer functor from the published small category of
pointed Galois covers to open normal subgroups. Normality follows from the commuting
actions of cover automorphisms and the fundamental group. Conversely, normality
makes every point stabilizer equal, and the existing pointed classification gives
transitivity of cover automorphisms. Full faithfulness lifts the explicit quotient
maps, and realization of open subgroups proves essential surjectivity. The inverse
equivalence has exactly the marked quotient labels in the theorem.

The remaining categorical and geometric clauses reuse the fully proved
UniversalCover construction. Projection surjectivity uses the initial tail `Over j`
and the existing affine-limit surjectivity theorem. Stage-transition surjectivity
uses the nonempty clopen image of a finite etale map. For affine charts the proof
reindexes the existing AffineOverLimit construction, compares its cone with the
published limit, and uses its relative-spectrum chart. Evaluation preserves
colimits, yielding the precise section-ring colimit and both required equations.
The etale stage ring maps give the ind-etale presentation, transported through
canonical ULift ring equivalences. The singleton covering follows from the proved
weak etaleness, surjectivity, and quasi-compactness.

Updated the existing node's proof, proof_deps and proof_origin to this route;
removed obsolete entries of its top-level tool_uses in their existing order.
The unit's finite-cover route is retained; the unit has no realized node steps
replaced by this delivery. No statement or definition is repaired or weakened.

Searches: msearch LeanFinder for pointed Galois objects/open normal subgroups,
Loogle for OpenNormalSubgroup, and grep for PointedGaloisObject and normal
stabilizers; local rg searches found the decisive UniversalCoverConstruction,
AffineOverLimit, GaloisObjects, OpenSubgroups and ring IndEtale APIs. No preexisting
theorem supplies the exact normal-subgroup equivalence with all chart equations.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.UniversalCover.exists_pointedGaloisLimitGeometry`
(node `lem-sfb-pointed-galois-limit-geometry`). Added 0 holes; split off 0.
No sorry remains in the delivered Lean file. This is a proof, not a decomposition.

Validation: single-file server compilation through lcompile.py, followed by the
normal deliver3.py compile/preflight/axiom probe. The proof explicitly handles the
trivial fundamental group, any normal subgroup (including the whole group), and
empty affine opens. It adds no characteristic, nonempty-chart, or cardinality
hypothesis. The existing scheme and point are used throughout.

## No longer needed

Removed these four private proof imports:

- WeilConjectures.AlgebraicGeometry.LimitAffineTransition
- WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceDegree
- WeilConjectures.AlgebraicGeometry.LimitFibreProducts
- Sheaf.AlgebraicGeometry.EtaleComparison

The private import of `thm-galois-fundamental` / FiberEquivalence is retained
because the delivery gate identifies it as a unit-route dependency. The proof
uses its fully proved finite-etale equivalenceContAction input without reapplying
the FLC comparison clauses.
`lem-weil-pbc-finite-etale-trace-degree` is unnecessary because nonempty finite
etale maps to connected stages are surjective by their clopen image.
`lem-weil-pbc-limit-affine-transition` is replaced by the already proved and
more directly usable AffineOverLimit and Mathlib affine projection APIs.
`lem-weil-pbc-limit-fibre-products` is replaced by the already proved
Scheme.isLimitPullbackCone used inside Scheme.surjective_of_isLimit.
`det-pe-morphisms-etale-comparison` is unnecessary because the published
UniversalCover.weaklyEtale_proj already supplies weak etaleness.

The obsolete top-level tool approvals removed are
`det-pe-morphisms-etale-comparison`, `lem-weil-pbc-limit-affine-transition`,
and `lem-weil-pbc-limit-fibre-products`.
`def-weil-pbc-affine-scheme-qcqs`, `lem-weil-pbc-limit-nonempty`, and
`pqf-lem-limit-qc-open-descends` remain needed through the proved source APIs.
No upstream declaration or module is deleted. No whole-library withdrawal is
claimed: other consumers may still need any of the removed dependencies.

## Where the brief, the DAG or earlier work was wrong

The statement is correct. The original plan did not exploit the published,
fully proved UniversalCover and AffineOverLimit APIs. Consequently several
large dependency theorems were unnecessary for this exact result. The plan's
trace-degree step can be replaced by the elementary clopen-image argument.
The original docstring is preserved as published; the updated DAG and this
report describe the shorter implemented proof.


The first delivery preflight classified the new scoped `variable` and local
`attribute` commands as potentially visible interface changes. Their scope is
limited to the new private-helper sections, and no existing declaration changes
its type. The requested change record is
`coord/changes/pointed-galois-limit-geometry-helper-scopes.md`. There are no
downstream modules or adapted consumers. The same preflight flagged removal of
FiberEquivalence as a unit-route issue; its private import and DAG tool dependency
are restored.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
