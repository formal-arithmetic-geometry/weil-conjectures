## What changed

Completed the existing sandbox reduction of
`AlgebraicGeometry.Scheme.exists_etale_neighbourhood_of_finite_flat_of_codimension_one`.
The signature and its public imports are unchanged. Four proof-only imports supply
an etale chart with a singleton fibre, its locally principal branch ideal,
dimension-one detection in that support, and the proved flat coheight equality.
The proof combines them with a closed-map specialization argument and the supplied
formally unramified neighbourhood hypothesis.

Added complete node records for the three new helper modules left by the previous
attempt, and updated the parent node's proof route and proof dependencies.
Read Stacks Tags 0BJH, 02LK, 0BJG and section 0BVH against the helper signatures.
All four modules compile through lcompile.py; the import-removal trial confirmed
that the QuasiFinite import supplies the necessary coheight theorem.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_etale_neighbourhood_of_finite_flat_of_codimension_one`
(node `lem-sbc-finite-flat-codimension-one-etale-neighbourhood`). No hole remains
in the item module. This is a decomposition into three strictly smaller statements,
not a proof without sorry dependencies: one hole closed, three holes added, net -2.

The three new holes are:

- `AlgebraicGeometry.Scheme.exists_finite_flat_singleton_fibre_chart`
  (`lem-sbc-finite-flat-singleton-fibre-chart`).
- `AlgebraicGeometry.Scheme.exists_locallyPrincipal_branch_ideal_of_finite_flat`
  (`lem-sbc-finite-flat-discriminant-branch-support`).
- `AlgebraicGeometry.Scheme.exists_dimension_one_generalization_in_locallyPrincipal_support`
  (`lem-sbc-locally-principal-support-dimension-one`).

The chart statement has no codimension-one ramification assumption and proves no
etaleness at the selected point. The branch ideal statement imposes no positive
local dimension and is valid for ramified maps. The support statement mentions no
morphism. The contradiction combining these independent pieces is proved in Lean.

## No longer needed

No imports or modules are pruned. The following old proof-dependency nodes are
no longer proof steps and remain only as statement dependencies:

- `def-weil-etale-morphism`
- `def-weil-finite-integral-morphism`
- `def-weil-flat-morphism`
- `def-weil-pbc-formally-unramified-morphism`
- `def-weil-pbc-krull-dimension-ring`
- `def-weil-pbc-noetherian-ring`

Their Mathlib definitions remain necessary to interpret the signatures;
the parent proof dependencies now identify the three substantive intermediate nodes.
The QuasiFinite module is needed for `Scheme.Hom.coheight_apply_of_flat`.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox contained a compiling reduction but no report or node records
for its three new helper modules. They are new split statements, not already existing
library dependencies. The earlier draft report's claim otherwise was corrected.

Searches for an existing matching declaration or node found no exact scheme-level
helper statement. LeanSearch was unavailable; its actual error is recorded in the
nodes rather than treated as a negative search result. The algebraic prime-chain
lemma `PrimeSpectrum.exist_mem_one_of_mem_maximal_ideal` does not directly state
local-dimension-one support detection on a scheme.

Edge cases checked: empty sources make the chart statement vacuous; rank-zero
finite flat pieces have discriminant ideal one and empty support; zero discriminant
is allowed and gives full support. The support lemma allows nonreduced and reducible
schemes, and explicitly excludes dimension zero. The target likewise excludes
zero-dimensional points. None of the new statements assumes the target conclusion.

The unit's recorded realized lists are empty, and the source discriminant route is
preserved. No existing definition or statement was changed and no other claimed
module was adapted. The independent second reading is intentionally left to the
second worker.

## New nodes

`lem-sbc-finite-flat-singleton-fibre-chart` states the etale localization step of
0BJH using 02LK, including pointwise etale-locus descent; its module is
`Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatSingletonFibreChart`.

`lem-sbc-finite-flat-discriminant-branch-support` states the finite flat
trace-discriminant branch-support step from section 0BVH as used in 0BJH; its
module is `Sheaf.AlgebraicGeometry.Morphisms.FiniteFlatDiscriminantBranchSupport`.

`lem-sbc-locally-principal-support-dimension-one` states the scheme-local form of
0BJG; its module is `Sheaf.AlgebraicGeometry.Morphisms.LocallyPrincipalSupportDimensionOne`.

Each carries a complete natural-language proof in the declaration docstring and
node record. There are no change records because no existing interface changes.

## Second reading by V3

1. Compared all four delivered modules with the repository. Only the item already
   exists there. Its sole declaration has the identical hypotheses, conclusion,
   universe, visibility and docstring; the difference is its proof and four plain
   proof imports. Removed an accidental extra space before `:=` to preserve the
   signature byte for byte. No definition, target or existing interface changed.
   The three helper modules and their matching nodes are new.

2. Compiled all four modules with `lcompile.py --all`: no errors or warnings.
   The item has no direct sorry; each helper has exactly one public named theorem
   with whole proof `by sorry`, its source, proof docstring and node. There are no
   definitions or forbidden declarations in the delivery. A scratch copy printed
   axioms for the item and each helper: only `propext`, `Classical.choice`,
   `Quot.sound`, and the expected `sorryAx`. The dimension equality
   `Scheme.Hom.coheight_apply_of_flat` uses only the three permitted axioms.
   Existential chart and ideal witnesses are eliminated inside a proof of a
   proposition, never used to define data from an unproved existence theorem.

3. Read [0BJH](https://stacks.math.columbia.edu/tag/0BJH),
   [02LK](https://stacks.math.columbia.edu/tag/02LK),
   [0BVH](https://stacks.math.columbia.edu/tag/0BVH), and
   [0BJG](https://stacks.math.columbia.edu/tag/0BJG) against every helper clause.
   The chart has no ramification assumption or etaleness conclusion at z; 02LK
   gives a finite open piece of the pullback with singleton fibre, and etale
   source/target localization gives its pointwise locus equivalence. The branch
   helper allows a zero discriminant, imposes no dimension condition, and retains
   precisely the existential ramified-point condition. Its trace determinants
   glue since changes of basis multiply by unit squares. The support helper has
   no morphism: 0BJG applied at y followed by prime contraction gives its three
   clauses. All are true and strictly parts of the argument, not restatements.
   Checked empty schemes, finite flat rank zero (unit ideal and empty support),
   positive-dimensional zero discriminant, dimension one (y itself works), and
   exclusion of dimension zero. Neither reducedness nor irreducibility is needed.
   Repeated LeanFinder searches with distinct queries for each helper, recorded
   in its node; searched the Sheaf/upstream/Mathlib sources with discriminant,
   trace-pairing, etale-localization, singleton-fibre and height-one terminology.
   `Algebra.discr` is only the affine determinant construction.
   `PrimeSpectrum.exist_mem_one_of_mem_maximal_ideal` requires a supplied strict
   prime chain and does not give the scheme support statement directly.
   `exists_etale_local_finite_multiple_points` was read in full: it supplies the
   finite singleton pieces, but selecting a lift, installing all base-change
   properties and proving the pointwise etale-locus equivalence remain. No direct
   duplicate was found and no helper could be closed in a few minutes.

4. Read the proof from its conclusion backward. Closedness of g lifts t's
   specialization into the closure of w; uniqueness over g(z) identifies its
   lifted point with z. Flat quasi-finite coheight equality gives exactly the
   required dimension at a(w). The supplied formally unramified open becomes
   etale by flatness and local finite presentation, contradicting the branch
   condition through the chart equivalence. All four new imports serve that
   proof; none is public. Existing public imports serve its signature. Enumerated
   all six retired old proof dependencies under `No longer needed`; they remain
   statement dependencies, and no module is pruned. Read
   `dag/units/sk-prop-input-spreading.json`: realized statement/step lists are
   empty; its depth-two extension and purity route is retained, and neither unit
   nor chapter is edited. This delivery remains a decomposition, net -2 holes.

5. Checked every node's Lean module/file/declaration and verbatim statement,
   chapter/unit, source, created/blueprint fields, and search records. Parent
   `proof_deps` is exactly the union of its steps' three helper references. Its
   proof text describes the actual specialization contradiction and records the
   proved coheight tool. Each new node matches its one open theorem and records
   the full source argument, with no unrecorded new statement or definition.
   No change record is required because no existing interface changes.

Changed signature spacing, completed the old-dependency inventory, and added
independent search evidence and this review. The mathematical proof was retained.
