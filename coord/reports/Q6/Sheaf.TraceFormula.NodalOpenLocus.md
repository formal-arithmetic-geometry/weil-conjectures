## What changed

Proved `AlgebraicGeometry.nodalOpenLocus` from the existing syntomic and unramified
locus declarations and a separate pointwise geometric recognition theorem. Its
signature, its three public definitions, and all original public imports are unchanged.
There are no source-library changes and no forced adaptations.

The open is constructed explicitly as the complement of the closed image of the bad
part of the first-Fitting singular subscheme. The proof establishes openness,
open-immersion invariance of the smooth-or-node predicate, comparison of open-subscheme
geometric fibres, geometric-point detection, largestness, arbitrary-base-change
largestness, and the entire-fibre criterion. In particular the base-change argument
uses associativity of geometric pullbacks instead of reconstructing the candidate
by repeating the Fitting-ideal calculation.

Added `Sheaf.TraceFormula.NodalCandidateGeometricCriterion`, containing the sourced
pointwise recognition step of Stacks 0DSC/0C59/0C4D. It concerns a fixed explicit
candidate set at a single geometric point. It constructs no open, and asserts no
openness, restriction invariance, maximality, or universal base-change property.
It is strictly the local geometric portion of the argument, rather than the original
statement with repackaged hypotheses. Updated the parent proof route and added its node.

Both modules compile via `lcompile.py --all`. The private helper proofs and the main
proof contain no `sorry`. New declarations use `autoImplicit false`. No target or
public definition changes, change records, deletions, or consumer adaptations are needed.

## Proved and sorry left

Closed the original body hole of `AlgebraicGeometry.nodalOpenLocus` (one of one).
Added one hole: `AlgebraicGeometry.nodalCandidate_geometric_criterion`, node
`lem-trf-nodal-candidate-geometric-criterion`. This is a decomposition, not a net
one-hole proof: original item 1 → 0 holes; new module 0 → 1; packet net 0 holes closed.
The remaining theorem has a full source/proof docstring and a DAG node with its
original local-algebra dependencies. There are no other retained or added holes.

The remaining work is the geometric first-Fitting base-change comparison and its
local complete-intersection/unramified recognition at a point. The existing
`NodalPointLocalCriterion`, `LciPointwiseCriterion`, `DthFittingSmoothLocus`,
`PresentationFittingIdeal`, and locus statements were read. None states the needed
combined comparison, and the differential/Fitting sheaf pullback nodes have no Lean
attachment yet. Those nodes were not recreated or assumed as already-proved facts.

Checked the new statement mathematically on empty fibres, smooth curves including
nonclosed points, the ordinary node uv=0 in all characteristics, a cusp, and a
double line. For the node the singular subscheme has reduced field stalk; for the
cusp it is nonreduced and unramifiedness fails; the double line is also excluded.
The complete-intersection condition was retained. Closedness of a node is retained
explicitly; the global open-immersion argument uses Jacobson spaces to preserve it.

## No longer needed

Removed these proof imports from the item:

- `Sheaf.AlgebraicGeometry.DthFittingSmoothLocus`
- `Sheaf.RingTheory.PresentationFittingIdeal`
- `Sheaf.AlgebraicGeometry.NodalPointLocalCriterion`
- `Sheaf.TraceFormula.RelativeDimensionBaseChange`
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`
- `Mathlib.RingTheory.Kaehler.TensorProduct`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.RingTheory.Jacobson.Ring`
- `Sheaf.TraceFormula.FiniteResiduePointClosedInFibre`
- `Sheaf.TraceFormula.LciPointwiseCriterion`

The local differential, Fitting, dimension and nodal-recognition dependencies remain
needed by the separate pointwise criterion and are listed in its DAG node; they are
moved out of the parent's direct proof dependencies, not globally pruned.

The old maximality route through `lem-weil-pbc-zariski-lemma` is unnecessary here:
`LocallyOfFiniteType.jacobsonSpace` and the open-embedding closed-points API give the
needed closed-point comparison directly. The old explicit affine faithfully-flat
argument (`lem-weil-pbc-field-extension-base-change-faithfully-flat` and
`lem-weil-pbc-faithfully-flat-surjective-spectrum`) is unnecessary: a map between
field spectra is surjective and Mathlib preserves surjectivity under pullback.
`lem-weil-pbc-lft-affine-pairs` is no longer a direct requirement for openness:
local finite type of the singular-subscheme morphism follows by typeclass composition
with its closed immersion. The affine fibre-product and differential base-change
nodes are still needed by the new local criterion.

No existing module is withdrawn. No global module-pruning claim is made. A transient
unused private candidate-membership helper and an unused ideal-sheaf functorial import
were removed before delivery.

## Where the brief, the DAG or earlier work was wrong

No statement was found false and no target or source definition was changed. The
original proof plan treats the differential/Fitting base-change gluing and affine
LCI-neighbourhood extraction as elementary glue, but their declared Lean interfaces
do not supply that combined pointwise result directly. It is isolated as a genuine
sourced local theorem rather than hidden in the main proof or in a definition.

The original field-extension projection argument can use Mathlib's existing
surjective-pullback instance, and the open-restriction closedness argument can use
Jacobson spaces. These shorten the global argument. The current blueprint unit
`sk-i-curve-zero` and all unit realizations are unchanged; this remains the historical
stable-modification input below `lem-trf-local-term-locality`.

## New nodes

`lem-trf-nodal-candidate-geometric-criterion` attaches the new pointwise theorem.
Its source is the fibrewise recognition in Stacks Curves 0DSC, 0C59 and 0C4D, using
Divisors 0C3I/0C3K. Its proof retains the original parent's local steps and dependencies;
its conclusion omits the parent's global open construction and all maximality clauses.
LeanSearch, LeanFinder, Loogle, local Lean source searches, and whole-blueprint searches
for nodal/Fitting found no duplicate of this pointwise statement. In particular the
existing global `nodal_curve_lci_criterion` does not give this local geometric
base-change membership equivalence. No change record is required.

## Second reading by Q6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
