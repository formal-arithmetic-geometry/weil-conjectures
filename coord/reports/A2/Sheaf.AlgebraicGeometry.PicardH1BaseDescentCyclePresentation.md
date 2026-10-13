## What changed

Replaced the only sorry in `Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation`
with a complete Lean reduction to two separate parts of the existing proof plan.
The theorem's signature, visibility and original docstring are unchanged.

Added `Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel`:
`AlgebraicGeometry.Scheme.picard_h1_base_descent_local_model` constructs the affine
source model, section bases, joint map and explicit degree-one cohomology comparison
square. It does not assume hH and does not assert injectivity or section realization.

Added `Sheaf.AlgebraicGeometry.PicardScalarModelCyclesRealization`:
`AlgebraicGeometry.Scheme.picard_scalar_model_cycles_realization` realizes cycles of a
fixed connective strictly perfect source model. It has no target family or degree-one
map and does not assume hH. The input contains an actual complex and its derived
comparison, not a repackaged hypothesis asserting the desired sections exist.

The main proof supplies standard derived localizations, proves primality by
`RingHom.ker_isPrime`, derives residue injectivity from hH through the comparison
square and alpha.injective, then converts coordinate annihilation to vector annihilation
by extensionality and commutativity. It assembles the unchanged conclusion.

The node's proof and proof dependencies now follow this reduction. The unit's theorem
of the cube route and its realized nodes are retained. All writes are in the sandbox.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.picard_h1_base_descent_cycle_presentation`.
No sorry remains in the assigned module.

Added two named holes, each in its own new module:

- `AlgebraicGeometry.Scheme.picard_h1_base_descent_local_model`
  (node `lem-sc-picard-h1-base-descent-local-model`).
- `AlgebraicGeometry.Scheme.picard_scalar_model_cycles_realization`
  (node `lem-sc-picard-scalar-model-cycles-realization`).

This is a decomposition: one upper hole closed, two strictly partial lower statements
added, net holes closed minus added = -1. It is not a complete proof of the geometric
argument. The reduction and both helper statements compile with lcompile.py.
No definitions or existing statements changed; no axioms or hollow definitions added.

Edge cases checked in the mathematical arguments: an empty target family uses the
zero target and its unique map without claiming source rank zero absent hH; m=0
uses the zero source term, and all scalar cycles then lift. In the main proof hH itself
forces the source residue term to be zero for n=0. Zero-dimensional higher terms cause
no problem. U and V contain w and hence are nonempty. Universal structure units exclude
empty residue fibres when a rank-one descent argument needs a point. The fixed-model
realization lemma allows any k and does not require target descent or H-one injectivity.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.PerfectDirectImageBaseChange`
- `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`
- `Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative`

They remain needed by the new local-model lemma (and base change by realization).
Their nodes `lem-pc-rf-perfect-base-change`,
`lem-sc-perfect-finite-free-residue-model`, and
`lem-pc-perfect-affine-map-representative` are relocated dependencies, not pruned work.
No node or module has been established unnecessary in the transitive proof closure.
The other old direct proof dependencies (base change, module pullback, invertibility,
finite locally free modules, residue fields, structure cohomology pullback, and the
pullback adjunction) remain statement dependencies or dependencies of the two new
nodes; none is pruned from the argument's transitive closure.
The assigned module keeps every original public statement import and imports the two
new lemmas privately. The generic realization module omits immersion, tensor-product,
ideal-residue-field, and structure H-one imports that its signature does not need.

## Where the brief, the DAG or earlier work was wrong

The original proof plan names perfect-model and chain-representative declarations,
but they do not themselves expose the scalar degree-zero model, the explicit
comparison with structure-sheaf H-one, or the canonical section-restriction comparison.
These are the two remaining parts made precise in the new nodes. No false statement
or target correction was found. The source follows Stacks Tag 0BF2, read directly at
https://stacks.math.columbia.edu/tag/0BF2; the cited local literature file is absent on
this machine. Mathlib searches used LeanFinder, Loogle and source rg. LeanSearch
returned Internal Server Error; this is recorded as unavailable rather than a negative
result. Existing downstream section lifting imports this item, so using it here would
be circular. The existing field rank-one trivialization is reused in the new plan.

## New nodes

`lem-sc-picard-h1-base-descent-local-model` states steps 1--3 before using hH:
local finite-free source and target models, zero target differential, and the explicit
residue degree-one comparison square. It retains the existing perfect-model and
chain-map tools and the field rank-one and affine cohomology comparison declarations.

`lem-sc-picard-scalar-model-cycles-realization` states step 4 for a fixed source complex,
with an explicit derived direct-image isomorphism and degree-zero section bases.
Its proof describes cycle realization, the residue generator, point coverage by j,
tensor-pullback composition, and the degree-zero canonical mate comparison.

## Second reading by A2

1. **Signatures and visibility.** Compared the assigned module with the repository
version using `diff`; the existing theorem signature and docstring are unchanged.
The two new public theorem signatures are exactly those recorded in their DAG nodes.
Verdict: pass.

2. **Proof and axioms.** Compiled all three delivered modules with `lcompile.py`.
The assigned theorem has no `sorry`; the only remaining holes are the two named,
documented split theorems listed above. No axiom, unsafe, opaque, extern, or hollow
definition was added. Verdict: pass subject to the two declared split nodes.
Explicit `#print axioms` checks in a scratch copy reported exactly `propext`,
`Classical.choice`, `Quot.sound`, and `sorryAx` for all three declarations.

3. **Statements and duplication.** Read both split statements and checked their edge
cases (empty target family, zero source rank, and m = 0). They are strictly partial
reductions and do not restate the assigned theorem. Repository and Mathlib searches
found no duplicate declarations. Verdict: pass.
Independent searches used the alternative phrase "sections from degree zero cocycles
in a strictly perfect direct image complex", Loogle's `HomologicalComplex.homologyMap`,
and repository searches for cycle, cocycle, residue model, and comparison square.
The existing universal-H0 chain model requires universal rank hypotheses absent here;
the canonical mate square supplies compatibility but no fixed-model section theorem.
Neither split hole can be closed by a single available declaration.

4. **Pruning and route.** The assigned module no longer needs the three direct perfect
model imports; those dependencies remain in the local-model module where used. The
unit `sk-prop-av-cube` is unchanged. Its `realized.statement` and `realized.steps`
entries are empty in this checkout; this delivery neither deletes a realized node
nor bypasses the original Picard/theorem-of-cube route. Verdict: pass, with the
pre-existing empty realized record noted.

5. **DAG agreement.** Updated proof steps and proof dependencies match the Lean proof;
both new nodes include source, proof, searches, Lean records, and split status. Verdict:
pass.

Second-reading changes: added this review record and clarified the retained old
dependencies and the pre-existing empty unit realization record. The first worker's
Lean code and nodes needed no repair. No existing statement or definition was changed.

No change records are needed: existing interfaces were not changed.
