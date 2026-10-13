## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.singletonTensorCech_normalized_coface`
by a compiling proof from two strictly smaller geometric section statements.
The proof uses the singleton product projection as the hom of `productUniqueIso`,
proves its injectivity, applies `ULift.ext`, and combines the two section equalities
by transitivity. Every existing signature is unchanged. The unit has no realized
nodes at this level; the original geometric restriction route is retained.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.singletonTensorCech_normalized_coface` (1 of 1).
This is a decomposition, not a completed proof without sorry dependencies: two
holes were added, so the net hole change is +1.

The remaining sorries added by this delivery are:

- `AlgebraicGeometry.Scheme.singletonTensorCech_coface_evaluation`
  (`lem-sc-singleton-tensor-cech-coface-evaluation`): the arbitrary-section
  component formula, with no normalization or tensor assumptions.
- `AlgebraicGeometry.Scheme.singletonTensor_normalized_restriction`
  (`lem-sc-singleton-tensor-normalized-restriction`): restriction of evaluated
  normalized pure sections, with no Čech coface or injectivity assertion.

No sorry remains in the original module. Both new declarations have complete
proofs in words and matching DAG nodes. No data construction is postponed.

## No longer needed

Removed the direct proof import `Sheaf.AlgebraicGeometry.EtaleTensorSections`
from the original module. Its semilinearity and composition declarations remain
needed by the normalized-restriction subproblem and are already available through
the normalization module. Thus no dependency module or node is pruned from the
closure; pruning: none. The two original proof dependency nodes remain needed
below the new lemmas.

## Where the brief, the DAG or earlier work was wrong

No mathematical error was found. The original three steps are implemented as
an arbitrary-section evaluation calculation and a normalized-section restriction
calculation followed by the fully proved singleton injectivity argument.

Attempts to prove the calculations directly reached correct component-map and
normalization goals, but rewriting/definitional conversion of the categorical
products and lifted section maps repeatedly exceeded the 60-second single-file
limit. Generic projection helpers compiled independently; their instantiation
and conversion to these geometric goals caused the expensive reductions.
These attempts are only in the scratchpad, not the delivery. The delivered
three modules compile together within the file limits.

Mathlib searches used LeanSearch (unavailable with Internal Server Error),
LeanFinder (unrelated hits), Loogle (`Pi.lift_π`, `Fin.prod_univ_succAbove`: tools),
and direct rg of both library roots and Mathlib. The existing
`singletonTensor_normalization_evaluation` only asserts existence of an additive
normalized evaluation, so it does not supply either missing identity.
Stacks Tags 03P2 and 03DR were read online. Degree zero (both j), empty schemes,
and zero modules obey the same formulas; no affine or invertibility assumption
was introduced.

## New nodes

`lem-sc-singleton-tensor-cech-coface-evaluation` records the original first step
for an arbitrary Čech section in the new module
`Sheaf.AlgebraicGeometry.EtaleSingletonTensorCechCofaceEvaluation`.

`lem-sc-singleton-tensor-normalized-restriction` records the semilinear scalar
and coefficient restriction calculation, including removal of the inserted unit,
in `Sheaf.AlgebraicGeometry.EtaleSingletonTensorNormalizedRestriction`.

The original node's proof dependencies now name these two statements. No
statement, definition, visibility, or target was changed; no forced adaptations
or change records are needed.


## Second reading by B2

1. Compared the delivered original module with the repository using `diff` and
   compared the theorem signature as bytes: identical, including the let-bound
   algebra instance, both normalization hypotheses, and the conclusion. No
   definitions or existing visibility changed. The existing node changes only
   `proof`, `proof_deps`, and `proof_origin`. The other two modules are new.
   Verdict: pass; no statement change record is required.

2. Independently compiled the three modules in import order with `lcompile.py
   --all`: 6.5, 7.3, and 6.6 seconds, with no errors or warnings. The only two
   textual sorries are the named split theorems listed above; there is no axiom,
   unsafe declaration, opaque declaration, extern, implemented_by, or postponed
   data construction. The main argument genuinely uses productUniqueIso_hom to
   prove projection injectivity, then ULift.ext and transitivity of the two
   different section identities. A scratch copy with #print axioms for all three declarations compiled
   successfully in 9.5 seconds. Each prints exactly propext, Classical.choice,
   Quot.sound, and sorryAx; the latter remains because the two split statements
   are open. No other axiom was reported. Verdict: a valid decomposition, not a
   sorry-free proof and not a renamed copy of the original theorem.

3. Read both new signatures, docstrings, and nodes against the normalization
   predicate and the definitions of singletonTensorCechCosimplicial,
   FormalCoproduct.evalOp, and FormalCoproduct.mapPower. Also read Stacks
   https://stacks.math.columbia.edu/tag/03P2 (the singleton affine comparison in
   the theorem's proof) and https://stacks.math.columbia.edu/tag/03DR (equation
   descent-equation-quasi-coherent-presheaf). The coface evaluation applies to
   every section and has no tensor normalization; normalized restriction has
   normalization but no coface or injectivity. These are distinct proper parts
   of the original argument. No affine, covering, or invertibility hypothesis
   is needed for these restriction identities. In degree zero, j=0 and j=1
   select the two projections; the omitted factor contributes the pullback of
   one in either case. Zero modules and empty schemes give zero sections.
   The over-U triangle supplies the coefficient composition, so no triangle
   hypothesis is missing. The landed semilinearity interface is an equality
   of additive maps; its evaluation supplies precisely the pointwise equation
   used in the word proof. Each hole has a complete word proof and matching
   node. Independent searches used Loogle `"Pi.lift_π_apply"`, LeanFinder
   `Evaluation of a formal coproduct presheaf on a Cech face is projection
   followed by restriction`, msearch grep `mapPower|evalOp|restriction.*smul`,
   and rg in the local library, DAG, and upstream WeilConjectures. They found
   projection tools, but no existing complete identity for either new theorem.
   Verdict: pass.

4. Read the original three planned steps and dag/units/sk-prop-h2.json. Its
   realized statement and step arrays contain no nodes to bypass here; the
   original coface evaluation, scalar restriction, and inserted-unit argument
   are retained. The normalization import is needed publicly by the signatures;
   both new imports in the original module are proof-only. No unused direct
   import remains. The original proof dependencies
   new-etale-affine-singleton-tensor-degree-comparison-hom-normalization and
   lem-sc-etale-qcoherent-presheaf-functorial remain needed through the new nodes;
   neither is pruned from the import closure. Tried a direct Pi.lift_π_apply
   evaluation proof in the scratchpad; the explicit geometric conversion did
   not finish within the file limit. No extra helper or experimental setting
   was added to the delivery. Verdict: pass; pruning remains none.

5. Checked each node's Lean declaration and verbatim recorded signature,
   chapter/unit, source, complete proof, proof_deps, creation, blueprint, and
   search records. The original node's two dependencies are exactly the two
   theorems invoked in the Lean proof; the new nodes describe their respective
   restriction subproblems and the statements used by their word proofs.
   Found and repaired one metadata fault: both new blueprint.from.node fields
   named the newly created coface node, which is not an imported blueprint
   node. They now inherit the original node's actual blueprint ancestor,
   lem-sc-etale-affine-qcoherent; their places specify its affine singleton
   Čech/Amitsur comparison calculation. The via chains retain their nodes but are reordered to put the coface
   node first, as the nearest parent, followed by the original ancestry chain. The generic ancestor script
   cannot follow created.item when it is a Lean module name, so the existing
   item's recorded ancestor supplies this linkage. Whole-blueprint searches
   for coface restriction and normalized tensor found no repeated statement.
   Verdict: pass after this metadata repair; no mathematical or interface
   repair was necessary.

Second reading changed the two new nodes’ blueprint ancestor references and
ordered their via chains nearest-first, and
added this independent audit. It confirmed that one original hole is closed and two lower holes are added,
with net holes increased by one. The delivered Lean files and all mathematical node fields were kept.
