## Repair of returned delivery

The prior delivery was returned because its private helper declarations repeated
statements already present in `RefinementPreservesFiniteLisse` and
`PullbackFiniteLocallyConstant`. The attempted repair added vacuous `True` parameters;
the current second reader removed that repair. The needed comparisons are now local
`have` steps inside the existing target proof, without dummy hypotheses or new helper
declarations. The repository's private helpers cannot be called from this module.
All existing public signatures remain unchanged.

## What changed

Repaired the returned delivery by removing sandbox copies of
`RefinementPreservesFiniteLisse` and `PullbackFiniteLocallyConstant` that had exposed
duplicate public declarations. The target constructs the necessary comparisons as local proof steps: the repository
helpers are private and cannot be called from this module. No adapted dependency module
is delivered. The target theorem statement is unchanged and the proof compiles.

The proof applies the existing component-local-constancy transport separately to each
component, then applies the new `DisjointComponentsLocallyConstantImage` assembly theorem.
Updated the item node's proof, proof_deps, and proof_origin to match the actual proof.

## Proved and sorry left

Closed: `AlgebraicGeometry.Scheme.isLocallyConstant_finite_disjoint_universalHomeomorphism_directImage`
(node `lem-weil-pbc-disjoint-universal-homeomorphisms-lisse-image`). No sorry remains in
the item module. Its proof still depends on the new assembly theorem below, so this
is a decomposition, not an axiom-free proof of the full theorem.

Added and left: `AlgebraicGeometry.Scheme.isLocallyConstant_disjoint_components_directImage`
(node `lem-weil-pbc-disjoint-components-locally-constant-image`) in
`Sheaf.AlgebraicGeometry.DisjointComponentsLocallyConstantImage`.
Its proof is exactly `by sorry`; its docstring gives the complete product/sheaf-axiom
argument, including n = 0. No other hole is added. One upper hole closed, one lower hole
added: net zero holes.

The new statement was checked mathematically for the empty family (X is empty and
f_*E has singleton underlying sections), a single component (the component inclusion
is the identity up to isomorphism), an empty base, and disconnected bases. Arbitrary
cardinality of stalks is permitted: only the number of factors must be finite.
All sandbox modules compile cleanly via lcompile.py.

## No longer needed

Removed sandbox-only duplicate copies of `RefinementPreservesFiniteLisse` and
`PullbackFiniteLocallyConstant`. Against the repository item, removed the proof imports
`Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance` and
`Sheaf.AlgebraicGeometry.PullbackFiniteLocallyConstant`; their old proof dependencies
`thm-weil-pbc-universal-homeomorphism-invariance` and
`lem-weil-pbc-pullback-finite-locally-constant` are no longer used. These are all entries
of the old item proof_deps. The site and topos equivalence parts remain used directly.

Second reading also removed redundant direct proof imports
`Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits`,
`WeilConjectures.Mathlib.CategoryTheory.Functor.Flat`, and
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types`. Their necessary declarations
and instances remain available through retained imports; their modules are not pruned
from the transitive closure. The composition-units node remains a proof dependency.

The broad cohomology, identity, composition, and base-change conjunction of the first
node is not used; the proof uses the existing site/topos equivalence and set-valued
comparison directly. In particular its proof dependencies
`Sheaf.AlgebraicGeometry.UniversalHomeomorphismIdentity`,
`Sheaf.AlgebraicGeometry.UniversalHomeomorphismComposition`, and
`Sheaf.AlgebraicGeometry.UniversalHomeomorphismPullback` are not needed by this route
(nodes `lem-weil-pbc-universal-homeomorphism-identity`,
`lem-weil-pbc-universal-homeomorphism-composition`,
`lem-weil-pbc-universal-homeomorphism-base-change`).
The finite-stalk part of PullbackFiniteLocallyConstant is not needed for this conclusion.
These are removals from this item's route; other callers may still need them.
No blueprint unit's statement or realized step was bypassed: sk-prop-sf-cbc has no
realized statement/steps recorded, and the component argument stays in its stated route.

## Where the brief, the DAG or earlier work was wrong

The item node's second step was marked elementary but contains a nontrivial sheaf
product identification and a finite common trivializing-cover construction. It is
now a named remaining task rather than an unproved implicit step.
The two original planned declarations do not directly expose the needed set-valued
local-constancy transport: PullbackFiniteLocallyConstant has a composite pullback and
finite-stalk conclusion, while UniversalHomeomorphismInvariance exposes the topos
comparison but does not assert transport of local constancy. Their necessary glue
is now proved explicitly. No statement is disputed or changed.

Searches actually run: LeanFinder for universal-homeomorphism disjoint direct image
returned eight condensed locally constant-function results; Loogle on Sheaf.IsConstant
reported an unknown identifier; LeanSearch for finite-product disjoint-cover assembly
was unavailable (Internal Server Error). Logged Mathlib grep returned fourteen
profinite/condensed results, no exact assembly theorem. Additional local rg read
ConstructibleSheaf/FinitePushforward and the constant-sheaf comparison modules.
Blueprint searches for disjoint and product/local-constancy found no identical node.
The literature path recorded in the item node is absent in this local clone; the
existing node and its complete proof docstring provide the source argument used here.

## New nodes

`lem-weil-pbc-disjoint-components-locally-constant-image`:
`dag/nodes/sec-smooth-purity/lem-weil-pbc-disjoint-components-locally-constant-image.json`,
with its module `lean/Sheaf/AlgebraicGeometry/DisjointComponentsLocallyConstantImage.lean`.
This isolates the disjoint-cover assembly step after all component local-constancy
claims have been proved. It introduces no universal-homeomorphism assumption, no
finite-stalk claim, and covers the empty family. No change record is needed because
all existing public declarations and public imports are unchanged.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered item module with the repository version. The target theorem signature and its public imports are unchanged; only the proof imports and proof body changed. The new assembly module and node are explicitly included in the delivery.
2. Compiled both sandbox modules with `lcompile.py --all`; both compile without errors. Sorries occur only as the complete proof of the named public assembly theorem, with its blueprint docstring and node. No axiom, unsafe, opaque, extern, implemented_by, or hollow definition was found.
3. Reviewed the split-off assembly statement against the disjoint-cover sheaf product argument, including n = 0, n = 1, empty base, and disconnected bases. It is strictly a component-assembly part of the argument and introduces no universal-homeomorphism or finite-stalk assumptions. Local searches found no existing declaration with this statement.
4. Checked the proof route from the top down. The item proof uses the explicit inverse-image, restriction, composition, and abelian-lift declarations, then the split assembly theorem. The old universal-homeomorphism-invariance and pullback-finite-locally-constant imports are unused and removed. The unit record has no realized statement or steps to bypass.
5. Compared the item node's proof, proof dependencies, and proof origin with the Lean proof. They match the three proof stages and the split theorem dependency; the new node records its statement, source, searches, and Lean declaration.

Changed during second reading: added this review section only; no Lean declaration or node statement was altered.

## Earlier second reading (a previous round; superseded)

1. PASS: diffed every existing delivered module against the repository. The only
existing module delivered is the item. Its existing theorem signature is byte for byte
identical, its public imports and existing docstring are unchanged, and there is no
public definition change. Local proved comparisons and proof imports are the other edits.
The assembly module and its node are new and declared in this report.
2. PASS: compiled both modules with lcompile.py. The item has no sorry; the only
new sorry is the complete proof of the named public assembly theorem. No prohibited
command or hollow definition is present. Scratch #print axioms for both public theorems
reports only propext, Classical.choice, Quot.sound and sorryAx. Existential comparisons
are used within theorem proofs, never to define arbitrary data from an open theorem.
3. PASS: read the assembly signature, docstring and node together. The disjoint-cover
sheaf axiom gives the finite product of component direct images, and finite common
refinement trivializes it. Checked n = 0 (empty source, terminal underlying direct image),
n = 1, empty base, and disconnected base. This isolates the assembly step after the
component local-constancy proof; it does not restate universal-homeomorphism transport.
Independent LeanFinder searched disjoint-union sheaf sections, Loogle searched IsConstant,
and logged grep plus local rg searched product/disjoint local constancy. Found general
sheaf product tools and constant-sheaf lemmas, but no exact assembly theorem; the existing
finite module-sheaf product theorem uses different hypotheses. Closing this hole requires
the natural component-section comparison and common-cover construction, not a short
application of the search results.
4. PASS: checked pullback local constancy, descent of covers through the site equivalence,
and the unit identification before the assembly application. Repository helper proofs
are private; keeping private proofs here avoids exposing or adapting another module.
Removed three redundant direct proof imports and confirmed compilation. No additional
pruning of nodes follows from those removals because their declarations remain used
transitively. The No longer needed list now includes both old proof_deps explicitly.
The unit sk-prop-sf-cbc has empty realized statement and steps, and the component route
of this node is retained.
5. PASS: the item's proof steps, proof_deps and proof_origin match the proof. Verified
that the site-equivalence and topos nodes record the actual declarations used, including
Hom.isEquivalence_etale and Etale.sheafEquivalence. The new assembly node has its source,
complete proof plan, statement dependencies, searches, creation data, blueprint provenance,
unit/chapter and verbatim Lean signature. Existing node changes are confined to proof,
proof_deps and proof_origin.

Changed during this second reading: removed the three redundant direct proof imports;
corrected the report's description of private helpers and completed its old-dependency
pruning list; added this independent review. No theorem statement or definition changed.
One upper hole closed and one assembly hole added: decomposition, net zero holes.

## Second reading by X3

1. PASS: diffed the existing item against the repository and checked its signature
byte for byte. Its public imports, target signature and target docstring are unchanged.
No existing definition or statement changed; the assembly module is the reported new
module. The existing node differs only in proof, proof_deps and proof_origin.
2. PASS: both modules compile through lcompile.py. Scratch #print axioms on the item
and assembly declarations gives only propext, Classical.choice, Quot.sound and sorryAx.
The assembly theorem is the only delivered sorry, as its whole named theorem proof.
There are no forbidden declarations or hollow definitions. Chosen isomorphisms occur
inside proofs; no data definition selects an arbitrary witness from an open theorem.
3. PASS: read the assembly theorem, source attribution, natural-language proof and node.
It is a proper component-assembly subproblem, without universal-homeomorphism transport
or a finite-stalk assumption. Checked zero components, one component, empty base and
arbitrary disconnected bases. Finite intersections of trivializing covers trivialize
the product; an empty source gives the terminal underlying set sheaf. Independent
LeanFinder searched finite products of locally constant sheaves and finite coproduct
sections; Loogle searched Sheaf.IsConstant (unknown identifier); logged Mathlib grep
and local rg searched product and disjoint-cover terminology. The upstream
Etale.isIso_piLift_of_disjoint proves the objectwise product step, not this full
natural direct-image comparison and finite-cover assembly. The upstream biproduct
results use abelian local constancy rather than the underlying-set hypothesis here.
No exact existing assembly statement was found, and closing it is not a short direct
application of these results.
4. PASS after repair: checked the component restriction, descent of the cover through
the site equivalence, reflection of constancy and equivalence-unit comparison. The
previous repair's unused True parameters were not legitimate mathematical progress
on duplication. Removed all of them and all duplicate top-level private helper
declarations. Their needed arguments now occur as local have steps within the target
proof, because the repository helpers are private and inaccessible here. This adds
no library declaration and does not change any hypothesis. The retained imports supply
the comparisons actually used; all previously listed removed dependencies remain
unused. The unit sk-prop-sf-cbc has empty realized statement and steps, and this proof
retains the component route. There is no newly bypassed unit step.
5. PASS: checked the existing node's three proof steps and dependency union against
the local proof and assembly application. The new node records a self-contained
statement, complete proof plan, source, searches, creation data, blueprint provenance,
chapter/unit and the verbatim Lean signature. No node statement changed.

Changed in this second reading: eliminated vacuous True parameters and duplicate
private library declarations by putting the comparisons inside the target proof;
corrected the report to describe that repair. No public signature, definition,
assembly statement, import list or DAG route changed. One original hole closed and
one assembly hole added; decomposition with net zero holes, not an axiom-free proof.
