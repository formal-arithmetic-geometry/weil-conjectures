## What changed

Proved `AlgebraicGeometry.etaleOpenObjectCohomologyMap_bijective` without changing its
signature or the canonical map. The new, proved module
`Sheaf.AlgebraicGeometry.EtaleOpenObjectHomBijective` verifies the identity-generator
comparison on Hom groups using sheafification/free/Yoneda and constant-sheaf adjunctions.
The original module contains a proved private general comparison lemma: exact pullback
preserving injectives propagates this Hom bijection to all Ext degrees. Its induction uses
actual injective presentations and cokernels, the two right-exact Ext segments, and the
right-exact five lemma. The two squares are proved by Ext functoriality and associativity.
Updated the original DAG node to this route and added the node for the Hom comparison.

Both modules compile cleanly through lcompile.py. Checked the full statement in degree zero,
the zero sheaf, and the empty open: no argument requires the open to be inhabited, and both
adjunctions and the injective-presentation induction apply without such a hypothesis.
The source read was Stacks Tag 03F3, Lemma cohomology-of-open, online; its exact left adjoint
and injective-preservation argument is retained. The unit sk-thm-p1 route is unchanged.

## Proved and sorry left

Closed the sole original hole in `AlgebraicGeometry.etaleOpenObjectCohomologyMap_bijective`
(node `lem-weil-pbc-etale-open-object-cohomology-map-bijective`). Also proved the new theorem
`AlgebraicGeometry.etaleOpenObjectHom_bijective`
(node `lem-weil-pbc-etale-open-object-hom-bijective`). No sorry remains in either delivered
module and no new holes were added. This is a proof, not a decomposition into open statements.
The private helpers `freeSectionEquiv` and `extComparison_bijective` are actual constructions
and complete proofs, respectively; no data is selected from an unproved existence theorem.

## No longer needed

Removed `Sheaf.Paper.SiteRestrictionInjectives` and its proof dependency
`lem-weil-pbc-site-restriction-injectives`: the existing exact open-immersion lower-shriek
adjunction and Mathlib's right-adjoint preservation theorem already give preservation of
injectives for the actual upperStar functor, at the coefficient universe used here.
Thus this proof does not call its subordinate open modules
`Sheaf.CategoryTheory.SiteExtensionByZeroExact` and `Sheaf.Paper.SiteRestrictionExact`, or their
nodes `lem-weil-pbc-site-extension-by-zero-exact` and `lem-weil-pbc-site-restriction-exact`.
These are no longer needed by this proof; other importers may still need them.
Removed `Mathlib.CategoryTheory.Abelian.Injective.Ext`: no explicit injective-resolution
comparison is called. The node `lem-weil-pbc-ext-via-injective-resolution` remains as the
underlying Mathlib Ext computation and injective-vanishing dependency; no resolution-section
comparison modules are imported. The existing open-immersion definitions and canonical-map
module remain needed, and the new Hom comparison replaces the degreewise adjunction glue.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable interface was found. The generic slice-site theorem
`siteRestriction_injectives` was unnecessary for the actual scheme upperStar functor and its
larger coefficient universe. Explicit injective resolutions can be replaced by dimension
shifting while keeping the exact same identity-generator map. No existing statement,
definition, target, visibility, or public import changed. No forced adaptations are needed.

## New nodes

`lem-weil-pbc-etale-open-object-hom-bijective` is a proved, strictly degree-zero comparison,
not a renamed cohomology theorem. Its statement introduces X, U, F, the free sheaf, the
constant integers, and the already constructed identity generator. It uses only existing
adjunctions and the inverse-image/restriction isomorphism, and has no sorry. The three searches
are recorded in the node and sandbox search log: LeanSearch was unavailable (HTTP 500),
Loogle found uliftYonedaEquiv, and grep found Yoneda and constant-sheaf ingredients.
The blueprint search for “free abelian representable” returned no exact node.
No change records were necessary.

## Second reading by E3

1. I compared the delivered cohomology module with the repository version. The target theorem
signature and all existing declarations are byte-for-byte unchanged; the added Hom module is a
new declaration with its own node. No definition or statement was altered.

2. I compiled both delivered modules with `lcompile.py --all`. They compile without errors or
warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`
declarations, and the only proof dependencies are the imported proved library declarations and
Mathlib. The use of `Classical.arbitrary` selects an injective presentation supplied by the
`EnoughInjectives` instance and introduces no unproved data.

3. The added Hom statement is a genuine degree-zero comparison: it identifies the map from the
free representable sheaf with sections and then computes the identity-generator map through the
constant-sheaf and restriction adjunctions. It is strictly simpler than the cohomology target,
has the same hypotheses needed by the proof, and its statement is true also for zero sheaves and
empty opens. The node records its source, dependencies, and searches; no duplicate library
statement was found.

4. The proof follows the unit route through the identity-generator map. Higher degrees use the
Ext exact sequences and injective presentations, while the actual upper-star functor obtains
injective preservation from the open-immersion lower-shriek adjunction. The removed imports and
nodes are listed above because the proof no longer uses the generic site-restriction exactness
route or explicit resolution comparison. Imports are minimal for the compiled declarations.

5. The DAG files match the Lean proof: the target node records the Hom comparison, exactness and
injective-preservation dependencies, and the new Hom node records its degree-zero construction.
The unit `sk-thm-p1` remains the realized route. I changed only the proof modules, the new node,
the target proof metadata, and this report.
