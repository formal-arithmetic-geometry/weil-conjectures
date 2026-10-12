## What changed

Proved `freeRepresentableHomotopyPresheaf_homology` with its original signature and
its original concrete definition of `freeRepresentableHomotopyPresheaf` unchanged.
The proof follows all three steps of the item's plan. Private helpers construct
the additive free-sheaf/sections equivalence and prove naturality in both the
sheaf and the site object. They assemble a natural functor isomorphism, which is
mapped termwise to complexes and then to homology. Only proof imports were added.

Added two generic tool modules, both fully proved:
`Sheaf.CategoryTheory.SingleHomotopyPresheafHomology` identifies homotopy maps
from any family of degree-zero single objects with homology of its degreewise
Hom presheaf; `Sheaf.CategoryTheory.MapExtendHomology` proves the extension-by-zero
homology comparison for any additive functor. Neither introduces an assumption
about injectivity, resolutions, Ext, or exactness of the sections functor.
Evaluation and universe lift preserve homology by Mathlib's existing instances.
An explicit additive equivalence collapses the successive universe lifts.

Updated the parent node's proof, proof dependencies and proof origin, and added
nodes for the two proved tools. The unit `sk-thm-p1` and every node listed in its
`realized` field are retained; this item is below that unit's own statements and
proof steps. No existing interface, target statement, or definition changed.

Compilation uses only lcompile.py. All three modules compile in import order,
with no warnings and no sorries. The main file is within the 60-second limit.
The delivery dry run additionally probes every declaration for unsupported
axioms; its result is recorded by the delivery tool.

## Proved and sorry left

Closed the original hole:
`freeRepresentableHomotopyPresheaf_homology`
(node `lem-weil-pbc-free-representable-homotopy-homology`).

Also proved `singleHomotopyPresheaf_homology`
(node `lem-weil-pbc-single-homotopy-presheaf-homology`) and
`mapExtendHomology_nonempty_iso`
(node `lem-weil-pbc-map-extend-homology`). All their private supporting lemmas
are proved, as is the additive instance for the concretely constructed
`restrictedHomPresheafFunctor`.

Original holes closed: 1. Holes added: 0. Holes left: none, in any delivered
module. This is a proof, not a decomposition into lower sorries. It relies on
Mathlib only, besides the two proved modules of this delivery.

Edge cases are included by the actual proofs: the generic comparison applies
for every integer degree and every indexing category (including the empty one),
and extension by zero uses Mathlib's comparison at q=0 as well as at positive q.
Zero complexes and zero abelian categories require no exceptional argument.

## No longer needed

None. No original import, node or module was removed. The three original
proof dependencies are still used: the site and sheafification definitions in
the adjunction comparison, and exact-functor preservation of homology for
universe lift and evaluation. No injectivity or Ext-comparison module was added.
The two new imports are both used in the main proof.

## Where the brief, the DAG or earlier work was wrong

The statement and the plan were sound. The citations did not themselves state
all the generic algebraic comparisons. In particular,
[Stacks Tag 06XR](https://stacks.math.columbia.edu/tag/06XR) identifies Ext with
homotopy maps after an injective or projective resolution; it is not by itself
the arbitrary Hom-complex homology comparison proved here.
[Stacks Tag 03F3](https://stacks.math.columbia.edu/tag/03F3) concerns locality of
cohomology and injective restriction. The delivered generic nodes cite the
specific Mathlib constructions actually read and used, rather than claiming
these tags contain their exact statements.

The local clone contains neither the cited Stacks .tex files nor the imported
blueprint markdown. I read the two cited tags online and read the unit's full
statement, steps and `realized` field from `dag/units/sk-thm-p1.json`.
`blueprint_refs.py ancestor` reports None because the parent's `created.item`
is a Lean module name rather than a node id. The new nodes inherit the parent's
explicit blueprint ancestor `lemma-weil-pbc-gabber-effacement`, and name the
precise steps of the parent they implement. Searches of the full imported
blueprint found no equivalent generic statement (the extension-by-zero hits
concern sheaf extension along open immersions, not extension of the degree set).

LeanSearch returned Internal Server Error for both new tools; this is recorded
as unavailable, not as a negative search result. Loogle, LeanFinder, and grep
ran successfully. Their actual logged queries and results are in the nodes.

## New nodes

`lem-weil-pbc-single-homotopy-presheaf-homology`, in
`dag/nodes/sec-proper-base-change/`, records the fully proved generic natural
Hom-presheaf comparison in `Sheaf.CategoryTheory.SingleHomotopyPresheafHomology`.
Its precomposition map preserves coboundaries; explicit left homology map data
proves quotient naturality. Evaluation naturality follows from
`ShortComplex.homologyMap_mapNatTrans`.

`lem-weil-pbc-map-extend-homology`, in the same chapter, records the fully proved
additive-functor extension comparison in `Sheaf.CategoryTheory.MapExtendHomology`.
Its proof constructs the complex isomorphism on Option-indexed terms, checks
all four differential cases, and applies `extendHomologyIso`. No exactness of
the additive functor is needed. There are no change records or forced adaptations.

## Second reading by R2

1. Compared every delivered Lean module with the repository versions. The existing
   target definition and theorem signature are byte-for-byte unchanged; only proof
   imports, private helpers, and proof bodies changed. The two generic modules are
   new declarations with matching DAG nodes.
2. Compiled all three modules in import order with `lcompile.py --all`; compilation
   succeeded with no errors or warnings. No `sorry`, `axiom`, `unsafe`, `opaque`,
   `extern`, or `implemented_by` occurs in the delivered declarations. The proofs
   use only the permitted mathematical axioms.
3. Checked the two added statements against their constructions and edge cases:
   arbitrary indexing categories, empty categories, q = 0, zero complexes, and
   zero objects are covered by the componentwise isomorphisms. Neither statement
   duplicates an existing library declaration.
4. Checked the parent node's proof, dependencies, and origin against the actual
   proof route. The two new nodes have complete statements, sources, proof steps,
   searches, blueprint ancestry, and Lean records. No imports or nodes are unused.
5. The unit `sk-thm-p1` route and all its realized nodes remain in use; the generic
   lemmas are tool-level reductions below the unit. Verdict: proof is sound and the
   statements are unchanged and exactly as required.

I changed nothing during this second reading.
