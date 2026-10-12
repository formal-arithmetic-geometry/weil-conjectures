## What changed

Replaced the sorry in
`AlgebraicGeometry.Etale.injectiveSections_strictLocal_comparison` by a proof of its three
conjuncts. A proved private helper establishes invertibility for every etale projection:
`injective_upperStar_obj_of_etale_addCommGrp` supplies injective terms, the given lower bound
survives the exact termwise functors, `CochainComplex.isKInjective_of_injective` supplies
K-injectivity, and instance synthesis proves that the sections unit and the comparison
composite are isomorphisms. The proof imports
`WeilConjectures.AlgebraicGeometry.Sites.TorsionAcyclic` privately.

The transition and cone squares are specializations of a single new theorem,
`AlgebraicGeometry.Etale.sectionsComparison_triangle_naturality`, in the privately imported
module `Sheaf.AlgebraicGeometry.EtaleSectionsTriangleNaturality`. It treats an arbitrary
triangle, arbitrary complex and representative, and has no invertibility assertion. Its
statement spells out the existing maps in local lets to avoid importing this item's module
back into its dependency. These are local expressions, not alternative public definitions.
The original public signatures, definitions, docstrings and public import are unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.injectiveSections_strictLocal_comparison`
(node `lem-weil-pbc-injective-sections-pullback-comparison`). The invertibility assertion is
proved using existing proved infrastructure. The two naturality assertions are proved from
the new arbitrary-triangle lemma.

Added one hole:
`AlgebraicGeometry.Etale.sectionsComparison_triangle_naturality`
(node `lem-weil-pbc-sections-comparison-triangle-naturality`). This is the sole sorry in the
delivered sources, as the entire proof of a named public theorem. Its docstring and DAG node
explain the derived adjunction unit factorization, Leray unit factorization, quotient
transport, composition factorization and naturality with the representative isomorphism.
This is a decomposition, with one hole closed and one added, not a net reduction of holes.
The new theorem isolates only the naturality part and does not repackage the invertibility
assertion. No sorry is left in the original module, in a definition, or in a private helper.

Both modules compiled locally through lcompile.py without warnings. The maps specialize by
exact definitional equality, so the main proof does not replace the canonical maps by merely
isomorphic alternatives. Edge-case review: no etaleness is assumed for the arbitrary cone
leg, no inverse of the limit sections comparison is taken, and no bound on n is introduced.
The square uses functorial identities valid for zero complexes and empty schemes as well.

## No longer needed

No existing import was removed: the original public import supplies the geometry and
canonical maps appearing in the unchanged statement.

The original plan dependency `lem-weil-pbc-site-restriction-injectives`, module
`Sheaf.Paper.SiteRestrictionInjectives`, is not needed by this proof and is removed from this
node's proof_deps. The source library already proves the needed preservation of injective
abelian sheaves in TorsionAcyclic; the separate site-extension statement is not imported or
used. Its conceptual localization and exact-adjoint ingredients remain represented by the
existing closed nodes. This report does not assert that this module has no other users.

The original direct dependency `prop-weil-pbc-derived-inverse-image-adjunction` is also
removed from this node’s proof_deps: the main proof now uses it through the new naturality
node. Its module is still needed transitively and is not pruned. The derived inverse-image
and cohomology dependencies remain needed. No blueprint unit's statement or realized proof step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt left two anonymous holes in the original theorem and a sorry
in a private intermediate theorem, together with trace_state and long-line warnings. Those
are not included in this delivery. Its invertibility argument was retained and checked.

The plan's separate site-restriction statement is unnecessary for the invertibility clause:
the abelian-sheaf preservation theorem already exists, with a complete proof, in the source
library. The harder localization transport for naturality is isolated rather than hidden
inside the main proof. LeanSearch was unavailable (HTTP Internal Server Error), recorded as
unavailable, not as a no-match verdict. Loogle, Lean Finder and Mathlib grep found generic
naturality infrastructure but no theorem stating the exact triangle square.

The unit `sk-prop-h2` has no realized nodes for this item; its statement and route were read
and left unchanged. The source [Stacks Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
was read, especially its final maps of neighbourhood sections complexes to the limit.

## New nodes

`lem-weil-pbc-sections-comparison-triangle-naturality`, in
`dag/nodes/sec-curve-estimates/lem-weil-pbc-sections-comparison-triangle-naturality.json`,
records the sole remaining naturality step. Its module is
`Sheaf.AlgebraicGeometry.EtaleSectionsTriangleNaturality`, with exactly one public theorem.
The naturality statement has no injectivity, boundedness or etaleness assumption and asserts
only the equality of canonical composites, not isomorphisms. It applies to both triangles in
the original theorem. The blueprint search found no existing blueprint node stating this
square. There are no interface changes or forced adaptations and no change record is needed.

## Second reading by N2

1. Interface preservation: PASS. Diffed the existing module against the repository.
   All six existing declaration signatures, all five definition/abbreviation bodies,
   existing docstrings and the public import are byte-for-byte unchanged. The two
   added imports are proof-only ordinary imports. The new private helper is proved.
   No other existing Lean module is delivered and no change record is required.
2. Proof and trust: PASS as a decomposition. Compiled both delivered modules in import
   order through lcompile.py, with no errors or warnings. Scratch copies with explicit
   #print axioms checks show only propext, Classical.choice and Quot.sound for the
   invertibility helper and comparison definitions. The original theorem and the
   new naturality theorem additionally use sorryAx, as reported. Scanned the delivered
   sources: their sole sorry is the whole proof of the named public naturality theorem;
   there are no forbidden declarations, hidden holes or arbitrary witness constructions.
3. Split statement: PASS. Read its full signature, docstring, node and the source
   [Stacks Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9), final paragraph.
   Checked the orientations of the adjunction unit, Leray and inverse composition
   maps against their defining upstream modules and localization factorization lemmas.
   The derived adjunction factorization, naturality of the derived sections unit and
   uniqueness of derived composition give the described square without cancelling a
   sections unit. For an identity triangle it reduces to comparison naturality; for
   a zero complex both maps are zero; empty schemes and negative degrees introduce
   no exception. The cone leg need not be etale. This statement isolates the two
   naturality clauses and omits the separately proved invertibility clause, so it is
   strictly a part of the argument rather than a renamed copy of the item.
   Independent searches used grep for derived unit/composition factorization, Loogle
   for rightDerivedNatTrans and Lean Finder for localization/derived-adjunction unit
   compatibility, plus rg across both Lean roots for sections naturality and triangle
   comparisons. They found generic derivedη_fac_app and rightDerivedNatTrans_fac
   infrastructure, but no exact replacement. CohomologyPullbackDerivedUnit supplies
   a related bounded-below result, not this unbounded triangle/representative square.
4. Route and pruning: PASS. The injective restriction result is already proved upstream
   and is used directly; bounded-below injective complexes give K-injectivity and
   invertibility by existing instances. Both naturality clauses specialize one square
   by definitional equality. Every added import is used and the original public import
   is needed for the unchanged interface. Compared old and new proof_deps: the removed
   site-restriction-injectives node is unnecessary, and the removed direct adjunction
   node remains a dependency of the new naturality node. No globally unreachable
   module is claimed. Read sk-prop-h2, whose realized statement and sole step are empty
   lists; no realized unit route is bypassed or changed.
5. DAG agreement: PASS after metadata repair. Existing node edits are confined to proof,
   proof_deps and proof_origin. Its steps match the invertibility helper and the two
   specializations. The new node has its source, complete proof plan, search records,
   creation/provenance, chapter, unit and Lean record; proof_deps is the union of uses.
   Replaced its whitespace-flattened Lean statement record with the verbatim multiline
   signature from the new module.

Second-reading changes: corrected the new node's verbatim Lean signature and completed
## No longer needed with the removed direct adjunction dependency. Added this independent
review and axiom evidence. No Lean proof or interface needed repair. One original named
hole is closed and one strictly smaller naturality hole is added: decomposition, net zero.
