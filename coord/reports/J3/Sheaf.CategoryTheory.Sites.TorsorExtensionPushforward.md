## What changed

Proved `CategoryTheory.Sheaf.Torsor.closedImmersion_extension_fibre_pushforward` with
its entire signature unchanged. Four proved private helpers construct the constant-sheaf
restriction, establish exactness for arbitrary closed embeddings by stalks, establish
pullback short exactness in an abelian category, and build the fibre isomorphism from
sectionwise pullback squares. The final proof specializes to the global integer section
one and checks translation using additivity and the first projection of the inclusion.

Replaced the unused public closed-subset exactness import by
`Mathlib.Topology.Sheaves.Abelian`; retained the private stalkwise-detection proof import. Updated only `proof`,
`proof_deps`, and `proof_origin` of `lem-sc-torsor-h1-ext-pushforward`.
The change record is `coord/changes/torsor-extension-pushforward-imports.md`.

Local compilation is clean. `#print axioms` reports only `propext`, `Classical.choice`,
and `Quot.sound`. The declaration-local heartbeat limit accommodates the explicit
pullback/lifting-torsor elaboration; compilation is comfortably within 60 seconds.
The inverse used in the sheaf isomorphism comes from a proved bijection, so it is
uniquely determined. No data is obtained from an unproved existence statement.

## Proved and sorry left

Closed one hole: `CategoryTheory.Sheaf.Torsor.closedImmersion_extension_fibre_pushforward`
(node `lem-sc-torsor-h1-ext-pushforward`). No `sorry` remains in the item.
No holes were added and no statements were split off. All four private helpers are proved.

## No longer needed

Removed import: `Sheaf.Topology.ClosedImmersionPushforwardExact`.
The second reading also removed redundant explicit proof imports
`Mathlib.CategoryTheory.Limits.Types.Pullbacks` and
`Mathlib.CategoryTheory.Abelian.Pseudoelements`; their declarations are already available
through the retained imports.
The proof no longer needs node `lem-sc-closed-immersion-pushforward-exact` or its module,
nor its dependency node `lem-sc-closed-pushforward-abelian-stalks` and module
`Sheaf.Topology.ClosedPushforwardAbelianStalks`. These are pruned from this module's
import edge, but other modules still import them, so no claim is made that they leave
the entire target closure. The existing proved stalkwise detection module remains needed.
The former proof dependency `def-sc-topological-abelian-cohomology` is also unnecessary:
this result constructs sheaves and torsors without a cohomology calculation.
No unit statement or realized unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The exactness dependency is stated for a literal closed-subset inclusion, whereas the item
uses the underlying map of a scheme closed immersion. This is not a false statement;
it needs either transport or the direct closed-embedding stalk argument supplied here.
The old theorem docstring describes the former dependency route; the delivered DAG records
the implemented direct stalk argument. The pullback and fibre steps had no ready-made
interface, but their universal properties suffice, so no new unproved theory was needed.

The semantic edge cases are retained: identity embeddings, empty Z, empty inverse-image
opens, and arbitrary non-surjective restriction on locally constant sections. The proof
uses no surjectivity of r and handles off-image stalks by the empty-open sheaf axiom.
Searches through LeanFinder, Loogle, launcher grep, and both library roots found no exact
existing theorem. Source texts were read at Stacks Tags 01AX, 02UV, and 02FQ online,
as their TeX files are absent from this checkout.


## Second reading by J3

1. Compared the delivered module with the repository by diff and compared the complete
   existing theorem signature as text: byte-for-byte identical. There are no changed
   definitions or existing declarations besides this proof. The public import replacement
   is declared in the change record. Its replacement is needed by the signature: a scratch
   copy without it fails to synthesize the sheaf zero-morphism instances. The sole direct
   importer, `Sheaf.AlgebraicGeometry.UnitsTorsorClosedRestriction`, compiles unchanged
   against the sandbox overlay. Verdict: pass.
2. Compiled the entire delivered module locally and checked a scratch copy with
   `#print axioms CategoryTheory.Sheaf.Torsor.closedImmersion_extension_fibre_pushforward`.
   Only `propext`, `Classical.choice`, and `Quot.sound` occur. Scanned for forbidden
   declarations and `sorry`: none. Read each of the four helper proofs and the final
   section and translation calculations. The inverse natural transformation comes from
   a proved bijection; no unproved existence theorem supplies data. Verdict: pass.
3. No statements are split off and no holes are added. The proved helpers genuinely
   implement separate steps, rather than restating the target. Checked identity and empty
   embeddings, opens disjoint from the image, and the lack of any surjectivity requirement
   on constant-section restriction. The off-image argument uses the empty-open sheaf
   axiom; the pullback argument only requires the original projection to be epi.
   Repeated LeanFinder and Loogle searches with a general abelian pullback query, and
   searched both library roots and Mathlib for pullback short exactness and direct-image
   exactness. The search supplies the epi-pullback instance already used by inference;
   no whole-result replacement or new unfinished lemma is needed. Verdict: pass.
4. Read `dag/units/sk-thm-curveestimate.json`: its realized statement remains
   `thm-sc-proper-cohomology`, and its recorded step list is empty. The present node is
   below that unit statement; the exactness and torsor-fibre argument are retained.
   Checked every former proof dependency against the new proof: the two removed direct
   dependencies are named under No longer needed. The indirect closed-subset stalk
   dependency is also named without claiming whole-closure pruning. Retained the
   stalkwise-detection import actually used. Two explicit Mathlib proof imports compiled
   away independently and were removed together. Verdict: pass.
5. Compared the node JSON with the repository: only `proof`, `proof_deps`, and
   `proof_origin` differ. The steps describe the actual stalk argument, sheafification
   restriction, pullback exactness, sectionwise fibre bijection, and translation check.
   The dependency list equals the union of the steps' uses. No new nodes are needed and
   the unit record is unchanged. Verdict: pass.

Second-reading changes: removed redundant imports
`Mathlib.CategoryTheory.Limits.Types.Pullbacks` and
`Mathlib.CategoryTheory.Abelian.Pseudoelements`, corrected the import descriptions in
this report, and added this review. No proof or signature repair was necessary.
