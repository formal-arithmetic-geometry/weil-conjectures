## What changed

Repair of reviewer X-e5795, returned head e57950ea7: added two DAG records attaching existing proved source declarations. The directed-pullback node now cites `lem-weil-pbc-grothendieck-directed-intersection` in its first step and proof dependencies. The local-image-sheaf node now cites `lem-weil-pbc-etale-covering-sieve-finite-affine-refinement` in its second step and proof dependencies. The records include the exact source signatures, surrounding universe and instance hypotheses, complete source proof summaries, and three logged search kinds. No Lean declarations or proofs changed during this repair.

Proved `AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck.eq_zero_of_locally_liftable_maps`
without changing its statement, universes, visibility, original public import, or qcqs hypotheses.
Its two new imports are private proof dependencies. A private helper proves that the categorical
local image of an epimorphism is the whole sheaf value. The theorem docstring and existing DAG
node now describe the implemented proof.

Added five fully proved helper modules: `Sheaf.AlgebraicGeometry.GrothendieckEtaleLocalImage`,
`Sheaf.CategoryTheory.GrothendieckDirectedPullback`,
`Sheaf.AlgebraicGeometry.GrothendieckEtaleLocalImageDetection`,
`Sheaf.AlgebraicGeometry.GrothendieckEtaleLocalImageDescent`, and
`Sheaf.AlgebraicGeometry.GrothendieckEtaleLocalImageSheaf`.
The definitions are actual subobject suprema, intersections, and uniquely determined
factorizations. No definition chooses arbitrary data from an unproved existence theorem.

The proof constructs the local image using local lifts after epimorphisms of their sources.
AB5 and the source library's proved `IsGrothendieckAbelian.inf_iSup_of_directed` give directed
pullback detection. Finite induction removes local-lifting assumptions one cover member at a
time, proving descent without requiring a source map to factor through one stage of a union.
Finite affine refinement on each qcqs test object then proves the sheaf condition. Finally,
epimorphy of the given sheaf map makes the subsheaf inclusion an isomorphism.

Validation: all six delivered modules compile together without warnings using `lcompile.py`.
The unchanged original consumer `Sheaf.AlgebraicGeometry.GrothendieckHypercoverLocalPrimitives`
also compiles against the sandbox artifacts; it needs no adaptation.
A separate probe against the sandbox's compiled artifacts prints exactly
`[propext, Classical.choice, Quot.sound]` for the original theorem. The finite-cover proof
includes the empty index type, and the sheaf proof includes empty objects and empty refinements.
The directed-family index is a universe-small shrink of the subtype of distinct subobjects;
nonemptiness comes from the image of the given morphism, even when it is zero.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.FiniteSplitEtaleHypercover.Grothendieck.eq_zero_of_locally_liftable_maps`.

Added zero holes. Remaining holes in the item and in every new module: zero.
This is a proof, not a decomposition into unproved statements. All four new main helper
lemmas and the entire local-image construction/API are proved. The original theorem has no
transitive `sorryAx` dependency, as checked against the sandbox's artifacts.

## No longer needed

Original direct proof import `WeilConjectures.AlgebraicGeometry.EtaleSheaves` was replaced by the two local-image proof imports; the source module is still used by the helper construction. Existing repository nodes or modules withdrawn: none.
The original DAG's two definition dependencies remain relevant.

The implementation avoids the plan-only pointwise-image presheaf Q, the subobjects indexed
by finite tuples of covers, finite matching kernels, products of image epimorphisms, and an
explicit equivalence with the qcqs basis. There are no separate assigned nodes for those
constructions to withdraw. The stronger overlap clause and the module
`Sheaf.AlgebraicGeometry.EtaleQcqsCofinalFiniteCoverings` are unnecessary: the proof uses the
already proved `Scheme.exists_finite_affine_of_mem_smallEtaleTopology` in
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit` directly for finite refinement.
No unproved theorem of that module is used.

## Where the brief, the DAG or earlier work was wrong

The returned DAG omitted two substantive source-library lemmas: directed-intersection distributivity was cited only through the Grothendieck-category definition, and finite affine refinement only through the etale-site definition. Both missing theorem nodes and the exact requested dependency edits are now present. No false statement or broken tool was found. The previous proof plan did not expose the
categorical local-image and finite-cover descent APIs. The present route proves those APIs
and replaces the matching-kernel step by finite source-refinement induction. The distinction
between pullback of directed unions and arbitrary jointly epic families is maintained.

Stacks Tag 00WL treats set-valued image subsheaves; it is a source for the method, rather than
an assertion that Stacks already states these arbitrary-coefficient theorems. Tag 079A
supplies the AB5 context. Tag 03Q4 supplies the qcqs covering context; the precise finite
refinement is the cited proved source-library theorem. The categorical generalization and
finite-cover induction are recorded as agent-written arguments in the new nodes.

The item's unit `sk-prop-h2` has no realized statement/step node that this route bypasses.
No existing definition, statement, or consumer module was changed. The dry-run checker
conservatively flags the scoped private-helper `omit` and scoped linter setting as context
changes. They are documented, with identical old/new public signatures and consumer analysis,
in `coord/changes/grothendieck-etale-local-epimorphism-proof-scope.md`. No forced adaptation
is necessary.

## New nodes

`def-weil-pbc-grothendieck-etale-local-image`: the local-lifting predicate, local-image
members and their canonical union, a small directed indexing family, and the canonical
extension from qcqs test objects. Its `lean.declarations` lists the fully proved construction
API along with the primary definition. The node carries the construction and its proofs.

`lem-weil-pbc-grothendieck-directed-pullback`: pullback of a small nonempty directed union
along a map factoring through that union has supremum top. Proved by separating the mono
and epi cases and combining them through the image factorization.

`lem-weil-pbc-grothendieck-etale-local-image-detection`: local lifts detect zero maps on
the local-image subobject, for arbitrary sheaf morphisms. Proved by directed pullback and
cancellation of the pulled-back witnessing epimorphisms.

`lem-weil-pbc-grothendieck-etale-local-image-descent`: factorization through the local
image descends along finite covering families. Proved by finite induction on removed
local-lifting assumptions and the cokernel universal property.

`lem-weil-pbc-grothendieck-etale-local-image-sheaf`: the extension from qcqs test objects
is a sheaf. Proved by gluing in G, finite affine refinement and finite-cover descent.

`lem-weil-pbc-grothendieck-directed-intersection`: attaches the existing proved
`CategoryTheory.IsGrothendieckAbelian.inf_iSup_of_directed` from
`WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Subobject:53`.
It records `C : Type u`, `Category.{v} C`, `IsGrothendieckAbelian.{w} C`,
`ι : Type w`, `Nonempty ι`, directedness, and the full distributivity equality.
Source proof: filtered colimits of the subobject diagrams and their kernel sequences.
LeanSearch, LeanFinder, Mathlib grep, and local source/Sheaf searches are recorded.

`lem-weil-pbc-etale-covering-sieve-finite-affine-refinement`: attaches the existing proved
`AlgebraicGeometry.Scheme.exists_finite_affine_of_mem_smallEtaleTopology` from
`WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit:71`.
It records an arbitrary base scheme, `CompactSpace W.left`, covering-sieve membership,
and all three conclusions: membership of every selected arrow in the sieve, affine sources,
and joint surjectivity. Its source proof takes finitely many affine opens in a cover.
LeanSearch, LeanFinder, Mathlib grep, and local source/Sheaf searches are recorded.
No additional module or hole is introduced by either attachment.

All seven new nodes have three actual logged Mathlib search kinds and complete proofs; none
leaves work for a later session. The scoped-command record is
`coord/changes/grothendieck-etale-local-epimorphism-proof-scope.md`.

## Earlier second reading (a previous round; superseded)

1. Compared the delivered item module with the repository version. The target theorem's
signature, hypotheses, universes, and visibility are unchanged; the proof-only private
helper and scoped linter commands are documented in the change record. The five added
modules and their new declarations are recorded by the corresponding nodes.

2. Compiled all six delivered modules together with `lcompile.py`; they compile without
errors or warnings. Searched the delivery for `sorry`, `axiom`, `unsafe`, `opaque`,
`implemented_by`, `extern`, and `debug.skipKernelTC`; none occur. The constructions use
actual subobject suprema, pullbacks, intersections, and factorization maps. A scratch
axiom probe for the target reports only `propext`, `Classical.choice`, and `Quot.sound`.

3. Read each new node and its Lean declaration. The local-image, directed-pullback,
detection, finite-cover descent, and sheaf statements are strictly intermediate results,
with complete docstrings and DAG nodes; none restates the assigned target. Empty covers,
empty objects, zero coefficients, and zero sources are covered by the definitions and
proofs. No arbitrary data is selected from an unproved existence theorem.

4. Followed the proof downward from the target. The original qcqs assumptions and the
unit route are retained, while the proof uses the local-image API, finite-cover descent,
and qcqs sheaf construction. The source `EtaleSheaves` import remains a private proof
import where needed; no unused original import or proof dependency was removed.

5. Checked every node's Lean declaration, proof steps, `proof_deps`, and `proof_origin`
against the delivered code. The new node metadata matches the helper declarations and
the target node now follows the actual local-image route. No existing target statement or
definition was changed.

Second-reading changes: added this audit section, verified the compiled helper modules
and axiom set, and confirmed that no holes were added and no further pruning is needed.

## Second reading by C1

1. Compared the delivered item module with the repository version. The target theorem's
signature, universes, hypotheses, and visibility are byte-for-byte unchanged. The proof
imports are private, and the scoped helper/linter commands are documented in the change
record. The five new helper modules and their declarations are included in this delivery.

2. Compiled all six delivered modules together with `lcompile.py`; every file compiled
without errors or warnings. Searched the delivered Lean and DAG files for forbidden
constructs and found no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, `extern`,
or `debug.skipKernelTC`. The target's compiled axiom set is exactly
`propext`, `Classical.choice`, and `Quot.sound`.

3. Read the target proof, every helper declaration, and every new node. The target
statement is unchanged, and each helper is a strictly intermediate construction or
reduction needed by the proof. The local-image definitions construct subobjects and
factorizations directly; no definition chooses data from an unproved existence theorem.
The finite-cover arguments include empty covers, and the constructions cover empty
objects, zero coefficients, and zero sources.

4. Followed the proof downward from the target and checked the unit route. The proof
uses the local-image construction, directed-pullback detection, finite-cover descent,
and the qcqs sheaf construction, while retaining the target's qcqs hypotheses. The
source-library finite affine refinement theorem and directed-intersection theorem are
recorded as existing DAG dependencies. No unused import or proof dependency was found.

5. Compared each node's Lean declaration, proof steps, `proof_deps`, and `proof_origin`
with the delivered code. The metadata agrees with the implementation, and the two
attached source-library nodes identify their existing declarations exactly. No target
statement or existing consumer declaration was changed.

Second-reading changes: added this required audit section; no Lean proof or statement
changes were needed after the independent review.
