## What changed

Replaced the sorry in `AlgebraicGeometry.exists_proper_limit_noetherian_core` by a
complete compiling construction. Take the proper finitely presented closed envelope
from `exists_proper_finitePresentation_closedImmersion_limit`, approximate its base,
descend the envelope to one proper stage, take the closed-image diagram, and reindex
both diagrams by a directed set. The Lean proof constructs the natural transformation,
transports both limit structures, derives stage properness by composition and base
change, and proves the commuting cone equations. All existing signatures and public
imports are unchanged.

Added two modules. `ProperNoetherianStage` is proved from upstream finite-presentation
descent and `EventuallyProper`; `ClosedImageLimitSystem` states the remaining general
closed-image reconstruction. The latter has a complete proof in words and its own node.
Updated the core node to describe the actual argument and dependencies.

Marked the existing affine clause STATEMENT-DISPUTED, without changing its statement.
All three delivered modules compile locally without warnings.

## Proved and sorry left

Proved (no direct sorry):
- `AlgebraicGeometry.exists_proper_limit_noetherian_core`
  (`lem-weil-pbc-proper-limit-noetherian-core`).
- `AlgebraicGeometry.exists_proper_noetherian_stage`
  (`lem-weil-pbc-proper-noetherian-stage`).

Sorries in delivered modules:
- `AlgebraicGeometry.exists_closed_image_limit_system`
  (`lem-weil-pbc-closed-image-limit-system`): closed subscheme reconstruction from
  stage images; the split statement concerns an arbitrary affine-transition diagram
  and contains no properness or finite-type conclusion.
- `AlgebraicGeometry.proper_limit_noetherian_affine_clause`
  (`lem-weil-pbc-proper-limit-noetherian-affine-clause`): unchanged sorry, now disputed.

These are reductions, not axiom-free final proofs: the main theorem also uses the
existing proper-envelope result, and the proved descent helper uses `EventuallyProper`.
The sorries in their dependencies are intentionally left for those items.

## No longer needed

No imports were removed from the repository version of the original item.
Second reading removed the redundant proof import
`Mathlib.CategoryTheory.Limits.Final` from the core and stage helper (already exported
by `Presentable.Directed`). In the new image module, the unused public import
`Mathlib.AlgebraicGeometry.AffineTransitionLimit` was replaced by
`Mathlib.CategoryTheory.Filtered.Basic`, which supplies the cofilteredness in its signature. Its core node originally had no
proof dependencies, so no previously recorded dependency is pruned. The construction
uses `ProperFinitePresentationClosedLimit` only for its envelope clause, and does not
need its closed-immersion inverse system itself. No separate finite-stage morphism
descent/coherence system or `FinalNoetherianBaseSystemProperties` import is needed:
one proper envelope stage suffices, and the fields of `NoetherianApproximation` supply
the base properties. No claim is made that those modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: `proper_limit_noetherian_affine_clause` is false. Choose the
singleton directed index, X = S = Spec Q, f = identity, and constant diagrams with
identity cone legs and structure map. Both cones are limits, f is proper, and S is
affine, quasi-compact and quasi-separated. The conclusion would say that Q is a
finite-type Z-algebra. A finite set of rational generators has denominators involving
only finitely many primes, so cannot generate reciprocals of all primes. Thus the
finite-type conclusion fails even when every stage is affine. Arbitrary stages cannot
be forced finite type by the affineness of their limit. The parent
`ProperLimitNoetherian` applies this false clause to an arbitrary core witness; its
affine refinement must eventually be built into the existential choice of witnesses.
This delivery preserves both signatures and does not derive any result from the false
clause.

The core node supplied no usable proof steps or dependencies: its sole step said to
apply a named intermediate construction that was not identified. Its old source
summary also differed from the current Stacks 0A0P proof, which uses a simultaneous
system of finitely presented proper approximations. The alternative here is explicitly
recorded as an argument written by N2. Stacks 0A0P, 01ZM, 081F and 01R8 provide the
approximation/descent/image ingredients, not a verbatim closed-image proof.

The local checkout lacks `literature/stacks-project/limits.tex`; Stacks 0A0P was checked
on its official page. WANTED: the local Stacks limits.tex and morphisms.tex sources for
the new image argument's references. The blueprint ancestor tool returns None for the
core node because its `created.item` is a module name; new nodes retain the actual
ancestor recorded on the parent node, with the core node added to `via`.

Edge cases checked for the new image statement: singleton systems give the original
closed subscheme; empty closed subschemes give empty image stages; cofilteredness
ensures a nonempty index, so no empty-diagram claim is made. No Noetherian hypothesis
is needed for the kernel-quotient calculation.

The unit's realized statement and steps are untouched. Finite-presentation descent
is an existing closed upstream tool used to descend the envelope; no unit route is
replaced.

## New nodes

`lem-weil-pbc-proper-noetherian-stage`, module `Sheaf.AlgebraicGeometry.ProperNoetherianStage`:
a single-stage cartesian descent assertion for a proper finitely presented morphism.
Its proof is complete Lean, using finite-presentation descent, directed reindexing,
and eventual properness. This is strictly the envelope-descent step of the argument.

`lem-weil-pbc-closed-image-limit-system`, module `Sheaf.AlgebraicGeometry.ClosedImageLimitSystem`:
a generic closed-subscheme approximation lemma for a fixed qcqs affine-transition
limit diagram. Its named public theorem has the only new sorry. The docstring and
node explain kernel images, transition factorizations, affineness, the quotient-ring
colimit, and the local-to-global limit verification. LeanFinder, Loogle and grep found no
existing declaration or duplicate blueprint statement; LeanSearch was attempted and
returned Internal Server Error, which is recorded without claiming an absence verdict. No change record is needed:
no existing statement, definition, or public import changed.

## Second reading by N2

1. Interface: PASS. Read the repository-to-sandbox diff and compared the raw signature
   slices of both existing declarations, from their theorem keyword to the assignment:
   they are byte-for-byte identical. Original public imports and docstrings are unchanged.
   There is no definition change or target change and no adaptation of another module.
2. Proof and trust: PASS as a reduction. Compiled all three modules in import order
   without errors or warnings, then compiled a scratch copy with four `#print axioms`
   commands. Each lists only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`.
   The two direct sorries are exactly the reported closed-image theorem and unchanged
   affine clause. There are no forbidden declarations or hollow definitions. The core
   really constructs its diagrams and cones: its final equation uses `hfactor`, the
   pullback projection identity, and `hw`. Properness follows from a closed immersion
   followed by a base change of the descended proper envelope. The stage helper uses
   actual finite-presentation descent, eventual properness, and pullback pasting.
3. Split statements: PASS. The stage helper assumes a proper finitely presented
   morphism and a given approximation; its cartesian square is exactly what the core
   needs. For a singleton approximation it returns the original morphism. The new
   sorry concerns a closed subscheme of an arbitrary fixed affine-transition diagram,
   not properness or finite-type models; it is strictly a part of the core argument.
   On an affine chart its image ring is `B_j/ker(B_j → B/I)`, and the filtered colimit
   is `B/I`: every element comes from a stage, while a stage class killed in `B/I` is
   already zero in that quotient. This checks the substantive local identification;
   monicity gives the compatible maps and gluing. Singleton and empty closed-subscheme
   cases hold; cofilteredness rules out the empty index category. Repeated LeanFinder,
   Loogle and grep searches with different phrases, and searched the upstream and Sheaf
   files. Read Mathlib's closed-subscheme cone construction inside
   `exists_mem_of_isClosed_of_nonempty`: it is a useful pattern, but supplies neither
   the scheme-theoretic image system nor the required pulled-back kernel equality.
   It is not a short replacement for the remaining sorry. The docstring gives the full
   kernel-quotient argument, and its source ingredients are recorded without claiming
   that Stacks 0A0P states this generic helper verbatim.
4. Route and pruning: PASS after import repairs. Read `dag/units/sk-thm-p1.json`,
   including all four `realized.steps` lists. Neither helper replaces any realized
   unit step. The closed-image route also matches steps 1–8 of the existing parent
   `ProperLimitNoetherian` docstring. The core's old `proof_deps` was empty; there are
   no old dependency nodes to prune. Removed the redundant Final imports and replaced
   the image module's unnecessarily broad public import. The upstream public import in
   the stage helper is necessary for `Scheme.NoetherianApproximation` in its signature.
5. DAG: PASS after documentation repairs. Checked every core dependency against its
   recorded declaration, the stage helper's directed reindexing, finite-presentation
   descent and eventual properness dependencies, and every image proof-step citation.
   `proof_deps` is the union of `proof[].uses`; sources and `proof_origin` distinguish
   the constructed Lean argument from the Stacks proof. New nodes have complete Lean,
   source, creation, blueprint and search records. Added missing definition citations
   to their self-contained mathematical statements and logged the independent searches.

Changes in this reading: three import repairs; new-node definition citations and
independent search records; this review and the pruning report. No proof body or Lean
statement needed repair. Independently confirmed the affine-clause counterexample:
for the singleton constant system on `Spec ℚ`, its conclusion forces ℚ finite type
as a ℤ-algebra, contrary to the finite-denominator-prime argument. The disputed clause
is not used by the delivered core proof. The maintainer must repair its existential
parent's affine refinement; the false universal clause cannot be closed unchanged.

Sources read: [Stacks 0A0P](https://stacks.math.columbia.edu/tag/0A0P) for the proper
approximation goal and [Stacks 01YX](https://stacks.math.columbia.edu/tag/01YX) for affine
projections and restrictions of limits. The kernel/image ingredient was checked against
Mathlib's `Hom.ker_apply`, `Hom.toImage_imageι` and `IsClosedImmersion.lift`; the
[scheme-image existence statement](https://stacks.math.columbia.edu/tag/01R6) also
confirms the universal closed-image factorization. The web fetch of 01R8 failed; no
claim of reading that page is made in this second reading.
