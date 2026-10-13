## What changed

Proved `AlgebraicGeometry.schemeOpenUnionImageComplex_shortExact` from a new sheaf-level
pullback theorem in `Sheaf.AlgebraicGeometry.OpenUnionModuleImagePullback`.
The proof establishes composition zero from pullback commutativity, proves overlap
epimorphy using `injective_restriction_surjective` and the restriction-unit identity,
and transports pullback exactness through the degreewise biproduct comparison.
It finishes with `HomologicalComplex.shortExact_of_degreewise_shortExact`.
Existing signatures and public imports are unchanged. Three proved private helpers
establish the needed epimorphisms. The existing node now records this route.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.schemeOpenUnionImageComplex_shortExact`.
Added one hole: `AlgebraicGeometry.schemeOpenUnionModuleImage_isPullback`, node
`lem-pc-open-union-module-image-pullback`. There are no holes in the target module.
This is a decomposition, net holes zero: the new statement is strictly the
sheaf-gluing part, applies to one arbitrary module sheaf, and has no injectivity
or complex hypotheses. The parent proves all the injective and homological glue.

## No longer needed

No original import or dependency is pruned. The cover-of-X modules
`KInjectiveMayerVietorisExact` and `KInjectiveMayerVietorisDegreewise` are not imported:
they require U sup V = top and start at I rather than the image on the union.
The exploratory zero/degreewise auxiliary module was discarded; it is not delivered.

## Where the brief, the DAG or earlier work was wrong

The stated proof dependencies do not expose gluing for an arbitrary open union.
The existing `schemeOpenModuleImage_isPullback` requires U sup V = top and has
M at the upper left, so it cannot be applied directly. The new helper isolates
that missing sheaf-level step. Empty opens, repeated opens and the empty scheme
satisfy exactly the same sheaf axiom, without extra assumptions.

## New nodes

`lem-pc-open-union-module-image-pullback`: the fixed restriction square of open images
is a pullback for one module sheaf. Source and complete proof are in its docstring
and node. No existing statement, definition, interface, or unit route changes.

## Second reading by H3

1. Compared the complete delivered target module with the repository using diff,
   and checked declaration records: the existing theorem statement is byte-for-byte
   unchanged, no declaration is removed, and public imports are unchanged. No existing
   definition or interface changes, so no change record or forced adaptation is needed.
2. Compiled both delivered modules through lcompile.py in import order, without errors
   or warnings. Read all proof bodies, including the three private epicity helpers.
   The target contains no sorry; the new helper has exactly its reported named theorem
   with `by sorry`. No forbidden declarations or hollow definitions are present.
   A scratch module printed axioms of both public theorems: only propext,
   Classical.choice, Quot.sound and sorryAx. The parent uses the open pullback helper,
   so it is a conditional reduction, not a claim of a sorry-free target.
3. Checked the split-off pullback square against the fixed transported restriction
   maps. Sectionwise its four terms are M(T intersect A), and sheaf gluing on
   T intersect (U union V) proves precisely the claimed universal property.
   Empty opens, an empty scheme, U = V, and one open contained in the other all
   satisfy this statement without additional hypotheses. The docstring gives
   the complete natural-language construction and uniqueness argument; its node
   records the exact Lean statement. Independent Loogle and Lean Finder searches
   found isLimitPullbackCone, existsUnique_gluing and interUnionPullbackConeLift;
   these are sectionwise tools, not this transported square. Local searches of
   lean/Sheaf, lean/WeilConjectures and Mathlib found no duplicate. The existing
   cover-of-X pullback has a different upper-left object and cannot be applied
   without further restriction/comparison work. Closing the new hole requires
   that transport and assembly; it is not a few-minute direct application.
4. Read the proof from the target downward. The parent proves epimorphy using
   the existing injective restriction theorem, cancellation of the restriction
   unit identity, and the biproduct inclusion. Mathlib's pullback exactness and
   evaluation biproduct comparison then give degreewise short exactness. All
   imports are used by the statements, actual proof or the remaining helper's
   stated proof dependency. Neither original proof dependency is obsolete.
   The unit sk-thm-picard-duality has realized = {statement: [], steps: [[]]};
   this delivery changes none of its statement, steps, realizations or route.
5. Checked the old node, both delivered nodes and their declarations. The parent's
   proof/proof_deps/proof_origin describe the actual Lean reduction. The new node
   has its source, complete proof plan, searches, creation, blueprint, unit,
   chapter and exact Lean record. Its sole proof dependency is the existing
   section-restriction comparison. One upper hole closed and one strictly simpler
   sheaf-level hole added: decomposition, net holes zero; no module is pruned.

Second-reading changes: added the missing plain proof-dependency import
Sheaf.AlgebraicGeometry.OpenModuleImageSectionRestriction to the new pullback
module; corrected its node's source place to Tags 01EB and 08BV, matching the
argument and docstring; recorded independent search results. No proved body,
existing signature, definition or public import was rewritten.
