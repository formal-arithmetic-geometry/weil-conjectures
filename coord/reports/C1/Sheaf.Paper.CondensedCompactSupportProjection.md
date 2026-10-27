## What changed

Replaced the sole hole in `Sheaf.Paper.CondensedCompactSupportProjection`,
`WeilConjectures.CompactSupportCondensedRealization.condensedProjection_refinement`,
by a `calc` proof chaining two explicitly named constituent equalities through
their common composite. The composite is written out in both statements. Added proof-only
imports of `Sheaf.Paper.CondensedPushScalarComposition` and
`Sheaf.Paper.CondensedProperOpenScalar`.

The first new theorem factors the original left side through the proper scalar
mate for `d.g`, the proper image of the three-map coefficient/open-lift paste,
and the original target compositor transported along `r.hom_g`. Its proof plan
uses proper coefficient compositor compatibility and naturality, independently
of scalar-extended constructibility. The second new theorem identifies this
same explicit composite with the original right side, using coefficient
compatibility of the open-unit-normalized lift and its final proper image.
Neither statement asserts the whole refinement square. Neither depends on the
other or uses the upper theorem.

Every arrow is an existing core construction. No new data definition, comparison
map, or choice is introduced. Existing theorem signatures, definitions, public
imports, exported instances, and the refinement composition proof are unchanged.
The item node records the two pasted steps and their transitive combination.
Validation: `lcompile.py --all` compiled all three packet modules cleanly.

## Proved and sorry left

Closed the original direct hole in
`WeilConjectures.CompactSupportCondensedRealization.condensedProjection_refinement`
(node `def-pur-condensed-compact-support-projection`). The item module has zero
direct holes. Its existing `fieldRefinement_comp` proof is preserved.

Added exactly two named holes:

- `WeilConjectures.CompactSupportCondensedRealization.condensedPushScalar_refinement_factorization`
  in `Sheaf.Paper.CondensedPushScalarComposition`, node
  `lem-pur-condensed-push-scalar-composition`.
- `WeilConjectures.CompactSupportCondensedRealization.fieldProperOpen_scalar_pasting`
  in `Sheaf.Paper.CondensedProperOpenScalar`, node
  `lem-pur-condensed-proper-open-scalar`.

This is a decomposition: one hole closed, two holes added, net minus one hole
closed. It is not a sorry-free proof of coefficient compatibility. Each remaining
hole is exactly `:= by sorry`, with its source and complete proof in words in its
docstring and a matching node.

## No longer needed

None. No existing import, module, node, or unit step is pruned. The existing
refinement composition dependencies remain used. The new modules publicly
import only the core supplying their statements. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original third proof step bundled the proper
coefficient compositor law with the coefficient compatibility of the normalized
open lift without separately stating either pasted conclusion. The two new
statements expose these distinct portions of that argument.

Direct component and generic pasting proofs from primitive coefficient squares
elaborated completely, but kernel checking exceeded the file limit. Local
irreducibility, implicit reducibility of thin presentation aliases, typed local
aliases, named generic proof lemmas, and focused component rewrites were tested.
The delivery states the two actual pasted conclusions and combines their
already-checked arrow equalities in local facts. Explicitly reconstructing the
intermediate in the item also exceeded the kernel limit; retaining the imported
types avoids that reconstruction. All diagnostic files and settings are
excluded from the packet.

Edge cases checked mathematically: identity refinements give the original
proper unit/compositor laws; identity coefficient maps give their scalar-unit
versions; zero inputs and empty schemes give zero morphism equations. The
proper scalar comparison is used only as a morphism. The first constituent
requires no constructibility of the scalar extension; the second explicitly
uses precisely that hypothesis for normalized-lift uniqueness. The unit's
route and all original normalizations are retained.

## New nodes

`lem-pur-condensed-push-scalar-composition`: the proper coefficient compositor
and naturality factorization of the original left side. Its argument expands
projection/refinement components, derives the restriction/direct-image
composition square from section maps, takes scalar mates, transports along
`r.hom_g`, and pastes the two naturality equations. The resulting composite
still contains the scalar image of the original open lift.

`lem-pur-condensed-proper-open-scalar`: the normalized proper/open coefficient
pasting equality from that explicit composite to the original right side.
Its argument transposes under the open adjunction, checks the original open
unit and proper counit normalization, uses uniqueness at the scalar-extended
bounded constructible object, then applies the final proper image and the
original compositor.

Both nodes belong to `sec-smooth-purity`, unit `sk-thm-purity-transport`, and
inherit the route to `thm-pur-rational-and-qbar-purity`. They are agent-formulated
constituents of Steps 15–16, not literal numbered results of Bhatt–Scholze.
No change record is required: no existing interface or construction changes.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
