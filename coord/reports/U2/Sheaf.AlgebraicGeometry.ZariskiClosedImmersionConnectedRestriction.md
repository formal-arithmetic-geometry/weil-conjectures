## What changed

Proved `AlgebraicGeometry.zariski_restriction_universe_transport` by constructing the
spectral ULift space and its closed subset, transporting the connectedness hypothesis,
applying the already proved `TopCat.spectral_closed_restriction`, and cancelling the
section equivalences in a commuting square. The statement is unchanged.
Simplified the already proved wrapper
`AlgebraicGeometry.zariski_closed_immersion_connected_restriction` to its application
of this theorem; removed its unused topological preparations.
Added the proof-only import `Sheaf.Topology.ClosedEmbeddingRestrictionTransport`.
Updated both existing nodes to match the Lean dependency route.

## Proved and sorry left

The single original sorry is reduced: the entire proof of
`AlgebraicGeometry.zariski_restriction_universe_transport` now compiles without a sorry.
The wrapper `AlgebraicGeometry.zariski_closed_immersion_connected_restriction` also
compiles without a sorry, as before.

The delivery leaves exactly one sorry, in the new public theorem
`TopCat.closed_embedding_restriction_transport_square`
(node `lem-weil-pbc-closed-embedding-restriction-transport-square`). This is only the
comparison of sheaf restriction units under a homeomorphism and identification of an
embedding with its image. It assumes no scheme, spectrality, compactness, closedness,
connectedness or restriction bijectivity. It gives two equivalences and their exact
commuting-square equation, not the desired bijection. All spectral/topological
hypotheses and the bijection deduction are proved in the original module.

## No longer needed

No imports of the existing module are removed: `Mathlib.AlgebraicGeometry.Properties` and
`Sheaf.Topology.SpectralClosedRestriction` are now used by the transport theorem;
the public imports are still needed by the unchanged signatures.
No branch of the substantive original plan is pruned. The original wrapper's former
direct dependencies (qcqs spectrality, closed immersion, spectral restriction,
conjugate unit equation, inverse-image definition) are now transitive through the
universe-transport theorem and its new comparison lemma. They remain needed and must
not be removed from the project. No existing module is rendered unreachable.

## Where the brief, the DAG or earlier work was wrong

The existing universe-transport theorem duplicated the complete scheme restriction
statement with a sorry, and the wrapper prepared spectrality and connectedness without
using them. Those preparations now occur in the actual transport proof. The spectral
restriction module is already proved, so it is used as a black box rather than copied.
The unit record `sk-thm-p1` does not realize either node as a separate fixed unit step;
the original ULift/spectral/unit-comparison route is preserved nonetheless.
LeanSearch returned an Internal Server Error; the new node records it as unavailable.
LeanFinder and grep found component tools but no exact commuting-square theorem.

## New nodes

`lem-weil-pbc-closed-embedding-restriction-transport-square`, in
`lean/Sheaf/Topology/ClosedEmbeddingRestrictionTransport.lean`, states the explicit
commuting square. Its docstring and node explain construction by the order isomorphism
on opens, the domain-to-image homeomorphism, and uniqueness of left adjoints compatible
with units. Edge cases checked: empty ambient/domain/image spaces, identity embeddings,
and arbitrary nonclosed embeddings; the comparison requires no points or closedness.
No statement/definition changes or change records are needed.


## Second reading by U2

1. Compared the delivered item with the repository file using `diff -u`: both
   existing declaration signatures and docstrings are byte-for-byte unchanged.
   Only their proof bodies and a plain proof-only import changed. There are no
   definitions or target statement changes and no change records are required.
2. Compiled both modules in import order with `lcompile.py --all`, without errors
   or warnings. A scratch copy printed the axioms of both existing declarations
   and the new comparison theorem: exactly `propext`, `Classical.choice`,
   `Quot.sound`, and `sorryAx`. The latter remains because the comparison theorem
   is open; this delivery does not claim an axiom-free completed target. Source
   scanning found exactly the one reported named theorem sorry and no forbidden
   declarations, attributes, or hollow definitions.
3. Read the comparison theorem, its docstring proof, and its complete new node.
   Its embedding hypothesis gives a homeomorphism from the domain to its image;
   the ambient homeomorphism induces an equivalence on opens preserving covers.
   These equivalences identify pushforwards, so uniqueness of left adjoints
   preserves units and supplies the required section equivalences. This works
   for empty spaces, an empty image in a nonempty ambient space, identity maps,
   and nonclosed embeddings. It asserts a commuting square, not bijectivity:
   it is strictly the categorical part of the original argument. Independent
   LeanFinder, Loogle, launcher grep and repository `rg` searches used
   inverse-image composition, presheaf equivalences and homeomorphism terminology.
   They found `presheafEquivOfIso`, `pullbackHomIsoPushforwardInv`, and unit
   uniqueness tools, but no exact cross-universe sheaf comparison. Closing this
   categorical construction is substantial and it remains explicitly open.
4. Read the spectral restriction implementation and `sk-thm-p1.realized`.
   The Lean proof transports the spectral-space instances and the connected
   intersections correctly, then proves injectivity and surjectivity by cancelling
   the two section equivalences. Neither item node realizes a fixed unit step;
   the route stays through spectral restriction. Read Stacks Tag 09ZG
   (https://stacks.math.columbia.edu/tag/09ZG): it states spectral restriction
   with nonempty connected intersections. The universe comparison is the agent's
   categorical elaboration of that application, not a separate lemma stated by
   Stacks. Removed the redundant new-module import
   `Mathlib.Topology.Homeomorph.Lemmas`; both modules still compile. All remaining
   public imports support signatures, and the two item proof imports are plain.
5. Checked all three delivered nodes against their Lean declarations. The two
   existing nodes change only proof metadata; their dependencies describe the
   wrapper application and the ULift/spectral/comparison proof respectively.
   The new node has its source, full statement, proof, search results, creation,
   blueprint, chapter/unit and verbatim Lean signature fields. The union of
   step uses equals `proof_deps` for each node. No substantive branch or unit
   step is discarded.

Changes by the second reader: removed the redundant homeomorphism import;
clarified the original-sorry count and documented the independent review.

For completeness, the wrapper's old direct dependencies removed from its
`proof_deps` are `lem-weil-pbc-qcqs-scheme-spectral`,
`def-weil-closed-immersion`, `lem-weil-pbc-h0-spectral-closed-restriction`,
`lem-weil-pbc-conjugate-iso-unit-equation`, and
`def-weil-pbc-topological-inverse-image`. The first four remain on the transitive
proof route; inverse image remains a statement dependency and occurs in the
comparison signature. Thus no node or module is pruned from the project.
