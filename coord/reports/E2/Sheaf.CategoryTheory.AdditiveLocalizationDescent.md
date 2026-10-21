## What changed

Repaired the return of delivery `85b2f7f2159`: started from the current shared
`lean/Sheaf/CategoryTheory/AdditiveLocalizationDescent.lean`, restored by the
build commit `45eba2ae8c4`, and replaced only its theorem proof. The current
statement, universes, imports, module layout and docstrings are preserved verbatim.
The obsolete change record for creating an absent module is removed from this
packet: this is now a proof-only change to an existing module.

The proof of `CategoryTheory.Functor.additive_of_additive_localization` follows
all six steps of `lem-pur-additive-localization-descent`. First transport
additivity across `e`. Additive functors preserve finite products, so a binary
product cone in `C` remains limiting after both `q` and `q ⋙ G`. Apply
`preservesLimit_of_preserves_limit_cone` to obtain preservation by `G` of the
image diagram. Essential surjectivity and `preservesLimit_of_iso_diagram`
transport this to every binary diagram in `D`. Cancellation by mapped
essential-image isomorphisms reduces zero-map preservation to
`(q ⋙ G).map_zero`. The Mathlib binary-product/zero-map criterion concludes
additivity. No assumption of fullness or a calculus of fractions is needed.

The existing node already describes this exact argument and its Mathlib leaves;
no node update, new imports, consumer adaptations or definition changes are needed.

## Proved and sorry left

Closed the one existing hole in
`CategoryTheory.Functor.additive_of_additive_localization`
(node `lem-pur-additive-localization-descent`). Zero holes remain; zero holes
are added; zero statements are split off. No additional declarations are added.

The repaired current module compiled through `lcompile.py` with exit code 0,
no diagnostics, in 1.4 seconds. A separate axiom probe compiled successfully
in 1.3 seconds and reports exactly `propext`, `Classical.choice` and
`Quot.sound`, with no `sorryAx`. The delivery preflight also checks the declaration.

## No longer needed

None. No imports, nodes, modules or dependencies are removed. All four existing
proof dependencies are Mathlib leaves used by this route: additive functors,
preadditive categories, additive categories, and the binary-product/zero-map
criterion. The localization hypothesis remains unchanged as a statement
dependency, although the argument needs only additivity and essential
surjectivity of `q`. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery reconstructed the file when it was absent at its base
`ca371c7a0`. Before landing, the shared branch restored the file, so the landing
correctly returned that stale packet. This repair starts with the restored
current file and applies only the complete proof body, rather than re-pushing
the previous created-file version.

The node's source-place description mentions full faithfulness on natural
transformations, while its reviewed six-step proof and the delivered proof use
products and zero maps. Its existing proof and dependencies need no correction.
Zero objects and zero summands require no exceptions: the construction only
transports objects and limit cones and never lifts arbitrary morphisms through
`q`.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
