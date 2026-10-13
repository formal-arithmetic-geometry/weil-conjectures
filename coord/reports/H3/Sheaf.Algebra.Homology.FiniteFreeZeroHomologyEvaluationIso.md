## What changed

Completed the body of `CategoryTheory.finiteFreeZero_homologyEvaluation_iso`, preserving its
signature and visibility. Added two proved private helpers: `fan_projection_isIso` constructs
an inverse to a product projection when every other factor is zero, and
`homObj_isZero_right` proves internal Hom into a zero sheaf is zero.

Added the public theorem `CategoryTheory.finiteFreeZero_homologyProduct` in the new module
`Sheaf.Algebra.Homology.FiniteFreeZeroHomologyProduct`. It states the coordinatewise homology
product calculation without any concentration assumption on K and without a supplied
homology evaluation map. Its cycle equation makes the comparison usable for the supplied c.
The main proof uses concentration to invert one projection, transports c across the E cycle
inclusion, uses both supplied compatibility equations, and cancels P's homology epimorphism.

Both modules compile cleanly through lcompile.py. No existing statement or definition changed,
no adapted modules, and no new definition choosing data from an unproved existence theorem.
The unit record has empty realized lists; the finite-duality/Koszul route is preserved.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.finiteFreeZero_homologyEvaluation_iso`
(node `new-v4-finite-free-zero-homology-evaluation-iso`). The assigned module now has no sorry.

Added one hole in its own module:
`CategoryTheory.finiteFreeZero_homologyProduct`
(node `new-h3-finite-free-zero-homology-product`). Its proof is exactly `:= by sorry`;
its docstring and node contain the source and full mathematical argument.
This is a decomposition: one upper hole closed, one lower hole added, net zero holes.
It is not a complete proof of the finite-free product calculation. The concentration,
explicit inverse construction, transport, and cancellation are complete Lean proofs.

Edge cases checked mathematically before stating the new theorem: E=0 and rank-zero terms
produce zero factors; empty support is a product of zero objects; arbitrary cohomology of K
is allowed and contributes all relevant coordinates. If -n is outside E's support the
surviving factor is also zero; the constructed inverse still satisfies both identities.
A zero ring or an empty site creates zero objects without changing the universal properties.
The argument uses finite support to avoid assuming exactness of infinite products of sheaves.

## No longer needed

Removed the direct proof import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact` from the assigned module;
it now belongs to the proof plan of the new product-calculation module. Its node
`lem-sc-finite-free-internal-hom-exact` remains required transitively, so this is an import
relocation, not a module pruned from the target closure. No node or module is claimed pruned.
All original public imports are preserved. No other proof import remains in the main module.

The complete list of old direct `proof_deps` removed from the evaluation node is
`def-pur-hom-complex`, `lem-sc-finite-free-internal-hom-exact`, and
`def-weil-sheaf-of-modules-category`. All three remain dependencies of the new product
node, so none is pruned from the import closure. The old direct dependencies
`lem-sc-hom-complex-projections` and `def-pur-sheaf-hom` remain in the evaluation node.

## Where the brief, the DAG or earlier work was wrong

The DAG gives the correct mathematical plan, but the finite-free short-exactness statement
alone does not supply the sheaf-valued Hom-complex product-homology comparison or its coordinate
cycle equation. Those are isolated in the new theorem. The existing
`HomologicalComplex.homology_finite_product_comparison_isIso` is restricted to abelian groups,
so it cannot directly supply this comparison in the category of sheaves of modules.

The blueprint ancestor script returns None for the assigned node: its existing blueprint.from
points at another newly created node and omits place/via. The new node follows the recorded
parent chain to `lem-sc-finite-duality`, as its parent evaluation node does; the existing
node's blueprint field was left unchanged because this delivery owns only its proof fields.

Sources read: Stacks Project [0BQY](https://stacks.math.columbia.edu/tag/0BQY), especially the
finite-free Hom computation in the proof, and [0A8X](https://stacks.math.columbia.edu/tag/0A8X),
the product Hom differential. The general product theorem is an agent-written expansion of
that computation, not a claim that Stacks directly states this exact generality.

## New nodes

`new-h3-finite-free-zero-homology-product`, in
`dag/nodes/sec-picard-framework/new-h3-finite-free-zero-homology-product.json`, isolates the
finite-free coordinate product-homology calculation. It has no concentration assumption,
no f or c from the original theorem, and no conclusion asserting IsIso of that supplied f.
The completed main proof combines its full product fan and coordinate equation with
concentration and zero-differential E transport. Searches of the library and all blueprint
nodes found no matching statement; actual Mathlib searches are recorded in searches.jsonl.
No change record is required: no existing interface changed.


## Second reading by H3

1. Compared the delivered evaluation module with the repository version. The sole existing
   theorem's signature is byte-for-byte identical; its visibility and docstring are unchanged.
   The only existing import change relocates a plain proof import. No definition, target,
   existing public import, or other module's interface changed. Verdict: passes.
2. Independently compiled both modules with `lcompile.py --all`; both compile cleanly.
   Scratch copies with `#print axioms` show only `propext`, `Classical.choice`, and `Quot.sound`
   for the two private helpers. Both public theorems additionally use `sorryAx`, as expected
   from the one named product theorem. No prohibited declaration or holed definition occurs.
   The selected product maps are used only inside a proof, never to define public data.
   Verdict: valid conditional proof; one-for-one decomposition, net zero holes.
3. Read the new product theorem and its node together with the fixed projection specification
   and finite-free exactness theorem. The coordinate functors are exact and only finitely
   many source terms are nonzero; their homology fan and cycle equation follow from kernels
   and cokernels. Checked zero source, zero rank, reversed/empty support interval, degrees
   outside support, arbitrary K cohomology, and zero ring cases. The theorem does not assume
   concentration or the supplied evaluation maps and does not restate the original item.
   Its source/docstring gives the argument, with the generalization identified as an agent
   expansion. Independent Loogle search for `"IsLimit", "IsZero"`, LeanFinder search for
   exact additive functors commuting with homology and finite biproducts, and local searches
   found general APIs, not the required sheaf-valued coordinate theorem. The existing finite
   product comparison is only for abelian groups and is itself open. Closing this new hole
   requires a substantial construction of coordinate complexes and comparisons; it is not
   a short application of an existing theorem. Verdict: true, needed, strictly lower part.
4. Read the proof from its target downward. The inverse to the surviving fan projection,
   vanishing of internal Hom into zero, transport through E's cycle and homology isomorphisms,
   and cancellation of P's homology epimorphism all implement the stated reduction. No unit
   route is bypassed; `sk-thm-picard-duality.realized` is unchanged with empty entries.
   Public imports support the statement, including sheaf/abelian/free instances; the new
   product and finite-free exactness imports are plain proof imports. No module is pruned.
   Verdict: passes after completing the report's list of removed direct dependencies.
5. Checked both node proof plans, their dependency unions, and the new node's verbatim Lean
   statement, source, searches, provenance, chapter/unit, and blueprint ancestry. Existing
   node edits are confined to proof-owned fields; the new node covers exactly the open
   product theorem. Verdict: passes.

Second-reading changes: completed `## No longer needed` with all three removed old direct
proof dependencies and their retained transitive status; added this independent review.
No Lean proof, signature, definition, import, or node change was necessary.
