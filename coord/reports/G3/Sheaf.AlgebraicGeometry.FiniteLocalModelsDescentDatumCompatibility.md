## What changed

The item module now packages a compatible natural transport structure into an `Over.DescentDatum`. Two intermediate theorem modules state the strictly smaller construction and its diagonal/cocycle laws; both remain named `sorry` theorems with source proof descriptions.

## Proved and sorry left

The target theorem `finiteLocalModels_descentDatum_compatibility` is reduced (one upper hole closed, two lower holes added; net -1) by combining the two intermediate results and constructing all fields of `Over.DescentDatum`.
The construction theorem `finiteLocalModels_descentDatum_compatibility_datum` remains `sorry` (node `lem-weil-pbc-finite-local-model-compatible-transport-datum`).
The laws theorem `finiteLocalModels_descentDatum_compatibility_transport` remains `sorry` (node `lem-weil-pbc-finite-local-model-compatible-transport-transport`).

## No longer needed

No original import or module is pruned. Of the old item proof_deps, `lem-galois-yoneda-fully-faithful` is transferred to the construction node; `def-weil-pbc-etale-site` and `def-weil-pbc-etale-sheaf-of-sets` are no longer proof applications and remain statement dependencies. `def-pd-descent-datum` remains a direct proof dependency. A redundant new direct import of `Sheaf.AlgebraicGeometry.FiniteLocalModelsDescentDatumCompatibilityDatum` was removed from the item because the laws module publicly imports it. The site and sheaf definition nodes are used through the signatures rather than as theorem applications.

## Where the brief, the DAG or earlier work was wrong

No original statement or definition was changed. The original direct proof plan omitted a Lean-level statement for the natural comparison transport and for the universal-point proof of its diagonal and cocycle laws. These are split into two strictly smaller intermediate nodes.

## New nodes

`lem-weil-pbc-finite-local-model-compatible-transport-datum` records existence of the natural section-compatible transport.
`lem-weil-pbc-finite-local-model-compatible-transport-transport` records its diagonal and cocycle laws.

`def-weil-pbc-finite-local-model-compatible-transport` records the data structure, with no hollow data.

The universal sources Q and Q ×_T U ×_T U are etale over T because Q → U and U → T are etale. Compatibility and naturality determine transport on arbitrary points by testing on Q ×_T U and pulling back. Edge checks: U need not be surjective; Q and T may be empty; finiteness is not used in the transport construction. The unit route is unchanged. No data definition chooses a witness from an unproved existence theorem.

The second reader removed the unused public import of
`WeilConjectures.CategoryTheory.Comma.Over.DescentDatum` from the new Datum module;
the item's original import of that module remains needed for its signature.

## Second reading by G3

1. Interface: compared the item module with the repository using diff. The existing
   declaration signature and docstring are byte-for-byte unchanged; only its proof
   and one private proof import differ. The two other modules and their three
   declarations are new. No target or definition used by a target was changed.
2. Proof: all three modules compile through lcompile.py. The item constructs each
   field of Over.DescentDatum from the two intermediate results and retains the
   compatibility equation. The only direct holes are the two public named
   intermediate theorems listed above, with matching nodes and source/proof
   docstrings. There is no hollow definition, arbitrary witness chosen in a data
   definition, or prohibited declaration. The local axiom probe checks all delivered
   declarations; sorryAx remains through the two explicitly listed open theorems.
3. Split statements: read both statements and their proofs in words. Construction
   omits the diagonal/cocycle laws; the laws theorem assumes an arbitrary natural
   compatible transport and asserts only those identities. These are two parts of
   the argument, not a renamed application of the item. For the laws, Q itself and
   Q times_T U times_T U are etale over T, giving universal tests even for arbitrary
   non-etale sources by naturality. Empty Q, U, or T and non-surjective U require
   no additional hypothesis. No property of finite cardinality is needed here.
   Searched again with msearch leanfinder (extension from etale test objects),
   loogle (uliftYoneda), and rg (transport, representability and full faithfulness).
   The upstream canonical overDescentDatum requires a big-site representation
   absent from these hypotheses. No duplicate or immediately applicable shorter
   theorem was found. Closing either remaining construction in Lean needs more
   than a short repair; both are retained as explicit decomposition holes.
4. Route and pruning: inspected sk-thm-p1.json realized; this item is below its
   realized statement/steps, and the curve-calculation and PBC route stays intact.
   The old dependency accounting is corrected above. The original public imports
   support the signature; the new transport-laws import in the item is private.
   Removed the unused DescentDatum public import from the new Datum module.
5. DAG: existing statement/stmt_deps untouched; proof steps, proof_deps and
   proof_origin match the packaging proof. All three new nodes have the chapter,
   unit, creation, blueprint ancestry, searches and verbatim normalized Lean
   statements. The construction's Yoneda dependency and laws' structure dependency
   match their stated proof plans. Reviewed the sources
   [03RV](https://stacks.math.columbia.edu/tag/03RV) and
   [02W5](https://stacks.math.columbia.edu/tag/02W5): the small-site and universal-point
   arguments expand their comparison construction; they do not assume the big-site
   theorem applies directly.

Changes by this reader: removed one unused import, corrected old proof-dependency
accounting, added the independent Loogle search to the new nodes, and recorded this
review. This remains a decomposition: one upper hole closed, two lower holes added,
net minus one; no module pruning is claimed.
