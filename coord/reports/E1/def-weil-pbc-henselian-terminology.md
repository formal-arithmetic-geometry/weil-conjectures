# def-weil-pbc-henselian-terminology

## Worker report

Item: `dag/nodes/sec-proper-base-change/def-weil-pbc-henselian-terminology.json`. No new nodes or attachments; no wanted source.

The master blueprint definition (order 1072) and the slopmaster2 sketch's “Henselian terminology” paragraph agree. Stacks `more-algebra.tex` Lemma Tag 09XI (`lemma-characterize-henselian-pair`), condition (3), states exactly the finite-algebra idempotent bijection used here; its equivalence with Definition Tag 09XE (`definition-henselian-pair`) is already the separate node `lem-weil-pbc-henselian-factorization-criterion`. Stacks `algebra.tex` Definition Tag 04GF (`definition-henselian`) gives the local and strictly henselian meanings. The notation for the closed subscheme uses `def-weil-affine-spectrum` directly, so I added that citation and statement dependency.

The complete definition has no exact sorry-free declaration in the slopmaster2 done branch at `71d63dcf`. Its `WeilConjectures/Mathlib/RingTheory/Henselian.lean` lines 29-31 identify the intended Mathlib classes, but `HenselianRing` itself is defined by the simple-root condition and Jacobson-radical inclusion; identifying it with this node's idempotent condition uses 09XI. Mathlib source `Mathlib/RingTheory/Henselian.lean` lines 94-111 confirms this. LeanSearch, Loogle and source grep are recorded in the item.

Blueprint search across all chapters found only this node stating the definition; `blueprint.same_as` is `[]`. The statement is unchanged except for the spectrum citation, and no blueprint proof step exists for this definition. As small cases, for `I=0` the reduction map on idempotents is the identity for each finite algebra; for a field regarded as a local ring with maximal ideal zero, the local henselian condition follows. The “strictly” clause still requires its residue field to be separably closed.

`tools/review_split.py` passes, `tools/blueprint_refs.py check` reports zero field errors, and `tools/check_dag.py` reports zero cycles. Its seven reach warnings concern unrelated existing nodes.

## Review by E1

I read the master blueprint definition at order 1072, More on Algebra 09XI (`lemma-characterize-henselian-pair`) condition (3) and 09XE (`definition-henselian-pair`), and Algebra 04GF (`definition-henselian`). The item's finite-algebra idempotent condition is exactly 09XI(3); 09XI proves its equivalence to the usual pair definition. The local and strictly henselian clauses agree with 04GF through that equivalence, and the added affine-spectrum citation defines the only extra notation. The statement did not change mathematically. No new node or proof step is present, so B/C/D apply only to the self-contained definition and its matching dependencies. The whole-blueprint search found no second definition with the same content, and the Mathlib root-lifting class is correctly recorded as a candidate that needs the existing comparison node. I checked I=0, a field with maximal ideal zero, and the separably closed residue-field requirement. No A-F issue was found or returned to the worker.
