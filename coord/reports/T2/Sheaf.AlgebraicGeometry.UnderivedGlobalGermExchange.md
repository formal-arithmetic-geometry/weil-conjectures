## What changed

Proved `AlgebraicGeometry.Etale.underivedGlobalGerm_exchange` in
`lean/Sheaf/AlgebraicGeometry/UnderivedGlobalGermExchange.lean`, with its signature and
visibility unchanged. The proof works for every commutative square and separably closed
coefficient field, without a cartesian or invertibility hypothesis.

Five proved private helpers expose the argument: `pullback_unit_germ`, `eval_eq_res`,
`pulledGlobalGerm_app`, `lowerStarCompGlobalSectionsIso_comp`, and
`squareLowerStarIso_globalSections`. The first adapts the existing private proof in
`FiniteEtaleUnitStalkInclusion` to abelian coefficients and separably closed fields; the
second uses the existing terminal-evaluation proof in `GlobalSectionsStalkComparison`.
The other three give the canonical germ/unit identity and the coherence of global sections
with pushforward composition and the square isomorphism. The main proof uses naturality,
`unit_map_baseChangeMap_app`, and cancellation of the global-sections isomorphisms.

Updated the existing node's proof and proof origin to record these compiled steps.
The proof dependencies remain the two original nodes. No definitions, public signatures,
visibility, instances, or imports changed. No other module is adapted.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Etale.underivedGlobalGerm_exchange`
(node `lem-weil-pbc-underived-global-germ-exchange`).

No holes remain in the item, and no holes or new nodes were added. This is a proof,
not a decomposition. Every private helper is proved. Local single-file compilation passed
without warnings; the delivery dry run supplies the axiom probe and mechanical checks.

## No longer needed

None of the original imports, nodes, or modules was pruned. Both original public imports
are needed by the unchanged statement. A trial explicit proof import of
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Comap` was removed: it is already
available through the original imports. The proof requires no new imports and preserves
the unit route in `sk-thm-p1`.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The existing plan's mate-expansion step can use the already
proved library theorem `unit_map_baseChangeMap_app`; no new intermediate theorem with
`sorry` is necessary. The existential, algebraically-closed-field result
`exists_globalSections_stalk_comparison` alone is not the required interface: this item
needs the specified canonical stalk isomorphism and only assumes a separably closed field.
The proved point-comparison formulas supply that stronger normalization directly.

## Second reading by T2

1. **Unchanged interface — PASS.** Diffed the only delivered Lean module against
   the repository version. The original theorem signature and the module preamble
   (imports, namespace, universes and local instances) are byte-for-byte unchanged;
   its docstring is unchanged too. Only five private proved helpers and the original
   theorem's proof are added. No definitions, public signatures or visibility changed,
   and no change record or forced adaptation is required.
2. **Proof and axioms — PASS.** Independently compiled the module through `lcompile.py`
   without errors or warnings. Inspected all helper proofs and the main proof; scanned
   for forbidden declarations and found none, and found no `sorry`. Compiled a scratch
   copy with `#print axioms` for all five private helpers and
   `AlgebraicGeometry.Etale.underivedGlobalGerm_exchange`: every result uses exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`. No data is chosen
   from an unproved existence theorem.
3. **Split statements — PASS (none).** No statements were split off and no new holes
   or public declarations were added. The private helpers express genuine parts of the
   argument: unit/germ compatibility, terminal evaluation, pulled-germ normalization,
   composition coherence and square coherence. Their universally quantified compiled
   proofs cover identity maps and the zero sheaf as well as general maps. The square
   argument uses commutativity only and assumes neither cartesianness nor invertibility.
4. **Shortest route, imports and unit — PASS.** Searched the library for global-section
   composition coherence and unit/germ formulas, read `UpperLowerStar.GlobalSections`,
   `BaseChange.Square`, `FiniteEtaleUnitStalkInclusion` and
   `GlobalSectionsStalkComparison`, and searched Loogle for
   `"ΓNatIsoSheafSections"`. No shorter applicable public theorem was found. The two
   existing private formulas cannot be imported as public lemmas, and the existential
   comparison assumes an algebraically closed field and does not identify the canonical
   isomorphism required here. The proof uses the already proved
   `unit_map_baseChangeMap_app`, avoiding a fresh mate-expansion lemma. Both public
   imports are used in the unchanged signature; neither is proof-only. Both original
   proof dependencies are used, so `## No longer needed` is complete. Read
   `dag/units/sk-thm-p1.json`: this item is below its realized steps, and none of those
   steps is bypassed or changed.
5. **DAG agreement — PASS.** Diffed the node and checked its four proof steps against
   the helper proofs and the main proof. Only `proof` and `proof_origin` change;
   `proof_deps` remains the union of the steps' `uses` and names both imported nodes.
   The node statement and verbatim Lean signature are unchanged. No new nodes need
   validation.

Second-reading changes: appended this review and recorded independent compilation,
search and axiom evidence. No Lean or DAG repair was needed. The delivery closes one
original hole, adds zero holes, and prunes no modules.
