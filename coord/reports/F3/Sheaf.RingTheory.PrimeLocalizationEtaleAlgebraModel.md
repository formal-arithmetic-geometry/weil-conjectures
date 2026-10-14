## What changed

Proved `AlgebraicGeometry.Scheme.primeLocalization_etale_algebra_model` without changing its
signature or visibility. The proof uses the existing proved ring-level theorem
`AlgebraicGeometry.exists_etale_algebra_of_filteredColimit`, the principal-localization
colimit, and Mathlib localization base change. Added four proof-only imports and updated
the module/declaration proof documentation and the node's proof route.

The proof constructs the maps explicitly from the descended tensor model. It checks the
structure-map equation and scalar-tower equation, and transports the localization structure
with exactly the algebra map induced by `i`. No definitions or other modules were changed.

## Proved and sorry left

Closed the sole hole: `AlgebraicGeometry.Scheme.primeLocalization_etale_algebra_model`
(node `new-lem-sbc-prime-localization-etale-algebra-model`). No holes remain in the item,
no holes were added, and no intermediate statements were split off.

The file compiled cleanly with `lcompile.py`. The delivery dry run also checks its axioms.
The construction allows a zero ring B or C; no injectivity or field hypothesis is used.
The finite index may be empty (its product is 1), and localization at a minimal prime
requires no separate case. All constructions preserve the original universe.

## No longer needed

The old planned dependency `lem-weil-pbc-etale-finite-data-descent`, module
`Sheaf.Paper.EtaleFiniteDataDescent`, is no longer needed by this item. It was not imported
in the original file, so no existing import was removed. Its scheme-level spreading,
etaleness descent, and affine-stage argument (01ZM, 07RP, 01Z6) are bypassed by the existing
ring-level descent theorem. `Scheme.exists_isAffine_of_isLimit` and the modules providing
that affine-stage machinery are not used. All four added proof imports are used.
This is pruning of this item's route; these modules may still be required by other callers.

## Where the brief, the DAG or earlier work was wrong

The planned scheme argument was unnecessarily long: Stacks
[00U2 (10)](https://stacks.math.columbia.edu/tag/00U2) proves this algebra-localization
statement directly from filtered-colimit descent (9), principal-localization etaleness (1),
and composition (2). The library already proves the required ring-level descent theorem.
Read that module's full proof and the Mathlib localization APIs. Checked Stacks 00U2,
00CR, and 00CP online because the Stacks TeX files are absent on this machine.

The unit `sk-prop-input-spreading` has no realized nodes in its statement or step lists;
this change is strictly below the unit and preserves its spreading argument. The existing
filtered-colimit algebra lemma is used as a proved tool from another unit, rather than
replacing any unit statement or realized step. No new nodes or statement changes.

## Second reading by F3

1. PASS: Compared the sole delivered Lean module with the repository by `diff` and
   checked the existing theorem signature byte for byte with a script. Its parameters,
   universe, conclusion, namespace and public visibility are unchanged. There are no
   new definitions, signatures, adapted modules or change records. The only node fields
   changed are `proof`, `proof_deps` and `proof_origin`.
2. PASS: Independently compiled the delivered file with `lcompile.py`, without errors
   or warnings. Compiled a scratch copy with
   `#print axioms AlgebraicGeometry.Scheme.primeLocalization_etale_algebra_model`:
   exactly `propext`, `Classical.choice`, `Quot.sound`, with no `sorryAx`.
   Scanned the source: no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`,
   `extern` or explicit `sorryAx`. Read the existing filtered-colimit descent proof
   and the localization transport and tensor-base-change APIs. In particular the
   final localization uses the algebra induced by the constructed map `i`, rather
   than an unrelated algebra structure.
3. PASS: No statements were split off and no new nodes or holes were added.
   Repeated semantic search with a differently phrased LeanFinder query and searched
   `lean/Sheaf` and `lean/WeilConjectures` for localization models and etale descent.
   The returned etale-locus lemmas concern localizing an already given R-algebra,
   and do not descend a given R_p-algebra. Checked the empty finite index (product 1),
   zero B or C, and minimal primes: no nonzero, injectivity or dimension hypothesis
   is needed. The existential model is obtained from a proved theorem, as the axiom
   check also certifies; no arbitrary data is chosen from an unproved existence result.
4. PASS: The ring-level filtered-colimit descent is a shorter existing proved tool;
   the explicit tensor and localization reduction is still needed. Each of the four
   added imports is proof-only and supplies a used ingredient: descent, the principal
   colimit, nested localization, and localization base change. The public Etale import
   supplies the signature. `No longer needed` names the sole removed old proof dependency,
   `lem-weil-pbc-etale-finite-data-descent`; no existing import was removed.
   Read `dag/units/sk-prop-input-spreading.json`: no realized statement or step is
   bypassed. This generic algebra tool changes only the subordinate node's route;
   the unit's spreading argument is preserved.
5. PASS: Read both node versions and compared each new proof step with the Lean.
   The first step invokes `exists_etale_algebra_of_filteredColimit`; the remaining
   steps record the etale composite, structure equation, scalar tower, nested
   localization and tensor localization transport actually used. `proof_deps` is
   exactly the union of the recorded node uses, and `proof_origin` cites the direct
   Stacks 00U2 (10) route through (9). No new-node requirements apply.

Second reading changed only this report by adding the independent review. The proof,
imports and node route were accepted as written. Holes closed: one, namely
`AlgebraicGeometry.Scheme.primeLocalization_etale_algebra_model`; holes added: zero;
remaining holes in the item: zero. This is a proof, not a decomposition.
