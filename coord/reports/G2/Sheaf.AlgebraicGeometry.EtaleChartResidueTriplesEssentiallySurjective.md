## What changed

Completed `AlgebraicGeometry.Scheme.etale_chart_residue_triples_essentially_surjective`
in `Sheaf.AlgebraicGeometry.EtaleChartResidueTriplesEssentiallySurjective` without
changing its signature or its public imports. The proof follows the existing node's
spectrum construction. It constructs the neighbourhood explicitly, identifies its
ring using `ΓSpecIso` and the component of δ, and proves both compatibility equations.
The equation over K follows by faithfulness of Spec followed by injectivity of the
subfield inclusion K → Ω. Private proved helpers identify the residue-field point
under `toSpecΓ` and lift a compatible ring isomorphism through Over, Under, and the
induced category of triples. No new module, public declaration, or node is needed.

The module compiles cleanly with the required local wrapper. A direct `#print axioms`
check reports exactly `propext`, `Classical.choice`, and `Quot.sound` for the theorem.
The diagnostic command was removed from the delivered file.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.etale_chart_residue_triples_essentially_surjective`
(node `lem-weil-pbc-etale-chart-essentially-surjective`). One of one original holes
is proved; zero holes added or split off. Neither private helper contains sorry.
There are no sorries left anywhere in this delivery.

## No longer needed

None. All three original public imports are still needed by the statement. The
existing proof dependency nodes describe the definitions, Spec identities and
étale composition used in the completed proof; the proof route is unchanged.
No additional proof-only imports are needed. The previous attempt's proposed
objectwise reconstruction helper is discarded rather than added to the library.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox's objectwise helper dropped the compatibility hypotheses and
attempted to call itself recursively. It was not a valid reduction and has been
removed. The reported reconstruction obstacle can be resolved directly with
Mathlib's `SpecToEquivOfField`, `ΓSpecIso_inv_naturality`, faithfulness of Spec,
and the Over/Under/InducedCategory isomorphism constructors.

The node's planned proof is valid and has been implemented without new holes.
The unit route is preserved. The cited local Stacks TeX file is absent on this
machine, so the original Tag 04HX and Tag 04HT texts were read at
https://stacks.math.columbia.edu/tag/04HX and
https://stacks.math.columbia.edu/tag/04HT. They support the spectrum-neighbourhood
translation used here. There are no statement or interface changes and no forced
adaptations.

## Second reading by G2

1. **Repository-visible statements:** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the theorem proof and private helpers were added. The node statement is unchanged.
2. **Proof and axioms:** Compiled the module with the required `lcompile.py` wrapper. The theorem has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; a scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
3. **Statements and split-offs:** No public statements or split-off nodes were added. The two private helpers are internal proof steps, and no existing Mathlib or library declaration duplicates the target.
4. **Pruning and route:** The proof constructs the spectrum chart directly, uses the existing spectrum and affine-neighbourhood declarations, and preserves the unit route. All three public imports remain required for the theorem statement; no proof-only imports were introduced, and no old proof dependency is unused.
5. **DAG agreement:** The existing node's proof, proof dependencies, source, and unit remain consistent with the implemented construction; no node changes are needed.

Changed after this reading: added this review record only; no Lean declarations, signatures, imports, or DAG nodes required repair.
