## What changed

Proved `AlgebraicGeometry.Scheme.Modules.moduleCup_equal_derived_maps_class` with its
signature, universes, hypotheses, and visibility unchanged. The proof obtains a common
resolution-class comparison and derived homology tensor from their existing proved APIs,
then applies the global naive/derived diagram to D and E. The two one-pair formulas agree
by `hmaps`, `ha`, and `hb`; injectivity of the class comparison gives the result.

Added the fully proved module `Sheaf.Paper.ModuleCupOnePairingHomology`. Its public theorem
`moduleCup_one_pairing_homology` computes one realized pairing using the supplied global
diagram. Three proved private helpers handle categorical augmentation cancellation,
naturality of localized cycle classes, and evaluation of a commuting diagram on homology.
The cycle calculation uses `C.on_cycles`, `P.on_cycles`, `cyclesMap_i`, the section formula
for the naive map, and `Realizes`; no cohomological product invariance is assumed.

The only new elaboration control in the item is local irreducibility of
`Functor.rightDerivedFunctor`, with an explained heartbeat budget. All work is in the
sandbox. The library and target statements were not edited.

## Proved and sorry left

Closed the item's one original hole:
`AlgebraicGeometry.Scheme.Modules.moduleCup_equal_derived_maps_class`.

Also proved the new public auxiliary declaration:
`AlgebraicGeometry.Scheme.Modules.moduleCup_one_pairing_homology`.
The private helpers `transport_pairing`, `localizedCycleClass_map`, and
`evaluate_pairing` are complete proofs. No `sorry` remains in either delivered module;
zero holes were added. This is a proof, not a decomposition into new open obligations.

Both modules compile within the 60-second limit. The standalone lower-formula check took
53 seconds with its final transparency setting; the last full two-module check before
that setting refinement took 57.1 seconds and 39.6 seconds respectively. The final dry run
is the authoritative compile and axiom verification.

## No longer needed

Removed these direct private imports from the item:
`Sheaf.Paper.ModuleCupNaiveDerivedCompatibility`,
`Sheaf.Paper.ModuleCupResolutionData`, and
`Sheaf.Topology.RingedSpaceModuleCohomology`.
The first remains a dependency through the lower formula, and the other two are supplied
by the preserved public statement interface. No whole library module is withdrawn.

The equality proof no longer calls `moduleCup_resolution_realization` or its canonical
H-zero normalization: it evaluates the supplied realizations directly. Its module remains
publicly imported to preserve the item's existing exported interface. The DAG's old direct
proof dependencies `lem-sc-module-cup-resolution-realization`,
`def-sc-module-cup-resolution-data`, and `def-sc-ringed-space-module-cohomology` are replaced
by the class-comparison, homology-tensor, global-diagram, and proved one-pair formula nodes.
The definitions still occur transitively where they are needed.

## Where the brief, the DAG or earlier work was wrong

An earlier draft attempted to introduce a second existential evaluation theorem. It was
discarded during this session, before delivery. The final proof instead uses the already
proved `CupDerivedClassComparison` and `CupDerivedHomologyTensor` APIs and proves their
one-pair evaluation formula completely. Neither downstream
`moduleCup_realization_evaluation` nor `moduleCup_resolution_invariance` is imported;
both depend on the assigned theorem and would create a cycle.

Past repairs recorded a single-pair formula but left it open or encountered slow
elaboration. The final formula is proved. Generic categorical cancellation and generic
homology evaluation avoid repeatedly unfolding the sheaf presentations. All sheaf
singleFunctor occurrences specify the category explicitly. The unit's `realized` record
contains no fixed lower-level route that this argument bypasses. Degree zero, zero cycles,
and zero modules are included; the proof uses no positivity or nonzero hypothesis.

## New nodes

`new-module-cup-one-pairing-homology` records the fully proved single-pair homology formula,
with the unchanged scheme universe, arbitrary nonnegative bidegrees, supplied natural cup
family, supplied naive map and diagram, and sectionwise realization hypothesis. Its source
is Stacks 0FKU, the global diagram following Lemma 20.31.3. The statement and all proof steps
are attached to `Sheaf.Paper.ModuleCupOnePairingHomology`; no hole is left for another worker.

Change record: `coord/changes/E2-module-cup-class-proof-transparency.md`.

## Second reading by E2

1. **Interface and accidental changes — pass.** I diffed the delivered item against the repository version. The existing theorem signature, universes, hypotheses, and visibility are byte-for-byte unchanged. The added `ModuleCupOnePairingHomology` module is a separate auxiliary statement; its node and declaration agree. No target statement or definition was changed.

2. **Proof and axioms — pass.** Both delivered modules compile with `lcompile.py --all` within the file limit. Neither module contains `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. Inline `#print axioms` checks for both public declarations report only `propext`, `Classical.choice`, and `Quot.sound`.

3. **Split statements — pass.** The auxiliary theorem is a strict one-pair evaluation formula, with no equality-of-two-pairings hypothesis and no normalization hypothesis. Its statement is needed by the target proof, covers degree zero and zero cycles, has a complete source/proof docstring, and is recorded by `new-module-cup-one-pairing-homology`. Searches recorded in `searches.jsonl` found no existing matching declaration.

4. **Route and pruning — pass.** The target proof follows the realized global diagram through the one-pair formula, then uses injectivity and congruence. The direct old proof dependencies removed from the target are not used by its proof; the one-pair module supplies the required transitive infrastructure. The unit `sk-prop-av-cube` is retained and no downstream cyclic module is imported.

5. **DAG agreement — pass.** The target node's `proof`, `proof_deps`, and `proof_origin` match the Lean proof and identify the new auxiliary node. The auxiliary node records its exact declaration, source, proof steps, dependencies, and module. No statement-change record is needed; the existing transparency record documents only local elaboration control.

I changed only the report by adding this second-reading record. No Lean proof or node repair was required after compilation, axiom, signature, and dependency checks.
