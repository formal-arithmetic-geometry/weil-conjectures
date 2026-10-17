## What changed

Repaired `Sheaf.AlgebraicGeometry.PushforwardSupportClosed` against the current
synced source library. The returned head `1cfb4debc` used
`exists_pushforward_support_closed` from the absent module
`Sheaf.AlgebraicGeometry.ProperPushforwardSupportClosed`. The repaired proof
constructs the closed support in the item itself, using the current source-library
coherent affine sections and affine finite-presentation criteria. It then applies
the degree-zero proper higher-direct-image theorem, transports finite presentation
along `rightDerivedZeroIsoSelf`, and applies finite-type support closedness.
The existing `pushforward_support_subset_of_closed_support`, with the closed set
`q(C)`, proves containment. All original public imports, the theorem signature,
and its docstring are unchanged. The node proof and proof dependencies now follow
this implementation. No other module is changed, and no definition or statement
repair or consumer adaptation is needed.

The sandbox initially contained only launcher metadata, rather than the retained
Lean and report files described in the brief. The current source was copied into
the sandbox and the returned proof route was reconstructed with the synced APIs.
This is a proof repair, not an unchanged rebase.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.pushforward_support_closed_subset`
(node `new-chow-pushforward-support-closed`).
The delivered module has zero `sorry`s. Holes added: zero. Split-offs: zero.
Imported declarations are used as the project's existing obligations; none is
restated or replaced. Single-file compilation of the repaired proof succeeded in
6 seconds before the final import cleanup; the delivery dry run rechecks the
final file and its axioms.

The argument applies without changes to zero coherent modules, empty support,
and empty source or target schemes. The closed set is the actual pushforward
support, so there is no choice of undetermined data.

## No longer needed

Removed the proof import `import all
Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`; the corresponding
public source theorem is imported directly from
`WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian`.
Replaced the retired `Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed`
wrapper with the current `WeilConjectures` module of the same suffix.
The returned proof's absent module
`Sheaf.AlgebraicGeometry.ProperPushforwardSupportClosed` and its
`exists_pushforward_support_closed` helper are not used or recreated.

Direct node dependencies no longer needed in this item's argument:
`pqf-def-coherent`,
`lem-pc-sections-higher-direct-image-quasi-coherent`,
`lem-weil-pbc-sheaf-sections-determined-by-germs`, and
`def-weil-pbc-module-stalk`.
The last two are encapsulated by the existing closed ambient support theorem;
quasi-coherence of ordinary pushforward here follows from finite presentation.
These are removals of direct proof edges, not claims that the underlying modules
are absent from the transitive import closure. No library module is withdrawn.
The blueprint unit statement and its realized steps are untouched.

## Where the brief, the DAG or earlier work was wrong

Return addressed: the pre-sync delivery's closedness helper module is absent from
the current source, and the old proof dependency imported all private helpers from
a retired `Sheaf` wrapper. The new proof avoids both and uses current public
source-library declarations. Its affine-section argument replaces the old node
step that relied on the private generator/kernel helper. The theorem's mathematical
statement is unchanged and no source error is asserted.

Searches rerun with `msearch.py`: LeanFinder for closed support of proper coherent
direct image, Loogle for `AlgebraicGeometry.Scheme.Modules.pushforward`, and grep
for support/pushforward. LeanFinder found ring-module support closedness and
closed maps, but no sheaf-level theorem replacing this argument; Loogle found the
pushforward functor and its standard adjunction/isomorphism API; grep found only
unrelated function/measure support results. Source searches found the exact
closed ambient support theorem and the affine-section/coherence APIs used above.

## Second reading by D3

1. **Interface preservation — pass.** Compared the delivered module and node with the
repository versions using `diff`. The theorem signature, namespace, visibility,
universe, docstring, and public imports are unchanged. The only Lean changes are the
proof and proof-only imports; no target, definition, or existing public declaration was
changed. The node changes are confined to `proof`, `proof_deps`, and `proof_origin`, in
accord with the implementation.

2. **Proof and axioms — pass.** Both the single-file and `--all` invocations of
`lcompile.py` compile successfully without errors or warnings. A scratch copy with
`#print axioms AlgebraicGeometry.pushforward_support_closed_subset` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. The proof contains no `sorry`, `axiom`,
`unsafe`, `opaque`, `implemented_by`, `extern`, or hollow definition. The closed set D is
constructed from the actual support and its proved closedness, so no arbitrary witness is
chosen from an unproved existence statement.

3. **Split statements and edge cases — pass.** No statement is split off and no holes are
added. The existing theorem is proved at its original strength. The construction and
containment argument do not assume nonemptiness or nonzero sections, so zero modules,
empty support, and empty source or target schemes are included.

4. **Shortest route, imports, pruning, and unit — pass.** The proof uses the current
coherent affine-section and finite-presentation criteria, the degree-zero higher-direct-
image theorem, the canonical underived comparison, finite-type support closedness, and
the existing closed-support pushforward lemma. Searches recorded in `searches.jsonl`
found no shorter sheaf-level Mathlib or library theorem. The removed direct dependencies
are exactly `pqf-def-coherent`,
`lem-pc-sections-higher-direct-image-quasi-coherent`,
`lem-weil-pbc-sheaf-sections-determined-by-germs`, and
`def-weil-pbc-module-stalk`; each is absent from the revised proof and node dependency
list. The unit record `sk-thm-p1` and its `realized` fields are unchanged; this support
lemma is subordinate to that unit and does not bypass its route.

5. **DAG agreement — pass.** Every declaration used by the Lean proof is represented by
the revised `proof_deps`, and the four revised proof steps correspond to the construction,
degree-zero comparison, support closedness, and containment code. No new node or change
record is required, and the node's statement and source remain unchanged.

Second-reading changes: none to the Lean proof or DAG beyond the already supplied repair;
this section records the independent compilation, axiom check, signature comparison,
pruning audit, and unit-route check.

