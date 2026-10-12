## What changed

Proved `AlgebraicGeometry.Etale.resolutionSection_canonical_whole_to_open` in
`Sheaf.AlgebraicGeometry.EtaleResolutionSectionCanonicalWholeToOpen`, with its signature
and public import unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.ConstantSectionAdjunctPullback`.

The proof represents a homology class by a global Hom cocycle, restricts it via the
free-sheaf sections adjunction, applies the two given cocycle normalizations, and computes
Ext precomposition. Private, fully proved helpers construct the free-to-integer map and
check its compatibility with the identity generator and the constant pullback comparison.
The pointwise restriction-unit helper adapts the already proved private helper in
`Sheaf.Paper.EtaleRestrictionPullbackUnitEq`; it uses the adjunction uniqueness unit equation
directly and imports no higher cartesian-square theorem.

Updated the existing node's proof, proof dependencies and proof origin to record the Lean
argument and its use of the constant-section adjunct formula. No new modules or nodes,
statement changes, definition changes to existing public declarations, or adaptations.
The unit `sk-thm-p1` and its realized route are preserved.

Validated by the prescribed single-file compiler, with no errors or warnings. The proof
works uniformly for degree zero, the empty open, identity restriction and the zero sheaf:
there is no positivity, nonemptiness or pointwise choice assumption. The representing
morphism and free-to-integer map are constructed by explicit adjunction equivalences;
the cycle witness is eliminated only in a theorem proof.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Etale.resolutionSection_canonical_whole_to_open`
(node `lem-weil-pbc-etale-resolution-section-canonical-whole-to-open`).

One of one original sorries proved. Zero holes added, zero split off, and no sorry left
in the delivered module. All private helpers are completely proved.

## No longer needed

None. No imports removed and no planned dependency nodes or modules pruned. The proof
uses the original normalization, sections, open-object cohomology, and pullback definitions.
The additional constant-section adjunct lemma supplies the generator computation.
No restriction-coherence, open-to-open, transfer, bijectivity or higher comparison theorem
is imported to prove this identity.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing DAG plan is valid and now realized in Lean.
Its previously implicit generator calculation needs the constant-section adjunct formula
and the localization-unit equation; these are recorded in the updated proof dependencies.

The shorter-route searches (Lean Finder, Loogle, and Mathlib/local grep) found useful
Mathlib identities, especially `InjectiveResolution.mk₀_comp_extMk`, but no ready-made
normalized restriction theorem. The local Stacks TeX files were absent on this machine;
the cited sources were read at https://stacks.math.columbia.edu/tag/03F3 and
https://stacks.math.columbia.edu/tag/0A50. No source or project file was downloaded or edited.

## Second reading by T1

1. **Statements and interfaces.** Compared the delivered module with the repository version. The theorem signature and all existing public declarations are byte-for-byte unchanged; the only interface-level import remains the original public import, with the added adjunct module imported privately for the proof. Verdict: pass.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it has no errors or warnings and no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. A scratch `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.

3. **Split statements and nodes.** No new split-off theorem or node was added. The existing target node remains unchanged in statement and its proof metadata now follows the actual cocycle, adjunction, and Ext calculation. Verdict: pass.

4. **Route and pruning.** The unit `sk-thm-p1` route is preserved. The proof uses the constant-section adjunct node and the open comparison data; it proves the localization-unit identity directly. I removed the stale `lem-weil-pbc-etale-inverse-image-restriction` entry from the node's `proof`/`proof_deps`, since no declaration from that node is used. Verdict: pass.

5. **Imports and delivery hygiene.** The added `Sheaf.AlgebraicGeometry.ConstantSectionAdjunctPullback` import is proof-only and is written as a plain import. No unused imports or accidental statement changes remain. Verdict: pass.

Changed the report and DAG metadata only as described above; no mathematical or public-interface changes were necessary.
