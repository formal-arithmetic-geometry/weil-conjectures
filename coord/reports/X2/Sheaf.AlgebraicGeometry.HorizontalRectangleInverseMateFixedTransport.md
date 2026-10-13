## What changed

Replaced the sorry in `AlgebraicGeometry.horizontal_rectangle_inverse_mate_fixed_transport`
with a proof from ordinary inverse-square pasting. Added the proof-only import
`Sheaf.AlgebraicGeometry.HorizontalInverseSquareFixedPasting`, whose one theorem isolates
ordinary pasting with the fixed upper adjunction comparison. The new statement has no
right adjoint to the bottom direct image, no bottom adjunction, and no input object K.
It is an equality on QCoh inputs before applying that bottom mates correspondence.

The existing module proves the generic reindexing step in a private lemma `mate_reindex`
using injectivity of the upper adjunction Hom equivalence, `mateEquiv_counit`, and
naturality of the counit and base comparison. It combines that lemma with Mathlib
`mateEquiv_vcomp`, the proved inverse-square characterization of the duality map,
full-subcategory inclusion, and cancellation of the fixed endpoint isomorphisms.
The private helpers `fixed_mate_transport` and `endpoint_cancel` prove the composition
and cancellation steps; `source_inv_map` identifies the lifted source comparison.
The remaining private helpers prove inclusion-map and pullback-alias identities.
Existing signatures and visibility remain unchanged. The unit route remains unchanged.

Completed and repaired the earlier sandbox attempt. Its main proof timed out after
60 seconds. The final proof scopes the two transparency-respect options to the main
theorem, supplies the horizontal pullback functors explicitly to `fixed_mate_transport`,
and rewrites the duality-map equality directly with `erw`. This avoids an expensive
auxiliary equality between expressions using different pullback aliases. It then
unfolds only the target endpoint formula and rewrites its component maps explicitly,
keeping the right-adjoint comparison as the local isomorphism `r`. Removed the unused
private helper `qc_pullback_app`. The main module compiled without warnings in about
nine seconds; the original 60-second limit is unchanged. No dependency definition,
existing signature, or public import changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.horizontal_rectangle_inverse_mate_fixed_transport`
(node `lem-sc-horizontal-rectangle-inverse-mate-fixed-transport`).

Added one hole:
`AlgebraicGeometry.horizontal_inverse_square_fixed_pasting`
(node `lem-sc-horizontal-inverse-square-fixed-pasting`), in the new module
`Sheaf.AlgebraicGeometry.HorizontalInverseSquareFixedPasting`.
Its proof is exactly `by sorry`; its docstring and node give the proof in words.
There are no sorries left in the assigned module or its private helpers.
This is a decomposition: one hole closed, one strictly simpler ordinary-square hole added;
net hole reduction is zero. It is not reported as a complete proof of ordinary pasting.

## No longer needed

No imports removed and no modules pruned. All three original public imports occur in the
unchanged statement. The old direct proof dependencies
`def-pc-derived-base-change-map` and
`lem-pc-ringed-spaces-derived-pullback-composition` are now used by the new ordinary
pasting node, rather than directly by the assigned module. They remain needed transitively.
`def-sc-duality-equation-base-change-map` remains a statement dependency; its proof role is
handled by `lem-sc-duality-base-change-inverse-square-mate`.

The existential comparison in
`Sheaf.AlgebraicGeometry.RectangleInverseBaseChangeMateTransport` is not imported: it
does not identify its target comparison with the fixed one required here. Neither a
middle right adjoint nor any invertibility assumption on second mates is introduced.

## Where the brief, the DAG or earlier work was wrong

The existing proof dependencies specify definitions, pullback coherence and the
single-square inverse-mate identity, but do not state ordinary horizontal pasting with
the fixed upper comparison. `schemeDerivedBaseChange_pasting` handles an upper-left
morphism, not these two consecutive base morphisms. The new node makes that missing step
explicit. No original statement is disputed or changed.

LeanFinder and Loogle returned generic mate composition and conjugation identities;
local source searches found no fixed ordinary-square pasting theorem. LeanSearch was
unavailable (Internal Server Error). The imported blueprint search for "inverse square
pasting" returned zero matches. The source texts were read at
[Stacks Tag 0ATM](https://stacks.math.columbia.edu/tag/0ATM) and
[Stacks Tag 0ATR](https://stacks.math.columbia.edu/tag/0ATR); Tag 0ATM omits the verification,
so the new node spells out the counit-transpose and fixed-comparison argument.

Edge cases: the new statement uses only natural transformations, equivalences,
adjunction identities and inverses of the assumed ordinary squares. Zero objects and
empty schemes are allowed; identity base maps reduce to the pinned unit/composition
comparisons. The supplied upper right adjunctions may vary: their right-adjoint uniqueness
comparison r and its inverse mate κ vary together, so the identity is invariant.

## New nodes

`lem-sc-horizontal-inverse-square-fixed-pasting` isolates the ordinary inverse-square
pasting equation before the bottom mates correspondence. Its module is
`lean/Sheaf/AlgebraicGeometry/HorizontalInverseSquareFixedPasting.lean`, and its node is
`dag/nodes/sec-picard-framework/lem-sc-horizontal-inverse-square-fixed-pasting.json`.
No change record is needed: the delivery adds a new theorem with a proof-only import and
changes no existing statement, definition, public import or visibility.

## Second reading by X2

1. **No accidental interface changes.** I compared the delivered rectangle module with the repository version. The existing theorem signature and all existing declaration signatures are byte-for-byte unchanged. The only interface addition is the explicitly reported proof-only import and the new split-off theorem/module; no target statement or dependency definition changed.

2. **Compilation and axioms.** I compiled both sandbox modules with `lcompile.py --all`; both compile without errors or warnings. The repaired target has no `sorry` in its body or helpers. The split-off ordinary-pasting theorem is the sole intentional `sorry`, with its named DAG node and source/docstring. A scratch `#print axioms` check reports only the permitted base axioms plus `sorryAx` inherited from that split-off theorem.

3. **Statement and split-off review.** The rectangle statement remains exactly the repository statement. The new ordinary-pasting statement is a strictly simpler pre-mate equality: it removes the bottom right adjoint and the object K, while retaining precisely the hypotheses used to define the three inverse ordinary squares and the fixed transports. Its edge cases include identity maps, zero objects, and empty schemes. Local searches found no existing declaration duplicating it.

4. **Route and pruning.** The proof follows the unit route: ordinary inverse-square pasting is isolated first, then generic mate reindexing and `mateEquiv_vcomp` transport the equality, and finally the fixed source/target comparisons are unfolded. The proof-only import is used by the target. No unused import or old proof dependency was left in the module; no module can be pruned from this delivery.

5. **DAG agreement.** The target node’s proof, proof dependencies, and proof origin match the declarations actually used. The new node has the required statement, source, proof steps, searches, creation metadata, and Lean record, and is marked `split`. The unit route and realized target are unchanged.

Changed during this reading: no Lean proof or statement changes were necessary; I added this review section only.

Independent searches used different terms: LeanFinder for “Beck Chevalley inverse natural transformation pasting pullback associativity comparison” found chosen categorical pullback counit identities, which do not apply to derived sheaf pullback here; Loogle for `CategoryTheory.mateEquiv_counit` confirmed the generic transpose formula already used. Local searches also found étale/six-functor pasting results, whose functors differ from these QCoh derived direct images. I read the fixed comparison definitions and the unit record (`realized` is unchanged), and independently checked [Tag 0ATM](https://stacks.math.columbia.edu/tag/0ATM) and [Tag 0ATR](https://stacks.math.columbia.edu/tag/0ATR). The sources support ordinary rectangle pasting and its dual transport. No short specialization closes the remaining geometric ordinary-pasting hole. The axiom checks permit `sorryAx` from still-open imported theorems as well as the new split-off theorem; they certify absence of any additional axiom, not completion of the import closure.
