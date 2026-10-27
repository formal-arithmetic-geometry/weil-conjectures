# Q60 stage-1 delivery: lem-sfb-nodal-branch-quasi-split-spreading

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-branch-quasi-split-spreading.json: statement, split; six proof steps, no change to its statement or statement dependencies. Mathlib searches find no match for the whole item.
- citations.json: verbatim statements for every step/node citation.
- report.md: this report. searches.jsonl retains the actual search-command log; write_split.py is a sandbox-only preparation helper.

Zero new nodes; zero new Mathlib leaves. The proof reuses existing nodes rather than adding branch-criterion or generic-splitting duplicates.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for quasi-split, quasiSplit, quasi_split, nodal and branch combinations. There is no declaration stating this item. Mentions of nodal curves in duality and other docstrings do not state the required theorem. The branch construction's Sheaf module is not evidence of a finished project theorem for this item.

## Wanted literature

WANTED: literature/de-jong-families-curves-alterations-1997.pdf, definition immediately before Lemma 5.7 and Lemma 5.7 first proof paragraph, printed p.615, for lem-sfb-nodal-branch-quasi-split-spreading. The local PDF is absent. I read the publisher's primary scan at https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf (PDF page 17, zero based), without downloading it. The proof is marked agent-written because it implements the relative branch-scheme reformulation rather than reproducing de Jong's simultaneous-normalization argument.

## Audit of the imported item and route

The statement is correct as imported. No STATEMENT-DISPUTED change is needed. Properness is used for the finiteness of the branch scheme over the base, and finite presentation gives finite branch fibres even without properness. Merely assuming local finite presentation would not justify a finite number of nodes in the first clause; the item has the required stronger assumption.

The current unit and chapter were read. This is a prerequisite below the direct-image constructibility alteration route, not a key unit node, so no unit realization record is changed. blueprint_refs.py ancestor returns None for this chain, and the inherited null ancestor and full via chain are retained. Whole-blueprint searches for quasi-split, branch scheme and generic fibre found no blueprint node stating this item; same_as remains empty. Existing DAG nodes provide every tool needed. No SGA source is used.

The original Mathlib searches are retained as historical data. Six new searches were actually run through msearch.py (LeanFinder twice, Loogle, grep twice, LeanSearch); searches.jsonl contains the exact results. The first search formulation concerns nodal branch rationality, the second concerns generic splitting of a finite scheme. Hits are residue-field maps, the classification of etale field algebras, finite fibres, the finite affine coproduct isomorphism, generic-point transport and local isomorphisms. I read the relevant FunctionField and LocalIso source excerpts and the finite sigmaSpec isomorphism at Mathlib/AlgebraicGeometry/Limits.lean:641. None states the whole item or specializes to it in one line. The useful finite coproduct result already has the Mathlib leaf lem-weil-pbc-finite-affine-coproduct-spectrum.

## Review by Q60

I read delivery-errors B-E in full and checked the actual statements used, not just their titles. I read Stacks curves.tex Tag 0CBT (remark-quadratic-extension), Tag 0CBW (lemma-split-node) and Tag 0CBY (lemma-etale-local-structure-nodal-family), morphisms.tex Tag 02G7 (lemma-unramified-over-field) and Tag 01TX (lemma-noetherian-finite-type-finite-presentation), and limits.tex Tag 01ZM (lemma-descend-finite-presentation). The publisher's de Jong scan confirms that the rationality of normalization branches is the intended definition, that smoothness of components is not required, and that the proof spreads a generic trivial finite cover to an open subset. No new source-backed node was created.

Step 1 uses the statement of lem-sfb-nodal-branch-double-cover for precisely its fibre comparison, reduced singular fibre, degree-two cover, and finite-etale fibre clauses. Flatness, local finite presentation, the dimension-one condition and geometric ordinary double points are all present in the item. The explicit definition def-weil-etale-morphism supplies unramifiedness, and lem-trf-unramified-field-fibre-decomposition supplies the decomposition into field spectra; it is not used as a bare definition. Finiteness of the index set follows from finite-dimensionality of the coordinate algebra, using the affine finite-morphism definition. I wrote that finite-dimensional argument instead of introducing a new elementary node.

Step 2 applies the actual rationality and two-point clauses of def-sfb-quasi-split-nodal-fibres to the normalization fibre identified in Step 1. Each field summand is then the ground field. Step 3 proves the converse, rather than introducing a new lemma that restates it: the degree-two fibre is nonzero, a branch over each singular point exists, and the canonical field maps k -> k(d) -> k(b)=k show that k(d) is k. The degree then counts exactly two rational branches. This checks that rational branches force rational singular points, with the structure maps respected. A field homomorphism is injective, so the definition's surjectivity is equivalent to the isomorphism used by the item.

Step 4 uses the proper clause of lem-sfb-nodal-branch-double-cover, and the finite base-change clause of lem-trf-finite-radicial-basechange; it does not assume flatness of B_f over V. On an affine Noetherian open W containing xi, the closed integral subscheme T gives S=Spec(A/I). Noetherianity of A/I is proved by the correspondence of ideals, so there is no uncited global Noetherian-subscheme theorem hidden here. The finite-morphism definition gives affine Z, and pqf-lem-finite-fp-locnoeth gives finite presentation. This citation really states finite presentation, not merely finite type.

Step 5 uses the existing finite affine coproduct Mathlib leaf, including the empty product. Its coordinate algebra is finite as a module, hence Y is finite by the definition and finitely presented by the same finite-over-locally-Noetherian lemma. The generic-isomorphism lemma explicitly requires all three schemes affine and the base integral. Those conditions have now been checked for Z,Y,S. It allows empty fibres. Thus its conclusion gives an open U containing xi and an isomorphism over U; it is stronger than a pointwise identification, which is exactly what this step needs.

Step 6 pulls back this isomorphism to residue fields and invokes the criterion already proved. Since U is open in a closed subscheme of V, its points have the same residue fields as their images in V. The pullback identifies the displayed branch fibre with the one in the criterion. No normalization-of-total-spaces/base-change assertion is used.

I tested the empty family and smooth family (D=B=empty, n=0), a rational split node (two rational branches), a nonsplit rational node (a quadratic branch algebra, so not a union of ground-field spectra), and nodes at nonrational finite-separable points (the field-tower argument prevents rational branch points). The proper smoothing example xy=t is compatible with the proof: its generic branch scheme is empty, and shrinking removes the special node. Persistent rational nodes give a nonzero even n. The proof does not infer constant degree over all of T, only over the resulting open. Characteristic two causes no change because the branch-cover comparison already provides etaleness, with no quadratic-form calculation here.

All non-elementary arguments are cited; the forward and reverse finite-point calculations and final base-change assembly are elementary steps. None of the six steps exceeds 2000 characters. No hidden standard comparison or new subclaim is being passed off as a long step. The only draft corrections were two source-tag numbers: finite base change is 01WL, not the composition tag 01WK, and finite affine disjoint union is 01I5, not 01Z0. I checked these in the local tag map. Every citation quote is the verbatim cited statement, copied from the current DAG.

## Tool uses

The generic field decomposition lem-trf-unramified-field-fibre-decomposition, finite-presentation result pqf-lem-finite-fp-locnoeth and affine generic-isomorphism theorem lem-sbc-generic-fibre-iso-spread-base-open are generic tools from other units. Their exact uses and why the nodal unit does not replace them are declared in split_report.tool_uses for maintainer review. The other off-unit results are existing Mathlib leaves or definitions.

## Not duplicates

No new nodes; no new/existing tag pairs to compare. Existing branch-cover, finite affine coproduct, finite-presentation and generic-isomorphism nodes are cited directly.

## Unfinished work

None within the stage-1 split. Existing dependency nodes remain in their current states; no claim is made that their Lean proofs are complete. Delivery validation is performed by the required server dry run.
