Files written:

- `dag/nodes/sec-smooth-purity/lem-weil-pbc-constructible-subobjects-noetherian.json`: split statement.
- `dag/nodes/sec-smooth-purity/lem-weil-pbc-constant-subsheaf-generic.json`: one new unsplit statement node; Mathlib search found no match.
- `citations.json`.

Attachments: none.

WANTED: none.

The Lean source was searched for the item id, its constructibility terminology, and the blueprint tag. No sorry-free declaration states this item. The existing kernel and cokernel declarations in `ConstructibleSheaf/KernelCokernel.lean` prove related closure results but do not state arbitrary subsheaf closure. The source and imported blueprint were checked against Stacks 03RY and 03RZ. The first proof step now cites the existing irreducible lisse strata node and the new generic subsheaf node. The second cites generic constancy and stalk conservativity. The induction step cites finite irreducible components, flat locally finite presentation implies open, exact stalks, stalk conservativity, and the generic subsheaf node. I checked that each cited statement supplies the fact used; no hypotheses were added or silently dropped. The new node was tested on the constant zero subsheaf, the full constant sheaf, and a proper constant submodule, and its Mathlib searches were recorded verbatim.

## Review by C1

I read the item source note and the proof text in the master blueprint, plus the source declarations in `ConstructibleSheaf/KernelCokernel.lean`. The item remains the Noetherian finite-ring constructibility assertion. Step 1 uses the existing irreducible-lisse-strata statement for the finite irreducible partition and the new node for the generic-open constant-submodule calculation. Step 2 uses the new node and the existing geometric-stalk conservativity statement to identify the constant subsheaf on the selected open. Step 3 checks Noetherian induction on closed subsets: finite components come from the existing Mathlib leaf, images of etale maps are open via the flat-lfp-open node, pullback exactness comes from the stalk exactness node, and the generic identification is propagated by the two stalk nodes. The new node is strictly smaller than the item and has only a statement, as required. Existing DAG searches found no duplicate generic-constancy node and no Mathlib theorem for it. The corrected item now records all proof dependencies and has a blueprint reference and split report.

## Not duplicates

lem-weil-pbc-constant-subsheaf-generic vs lem-weil-pbc-constructible-subobjects-noetherian: the new node treats one constant sheaf on one irreducible scheme and only produces a generic open; the existing item treats arbitrary constructible sheaves globally on a Noetherian scheme.
lem-weil-pbc-constant-subsheaf-generic vs lem-weil-pbc-constructible-module-finite-presentation: the new node is a generic geometric subsheaf calculation, while the existing node concerns finite presentation of constructible module sheaves.
lem-weil-pbc-constant-subsheaf-generic vs thm-constructible-serre: the new node proves generic constancy for a subsheaf of a constant sheaf, while the existing theorem is global closure of constructible sheaves under kernels and cokernels.
lem-weil-pbc-constant-subsheaf-generic vs lem-weil-pbc-constructible-stratification-intersection: the new node has one irreducible constant stratum and a subsheaf; the existing node constructs common refinements of two stratifications.
lem-weil-pbc-constant-subsheaf-generic vs lem-kun-03sa: the new node is about generic constancy of a subsheaf, while the existing node is a general colimit presentation of constructible sheaves.

## Second reading by C1

- Item statement: checked against Stacks Tag 03RY, Proposition 59.74.1(3), with the Noetherian and finite-ring hypotheses retained; verdict: agrees (finite commutative rings are Noetherian).
- New node `lem-weil-pbc-constant-subsheaf-generic`: checked against Tags 03RY and 03RZ and the proof under `proposition-constructible-over-noetherian`; verdict: strictly smaller generic-open assertion, self-contained hypotheses, and source tags/labels recorded.
- Step 1: checked the `W_m` open-locus argument against the flat locally finitely presented openness leaf and the irreducible lisse-strata statement; verdict: cited nodes supply the non-elementary facts, including openness and the finite constant trivialization.
- Step 2: checked the generic-point intersection and stalkwise isomorphism against the generic-subsheaf and stalk-conservativity statements; verdict: the finite intersection is nonempty on an irreducible scheme and conservativity gives the sheaf isomorphism.
- Step 3: checked Noetherian induction, finite components, pullback exactness, and etale-open images against the finite-components, flat-open, stalk-exactness, stalk-conservativity, and generic-subsheaf statements; verdict: all cited statements say the facts used and the closed-complement induction is proper.
- Edge cases: checked the zero subsheaf, full constant sheaf, proper constant submodule, a field coefficient ring, the empty scheme (vacuous item), and the finite-module cases of size zero and one; verdict: no contradiction or missing hypothesis.
- Changes: corrected the new node source place to name Tags 03RY/03RZ and the proposition/lemma labels, and added this per-step second-reading record; no proof statement was changed.
