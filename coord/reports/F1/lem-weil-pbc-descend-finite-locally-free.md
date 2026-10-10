# Worker report: lem-weil-pbc-descend-finite-locally-free

## Files delivered

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-descend-finite-locally-free.json`: existing statement split into four steps; statement unchanged.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-descend-flat-finite-presentation.json`: new unsplit statement, Stacks 04AI flatness descent; no Mathlib match.

The stale partial children `lem-weil-pbc-colimit-flat-finite-presentation` and `lem-weil-pbc-finite-flat-is-locally-free` are unnecessary to this split and should be excluded from the delivery if uncommitted. They are not proof dependencies. No Lean, compilation or git operation was performed.

## Attachments

None.

## WANTED

None. Stacks sources are available in `/tmp/stacks-project`. Initial source reading and Mathlib source grep were performed against the server copies before the lead prohibited further server source reads; no further server reads were performed after that instruction. This report does not represent those reads as local checkout searches.

## Sources and cited statements checked

Read Limits `lemma-descend-finite-locally-free` (06AC), `situation-descent-property` (081D), and `lemma-descend-flat-finite-presentation` (04AI); read Morphisms `lemma-finite-flat` (02KB), `lemma-base-change-finite-presentation` (01TS), `lemma-finite-presentation-finite-type` (01TW), and `lemma-base-change-finite-locally-free` (02KD). The item follows the two paragraphs of 06AC, expanding the hypotheses and intermediate base changes. The new child states precisely 04AI in the explicit setting of 081D: only S_0, X_0, Y_0 are assumed qcqs; f_0 is locally of finite presentation, and flatness is assumed after base change to the limit.

Step 1 uses `lem-weil-pbc-descend-finite`, whose statement requires finite f and locally finite type f_0; the latter follows directly from the finite polynomial presentation in `def-sbc-locally-finite-presentation` and `def-weil-finite-type-morphism`. The new 04AI child gives flatness at another stage. `lem-weil-pbc-cartesian-square-pasting` identifies the later morphism as the base change of either earlier one. Clause (a) of `lem-weil-pbc-finite-morphism-permanence`, `lem-weil-pbc-flat-morphism-base-change`, and clause (3) of `lem-weil-pbc-qcqs-morphism-permanence` preserve finite, flat, and lfp respectively. `def-pc-finite-locally-free` defines their conjunction as finite locally free, so a separate criterion child would add nothing.

Step 2 uses `lem-weil-pbc-finite-locally-free-degree-locally-constant` for the clopen degree-d locus. Clause (2) of `lem-weil-pbc-finite-flat-rank-iso` states the rank equality under arbitrary base change and identifies rank with fibre degree. Together with square pasting this proves that the image of Y lies in the locus; local constancy alone would not prove that inclusion.

Step 3 uses `lem-weil-pbc-scheme-over-limit`, whose statement gives Y as the limit of its base changes and affineness of their transitions. `lem-weil-pbc-affine-morphism-permanence` states that affine morphisms are qcqs; clause (2) of qcqs permanence then gives qcqs Y_j from qcqs Y_0. The step writes out why a clopen subset is retrocompact, hence constructible by `def-weil-constructible-subset`. The existing `lem-weil-pbc-limit-contained-in-constructible` states precisely the constructible specialization of Limits 05F4 (`lemma-limit-contained-in-constructible`): a constructible subset containing the image of a qcqs affine-transition limit contains the image of every sufficiently late stage. All its hypotheses are supplied here.

Step 4 repeats the three permanence statements and uses the rank base-change clause pointwise. Every image point belongs to W_d, so the resulting fibre dimension is d, exactly the degree condition of `def-pc-finite-locally-free`.

## B–E checks and repairs

B: The only necessary new child is unsplit, with empty proof and proof dependencies. Its statement introduces the directed index set, chosen base index, schemes, transitions, limit, morphism and all base changes. Scheme, affine morphism, qcqs, fibre product, flatness and lfp notions cite their definition/interface nodes. Its source uses tag 04AI and the TeX label, rather than a changing section number. TeX uses single mathematical backslashes after JSON decoding. No Mathlib leaf is claimed.

C: Searched the existing DAG by the 04AI/flat-descent concept and by existing filenames before retaining this partial child. Reused existing finite descent, rank/local-constancy, scheme-over-limit and 05F4 nodes. Each substantive proof fact is carried by a cited statement; source tags are source locations, not substitutes for dependencies. The lfp-to-lft observation is written out as the finite-generation consequence of a finite polynomial presentation. No external-unit proof route replaces the unit's argument.

D: The split contains the actual simultaneous-descent and degree-locus argument. The new 04AI fact is strictly smaller: it asserts only eventual flatness and has no finite or degree assertion. Removed the unnecessary algebra-descending-flatness grandchild from the item's dependencies and the tautological finite-flat criterion child. The child itself remains unsplit.

E: Checked finite descent's locally finite type hypothesis, flat descent's lfp hypothesis, common-stage base-change identifications, and every qcqs/constructibility hypothesis of 05F4. The rank equality is explicit in both uses. Tested the empty-base and degree-zero cases: image containment and the pointwise degree condition remain valid, including when the degree-d locus is empty. No claim of factorization through a closed subscheme from set-theoretic containment is used; the argument only needs rank at image points. No source error was found.

## Mathlib searches actually performed

For the new 04AI child, LeanSearch query: “flatness descends to some stage of inverse limit of schemes affine transition morphisms locally finite presentation”. Results included `Flat`, `Flat.flat_of_affine_subset`, flat-descent instances in `Morphisms.FlatDescent`, and `instLocallyOfFinitePresentationOfIsSmooth`; none is inverse-limit descent. LeanFinder query: “flatness of finitely presented morphism descends along inverse limit of schemes”. Results: `UniversallyOpen.of_flat`, `Flat.instDescScheme`, `Flat`, `Flat.instHasRingHomPropertyFlat`, `Flat.comp`; none matches. Actual read-only server grep over the pinned Mathlib `AlgebraicGeometry` tree for `stacks 04AI|colimit.*flat|flat.*colimit` found no matches. These three records are in the child. Existing item searches were retained.

Additional exploratory searches for the finite-flat criterion returned `IsFinite`, `Flat`, and local-finite-presentation APIs, while Loogle located `Scheme.Hom.isLocallyConstant_finrank`; neither justified a new leaf. Loogle and LeanSearch also confirmed the finite-presentation base-change instance and lfp-implies-lft instance. Read `FinitePresentation.lean` around lines 62–92, including the base-change instance at 85; these were exploratory checks and did not create a new leaf.

## Validation and remaining limits

`python3 tools/review_split.py lem-weil-pbc-descend-finite-locally-free`: PASS. `python3 tools/check_dag.py`: zero cycles and zero self-loops; eight reach errors elsewhere in the shared tree. Two unnecessary partial child files remain a delivery-scope decision for the lead. The item and necessary child are complete for this worker's stage-1 scope; final mathematical review and any `reviewed` field belong to the lead.

## Review by F1

I read `limits.tex` at Situation 081D, Lemma 04AI (`lemma-descend-flat-finite-presentation`, line 1868), Lemma 06AC (`lemma-descend-finite-locally-free`, line 1902), and Lemma 05F4 (`lemma-limit-contained-in-constructible`, line 530). The item's statement has the qcqs schemes, affine transition maps, locally finite presentation of `f_0`, and finite locally free limit morphism required by 06AC; the degree clause is conditional exactly as in that lemma. The new unsplit 04AI child introduces the entire inverse system and base changes, then concludes only eventual flatness. Its source, definition dependencies, actual three search kinds, empty proof and `created.item` meet B1–B7; neither stale partial child is included.

Step 1 checks the locally finite type hypothesis of the existing finite-descent node from a finite polynomial presentation, uses the new 04AI node for flatness, and passes both to a common later stage through the cited square-pasting and permanence statements. The qcqs-permanence node's clause (3) explicitly preserves locally finite presentation under base change, so `def-pc-finite-locally-free` applies. Step 2 uses the stated clopen degree locus and the rank-base-change clause to place the image of `Y` in it. Step 3 uses the scheme-over-limit and affine/qcqs permanence statements to meet 05F4's limit hypotheses; a clopen subset is locally constructible. Step 4 uses the rank-base-change statement again to transfer degree `d` to every point of the later stage. Each non-elementary fact is in a cited node's statement, and the steps reproduce the two paragraphs of 06AC without replacing the unit route (C1–C7, D1–D5).

I checked that no argument treats set-theoretic image containment as scheme-theoretic factorization: only pointwise rank is used. Empty `Y` and degree zero make the image/rank clauses vacuous or tautological; no nonempty degree locus is assumed. The new 04AI child is not a restatement of finite locally free descent and has no proof hidden in its statement (E1–E5). The worker discarded a tautological finite-flat child and an unnecessary colimit child from the dependency route. Preflight follows on an isolated branch.
