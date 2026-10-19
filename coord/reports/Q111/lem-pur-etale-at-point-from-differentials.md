## Worker report

Files written:
- `dag/nodes/sec-smooth-purity/lem-pur-etale-at-point-from-differentials.json`: statement, split; six proof steps, fifteen distinct proof dependencies, no statement change. Existing Mathlib search records retained and five actually executed searches appended.
- `citations.json`: seventeen step/node entries, quoting the full statements verbatim so their hypotheses are visible.
- `report.md`: this report. `searches.jsonl` is the search command's log; `build_split.py` is sandbox-only preparation material.

New nodes: none. New Mathlib leaves: none. Existing Mathlib leaves and a Lean-closed Jacobian criterion are reused.

Attachments: none for the item. The existing attachment `Algebra.Etale.iff_exists_squareJacobianPresentation` belongs to `lem-exc-etale-jacobian-presentation`; I read its declaration and proof at `WeilConjectures/Mathlib/RingTheory/Smooth/StandardSmoothOfFree.lean:51–74`. It gives the algebra criterion used in step 6, not the scheme-level assertion about prescribed functions and a cotangent fibre, so it does not finish this item.

WANTED: none.

The imported item is a correct statement but has no proof steps. I retained its statement, source, ancestry, unit, chapter, historical searches and audit. The current blueprint ancestor's proof in `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-prop-an/lem-pur-regular-immersion-linearization.proof.md`, second paragraph, invokes the local differential criterion and shrinking. This split makes that implication explicit using affine standard smooth charts. It does not alter the unit route or use SGA. This item is not the unit's key statement, so no unit realization fields were changed.

Nothing mathematical remains unfinished in the item's split. The existing local-chart theorem is reused in its recorded state; its downstream work is outside this split. Independent second reading and actual delivery remain for the next worker; this worker runs only the required dry run.

## Searches and reuse

I searched project source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item tag and etale/differential/basis words, and checked `dag/lean_names_upstream.json` and upstream master for the exact id. No project declaration states the item. The audit is `none` on both sources. Upstream master's sorry declarations were not treated as completed proofs.

I searched the whole DAG for the tags 01V7, 00T7 and 02GU, and for standard smooth, Jacobian, cotangent/differential bases and principal opens. Blueprint searches were `Jacobian`, `etale.*differential`, `differential`, `square Jacobian`, `standard smooth`, `local coordinates`, and `cotangent`; the ancestor command returned `lem-pur-regular-immersion-linearization`. No other blueprint node states this criterion, so the item's `same_as` remains `[]`. The existing square-Jacobian node is an algebra criterion, not the chosen-coordinate scheme criterion.

Five Mathlib queries were run through the required Q111/item msearch command and their real results are in `searches.jsonl` and appended to `mathlib_searches`: two LeanFinder phrasings, Loogle on `Algebra.FormallyEtale, KaehlerDifferential`, grep for etale/differential and etale/basis combinations, and LeanSearch for the prescribed-coordinate criterion. All services succeeded. I read `RingTheory/RingHom/StandardSmooth.lean` (in particular the existential coordinate theorem at line 200), `RingTheory/Smooth/StandardSmoothCotangent.lean` (basisKaehler at 226), `RingTheory/Etale/Basic.lean` and `AlgebraicGeometry/Morphisms/Etale.lean`. Existential etale coordinates do not prove etaleness for the given functions. The formally etale differential results assume etaleness or need the extra cotangent-homology condition; none directly matches the item. I did not repeat the earlier Q32 queries or present them as my own.

## Not duplicates

No new nodes were created. The existing local-chart, differential-basis, affine stalk-localization, square-Jacobian, affine-etale and principal-open results are cited rather than duplicated. In particular no child restates the item or moves its conclusion into a new node.

## Review by Q111

I read Morphisms Tag 01V7 (`lemma-smooth-locally-standard-smooth`), Algebra Tag 00T7 (`lemma-standard-smooth`, statement and its differential calculation), Morphisms Tag 02GU (`lemma-etale-at-point`, especially square-Jacobian condition (8)), Morphisms Tag 02GJ (`lemma-etale-characterize`), Algebra Tag 00U9 (`lemma-etale-standard-smooth`), and Schemes Tags 01HV (`lemma-spec-sheaves`, especially the stalk assertions) and 01I3 (`lemma-standard-open-affine`). The requested criterion is a consequence of these sources; its graph-presentation and block calculation are written out here, so `proof_origin.by` is honestly `agent`, not a claim that a source verbatim states this proof. There are no new statements to compare with sources.

Step 1 uses exactly the statement of `lem-weil-pbc-smooth-locally-standard-smooth` to obtain a standard smooth affine chart. Its smoothness hypothesis holds for the given structural morphism. Its base affine neighbourhood must be the whole one-point scheme Spec(k). `def-weil-pbc-standard-smooth-algebra` supplies the actual quotient presentation and invertible minor, and `def-weil-affine-spectrum` supplies the prime and affine scheme meanings. I did not assume smoothness of the desired coordinate map. The chart lemma is explicitly declared in `split_report.tool_uses` as a generic algebraic geometry tool from sk-thm-p1; no sk-prop-an node gives that chart.

Step 2 uses precisely the specified free basis in `lem-weil-pbc-standard-smooth-kahler-basis`, whose standard smooth presentation hypothesis is supplied by step 1. `def-sc-relative-differential-sheaf` supplies its affine associated-module description. `lem-weil-pbc-spec-tilde-stalk-localization` supplies the stalk/germ localization statement for an arbitrary module. The displayed maps then identify its residue fibre with scalar extension directly. The denominators lie outside q, so their residues are invertible. `def-weil-module-base-change` supplies tensoring the basis isomorphism and its inverse. Equality d=n-r is ordinary finite-dimensional basis counting over the nonzero residue field; no equality with local ring Krull dimension is assumed.

Step 3 uses the affine-space coordinate-ring description in `def-sbc-affine-space` and the contravariant affine morphism/ring map correspondence in `def-weil-affine-spectrum`. Its quotient isomorphism is elementary evaluation, with its inverse written down. The lifts exist because the polynomial quotient in step 1 is surjective. Each T_j acts by the original restricted function. Counting the equations uses step 2.

Step 4 cites only the two derivation definitions it uses: `def-weil-pbc-kahler-differentials` and `def-weil-pbc-polynomial-partial-derivative`. The polynomial differentiation identity follows by monomial Leibniz and additivity as written. With the previously obtained bases, solving the first block equations and eliminating rows yields the explicit Schur complement. This is elementary matrix calculation, not an unstated Jacobian theorem. The square block B is invertible already on the chart; the complementary block is invertible over the residue field because dh_j is a basis. Therefore the full determinant has nonzero residue. No perfectness, algebraic closedness, rationality or closed-point hypothesis is used.

Step 5 invokes `def-weil-ring-localization-away` for the fraction/universal localization description and `def-exc-jacobian-presentation` for what a square presentation means. The two inverse algebra maps are specified, and the enlarged Jacobian and its determinant are computed. These are elementary presentation and triangular-determinant calculations. The determinant is delta squared, not merely delta; it is a unit in precisely the localization being used. The number of equations and variables is n+1 on both sides. No new node is needed for this calculation.

Step 6 uses only the square-presentation-to-etale direction of `lem-exc-etale-jacobian-presentation`, whose full statement and existing Lean proof I read. This is not an inference from its internal proof. `lem-weil-pbc-etale-ring-map-iff-etale-affine` states exactly the ring/scheme equivalence required. `lem-weil-pbc-principal-localization-open-immersion` includes the image D(delta), so it really identifies the affine source with an open neighbourhood, not merely an abstract isomorphic scheme. Finally `def-weil-affine-spectrum` states uniqueness of a morphism from its ring map, verifying that the map proved etale is the restriction of the prescribed h. No uncited openness-of-etale-locus theorem is used.

I tested d=0: the complementary block is the empty invertible matrix, and this proves the structural map etale near a point with zero differential fibre. I tested r=0 (an affine polynomial chart): the full Jacobian is simply the chosen-function derivative matrix. For n=r=d=0 the original determinant is 1 and the adjoined relation is t-1, so the localization and presentation remain valid. At non-closed points K is an arbitrary residue field; every argument still uses only invertibility in K. In characteristic p the map x to x^p fails the basis hypothesis, as it should. A nonconstant smooth component elsewhere in U causes no problem because W is a single standard smooth neighbourhood.

Checks against delivery-errors B–E: no new nodes or duplicate definitions; statement and metadata retained; TeX uses ordinary JSON escaping and block matrices are described by their entries; every non-elementary fact is supplied by a cited statement, with seventeen verbatim citation entries; no proof of a cited node is mined for additional conclusions; no child restates a clause or moves the whole item; all source hypotheses used are explicitly verified above. The three central calculations are kept in elementary steps with their arguments. I corrected the tempting incomplete argument “vanishing relative differentials implies etale” by proving the square Jacobian invertible, which supplies etaleness without assuming flatness of h. No statement dispute was necessary.

## Dry-run repair

The first server preflight rejected the two valid TeX matrix row separators as doubled backslashes (B4). I replaced the two matrix displays with explicit descriptions of the same four blocks; no mathematical step or dependency changed. The report records this formatting limitation for maintenance.

## Validation

The handoff gate is the required `deliver.py Q111 lem-pur-etale-at-point-from-differentials --no-push`, which runs the server preflight, DAG and split checks. The worker issues READY only when that command prints OK on the final sandbox; the terminal result is reported in the one-line handoff. The first run and its formatting repair are recorded above. No Lean file was written and no compiler, Lake command, local DAG checker, git command in the shared repository, or delivery push was run.

## Second reading by Q111

- Statement: checked the field, finite-type smooth scheme, arbitrary point, global coordinate functions, residue-cotangent basis, and neighbourhood conclusion against the chosen-coordinate consequence of Stacks Tags 01V7, 00T7, and 02GU; all hypotheses and the case $d=0$ are retained.
- Step 1: checked Tag 01V7 and the standard-smooth presentation definition; the affine chart, prime, and invertible first Jacobian block are obtained under the stated smoothness hypotheses.
- Step 2: checked Tag 00T7(2), the relative differential sheaf, stalk localization, and tensor base change; the fibre identification and rank count are justified, including arbitrary residue fields.
- Step 3: checked the affine-space and affine-spectrum definitions; the graph presentation and its inverse are elementary and use exactly the restricted functions.
- Step 4: checked the Kähler derivation and polynomial partial-derivative definitions; the block elimination correctly turns the assumed differential basis into a nonzero full Jacobian determinant, including empty-block cases.
- Step 5: checked the localization definition and square-Jacobian presentation; the added variable gives determinant $\Delta^2$, with matching equation and variable counts.
- Step 6: checked the square-Jacobian etale criterion, affine etale equivalence, principal-open immersion, and uniqueness of affine morphisms; the resulting open contains $u$ and carries the original coordinate map.
- New nodes: none; therefore B1–B7 and duplicate/Mathlib-node checks were rechecked for the absence of new files. Existing Mathlib leaves and the Lean-closed Jacobian criterion are cited by their statements.
- Edge cases: tested $d=0$, $r=0$, $n=r=0$, nonclosed points with arbitrary residue fields, and characteristic-$p$ failure of the basis hypothesis; each behaves as required.

Changes made during second reading:

- No mathematical or dependency changes were needed. The split already writes the graph presentation, Schur-complement calculation, localization, and shrinking explicitly and keeps all citations verbatim.
- No node was added or removed. Maintainer-owned creation metadata was left unchanged, and the report now records this second reading and its source-by-source verdicts.
