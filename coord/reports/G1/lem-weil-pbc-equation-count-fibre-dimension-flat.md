# Delivery report: lem-weil-pbc-equation-count-fibre-dimension-flat

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-equation-count-fibre-dimension-flat.json`: split into three proof steps; status `split`.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-fibre-dimension-neighborhood.json`: new statement node, Mathlib verdict **no match** (upper semicontinuity of algebraic fibre dimension is absent).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-relative-global-complete-intersection-flat.json`: new statement node, Mathlib verdict **no match** (syntomic/relative complete-intersection notions are absent).

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-polynomial-quotient-dimension-lower-bound.json`: new unsplit statement of the dimension lower bound; no exact Mathlib match, only local dimension/height tools.

## Attachments

None. No Lean declaration was listed by the item audit.

## WANTED

None. Read the shared source `/home/ubuntu/worker-F-chow/weil-conjectures-sheaf/literature/stacks-project/algebra.tex`. Mathlib grep uses `/home/ubuntu/SHEAF/project/lean/.lake/packages/mathlib/Mathlib`.

## What was checked and changed

The item statement already agrees with the equation-count assertion in Tag 00ST part (3): the fibre point Q supplies the relative dimension N−c. The split follows the source: Tag 00QH gives an open neighborhood on which fibre dimensions are at most N−c; the standard lower dimension bound for a quotient of an N-variable polynomial algebra by c equations gives equality, yielding a relative global complete intersection. Tag 00SW gives flatness. Tag 00HT parts (2) and (6), represented by existing node `lem-weil-pbc-flat-local-ring-maps`, gives flatness after localization and the induced local map.

The new statements introduce all rings, primes, fibres, and hypotheses. Their Mathlib searches used LeanSearch, LeanFinder, Loogle and source grep; no matching theorem exists. The existing node `lem-weil-pbc-relative-global-complete-intersection` was searched and reused rather than duplicated. No cycles were introduced; `tools/check_dag.py` reports 0 cycles and `tools/review_split.py lem-weil-pbc-equation-count-fibre-dimension-flat` passes.

## Delivery-errors B–E check

- **B1–B2:** all three new nodes are statement-only and self-contained; TeX is escaped in JSON.
- **B3–B4:** every non-elementary notion is introduced or cited by its defining node; no prose proof is embedded in a new statement.
- **B5–B8:** sources use exact Stacks tags and labels (00QH, 00ST, 00SW); no Mathlib leaf was claimed.
- **C1–C7:** every proof step cites nodes for its substantive input; no tag is used as an uncited premise; existing localization-flatness node is cited; no duplicate or cycle was created.
- **D1–D5:** new nodes are strictly smaller than the item. The upper-bound and flatness arguments are separate reusable facts; the lower-bound equality is explicitly stated in the item step rather than hidden behind “details omitted.”
- **E1–E6:** checked g∉q, nonempty fibres, the N variables/c equations presentation, the distinction between Q and q, and the canonical identification (S_g)_{qS_g}≅S_q. The N=c=0 and empty-fibre cases are covered by the dimension equality and the definition of relative global complete intersection.

## Repairs before review

Corrected the localization presentation: it has N+1 variables and c+1 equations, including hz−1. Added a statement-only lower-dimension-bound node, so the bound is a cited premise rather than an uncited assertion. Wrote both inverse maps of the localization presentation and cited polynomial scalar extension and quotient base change for the fibre presentation. Defined Q as the kernel of the fibre-to-residue-field map, introduced both residue fields, and replaced plain-text statements with TeX. Corrected the source labels to lemma-dimension-fibres-bounded-open-upstairs (00QH) and lemma-relative-global-complete-intersection (00SW). The R-flatness of S_q is now proved by tensoring twice, separately from the local R_p-flatness.

## What could not be finished

None for the one-level split. New nodes are unsplit items. No Lean code was written or built.

## Review by G1

I read Algebra Tag 00ST (`lemma-localize-relative-complete-intersection`), especially part (3) and its proof, together with Tag 00QH (`lemma-dimension-fibres-bounded-open-upstairs`), Tag 00SW (`lemma-relative-global-complete-intersection`), and the paragraph after Definition 00S9. The item retains the finite polynomial presentation, the prime over `R`, and the dimension-at-the-fibre-point hypothesis. Its conclusion asks for flatness of a principal localization and its localizations, which follows from the stronger relative-global-complete-intersection conclusion of 00ST. The new upper-bound node states the principal-open form used in the proof of 00ST, including `g` outside `q`, and defines the fibre prime via the map to `kappa(q)`; it is not an assertion of a bound on all of `Spec S`. The lower-bound node is the repeated one-equation dimension inequality 00KW at a maximal ideal, starting from dimension `m` of affine space by 00OP. The 00SW node states only flatness of a relative global complete intersection. All three are strictly smaller statements with no proof steps while unsplit.

In item step 1, the upper-bound node gives the required `g`; the existing localization universal-property node justifies the two explicit inverse maps between `S_g` and the `N+1`-variable, `c+1`-equation presentation. The cited polynomial scalar-extension and tensor-quotient statements give the displayed fibre presentation. The new lower-bound node applies only to a nonzero fibre, exactly as the step says. It combines with the upper bound to satisfy the statement of the existing relative-global-complete-intersection definition. Step 2 applies the statement of the 00SW node to that presentation. Step 3 uses the existing localization-of-localization and localization-flat nodes, writes the tensor-associativity argument for flatness over `R`, and uses the existing flat-local-ring-map node for `R_p -> S_q`; none of those nodes is asked for a stronger conclusion than its statement provides.

The algebra `S` is finite type because its variable classes generate it; `g` is outside `q` by 00QH. The zero fibre is excluded only where the dimension lower bound is applied, matching the relative complete-intersection definition. The `N=c=0` case has no equations, and the localization presentation still adds one variable and one relation `hz-1`, preserving the dimension difference. I checked the new statements for their objects, exact tags and labels, three search kinds, and absence of a duplicate in the current DAG. I sent back the first version for its uncited dimension bound and incorrect `N`-variable localization claim (C1/E4), then for an undefined fibre prime and an unperformed grep record (B2/search rule). The corrected files address these points. `review_split.py` and `check_dag.py --cycles` pass on the isolated tree.
