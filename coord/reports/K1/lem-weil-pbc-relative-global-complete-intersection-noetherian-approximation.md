# lem-weil-pbc-relative-global-complete-intersection-noetherian-approximation

## Worker report

The item is split into six proof steps following Stacks Algebra Lemma Tag 00SU. The steps make the fibre-dimension comparison, principal-open cover, finite coefficient enlargement, and final dimension equality explicit. No auxiliary nodes were created. `review_split.py` passes and the item records its complete blueprint object and `split_report.blueprint`.

## Review by K1

### Source and attachment check

I read the pinned Stacks source in `/home/ubuntu/weil-conjectures-sheaf-F2/literature/stacks-project/algebra.tex`: Lemma Tag 00SU (`lemma-relative-global-complete-intersection-Noetherian`), statement at lines 36727--36737 and proof at lines 36739--36764. The item statement has the same commutative ring, polynomial presentation, relative global complete-intersection hypothesis, finite-type `Z`-subalgebra, coefficient containment, and descended quotient conclusion. No hypothesis is added or omitted.

Before reviewing the split I searched the read-only slopmaster2 source `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, `(blueprint: lem-weil-pbc-relative-global-complete-intersection-noetherian-approximation)`, `00SU`, complete-intersection notions, and noetherian-approximation declarations. There is no exact declaration or blueprint tag. The matches are unrelated generic noetherian-approximation results (for schemes, finite-pushforward, or flat-algebra fibres), so this remains a split and no Lean attachment is claimed. No source file was changed.

### A--D: structure and citations

The delivery changes only the item's node and this report; there are no new nodes. The item carries `status: split`, a six-step `proof`, matching `proof_deps`, the Stacks proof origin, three Mathlib search records with a no-match verdict, and the required blueprint fields (`from`, `same_as: []`, and `split_report.blueprint`). All displayed TeX is escaped once. The statement and each step cite Stacks's tag and label rather than a section number.

Step 1 constructs the coefficient subring and `S_0`, then uses `lem-weil-pbc-polynomial-scalar-extension` and `lem-weil-pbc-tensor-quotient-base-change` for `R ⊗ R_0 S_0 ≅ S`; the quotient and polynomial lifting operations are elementary from the definitions.

Step 2 contracts a prime and compares the two fibre rings using `lem-weil-pbc-tensor-cancel-base-change` and `lem-weil-pbc-prime-in-image-iff-fibre-ring-nonzero`. The item definition supplies dimension `n-c` for the nonempty original fibre. `lem-weil-pbc-field-extension-base-change-faithfully-flat`, `lem-weil-pbc-faithfully-flat-surjective-spectrum`, `lem-weil-pbc-dimension-at-point-field-extension`, and `lem-weil-pbc-dimension-supremum-local-dimensions` justify equality of global dimensions and the resulting local upper bound at the contracted prime.

Step 3 applies `lem-weil-pbc-fibre-dimension-neighborhood` to that local dimension and uses `lem-weil-pbc-spec-localization-away-basic-open` to identify the resulting principal open and its pullback. The finite-type hypothesis is supplied by `def-weil-pbc-finite-type-algebra`.

Step 4 uses quasi-compactness and the unit-ideal criterion in `lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact` to choose finitely many opens. Polynomial representatives, quotient lifting, and the displayed relation `1 - Σ h_j G_j = Σ a_i f_i` are direct ring calculations from `def-weil-pbc-mv-polynomial-ring` and the quotient presentation; the zero-ring case is handled explicitly.

Step 5 enlarges the coefficient ring by the finitely many coefficients in that relation. The cited polynomial/tensor and localization base-change nodes identify the new fibres with field extensions of the old localized fibres. `lem-weil-pbc-dimension-at-point-field-extension`, `lem-weil-pbc-dimension-supremum-local-dimensions`, and `lem-weil-pbc-dimension-at-point-open-subspace` give preservation of the local bounds, while the basic-open node gives the fibre cover.

Step 6 treats the zero quotient separately. Otherwise a prime gives a nonempty fibre and the upper bound forces `c ≤ n`; the polynomial quotient lower bound node and the upper bound yield dimension exactly `n-c` for every nonempty fibre, which is precisely `def-weil-pbc-relative-global-complete-intersection`.

No step cites proof-only material from another node, relabels the item, or introduces a circular auxiliary statement. `review_split.py` passes with zero new nodes. `check_dag.py --cycles` reports no new cycle (only the repository's known unrelated reachability warnings).

### E: mathematics and edge cases

The fibre in Step 2 is nonzero because it comes from the chosen prime; the residue-field map is a field extension, and the finite-type condition needed by the local-dimension comparison is inherited from the polynomial quotient. The principal-open theorem is applied at the contracted prime, so its dimension bound is available before taking the finite cover. The finite Bezout relation in Step 4 is retained when passing to the enlarged coefficient ring, and the empty-cover equation handles `S = 0`. In the final step, if `S_1 = 0` the relative condition is vacuous; otherwise the existence of a prime and the lower-bound node rule out an inconsistent `c > n` case.

I checked the edge cases `c = 0` (the quotient is a polynomial ring and the construction takes a finite coefficient subring), `n = 0`, and the zero quotient `S = 0`; the stated conclusion and the empty-fibre convention remain well-defined. No false source assertion or missing hypothesis was found.

### F: lead outcome

I requested no changes: the worker's corrected tensor-cancellation citation and polynomial lift/Bezout construction are present in the final JSON. The source, node statements, six steps, dependency list, Mathlib searches, and blueprint metadata are internally consistent. This item is ready for the lead's single-commit delivery workflow after fetching and rebasing on the current `origin/sheaf-dag`.
