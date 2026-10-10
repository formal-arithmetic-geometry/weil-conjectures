files written:

1. `def-nagata-relative-finite-affine-presentation.json`: definition marked split; its statement dependency is `def-weil-pbc-scheme-conventions`.
2. `citations.json`: empty, because this is a proof-free definition and has no proof steps.

attachments:

none.

WANTED: none.

The item is a definition, so I did not create theorem nodes or proof steps. I checked the blueprint node and its status note: the finite affine presentation bookkeeping is explicitly bypassed by the formalized route. I searched the source repository for the target blueprint tag and for the two bypass declarations. `AlgebraicGeometry.Scheme.nonempty_noetherianApproximation` and `AlgebraicGeometry.Scheme.exists_isPullback_of_finitePresentation_of_isSeparated` occur in `WeilConjectures/Compactification/FinitePresentation.lean`, but they establish approximation and compactification existence rather than selecting and recording the finite affine datum `R_X`; therefore neither is an attachment. The statement's qcqs, affine, and finite-presentation terminology is covered by `def-weil-pbc-scheme-conventions`, which is now the sole statement dependency.

## Review by G1

I read the item source at `literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-approximation/def-nagata-relative-finite-affine-presentation.md`, the chapter record, and the unit record. The source statement is unchanged. I read the neighboring imported definitions and the formalized `Compactification/FinitePresentation.lean`. The blueprint says this stage-by-stage data is bypassed; consequently the definition has no proof steps and `citations.json` correctly contains no step entries. I verified that the only nonlocal notions in the statement are the scheme and morphism conventions already collected by `def-weil-pbc-scheme-conventions`; no theorem node is needed to define the selected record. I also ran LeanFinder, Loogle, and Mathlib grep searches for finite affine covers, finite-presentation affine charts, and overlap gluing. The hits were general Mathlib APIs and did not state this project-specific record, so no Mathlib attachment or new leaf was made. I corrected the imported node's missing definition dependency, changed its status to `split`, and normalized `blueprint.same_as` to an empty list.

## Second reading by G1

- Item statement: checked the finite affine cover, finite chart presentation, overlap, and cocycle clauses against the blueprint source node and status note; verdict: agrees, with the source bypass recorded.
- Proof steps: none; this is a proof-free definition, so there are no step dependencies to repair.
- New nodes: none; no B1-B7 review or duplicate-node repair applies.
- Small cases: this is data-selection syntax rather than an existence theorem, so the empty scheme, a field, and zero-object cases add no assertion; `n = 0,1` is inapplicable.
- Mathlib searches: checked the recorded LeanFinder, Loogle, and grep results; none states this project-specific record, so no Mathlib leaf is needed.
- Blueprint provenance: set `blueprint.from` to the item itself with the exact statement clause and retained `same_as: []`, as required when the nearest blueprint ancestor is the item.
