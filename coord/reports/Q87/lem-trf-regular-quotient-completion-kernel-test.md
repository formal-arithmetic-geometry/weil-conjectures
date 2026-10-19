# Stage 1 report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-regular-quotient-completion-kernel-test.json` — split statement.
- `dag/nodes/sec-trace-formula/lem-trf-completion-regular-kernel-preservation.json` — new unsplit statement node; Mathlib searches found no complete match.
- `dag/nodes/sec-trace-formula/lem-trf-complete-local-ci-presentation-independence.json` — new unsplit statement node; Mathlib searches found no complete match.
- `citations.json` — verbatim citations for every non-elementary use in the item proof.

## Attachments

No exact sorry-free declaration was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `/home/ubuntu/weil-newtargets-master/WeilConjectures`.

## WANTED

None. The cited Stacks sources are present in `literature/stacks-project/`.

## Not duplicates

- `lem-trf-completion-regular-kernel-preservation` vs `lem-trf-regular-quotient-completion-kernel-test`: the new node concerns only the canonical completion map from `R^` to the completion of `R/I`; it has no arbitrary second regular-local presentation `Q -> R^/I^`.
- `lem-trf-complete-local-ci-presentation-independence` vs `lem-trf-regular-quotient-completion-kernel-test`: the new node compares two presentations of an already complete local ring and contains no ideal `I` or quotient-completion construction.
- `lem-trf-completion-regular-kernel-preservation` vs `lem-trf-complete-local-ci-presentation-independence`: the first compares a ring to its own completion, while the second compares distinct regular-local presentations of one complete target.

## Review by Q87

I read the imported item and its parent `lem-trf-completion-local-complete-intersection`, then checked the Stacks passages for Tags 09Q1 and 09PZ in `literature/stacks-project/dpa.tex`, together with the completion facts at Tags 00MA, 00MB, 05GG, 05GI, 0316, 0325 and 07NY. I also checked the statements of every cited existing node: quotient-local structure supplies that `R/I` is nonzero local with maximal ideal `m/I`; surjective images of Noetherian rings are Noetherian; completion is Noetherian, local, and complete. Step 1 verifies `I ⊂ m` makes the quotient proper and that any surjection from a local ring to the nonzero local target is local. Step 2 uses the new canonical-completion node exactly for the equivalence between `I` and the kernel of `R^ -> B^`, and uses the existing completion-regular-local statement to verify the source is regular. Step 3 applies the new 09PZ independence node to precisely the canonical map and the given `π`; all hypotheses (Noetherian complete local target, regular local sources, surjective local maps) were checked in steps 1–2. Step 4 is the elementary transitivity of the two equivalences. I tested the empty sequence, `I = 0`, a regular quotient by one parameter, and a non-complete presentation source; these agree with the statement. I corrected the citation for the completion-Noetherian node to quote its exact sentence and checked every citation quote verbatim against its node statement. No SGA source is used, and the new nodes are strictly smaller than the item.

## What was wrong or changed

The imported item was unsplit with an empty proof. I filled its blueprint ancestry and split proof, retaining its statement and dependencies. The two new nodes carry only the intermediate completion and presentation-independence facts; neither restates the item's arbitrary-presentation equivalence.

## Unfinished

Nothing.

- `lem-trf-completion-regular-kernel-preservation` vs `lem-pod-adic-limit-finite-modules`: the existing node concerns inverse limits of finite modules, while this node compares regular-sequence generation of a defining ideal with the kernel of a completed quotient map.
- `lem-trf-completion-regular-kernel-preservation` vs `def-weil-pbc-coherent-formal-modules-affine-quotient-cone`: the existing node defines an affine formal quotient cone and its module-level kernel, while this node is a ring-theoretic regular-sequence equivalence.
- `lem-trf-completion-regular-kernel-preservation` vs `lem-weil-pbc-affine-formal-map-limit-dictionary`: the existing node translates affine formal systems and inverse limits, while this node compares regular sequences under ring completion.
- `lem-trf-completion-regular-kernel-preservation` vs `lem-weil-pbc-affine-global-formal-comparison`: the existing node compares global formal module constructions, while this node concerns a single local ring quotient and regular kernels.
- `lem-trf-completion-regular-kernel-preservation` vs `lem-weil-pbc-coefficient-subring-principal-source`: the existing node treats a principal coefficient source in a formal module setting, while this node treats arbitrary finitely generated ideals and regular sequences.
- `lem-trf-completion-regular-kernel-preservation` vs `lem-weil-pbc-coherent-formal-modules-affine-complete`: the existing node asserts affine formal-module completeness, while this node asserts preservation and reflection of regular-sequence generators.
- `lem-trf-completion-regular-kernel-preservation` vs `lem-weil-pbc-coherent-formal-modules-affine-quotient-cone`: the existing node is a coherent-module quotient-cone construction, while this node is a local ring regular-kernel criterion.
- `lem-trf-completion-regular-kernel-preservation` vs `lem-weil-pbc-complete-local-quotient`: the existing node says quotients of complete local rings remain complete local, while this node compares regular-sequence kernels before and after completion.
- `lem-trf-completion-regular-kernel-preservation` vs `lem-weil-pbc-completed-affine-coherent-iso-lift`: the existing node lifts coherent affine-module isomorphisms through completion, while this node compares regular-sequence generation of ring ideals.
- `lem-trf-completion-regular-kernel-preservation` vs `lem-weil-pbc-completion-exact-finite-modules`: the existing node gives exactness for finite-module completion, while this node applies completion flatness and quotient identification to regular sequences.
- `lem-trf-completion-regular-kernel-preservation` vs `lem-weil-pbc-completion-finite-extension`: the existing node concerns completion of finite ring extensions, while this node concerns the kernel of the canonical completion quotient map.
