# Stage-1 report: lem-trf-strict-transform-sheaf-kernel

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-strict-transform-sheaf-kernel.json`: existing statement node, split proof; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement excerpts for every cited node at every proof step.

## Attachments

None. I searched the slopmaster2 source and found no declaration tagged `lem-trf-strict-transform-sheaf-kernel` and no sorry-free declaration stating the item.

## WANTED

None.

## What was wrong or incomplete

The imported item was unsplit: it had the correct 080D statement but no proof, proof dependencies, or split report. I kept the mathematical statement unchanged and added `def-pc-fibre-product` to `stmt_deps` because the displayed fibre product is part of the statement. The proof now follows the 080D definition and its preceding paragraph, with Tag 07ZP for supported sections and the existing affine power-torsion quotient lemma for the no-residual-support clause. No source error or statement dispute was found.

## Review by Q37

I read the complete Tag 080D passage in `literature/stacks-project/divisors.tex` (including the exceptional-divisor paragraph, both definition clauses, and the local affine discussion), Properties Tag 07ZP in `properties.tex`, the Tag 01BG pullback-quasi-coherence source, and the Tag 01LC qcqs-pushforward source. I also opened the full statements of every node used in the four steps: blowup principalization, affine-open and localization topology, quasi-separatedness, pullback quasi-coherence, qcqs pushforward, quasi-coherent kernel and cokernel/image closure, the strict-transform module definition, the power-torsion quotient lemma, the structure-sheaf pullback isomorphism, and the strict-transform definition.

Step 1 verifies all hypotheses needed for the complement open: the finite-type centre gives a locally principal effective Cartier exceptional divisor; the affine-basis, affine-spectrum quasi-compactness, and localization nodes justify retrocompactness, and the open immersion has an isomorphic diagonal. Step 2 uses the existing generic pullback and pushforward statements and the kernel/cokernel statements to prove quasi-coherence of the supported kernel and quotient, while the module-strict-transform definition supplies the canonical surjection and its kernel. Step 3 checks the edge-local calculation: on a principal chart Tag 07ZP identifies supported sections with power torsion, and the cited quotient lemma rules out any nonzero class killed by a power; this gives both the complement isomorphism and the no-supported-sections claim. Step 4 uses the canonical pullback of the structure sheaf and Tag 080D(2) to identify the kernel with the ideal of the scheme strict transform and the quotient with its pushed-forward structure sheaf.

I checked empty schemes, empty centre/unit centre, zero module, and the identity blowup: the quotient and support assertions reduce respectively to the zero module, the identity, and the usual restriction cases. Every `uses` entry is in `proof_deps`, and every `citations.json` quote is copied verbatim from its node statement. I did not write Lean or run any compiler/build tool.

## What I could not finish

Nothing; the required stage-1 split and review are complete.
