# Stage-1 report

Files written:

- `dag/nodes/sec-trace-formula/lem-trf-space-qc-separated-quasi-coherent-pushforward.json`: split statement; four proof steps; no Mathlib match for the algebraic-space theorem.
- `dag/nodes/sec-trace-formula/lem-trf-space-pushforward-atlas-equalizer.json`: new statement-only helper; no Mathlib match.
- `citations.json`: verbatim statement quotes for every cited node in every proof step.

Attachments: none. The source checkout has only scheme-level affine/closed-immersion pushforward declarations; no sorry-free declaration states the algebraic-space qc-separated theorem exactly.

WANTED: none.

The item statement is unchanged. Its “separated” hypothesis is sufficient for the source lemma’s quasi-separated hypothesis because the representable diagonal is a closed immersion and hence quasi-compact on scheme tests. The imported node had no proof; the source proof is Tag 03M9. The only new dependency is the atlas equalizer helper, which records Tag 03M8’s exact sequence and does not restate the item’s quasi-coherence conclusion.

## Not duplicates

`lem-trf-space-pushforward-atlas-equalizer` vs `def-trf-space-etale-module-functors`: the new node proves the Čech kernel exact sequence for a surjective étale atlas, while the existing definition only defines direct image by its compatible-chart limit and gives no atlas equalizer theorem.

`lem-trf-space-pushforward-atlas-equalizer` vs `lem-trf-space-etale-module-pushforward-restriction`: the new node computes a Čech kernel from a surjective étale atlas, while the existing node gives arbitrary étale base-change/restriction for direct images and tensor pullback.

`lem-trf-space-pushforward-atlas-equalizer` vs `lem-trf-space-qc-separated-etale-local`: the new node is an exact module equalizer for a fixed atlas; the existing node is locality of geometric quasi-compactness and separatedness.

`lem-trf-space-pushforward-atlas-equalizer` vs `pqf-lem-pushforward-qcoh`: the new node concerns arbitrary algebraic-space sources and an atlas kernel formula; the existing node concerns quasi-coherence of pushforward for qcqs scheme morphisms.

## Review by Q05

I read the item node, the fixed chapter `sec-trace-formula`, and unit `sk-i-curve-zero`, then checked the proof against `spaces-morphisms.tex` Tag 03M9 and its cited Tag 03M8, `spaces-properties.tex` Tags 03LX and 03E3, and `schemes.tex` Tag 01IC. I also read the statements of `lem-trf-space-qc-separated-etale-local`, `lem-trf-space-etale-module-pushforward-restriction`, `lem-trf-space-fibre-products-etale-covers`, `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence`, `lem-weil-pbc-closed-immersion-base-change`, and `lem-weil-pbc-quasi-coherent-module-kernel` before citing them.

Step 1 uses the locality node exactly for the family consisting of the chosen affine étale test and the identity, and uses the module-restriction node for the displayed base-change isomorphism. The quasi-coherence definition supplies the local-presentation criterion; affine étale charts cover every test object. I verified that no representability of `X` is assumed.

Step 2 uses the locality statement’s definition of quasi-compactness to obtain a quasi-compact scheme atlas after the target has been made affine. A finite affine refinement and finite disjoint union produce the affine atlas `U`; the fibre-product node explicitly says that `U ×_X U` is a scheme. The new helper states exactly the kernel/equalizer computation from Tag 03M8, including the module direct-image scalar structure.

Step 3 checks the geometric hypotheses needed later. The relation `R -> U ×_V U` is the base change of the separated diagonal, so the existing closed-immersion base-change leaf applies. Since the target is affine, this makes `R` affine over an affine scheme and hence gives qcqs scheme maps `a` and `b`. Restricting a local quasi-coherent presentation along the étale charts is justified by the definition and the existing restriction description.

Step 4 uses the existing Zariski/small-étale equivalence node, whose statement explicitly supplies quasi-coherent direct images for qc separated scheme maps and identifies them with the small-étale direct images. I used the existing kernel theorem only after transporting the difference map across that equivalence; equivalences preserve the finite kernel used here. The atlas helper then identifies that kernel with `f_*F`, and the affine tests from Step 1 conclude the item.

I tested the argument on the identity morphism, an affine morphism, the empty algebraic space, and a closed immersion; all reduce to the stated kernel sequence and give the expected quasi-coherent module. The helper’s four Mathlib searches were run with `msearch.py` and found only generic or scheme-only declarations, so it remains an unsplit statement node. No statement was weakened, no SGA source was used, and no long proof step hides an additional lemma beyond the cited atlas computation.

What could not be finished: no Lean was written or compiled, as required for stage 1.
