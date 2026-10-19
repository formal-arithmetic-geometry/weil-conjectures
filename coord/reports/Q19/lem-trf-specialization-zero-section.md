## Files written

- `dag/nodes/sec-trace-formula/lem-trf-specialization-zero-section.json`: item, split, ten proof steps; statement unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-nearby-cycle-finiteness-exchange.json`: new statement-only lemma, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-dnc-generic-zero-section-vanishing.json`: new statement-only lemma, unsplit; no Mathlib match.
- `citations.json`: one verbatim statement quote for every use in every item step. Full statements are quoted to retain all domain restrictions.
- `searches.jsonl`: actual search-command log. The new lemmas each have LeanFinder, Loogle, grep, LeanSearch, and a second semantic phrasing; all services responded.

## Attachments

None. Searched the entire project `WeilConjectures/` in slopmaster2 for the item's blueprint tag and nearby-cycle, specialization and zero-section notions, and inspected the smooth-purity deformation candidates. Those concern the deformation of a smooth section's dualizing invariant, rather than arbitrary closed-subscheme Verdier specialization. No declaration states every clause of this item. Upstream master is reference material only.

## Wanted sources

None. The local Varshavsky PDF contains the source and its detailed proof, including §3 explicitly devoted to this zero-section theorem. No SGA source is used.

## What was wrong and what changed

The imported statement has no proof. Its first clause is Varshavsky Proposition 1.4.2 and equation (1.8), its constant-family assertions are Examples 1.3.3(a)--(b), and its final clause is the nilpotent-invariance argument used in Theorem 2.1.3(b). The statement is retained exactly; there is no STATEMENT-DISPUTED correction.

My initial draft quoted Proposition 1.4.2 instead of giving its argument, and incorrectly tried to apply the finite-type-over-k stability package to nearby cycles over a trait. Both gaps are repaired. The item now first proves constant-family constancy independently using Remark 3.2.5, then proves the zero-section theorem by the reduction and affine-hyperplane induction in §3.2.1--3.2.4. The two new lower lemmas expose exactly the missing trait formalism and the genuinely smaller generic-point vanishing step. Neither lemma is a relabelling of the item or an entire clause: one is a general functor/exchange theorem without a zero-section conclusion, and the other only proves generic vanishing on a normal principal pair for complexes zero on the divisor. The item still carries the localization, blowup, hyperplane, and dimension induction needed to obtain the global theorem.

The finite-support projection is written explicitly using a nonzero vanishing polynomial, a direction avoiding its top homogeneous part, and the resulting monic equation. This supplies both finiteness on the support and absence of its projective closure at infinity. In particular the final conservativity argument is not justified by properness alone. The finite-stalk theorem makes it exact and conservative on the specified finite support. Both dimension inductions use bounded constructible etale complexes; `thm-dg-finite-type-constructibility` supplies their direct-image domain, whereas finite Tor amplitude is checked separately on the original item using the new nearby-cycle theorem and the comparison-amplitude lemma.

## Not duplicates

- `lem-trf-nearby-cycle-finiteness-exchange` vs `thm-sf-ctf-stability`: the latter concerns finite-type k-morphisms, not geometric nearby cycles from a geometric generic fibre over D. The same distinction separates it from `prop-functor-package`.
- `lem-trf-nearby-cycle-finiteness-exchange` vs `lem-trf-trace-specialization`: the latter is an equality of trace classes, not a preservation/exchange result for nearby cycles.
- `lem-trf-dnc-generic-zero-section-vanishing` vs `lem-trf-specialization-zero-section`: the new lemma is only the generic-point vanishing of Claim 3.2.3 under normality, a principal divisor, and zero restriction. It does not give the comparison on all of Z, any arbitrary-pair reduction, the constant-family unit, or the Borel--Moore identity.
- `lem-trf-dnc-generic-zero-section-vanishing` vs `thm-pur-dnc-invariance` / `sk-thm-dnc`: the purity statements concern smooth sections and their relative dualizing invariant. This lemma concerns arbitrary bounded constructible etale input zero on a principal divisor and its nearby-cycle generic stalks.

Whole-DAG and whole-blueprint searches for nearby cycles, generic vanishing, normal-cone specialization, and principal divisors found no existing statement of either new lemma. The source citations are to Varshavsky, not to reused Stacks tags. The supporting Stacks/Mathlib facts already have DAG nodes and are cited directly.

## Review by Q19

I read Varshavsky §1.3.1(e), §1.3.2(b)--(c), Examples 1.3.3, Notation 1.4.1, Proposition 1.4.2, Lemma 3.2.1, all three reduction paragraphs of §3.2.2, Claim 3.2.3 and its proof, §3.2.4, Remark 3.2.5, and the final reduction paragraph of Theorem 2.1.3(b). For the generic-vanishing new node I also read §3.1, including the contractible rank-one case and its homotopy argument. For the nearby-cycle new node I checked the stated finite-Tor functor domain in §1.3.1(e), the construction of ordinary/exceptional exchange in §1.3.2(b), and proper/smooth invertibility in (c), as used on Db_c in §3.2. The statement-only nodes preserve these hypotheses, including geometric nearby cycles, ell invertible, and the source's normal/principal assumptions.

Step 1: I read the constructible-origin and comparison-amplitude statements, both directions of the latter, and checked the Rees lift is exactly the separated finite-type D-scheme to which the new nearby-cycle theorem applies. I did not identify the pro-etale category with the etale category without those citations. The new output theorem supplies preservation; a definition is not cited as a preservation theorem.

Steps 2--3: the new nearby-cycle statement includes exactness, smooth/proper exchange and compatibility with the unit, which is what the defect construction needs. Constructibility gives a dense open with locally constant cohomology, and finite truncation triangles reduce to locally constant sheaves; no claim that those cohomology sheaves are projective is used. I checked the relative P1 projection is proper by the precise projective-space node, all its schemes are finite type over k for `thm-dg-finite-type-constructibility`, and the finite support includes the infinity section. The cited finite-stalk formula is for abelian sheaves; its maps retain the A action, and its finite-product formula gives the corresponding module assertion. I separately read and cited `prop-weil-pbc-geometric-stalks-exact`; exact geometric stalks and their cited conservativity then give exactness and detection on cohomology complexes. This is the independent proof of the constant-family unit, so the later equation (1.8) is not used circularly.

Step 4: the existing Rees geometry says that the comparison to the base change is a closed immersion and that the inverse-image zero section is correct. It does not say flat base change is an isomorphism; I supplied that calculation by tensoring the Rees subalgebra inclusion with the flat algebra, using the actual injectivity clause of `lem-weil-pbc-flat-tensor-exact`. The proper/smooth permanence statements then have their required hypotheses. The trait exchanges come from the new node; the k-special-fibre exchanges come from the functor package. Their unit compatibility identifies the canonical gamma maps and not merely their sources and targets.

Steps 5--6: I read the full localization, blowup properness, complement-isomorphism and principalization statements. The centre ideal is coherent of finite type on a Noetherian scheme; the blowup is therefore proper and has Cartier total transform. The unit L to Rb_*b^*L is checked separately on the complement and the centre by proper base change. The affine embedding explicitly sends one coordinate to the chosen equation f, so its pulled-back hyperplane is the original closed subscheme, including multiplicities. I read `prop-weil-open-closed-recollement-adjunctions`: its invertible closed counit proves faithfulness after applying i*. Exactness comes separately from the localization node. These statements justify reflection of defect vanishing.

Steps 7--8: the new generic lemma applies to a normal coordinate hyperplane pair and inputs with zero restriction. Its conclusion only removes generic support. The item supplies the induction base n=1 and the n to n-1 step. Choosing the projection direction inside H makes q inverse-image of Z' equal H; replacing it by a direction outside H would invalidate the pair comparison. The monic polynomial ensures the closure of Y has no point at infinity. The defect can have additional support there, but that section is finite too, which is why the conservative finite-direct-image argument applies. The lower-dimensional input is bounded constructible by the explicitly cited direct-image theorem, with coefficient order invertible in k. All comparison facts in these steps refer to their statements, not to hidden proofs of other nodes.

Step 9: I checked the Borel--Moore specialization definition and the ordinary/exceptional exchanges and their adjoint mates. The proof now writes the actual formula: naturality gives sp(alpha) theta_A = theta_omega alpha, and the ordinary/exceptional mate compatibility gives b theta_omega = id by the triangle equations. Thus b sp(alpha) theta_A = alpha. No invertibility of alpha or properness of T is assumed.

Step 10: I checked the distinction between total D-schemes and special-fibre k-schemes. Topological invariance on the total schemes is cited from the unrestricted etale-site equivalence node, and proper nearby-cycle exchange applies to their closed immersion, whose properness is explicitly cited from the unrestricted proper-permanence node. Only the finite-type special fibres use `i-topology`. Its inverse equivalence makes the unit and the exceptional counit invertible, and dualizing-complex composition identifies the exceptional pullback with omega_T. The composition is therefore the constant identity followed by the equivalence of Hom modules, proving the precise final isomorphism.

Small cases checked: empty X or Z; Z=X (zero ideal); zero coefficient complex; nonreduced Z=V(x^e) in A1; the basic open-extension input j_!A with zero restriction; the dimension-one induction; and a square-zero thickening of the constant lift. No smoothness/regularity is assumed for the original closed pair. Finite Tor amplitude is never silently inferred from bounded constructibility. I kept the chapter, unit, created metadata and ancestor unchanged; the item is not the key node of its unit. The ten steps cite existing nodes or the two statement-only lower nodes, with a verbatim quote for each citation. Off-unit generic tools are declared in split_report.tool_uses. No Lean, Lake, compiler or git command was run by the worker.

## What remains

The two new lemmas are intentionally unsplit and join the next stage-1 frontier. The item proof is complete by those cited statements. The required deliver.py --no-push is the final check; no push is authorized for this worker.

## Dry run

The first complete split passed deliver.py --no-push on 2026-10-17 (commit 49fffb52dc). A final citation audit added the exact-stalk theorem, the invertible closed counit used to reflect vanishing, explicit properness of the nilpotent immersion, and the naturality formula for the Borel--Moore identity. The final files are submitted to the same dry run again; no push is performed.

## Second reading by Q19

- Item statement: checked against Varshavsky Proposition 1.4.2 (equation (1.8)), Examples 1.3.3(a)--(b), and the final reduction in Theorem 2.1.3(b); all clauses and hypotheses agree, including arbitrary closed subschemes and the nilpotent-thickening clause.
- Step 1: checked against §§1.3.1(e), 1.3.2(a), and Notation 1.4.1(a)--(d), plus the cited etale/pro-etale comparison statements; the Rees lift, finite-Tor transfer, and category change are stated dependencies and the verdict is correct.
- Step 2: checked against Remark 3.2.5 and the constant-family defect argument; proper and smooth exchange is used on the unit maps, and the dense-open constructibility reduction is explicit; pass.
- Step 3: checked against Remark 3.2.5 and §3.2.4; the monic-polynomial finite projection, projective compactification, finite-support conservativity, and closed-counit faithfulness are all supplied; pass.
- Step 4: checked against equation (1.8), Lemma 1.4.3(c)--(e), and Lemma 3.2.1(a)--(b); the flat Rees algebra calculation and proper/smooth exchange hypotheses match; pass.
- Step 5: checked against §3.2.2(I), including $Z=X$ and $Z=\\varnothing$; localization and exact defect reduction are correctly applied; pass.
- Step 6: checked against §3.2.2(II)--(III) and the cited blowup, properness, and recollement statements; the nilpotent and nonreduced cases are retained; pass.
- Step 7: checked against Claim 3.2.3 and the $n=1$ base case; the generic-stalk conclusion is exactly the new lemma's affine specialization; pass.
- Step 8: checked against §3.2.4; the chosen direction lies in the hyperplane, the monic equation removes infinity support, and the finite projection is used conservatively; pass.
- Step 9: checked against Examples 1.3.3(a)--(b); the displayed naturality and mate calculation proves the identity without properness; pass.
- Step 10: checked against the final paragraph of Theorem 2.1.3(b), the universal-homeomorphism site equivalence, and $i$-topology; the total and special-fibre schemes are kept distinct and the closed immersion's properness is cited; pass.
- New node `lem-trf-nearby-cycle-finiteness-exchange`: checked against §§1.3.1(e), 1.3.2(b)--(c), and Remark 3.2.5; repaired the statement to quantify the bounded constructible generic-fibre inputs for both exchange maps; searches remain recorded and no duplicate exists.
- New node `lem-trf-dnc-generic-zero-section-vanishing`: checked against Claim 3.2.3 and its §3.1/§3.2 proof; removed an extra non-zero-divisor hypothesis absent from the source (the affine coordinate case remains valid); searches remain recorded and no duplicate exists.

Changes made: repaired both new-node statements for source fidelity and self-contained quantification; refreshed the affected verbatim citation quotes; no proof step or item clause was otherwise changed.
