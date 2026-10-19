# Worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-strict-transform-affine-torsion-comparison.json`: statement item, split into four steps; not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- `citations.json`: nine verbatim excerpts, one for every node used by every numbered proof step.
- `searches.jsonl`: actual search-command log. The node retains the inherited search records and adds the five searches made here.

## Attachments

None. The item has no Lean audit declaration. I searched its id and blueprint tag in the project Lean sources, and searched `powTorsion`, strict-transform and blowup concepts. The power-torsion API in `WeilConjectures/Mathlib/Algebra/Module/Torsion.lean` contains the definition, localization kernel and quotient results, but no comparison between a-power and xa-power torsion on the tensor product with a blowup chart. The scheme strict-transform API is not this module comparison. The exact master checkout is reference material only.

## WANTED

None: the source is present as `literature/stacks-project/divisors.tex`, Tag 080H, label `lemma-strict-transform-different-centers`, proof of (2), the paragraph beginning “following algebra problem”. The tag-to-label mapping was checked in `literature/stacks-project/tags/tags`.

## Findings and changes

The item's statement is correct and unchanged, including arbitrary commutative A, arbitrary ideal I, a in I, x a nonzerodivisor and Gamma_x(M)=0. Added the already existing tensor-product definition to stmt_deps because the tensor product is part of the statement. No finiteness or flatness assumption was added. The source retains a regularity hypothesis on x in A that this algebra proof does not need; I retained it too.

The source's final “This implies the result” previously had no split. I expanded its localization observation into a tensor localization and explicit annihilation bounds for the map u(m)=m tensor 1. The final step gives the actual exponents r,n,s: from a^r z=u(m) and (xa)^n z=0, the kernel bound gives x^n a^(s+n)m=0, hence a^(s+n)m=0 and a^(s+n+r)z=0. There is no assertion that tensoring with B preserves injectivity.

The existing blueprint ancestor is `lem-trf-local-term-locality`, through the recorded Orgogozo/strict-transform-composition ancestry. I read the chapter and unit records, the current main-20261015 local-term proof and the immediate parent `lem-trf-strict-transform-different-centers`. This item's affine computation is supporting algebra beneath that route, not a replacement for the contracting-correspondence or modification argument. The existing precise from.place and via are retained. Whole-blueprint searches for affine torsion comparison, torsion and localization tensor found no blueprint node stating this comparison; same_as remains empty. The already existing localization-tensor-product Mathlib leaf supplies the only non-elementary operation.

The live parent changed metadata during the read (its latest creator differs from the ancestry originally imported into this item); I have not edited parent or maintainer metadata. The assigned item's current statement and source remain the same.

## Unfinished work

None in this one-level split. No statement-only helper had to be created.

## Mathlib and duplicate search

The inherited item searches are retained. Additional exact recorded queries used LeanFinder twice, Loogle, grep and LeanSearch. The hits for `Submodule.torsionBy`, `Submodule.isTorsion'_powers_iff` and the regularity-of-localization results do not state the required comparison on M tensor A[I/a]. The grep returned the power-torsion criterion in `Algebra/Module/Torsion/Basic.lean` and uses in `Algebra/Module/PID.lean`; none gives the item. Thus the item is not declared a Mathlib leaf. General tensor localization was already searched and recorded by `lem-weil-pbc-localization-tensor-product` and is reused as such. Early exploratory searches for a possible general kernel/cokernel helper were not used to create any node; that helper is elementary from the cited localization criteria and stays in Step 3.

I searched the entire DAG by localization/tensor/torsion concepts and read the statements of the candidate localization nodes. `lemma-nagata-power-torsion-kernel-localization` gives only the localization kernel; `lemma-nagata-power-torsion-localization` gives localization of the torsion submodule. Neither states the xa comparison. No duplicate new node exists, since this delivery creates none.

## Not duplicates

No new nodes, so there are no new/existing pairs requiring a distinction.

## Review by Q04

I read Tag 080H's algebra paragraph with the item open. The ring A, ideal I, generator a, regular x and x-torsion-free M are exactly those in that paragraph. The positive-power convention in the item agrees with `def-nagata-power-torsion`, which allows exponent zero: if exponent zero kills an element, the element is zero and exponent one also kills it. This is made explicit in Step 4. No assertion of a global uniform torsion exponent is used.

For Step 1 I opened `def-nagata-blowup-chart-ring`, `def-weil-ring-localization-away` and `lem-weil-pbc-localization-tensor-product`. The first defines B as a subalgebra of A_a, not as an arbitrary algebra presented by equations, so its inclusion really is injective. The ring-localization definition supplies the invertibility of a and representation c/a^r. The tensor-localization node explicitly states conditions (a)--(c) for a module localization; I verified them for i:B to A_a, with c represented by its image in B and with s=1 in condition (c). This is a direct three-condition check, not a hidden chart lemma. It is valid even if the map A to B has a kernel.

For Step 2 I opened the same tensor-localization statement, `def-weil-pbc-module-localization-away` and `def-weil-pbc-module-tensor-product`. They give respectively the localization of a tensor product into a tensor product over the localized base, the actual map M to M_a, and the bilinear universal property and pure-tensor generators. The base localization algebra is A_a; both M_a and A_a are A_a-modules, and B to A_a satisfies all localization hypotheses by Step 1. The right tensor unit is written as mutually inverse maps v tensor t to tv and v to v tensor 1, checked by the balancing relation. Thus j:N to M_a is a localization and ju is exactly the canonical map, on every pure tensor. This uses an actual statement of the cited node, not its proof. There is no flatness assumption on B.

For Step 3 I reread the fraction-zero criterion in the module-localization definition and condition (c) in the tensor-localization statement. The kernel computation is ju(m)=m/1=0. For the cokernel calculation, j(z)=m/a^r and j(a^r z-u(m))=0, then condition (c) gives one a^k killing that difference. This yields a^(k+r)z=u(a^km). These are two short direct applications of the cited statements; no new lemma is warranted. The reported citations include both the fraction criterion and the full localized-map characterization, verbatim.

For Step 4 I opened `def-nagata-power-torsion`. It supplies exactly the witnesses n and q and the inference from Gamma_x(M)=0. I checked every exponent and scalar action in the displayed calculation. Commutativity of A, A-linearity of u, and the structural A-action on N justify rearrangement. The vanishing of Gamma_x(M) is used on a^(s+n)m in M, not on N. The reverse inclusion is simply multiplication of a^qz=0 by x^q. Every non-elementary input is the existing Mathlib tensor-localization leaf in Step 2. Steps 1, 3 and 4 are explicit consequences of cited definitions/criteria. All steps are under 2000 characters, with no standard comparison concealed in a long paragraph.

I tested the statement and the argument at M=0, a=1, a=0 and nilpotent a (then B=A_a=0), and a a zero divisor (e.g. A=Z/6, I=(2), a=2, x=5). For A=Z, I=(2), a=2, x=3, M=Z/2, both torsion submodules are all of M; replacing M by Z/3 violates the x-torsion hypothesis and makes the asserted equality fail, confirming why the hypothesis matters. For a genuinely nonflat tensor example, take A=k[s,t], I=(s,t), a=s, x=t and M=A/(t-s). Then M=k[s] has no t-torsion, B=k[s,v] with t=sv, and N=k[s,v]/(s(v-1)). The class v-1 is newly t-torsion, so one must not claim x remains injective on N; it is already a-torsion, as the proof requires. The element chase handles it. No source or statement dispute was found.

I checked the delivery-errors B--E requirements against these files: no helper statements or duplicated clauses were created, all proof uses have verbatim citation excerpts, proof_deps is their union, the existing item's other fields are retained, and the route/source is Stacks rather than any SGA source. No Lean file was written, no compiler or Lake tool was run, and all authored files are in the item sandbox. The first required server dry run completed successfully and wrote a durable .stage1-ready.json receipt. After this report update, I will rerun the dry run on the final content and then push only after it exits successfully.
