# Q139 stage-1 delivery

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-universal-exact-affine-power-reduction.json`: item split in seven steps; no Mathlib match for the full statement. The item statement and its statement dependencies are unchanged.
- `citations.json`: fourteen step/node entries with verbatim statement quotations.
- No new nodes and no Mathlib leaves. The other sandbox files are search and writing records only.

## Attachments

None. I searched `lean/WeilConjectures/` by the exact blueprint tag and by universal exactness and affine-power terminology. The hits on affine universal tensor exactness, flat opcycles, formal polynomial powers, and completed sections do not state all clauses of this item. No finished project declaration was found for attachment.

## WANTED

None. All mathematical sources used are present locally.

## Findings and corrections

No statement dispute. No hypotheses or conclusions were changed. The empty proof is replaced with an argument that explicitly identifies both arrows, rather than identifying only the three modules. Affine exactness is justified from the existing image/cokernel statement, rather than incorrectly extracting exactness from the definition of quasi-coherence or from the adjunction alone. Universal exactness is instantiated with both B and T_n; no flatness of C over A is introduced.

I read the current `literature/blueprint/latest/` chapter, unit, ancestor statement and ancestor proof. The current ancestor proof is the contracting-correspondence argument. The item's older inherited flattening branch is recorded in its blueprint provenance, not explicitly in the latest ancestor proof. This delivery retains that branch and proves the assigned strictly local input using Stacks 080W; it does not change the chapter or unit route. The existing provenance fields are retained and the difference is made explicit in split_report.blueprint.

The local text of 080W ends with a separate variable slip in its final torsion chase (with its notation, the intended expression is a^n(x-z)=0). This item concerns only its preceding universal-injectivity reduction and does not use that final chase; its statement has no corresponding error.

## Mathlib and duplicate searches

The inherited item searches are retained. I ran the mandatory msearch command for LeanFinder, Loogle, grep and LeanSearch, with two different semantic phrasings, and read their returned hits. Loogle finds generic ShortComplex short exactness and invariance under isomorphism. LeanSearch finds the scheme/module pullback definitions and the abstract presentation-based quasi-coherence notion. LeanFinder finds injectivity of structural scheme stalk maps and finite-stage section vanishing. Grep finds universally injective scheme morphisms and an ideal-sheaf quotient calculation. None is the full module-sheaf statement here. The commands and digests are in searches.jsonl, and the exact query strings and verdicts are appended to the item.

I searched the whole DAG by affine exactness, quasi-coherent pullback, associated sheaves, quotient tensors and fibre-product/open-base-change terminology, reading the matching statements before choosing citations. Whole-blueprint searches using blueprint_refs.py for `affine exact`, `base change quotient`, `universal exact`, `divisibility` and `pullback` produced no equivalent blueprint item. Instead of creating redundant lemmas for affine sections, affine quotients or affine pullback, the proof reuses existing nodes.

## Not duplicates

No new nodes were created. All comparison facts are existing nodes or explicit elementary calculations.

## Review by Q139

I read divisors.tex, Tag 080W, label lemma-strict-transform-universally-injective, particularly its opening affine reduction and the application of universal injectivity to M_1/a^n M_1. For the expanded comparison I read schemes.tex at Tags 01I4/01JQ (affine fibre products), 01I7/01IB (tilde/global-sections adjunction and affine equivalence), 01I9 (functorial affine pullback), 01IC/01LB (images and cokernels on affine opens), and 01JY (base change of open immersions), modules.tex Tag 01BG (pullback of quasi-coherent modules), and algebra.tex Tag 00DF (tensor exactness underlying the quotient tensor formula). No SGA source is used. There are no new nodes requiring additional sources.

Step 1 uses lem-weil-pbc-module-pullback-quasi-coherent exactly for quasi-coherence after p, and lem-weil-pbc-affine-tilde-gamma-adjunction for its natural counit on quasi-coherent modules. The universal exactness hypothesis itself supplies the short exact sequence on Y; the adjunction is not cited as a theorem asserting arbitrary-section exactness.

Step 2 uses clause (3) of lem-weil-pbc-quasi-coherent-module-cokernel-image. I checked that it explicitly identifies affine image sections with the image of the section map and makes the cokernel section map surjective. Together with the sectionwise kernel and the given short exactness, this is the displayed three-line affine exactness argument, marked elementary. The short exact sequence identifies the third sheaf with this actual cokernel. Thus no uncited affine acyclicity theorem is being used.

Step 3 uses the universal property in def-pc-fibre-product for the pasting isomorphism, writing its inverse through the projections, and lem-weil-pbc-open-immersion-base-change for the open inclusion. Z is open in Y_V because it was chosen in q^{-1}V. The base-changed open is an open of X_n, not an unjustified closed immersion or an affine whole X_n.

Step 4 uses the full statement of lem-weil-pbc-fibre-product-affine-spectra, including affineness and projection ring maps. The remaining ring quotient calculation is written out with its inverse, balancing, products and units. In particular no flatness of C over A is needed, and no tensor equality is deduced by assuming injectivity of A into C.

Step 5 uses def-pc-module-pullback for the composition isomorphism, the natural counit from lem-weil-pbc-affine-tilde-gamma-adjunction, and lem-weil-pbc-tilde-pullback-base-change for its natural isomorphism to the tensor-module sheaf. I read these statements: the latter includes naturality in M and normalization on 1 tensor m. Since the two composites to X agree, this compares the original pulled-back arrows, rather than arbitrary chosen object isomorphisms.

Step 6 uses clause (1) of lem-weil-pbc-tensor-over-quotient-ring for C and the ideal (alpha^n). Its inverse and the equation for an arbitrary linear map are written on pure tensors, so the two quotient arrows are identified explicitly. The step is an elementary use of this existing general formula, not a new node rephrasing a clause of the item.

Step 7 uses pullback quasi-coherence again on X_n, clause (3) of the same image/cokernel node to apply Step 2 there, and the unit isomorphism in the affine adjunction to recover the actual quotient module maps as sections. The quotient-module definition is cited for kernel membership and the final divisibility equivalence. The hypothesis quantified over every T allows the particular T_n regardless of its relation to B. The result is injectivity of the specified quotient i, with compatibility for j already established.

I checked n=0, when a^0=1 and both the quotient spectrum and all quotient modules are empty/zero; a=0; nilpotent a; a a unit; zero rings and zero modules; and zero divisors. The ring inverses and map formulas work in each case. As a check on the universal hypothesis, the sequence 0 -> Z --2--> Z -> Z/2 -> 0 with a=2 fails after reduction mod 2 and does not satisfy the asserted divisibility; our proof excludes it precisely at the universal-exactness use, rather than making an unwarranted tensor-flatness inference.

Every cited statement was opened, and every step/node pair has a verbatim quote in citations.json. No step exceeds 2000 characters (the largest is below 900), and the ring/quotient identifications contain their complete elementary calculations. The three off-unit unsplit/split tools are declared in split_report.tool_uses: quasi-coherent pullback, affine image/cokernel sections, and natural affine tilde pullback. They are generic scheme-module tools; no result of the trace-formula unit supplies them. Other off-unit citations are definitions or Mathlib leaves. I checked the B--E checklist: self-contained item retained, no new statement-only or duplicate-node issue, existing declarations inspected, no imaginary searches, no use of a cited node's proof in place of its statement, and no strengthened hypotheses.

## Unfinished work

None in the assigned one-level split. The dependencies already in the DAG retain their own independent stage states.
