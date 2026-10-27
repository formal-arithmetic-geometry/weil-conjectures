## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-completed-graded-model.json: statement, split; no exact Mathlib match. The statement and its statement dependencies are unchanged.
- citations.json: one verbatim statement quotation for each dependency of each proof step.
- searches.jsonl: real search-command results; inherited search records in the item are preserved.

No new nodes and no Mathlib leaves were created. The scratch script write_split.py reconstructs the sandbox JSON only.

## Attachments

None. Searched lean/WeilConjectures for the blueprint tag and for nodal, quadratic normalization and completed normalization terminology. The normalization/completion results found there concern coherent completion, not this explicit quadratic ring and graded formula. No project declaration states every clause of the item.

## WANTED

None. All cited source texts are present in literature/.

## Errors and changes

No statement dispute. The imported item was statement-only. The main work was to supply the omitted graded computation without duplicating the existing explicit normalization nodes. The current latest blueprint direct-images proof (3) supplies the inherited six-functor route; this node is the local algebra input deep under its nodal alteration reduction. The chapter and unit records were read and left unchanged. The inherited blueprint ancestor is null, which blueprint_refs.py ancestor confirms; its detailed from.place and via chain are preserved. Searches over all imported blueprint nodes for nodal, quadratic, power series and associated graded found no imported statement giving this entire result.

Read Stacks curves.tex Tag 0CBT (remark-quadratic-extension), including its explicit statement that the equivalence with construction (3) is omitted; read the completion reduction and both split/nonsplit calculations in Tag 0C4A (lemma-2-branches-delta-1). Read varieties.tex Tag 0C3V (lemma-normalization-same-after-completion), its proof and the preceding normalization finiteness argument (0C3S). Read algebra.tex Tag 05GG (lemma-hathat-finitely-generated), statement and proof. The proof is correctly agent-origin because the coefficient/graded argument fills details Stacks omits.

The generic normalization comparison lem-trf-curve-normalization-completion is an off-unit tool, explicitly declared in split_report.tool_uses. It supplies commutative algebra, not an alternative six-functor route.

## Not duplicates

No new nodes. Existing lem-sfb-quadratic-series-integral-closure supplies the completed quadratic model, and lem-trf-curve-normalization-completion supplies its connection with the original local ring. They are cited directly. The broader excellent/punctured-completion node is unnecessary. The sibling lem-sfb-quadratic-coefficient-proj-branches gives Proj and branch-point assertions that this proof does not need; it is neither recreated nor cited to hide the graded calculation. The existing Mathlib leaf lem-weil-pbc-adic-completion-mod-power supplies exactly the finite quotient maps.

## Review by Q10

I checked each step against the cited statements with the node files open, not merely their identifiers. Step 1 needs no theorem: one of (1,0), (0,1), (1,1) has nonzero q-value, including over F_2. Completing that vector to a basis gives the new leading coefficient, and the discriminant transformation is a polynomial identity; inverse linear matrices induce inverse substitutions in each finite homogeneous degree. No perfection, infinite-field assumption, division by 2 or algebraic closure is used.

For step 2 I read the full statement of lem-trf-curve-normalization-completion: its reduced, local, essentially finite type and one-dimensional hypotheses are exactly in this item, and its conclusion explicitly includes finiteness and the canonical denominator-preserving map, so that fraction compatibility is not inferred from an unspecified isomorphism. I read lem-sfb-quadratic-series-integral-closure: it gives the injective displayed substitution with image F+tL[[t]] and identifies L[[t]] as the integral closure in Q(R). Its two additional hypotheses a nonzero and discriminant nonzero hold after step 1. Both comparisons are over R, so composing them preserves the structural image and the original denominator convention. No property is taken only from either cited node's proof.

Step 3 cites def-weil-pbc-noetherian-ring for finite generation of m and lem-weil-pbc-adic-completion-mod-power for its surjections and exact kernels at every positive exponent. The source 05GG really gives all powers, not just the residue quotient. Commutation with transition maps follows by sending the same representative a to its completion. Residue preservation in the hypothesis identifies the kernel at n=1 with the zero-constant-term series in F+tC. This avoids assuming without proof that mR is the maximal ideal of R.

Step 4 is a finite-product argument inside S, not an invocation of extended ideal equality in C. For the reverse inclusion t^nh=t^{n-1}(th), every one of the n factors belongs to tC, including at n=1. Thus (tC)^n=t^nC as subsets of S. Extension commutes with finite ideal products by their defining finite sums. This is enough to obtain the asserted image of m^nR without a flatness lemma.

Step 5 cites the actual associated graded definition, which states its graded pieces, its homogeneous multiplication formula and its residue-field scalar action. The preceding quotient isomorphisms identify the kernels of successive quotients; these kernels are the positive graded pieces. Coefficient extraction has the displayed kernel and the explicit preimage lambda t^n. The coefficient convolution calculation verifies multiplication and the degree-zero scalar action. This is an elementary assembly from the already proved quotient maps, rather than an unproved completion-preserves-grading assertion. In particular the scalar field acting on gr_m A is A/m; a coefficient field in A itself is not assumed.

Step 6 chooses a class through the degree-one bijection already proved. Representing it by f in m gives exactly coefficient 1 at t and zero constant coefficient, so shifting the remaining coefficients defines h and proves f=t(1+th). No Hensel lifting, choice of a parameter in A, or unjustified unit assertion is needed.

I tested the split algebra q=X^2+XY (over F_2 as well), the nonsplit quadratic algebra q=X^2+Y^2 over the reals, and the original coordinates q=XY with a=0. The last is handled by X_original=X_new, Y_original=X_new+Y_new, producing a nonzero new leading coefficient. Split L has zero divisors, but t^nh=t^{n-1}(th), coefficient extraction and all kernel computations remain valid for L a product; none cancels a general element of L. At exponent 1 the quotient is F, whereas positive graded components are L, and this distinction is retained. Singular repeated-root quadrics are excluded by the given discriminant condition.

For delivery-errors B I checked self-contained original statement, single TeX escaping, precise tags/labels and blueprint placement. For C I generated citations.json from the actual full node statements and verified each use above; no cited proof is used in place of its statement. For D there are no new clause-shaped nodes; the proof contains the ideal-power, kernel and multiplication arguments themselves. For E all hypotheses and characteristics were checked as above. Every proof step is below 2000 characters, so no long step hides a separate comparison lemma. Mathlib hits were read as returned: Weierstrass division, Laurent-series integer rings, general scheme normalization and generic graded/completion constructions do not state this full item, even by one-line specialization. All newly appended searches are real logged calls; the preliminary formal-division search was kept in the record even though the existing DAG calculation made a new division node unnecessary.

## Unfinished work

None in this one-level split. Existing cited nodes retain their own stage status; no Lean is written or compiled. Required server dry-run and delivery results follow the tool output.
