# Stage-1 worker report: lem-sfb-bialgebra-counit-word-product-rule

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-bialgebra-counit-word-product-rule.json`: item split into six proof steps; existing mathematical statement unchanged; tensor-product definition added to statement dependencies.
- `citations.json`: exact statement quotations for every proof-step citation (steps 1, 3 and 5).
- `report.md`: this report. The required search command also wrote `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. The proof reuses `lem-sfb-convolution-linear-map-algebra`, already a Mathlib leaf, rather than recreating its associativity and unit assertions.

## Attachments

None. Searched the project source `lean/WeilConjectures/` for the exact blueprint tag and notions including counit derivations, bialgebra and convolution. The project convolution hits concern categorical convolution, Fourier kernels, or graded coefficient products; none states this ordered scalar-valued word formula. No upstream sorry declaration is offered as a completed proof.

## WANTED

None. Read Milne, *Algebraic Groups*, the local `literature/milne-algebraic-groups_iAG2017.pdf`, printed pp.216–218: 11.24, Theorem 11.25, Proposition 11.26 and Lemma 11.27. The ordered formula is an agent-written elementary calculation supporting the evaluation pairing in Lemma 11.27, not a theorem quoted verbatim from Milne. No SGA source is used.

## Source scope and corrections

The existing node has a correct bialgebra-level statement, without finite generation, antipode, characteristic or cocommutativity restrictions. Its prior searches and blueprint provenance were retained. Milne's printed Lemma 11.27 uses invariant derivations to calculate a degree-n pairing; the printed notation for the derivations and their values must be interpreted after evaluation at the identity, as the parent item already explains. This proof instead uses scalar-valued convolution directly and makes no assertion that a global invariant derivation takes a coordinate to a constant function. No statement dispute or statement correction was necessary.

Read the chapter and unit records, the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`, and its direct-images proof, specifically (3). This item is a supporting algebraic prerequisite deep in the inherited alteration/representation-theoretic branch; it neither replaces a unit step nor changes a unit statement. The null nearest-blueprint ancestor and long `via` chain are inherited provenance, not a new assignment of a route.

## Searches and reuse

Searched the entire DAG for convolution, bialgebra, counit derivations, ordered convolution and primitive elements; read the statements of the existing convolution-algebra node, the tensor-product definition and the parent augmentation-monomial pairing. Ran `tools/blueprint_refs.py ancestor` for the item and whole-blueprint searches for convolution, counit and Leibniz. None gives another blueprint node stating this ordered formula. The existing algebra-valued convolution theorem gives exactly the associative algebra and counit-unit facts needed; no duplicate node was created.

The item already records two semantic phrasings and related grep/Loogle results. Retained those records and ran new recorded LeanFinder (two phrasings), LeanSearch, Loogle and Mathlib grep searches under N8 for this item. Read the returned signatures and local Mathlib `RingTheory/Coalgebra/Convolution.lean` (multiplication at 55–68, unit/algebra at 174–193 and ring at 212), `RingTheory/Bialgebra/Basic.lean` (multiplicativity at 92–99), and the derivation interface. Coalgebra convolution evaluation is one multiplication; bialgebra multiplicativity is already a hypothesis; single derivation and analytic derivative product rules do not give this ordered assignment identity. None is an exact match or one-line specialization for the whole item.

## Not duplicates

No new nodes. Reused `lem-sfb-convolution-linear-map-algebra` and `def-weil-pbc-module-tensor-product` directly. The parent `lem-sfb-hopf-augmentation-monomial-pairing` is a different, stronger application concerning augmentation quotients and factorial pairings; citing it here would be circular, and the proof does not do so.

## Review by N8

I read Milne's local text at 11.24–11.27 and the current blueprint places above, and checked the item against its own explicit bialgebra hypotheses. This is the scalar-valued ordered product rule needed for the parent's evaluation calculation. Every imported clause survives, including r=0, arbitrary m>=1 and the inherited increasing order of subwords. No new statement-only node or Mathlib leaf needs a separate source review.

Step 1 uses the statement of `lem-sfb-convolution-linear-map-algebra`: it says associative unital convolution, explicitly identifies the unit as the counit, and excludes finiteness and cocommutativity assumptions. Taking R=B=k is permitted and uses exactly the coassociativity and counit hypotheses of this item. The empty-word base case is multiplicativity of the assumed algebra map epsilon, not an assertion imported from another Hopf-algebra result. Step 1 is marked non-elementary because it invokes that existing theorem.

Step 2 proves the finite-product version of a single counit derivation by writing its m=1 base and its m-to-m+1 induction. It uses only the binary identity in the item's hypotheses and multiplicativity of epsilon. It is elementary, not an uncited higher Leibniz theorem.

Step 3 cites `def-weil-pbc-module-tensor-product`, whose statement explicitly says pure tensors generate the module; its universal property also permits the linear evaluation on a tensor. Finite sums with scalar coefficients absorbed in a tensor factor therefore exist for each Delta(c_j), even without finite-dimensional C. The displayed product expansion uses the stipulated algebra-map property of Delta and the defining multiplication of the tensor algebra. The convolution evaluation then follows by linearity, so no additional theorem about bialgebras is being assumed.

Step 4 applies the simultaneous length-r induction hypothesis to the actual elements x_j in each finite tensor expansion, then substitutes step 2 for the last derivation. I checked the three indexing sets and the scalar factors in the displayed formula: every old index belongs to exactly one fiber T_l, and only one factor receives the last derivation. This is finite distributivity, not an appeal to a hidden comparison or a commutativity assertion for convolution.

Step 5 factors the independent finite sums and recognizes their factors by the definition of convolution. It again cites the existing convolution-algebra node precisely for W*epsilon=W. For the selected factor, the greatest index r+1 is appended on the right of W_T; for an empty T the left-unit law gives epsilon*v=v. The quote in citations.json was checked against the actual node statement, including the full associative algebra clause in step 1. Tensor generation in step 3 is also quoted verbatim. Every cited node has exactly the asserted content (C3/C4).

Step 6 supplies the explicit indexing bijection: restriction of g and its last value recover f and j. This proves the general assignment formula and preserves internal subword order without any interchange of two v_i. Steps 2–6 consist of the written finite identities, induction substitution, or explicit reindexing, so their elementary flags do not conceal a lemma. Every step is shorter than 2000 characters; no argument was moved into a new node to restate a clause of the item (D1/D2).

I checked the small cases r=0, r=1, m=1, empty fibers and a zero v_i. For m=1 there is one assignment and step 5 appends the last index to the sole fiber. For r=1, step 1's empty word and step 5's left-unit identity recover step 2. There is no division by a factorial, so in characteristic 2 the additive bialgebra k[t] with v extracting the coefficient of t gives (v*v)(t^2)=2=0, agreeing with the two assignment terms.

I also checked that cocommutativity is genuinely unnecessary: in k[x,y,z] with Delta(x)=x tensor 1+1 tensor x, Delta(y)=y tensor 1+1 tensor y and Delta(z)=z tensor 1+1 tensor z+x tensor y, with counit evaluation at zero, coefficient-at-zero derivations v_x and v_y satisfy (v_x*v_y)(z)=1 while (v_y*v_x)(z)=0. The induction keeps the former ordered word throughout; it never replaces it by the latter. Finite decompositions are needed only for the finitely many input coproducts, so no finite-generation hypothesis enters.

Against delivery-errors B–E: the unchanged item is self-contained; field and tensor notions have their definition dependencies; no new nodes require searches, leaf lines or duplicate-pair explanations; all new item searches were actually run and logged; the proof dependencies are precisely the union of uses; citations are from statements; no cycle is introduced because the convolution leaf and tensor definition have no proof dependencies on this item. The statement is proved by its finite expansion and induction rather than by renaming the conclusion. The only changes needed during self-review were to include the tensor-product statement dependency and expand the step-1 quotation to cover associativity as well as the unit.

## Unfinished work

None in the requested one-level split. No Lean was written and no compiler, Lake or library build was run. Delivery validation is performed by the required server-side dry run.
