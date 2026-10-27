## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-sheaf-polynomial-differentials-free.json — statement, now split; no Mathlib match for the entire sheaf assertion.
- citations.json — one exact statement quotation for each of the 13 step/node citations.
- searches.jsonl — the five searches actually run by Q85, with original outputs inspected; inherited live-node searches retained separately in the node.

No new nodes and no new Mathlib leaves. The existing arbitrary-variable polynomial basis node is a Mathlib leaf; the sheaf assertion itself requires nontrivial comparisons and is not a one-line specialization of that ring theorem.

## Attachments

None. I searched lean/WeilConjectures/ for the exact blueprint tag, polynomial/differential terms, mvPolynomial, and polynomial/sheaf combinations. The hits concern ring or field differentials, scheme charts, or weight polynomials. None states this arbitrary-site, arbitrary-generator-sheaf theorem. No Lean declaration is claimed as an attachment and nothing was compiled.

## WANTED

None. All sources used are available in literature/stacks-project/.

## Corrections and route

The live statement is retained exactly, as are its statement dependencies. Its proof was empty. I supplied five steps and their union of proof dependencies, filled proof_origin and split_report, and retained the original search records. The result makes no surjectivity hypothesis, even though Tag 08UJ discusses the result while presenting a surjective polynomial algebra: its polynomial-basis and tensor arguments do not require surjectivity. There is no statement dispute.

The latest blueprint read was literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). The inherited from.place describes the older alteration reduction and the chain of supporting deformation-theory tools. This proof supplies that chain's algebraic input and does not replace the unit route. The read-only ancestor command prints blueprint.from.node = None; I retained that inherited value and the existing descriptive place, rather than inventing an ancestor. Blueprint searches for "polynomial differentials", "free module", and "differentials" found no imported node stating the same arbitrary-site claim, so same_as remains [].

## Not duplicates

No new nodes were created. Existing nodes were reused: the ring basis for arbitrary variables is not a sheaf theorem; 08TP identifies sheafified differentials for an arbitrary ring presheaf, not their polynomial basis after evaluation; 0GMW compares sheafification and tensor products; the free module sheaf node provides the construction and uniqueness on generators. None alone restates this item's two clauses.

## Review by Q85

I read the item source in defos.tex, Tag 08UJ, lemma-NL-represent-ext-class-ringed-topoi, lines 4136–4192. The first proof paragraph identifies the evaluated differentials with the sheaf associated to the sectionwise direct sums. The later change-of-generators construction uses precisely the generator map in the item's naturality assertion. To justify the omitted comparisons I read sites-modules.tex Tag 08TP (lemma-differentials-sheafify, including its free-relation proof), Tag 0GMW (lemma-sheafification-tensor), Tag 03CY (lemma-sheafification-presheaf-modules, including the extension-of-action and factorization clauses), and the construction of free module sheaves and universal differentials in Tag 04BL (lemma-universal-module). I read algebra.tex Tag 00RX, lemma-differentials-polynomial-ring, including its generating and independence arguments. The tag-to-label map confirms these tags. No SGA source is used.

For step 1 I opened lem-weil-pbc-polynomial-ring-kahler-basis-any-variables: its statement explicitly allows any set of variables and any algebra of coefficients, and explicitly includes the base-changed differential basis. It therefore applies to A(U), E(U), and B(U) with the evaluation algebra structure. It does not require a finite set, an injective base ring map, a flat algebra, or a surjective evaluation. I also opened def-weil-pbc-module-tensor-product: its universal property and generation by pure tensors justify the displayed flip in the tensor order and the balancing in the inverse formula. The ring basis itself is non-elementary and the step is marked accordingly.

For step 2 the cited definition of Kähler differentials includes the full representing property, not just a name for the module. The composite of restriction with the target universal derivation is a derivation over A(U), giving the semilinear restriction on D. The tensor definition supplies its extension to T. I wrote out the square on b[e], with restrictions on both coefficient and generator, rather than asserting an unstated naturality theorem. Identity and composition follow by uniqueness. This is a short calculation from the cited definitions and step 1, and is marked elementary.

For step 3 I opened the complete statements of lem-trf-sheafified-module-differentials-cokernel, lem-pc-sites-module-sheafification-tensor, and lem-pc-sites-module-sheafification-interface. The first explicitly applies to ring PRESHEAVES and preserves universal derivations; the second explicitly allows the base ring to be a presheaf, so it applies with Q, not just P_E; the third extends module actions across Q to Q-sharp and provides functorial factorization. This matters because Q(U) need not equal P_E(U). I apply the tensor comparison to D and B viewed as Q-module presheaves and use Q-sharp = P_E and A-sharp = A. The tensor comparison is not an assertion that evaluation is flat. The generator formula and B-linearity are checked on the actual sectionwise pure tensors and extended through sheafification. This step is non-elementary, with both comparison theorems cited.

For step 4 the interface statement gives a functor, so sheafifying the two inverse maps preserves their composites. The free module sheaf universal-property node explicitly defines B[E] as the module sheafification of the direct-sum presheaf and explicitly states determination of maps by the generator sheaf. Thus the claimed L-sharp identification and canonical normalization are in its statement. This is elementary assembly, not an uncited Yoneda or a reconstruction from a proof of another node.

For step 5 I checked that v is over B, so the polynomial map commutes with evaluation and the differential map extends to a B-linear map after tensoring. The Kähler universal property, tensor universal property and module-sheafification functor are the cited statements used for that construction. The two composites send [e-prime] to d[v(e-prime)] tensor 1; the free module sheaf node explicitly supplies uniqueness for this generator comparison. I used no stronger naturality claim hidden in a cited proof. This also handles noninjective v: collided variables are summed in the free module map, and both linear composites have the same generator values.

I tested the statement and argument on E empty (both modules zero), a singleton E with arbitrary evaluation (one copy of B), infinite E (each polynomial and linear combination has finite support), B the zero sheaf (both sides zero), a nonsurjective evaluation A[x] to A[y] with x sent to 0, and a generator map merging two variables. No finiteness, flatness, surjectivity, stalk-points, or enough-points hypothesis is used. The site is small in the stipulated universe, so all indexing sets and sheafifications used are those allowed by the item. No sheaf section is incorrectly treated as a global polynomial.

Against delivery-errors B–E: no unsplit new nodes or repeated clauses were introduced; all non-elementary facts are existing cited statements, whose full texts were opened and copied verbatim into citations.json; the proof does not use internal constructions available only in their proofs. Dependencies are exactly the union of step uses, no new statements create cycles, and off-unit generic sheafification/free-module tools are declared in split_report.tool_uses for maintainer judgement. All steps are below 2000 characters. The source's sketch is expanded into the necessary sectionwise map, restriction square and sheafification/tensor comparisons; the proof does not move its conclusion to a new node.

## Unfinished work

None in this stage-1 split. Dry-run and delivery results are supplied by the required delivery command.
