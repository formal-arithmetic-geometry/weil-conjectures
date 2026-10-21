1. Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-sheaf-tensor-ideal-quotient.json`: statement node, split into nine proof steps. No exact Mathlib match. The statement and its statement dependencies are unchanged.
- `citations.json`: verbatim statement excerpts for every step/dependency pair.
- No new nodes, Mathlib leaves, unit records, Lean files or repository files are written. `searches.jsonl` contains the six new actual searches. The item's inherited NG search records are retained as inherited evidence.

2. Attachments

None. I searched the live `lean/WeilConjectures/` for the blueprint tag and for tensor/quotient/ideal terminology. The tag has no hit. `ModuleCat.quotSMulTopCompRestrictScalarsIso` in `Algebra/Category/ModuleCat/QuotSMulTop.lean` is for ordinary modules, not sheaves with a varying coefficient ring. `CategoryTheory.Sheaf.reductionDatum` in `Algebra/Category/ModuleCat/Sheaf/Reduction.lean` concerns a constant coefficient ring and a principal kernel. Neither states this item with all its hypotheses and clauses.

3. WANTED

None. All sources needed for the argument are in the read clone.

4. What was wrong or missing

The item was an unsplit statement with no proof. Its statement is correct. The proof must not replace the sheaf quotient by sectionwise quotients on every object: quotient sections need only lift locally. The split explicitly handles this issue before constructing the tensor map. I also avoided two existing lemmas with insufficient generality: `lem-weil-pbc-module-sheafification-underlying-sets` is stated only for the opens of a topological space, and `lem-weil-pbc-ring-sheafification-underlying-sets` only for a small etale site. Instead I used the arbitrary-site abelian/ring result `lem-pc-sites-sheafification-underlying-sets`, combined with the module sheafification definition's underlying abelian sheaf. No statement dispute or unit-route change is needed.

5. Unfinished work

None for this stage-1 split. This is a natural-language proof, not a claim to have proved a Lean declaration.

## Blueprint and duplicate searches

I read the chapter and unit records and the current `main-20261015` text of `def-weil-pbc-completed-pullback` (order 1329). This item supplies ordinary quotient-tensor maps behind its nth evaluation on the reduction tower and completion-map clause. The ancestor command confirms `def-weil-pbc-completed-pullback` through the two existing intermediate items. I retained that provenance and searched the whole DAG and blueprint using `tensor quotient`, `ideal quotient`, `F/IF`, and `quotient tensor`, as well as tensor-product and sheafification terminology. No blueprint node states the full arbitrary-ideal, varying-ring-sheaf result with its two naturality squares. I reused the existing general sheafification results instead of creating local lifting, equality, quotient-action, or tensor-descent nodes.

## Not duplicates

No new nodes were created; there are no new/existing pairs to distinguish. The ordinary-module equivalence and constant principal-reduction theorem mentioned above are special cases, not attachments for this statement.

## Mathlib search assessment

I ran the mandated search command for this item with LeanFinder, Loogle, LeanSearch, and grep, then used a second conceptual phrasing and a grep restricted to `Algebra/Category/ModuleCat/Sheaf`. All six calls returned actual results and are recorded with their exact query strings. LeanSearch/LeanFinder found `TensorProduct.tensorQuotEquivQuotSMul` and its projection formulas, read in `Mathlib/LinearAlgebra/TensorProduct/Quotient.lean`; these apply to ordinary modules over a single commutative ring. The second LeanFinder phrasing found `SheafOfModules.Presentation.map` and the free-cokernel presentation API. I read the relevant `Sheaf/Quasicoherent.lean` declarations: they provide presentations and relations, not this quotient-tensor comparison. Loogle returned no hits for the sheaf/quotient query. These results do not justify declaring the entire item a one-line Mathlib specialization.

## Review by N5

I checked the item and every cited statement against the sources open in the read clone: Stacks `sites-modules.tex`, Tag 03EK (`section-tensor-product`), including its displayed bilinear universal property; Tag 03CY (`lemma-sheafification-presheaf-modules`); and `sites.tex`, Tag 00YR (`section-sheaves-algebraic-structures`) and Tag 00WK (`lemma-sections-sheafification`). The proof is marked agent-written because the normalized quotient comparison and both naturality squares are worked out here, rather than claimed to be a theorem already stated in 03EK. There are no new-node sources to review.

Step 1 uses the module sheafification definition for its underlying abelian sheaf, the arbitrary-site `lem-pc-sites-sheafification-underlying-sets` for abelian groups and commutative rings, and `lem-weil-pbc-site-sheafification-sections-local` for both local representatives and local equality. I checked that these are statements of the cited nodes. The site is small and the argument works in a common sufficiently large value universe, as the local-section lemma requires. Cover comparisons are formulated on common restriction cones or covering sieves; no fibre-product existence or enough-points assumption is introduced.

Step 2 uses the local-section statement and the definitions of module sheaf and module sheafification. It proves closure and gluing of IF from its actual finite-sum prescription, then proves kernel equality and right cancellation for q directly. In particular, it does not cite the topological-space cokernel lemma on a general site and does not assume that q is surjective on sections. The cited category definition indeed describes module morphisms and sectionwise kernels.

Step 3 uses the full presheaf-ring version of `lem-pc-sites-module-sheafification-interface`: its statement really permits a coefficient presheaf O and its ring sheafification, and equips the abelian sheafification with the O#-module action. Here O is S0(U)=R(U)/I(U), P(U)=F(U)/IF(U), and well-definedness of the S0 action is checked explicitly. This is the missing coefficient hypothesis that the version for an already sheaf coefficient would not supply by itself.

Step 4 uses local representatives for S and local equality for two lifts, then the sheaf condition to glue q(rf). The only tensor construction it uses is exactly the sheafification of the sectionwise tensor in `def-pur-sheaf-tensor-product`; the module-sheafification adjunction cited in the step extends the compatible sectionwise maps. The well-definedness, additivity, balancing and restriction checks are written out, rather than hidden in an uncited quotient-comparison lemma.

Step 5 uses the stated pure-section bilinearity and restriction compatibility in `def-weil-pbc-ringed-tensor-section-calculus`. The equation if tensor 1 = f tensor i = 0 kills local generators of IF; the target's separatedness kills IF itself. The module-sheafification universal property then extends the quotient-presheaf map. No flatness enters this argument.

Step 6 computes the two inverse composites and checks S-linearity after local lifting of both scalar sections. It cites local representatives and the ringed-tensor node's stated extensionality, not any unstated claim from a node's proof. Step 7 is only cancellation with the already constructed inverse and the kernel calculation in step 2, so it needs no new external fact or node.

Step 8 checks that h carries IF into IG before defining the quotient map. The square is verified by the two explicit values [h(rf)] and [r h(f)], equal by R-linearity. Step 9 checks I'F is contained in IF before sheafifying the quotient maps. It evaluates both composites on f tensor r-bar to [rf] and checks the unit identity using t(1)=1. Both steps cite exactly the module sheafification functor, local-section theorem, and pure-section extensionality that their statements provide.

I tested I=0 (the ordinary unit comparison), I=R (both sides zero), F=0, I'=I (identity transition), I'=0, and a one-object site (the familiar module quotient). The construction also works for non-flat F, for example Z/2 over Z, because no preservation of a monomorphism by tensor is used. On an object whose quotient sections fail to lift globally, every use of a lift is preceded by the covering refinement justified in step 1. The empty covering case uses the sheaf condition, which makes the corresponding section sets singletons. All steps are under 2000 characters, and none hides a separate standard comparison lemma. The split keeps every non-elementary dependency as a citation of an existing statement, with `proof_deps` exactly the union of step uses and a verbatim quote in `citations.json` for every use.

I checked delivery-errors B1-B10: no new node can carry an illicit proof, duplicate statement, missing definition or unsearched Mathlib claim; the existing statement and metadata are preserved and the blueprint origin is explicit. C1-C8 were checked step by step above, including the arbitrary-site hypotheses and the statements rather than proofs of dependencies. D1-D5 are addressed by the actual balanced-map, inverse, kernel and naturality arguments in the item itself, with no new node restating its clauses. E1-E7 were checked by the concrete quotient maps and small cases above. There is no SGA citation or change of the unit or chapter route, and no Lean or compiler invocation.
