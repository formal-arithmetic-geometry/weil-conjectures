# Q36 stage-1 repair: lem-a1-finite-type-fppf-source-algebra

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-finite-type-fppf-source-algebra.json`: parent statement, statement dependencies and literature route retained; assembly proof has 1397 characters.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-finite-coefficient-polynomial-lifts.json`: statement, unsplit, no complete Mathlib match; simultaneous coefficient construction carrying old steps 2-3.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-fppf-tensor-model-surjectivity.json`: statement, unsplit, no complete Mathlib match; tensor comparison and faithful-flat surjectivity argument carrying old steps 4-6.
- `citations.json`: verbatim statements for each parent step citation. `searches.jsonl` and `search-results/` retain the actual search records and full hits.

## Attachments

No new attachment. The reused `lem-a1-fppf-integer-model` is already closed, attached to `Algebra.FinitePresentation.exists_isPushout_faithfullyFlat` (WeilConjectures/Mathlib/RingTheory/Finiteness/Descent.lean:195-217). The parent's Sheaf declaration at FiniteTypeFppfSourceDescent.lean:69-76 has `sorry`, so is not an attachment. Whole-project searches under WeilConjectures for the blueprint id, finite-type fppf descent, coefficient enlargements and tensor surjectivity found no complete closed declaration of the item or the new helper statements.

## WANTED

None. The Stacks sources are present and were read.

## Returned issue and repair

The released repair note requires at least two comparable statement-only tasks and an assembly of at most 3000 characters. The sandbox initially held only dispatcher marker files, no earlier node, report or search log; the current live parent with the exact six returned steps was therefore copied as the baseline (also retained at `returned-node.json`). No earlier written mathematical work was discarded. The unchanged main statement is valid; no STATEMENT-DISPUTED correction is needed. Maintainer-owned Lean, reviews, import and unit metadata remain untouched. The delivery tool rebases split-owned fields onto current origin.

The two helpers require distinct work: finite coefficient extraction, polynomial evaluation and finite generation; versus the base-change square, explicit inverse maps, surjectivity reflection and quotient generators. Their old argument sizes are 1336 and 1802 characters respectively. Neither repeats the parent hypotheses/conclusion, neither depends on the other, and neither is just an elementary new fact. The existing closed integer-model lemma carries old step 1. No old argument is deleted: the complete old text is preserved below, assigned to its task. New nodes have statements only and empty proof/proof_deps; their proof plans are documented here, not disguised as statements or proof steps in those nodes.

## Mathlib and duplicate searches

Read the complete saved msearch outputs. The first node has semantic searches with two phrasings, LeanSearch, corrected Loogle, and source grep. `PolynomialLaw.exists_lift` (PolynomialLaw/Basic.lean:452-456) handles one tensor over C, not simultaneous lifts over the prescribed relative polynomial base and finite R-generators; `exists_fg_and_mem_baseChange` (Adjoin/FGBaseChange.lean:26-34) handles one finitely generated subalgebra, not that model. FiniteStability.lean:42 supplies a permanence ingredient, not the whole statement. The rejected namespace query is recorded as rejected rather than evidence of absence. The second node likewise has all search kinds and two semantic phrasings. Read TensorProduct/Maps.lean:469-490 and Flat/FaithfullyFlat/Descent.lean:28-68. They give cancellation and descent separately, but neither identifies the arbitrary chosen e and q, proves surjectivity from the lifted R-generators, and supplies the generator images. These are useful candidates for its future worker; no complete one-line Mathlib leaf is claimed. The parent's searches and results from its previous review are retained unchanged and were reread: they distinguish source-tower descent from ordinary base descent.

Before creation, searched all DAG statements/source tags for 0367 and 034Y and key words coefficient, polynomial enlargement, surjectivity/tensor cancellation; also searched all blueprint nodes via blueprint_refs.py for those tags, finite type, coefficient enlargement, faithfully flat, tensor comparison, polynomial enlargement, polynomial lifts and tensor model. Existing general tensor cancellation and module surjectivity nodes do not state either helper's complete criterion. In particular `lem-weil-pbc-tensor-cancel-base-change` is reused conceptually by the future proof, not duplicated as a new cancellation-only node. The new nodes retain the exact ancestor `lem-a1-affine-hc0` and add the item to its existing via chain. Their `same_as` is empty. Read the current main-20261015 ancestor, chapter and unit: this is the already chosen auxiliary schemehood branch, not a replacement of the unit's cohomological route.

## Not duplicates

- lem-a1-finite-coefficient-polynomial-lifts vs lem-a1-finite-type-fppf-source-algebra: The parent descends finite type in an fppf ring tower. This helper constructs a finite polynomial coefficient model for an arbitrary finite family of tensors, without flatness and without concluding finite type of A.
- lem-a1-finite-coefficient-polynomial-lifts vs lem-a1-lft-flat-lfp-source-descent: The existing node states Let $X,Y,S$ be schemes [def-pc-scheme], let $q:X\to Y$ be a morphism flat [def-weil-flat-morphism], locally of finite presentation [def-sbc-locally-finite-presentation], and surjective on underlying points, and let $h:Y\to S$ be a morphism. If $h\circ q:X\to S$ is locally of finite type [def-weil-finite-type-morphism], then $h$ is locally of finite type. No quasi-compactness or separation hypothesis is imposed on $q$, $h$ or the schemes. This helper is a ring-level coefficient construction, not scheme-locality, and supplies only one argument inside the parent ring lemma.
- lem-a1-finite-coefficient-polynomial-lifts vs lem-a1-fppf-integer-model: The existing closed node constructs C,D and the absolute integer-model isomorphism from fppf A to B. This helper takes C,D as input and constructs simultaneous polynomial lifts over R tensor Z C.
- lem-a1-fppf-tensor-model-surjectivity vs lem-a1-finite-type-fppf-source-algebra: The parent descends finite type in an fppf ring tower. This helper takes an already chosen coefficient model and lifts of algebra generators, proves the specific tensor comparison and surjectivity, and propagates its generators. It does not construct a model or assume A to B finitely presented.
- lem-a1-fppf-tensor-model-surjectivity vs lem-a1-lft-flat-lfp-source-descent: The existing node states Let $X,Y,S$ be schemes [def-pc-scheme], let $q:X\to Y$ be a morphism flat [def-weil-flat-morphism], locally of finite presentation [def-sbc-locally-finite-presentation], and surjective on underlying points, and let $h:Y\to S$ be a morphism. If $h\circ q:X\to S$ is locally of finite type [def-weil-finite-type-morphism], then $h$ is locally of finite type. No quasi-compactness or separation hypothesis is imposed on $q$, $h$ or the schemes. This helper is a ring-level coefficient construction, not scheme-locality, and supplies only one argument inside the parent ring lemma.

## Landing-return repair: current DAG rebase

The landing return was administrative: the side-project completion had not been promoted to the live DAG read by the queue. I rebuilt the item from the current shared DAG and reapplied only its split-owned fields. The retained `returned-node.json` is identical, field for field, to the current live parent; the live parent still has the six old proof steps. Both proposed helper ids remain absent from the live DAG. The released stage-1 repair note still explicitly requires at least two comparable statement-only nodes and an assembly under 3000 characters, so the old reviewed status does not supersede this work.

I reread every current live statement used by the parent: `lem-a1-fppf-integer-model` still supplies the compatible absolute model and is audited closed, and `def-weil-pbc-finite-type-algebra` still supplies the finite algebra-generator characterization. I also reread all seven live statement dependencies of the parent and helpers, including the tensor universal property, tensor-product generators, polynomial evaluation, finite presentation and faithful-flat exactness reflection. No cited statement requires a changed application or an additional hypothesis. All five citation records match their current statement verbatim. Stacks 0367 and 034Y were reopened, and the saved actual search outputs were reread without rerunning unchanged queries. The current project source still offers no finished attachment of the parent; its Sheaf theorem ends in `sorry` at line 70. The existing source-library integer-model theorem is the already cited supporting result, not the parent.

The initial delivery dry run completed with `OK (not pushed)` at a69a15cc497. The report and split summary now explicitly identify this landing-return repair; the final dry run and push will rebuild on the server's current base. No old argument, citation, report, or search log has been discarded.

## Review by Q36

I read Stacks descent.tex Tag 0367, label lemma-finite-type-local-source-fppf-algebra, including its whole proof, and algebra.tex Tag 034Y, label lemma-descend-faithfully-flat-finite-presentation, including the absolute integer case and the final relative base extension paragraph. For `lem-a1-finite-coefficient-polynomial-lifts` the source's 'add some elements' sentence becomes the precise finite tensor coefficients and polynomial algebra; its R-generators record both the integer-model base extension and the new variables. For `lem-a1-fppf-tensor-model-surjectivity` the source's surjectivity paragraph and displayed tensor comparison become a criterion with explicit forward/inverse formulas and a finite-generator conclusion. The full supporting proof plans, copied below, retain all calculations for the workers who will split these statements.

Parent step 1 uses only `lem-a1-fppf-integer-model`. I opened its complete statement: it supplies finite presentation of C over Z, faithful flatness of C to D, the compatible maps and e with exactly the pure tensor formula taken by the step. The original hypotheses on A to B are exactly its two input hypotheses. Its now-closed upstream attachment makes this reuse appropriate.

Parent step 2 uses `def-weil-pbc-finite-type-algebra` for the finite b_j, and `lem-a1-finite-coefficient-polynomial-lifts` for P, its R-generators, phi and z_j. I checked the first cited statement's equivalence with algebra generators and the whole new helper statement. Applying it to x_j=e inverse(b_j) needs only R to A, C to A,D and C finitely presented over Z, all already supplied; R need not map to D. The lift equation lambda(z_j)=x_j implies e(lambda(z_j))=b_j, with no unquoted descent assertion. The P, R, C compatibility is expressly in the helper statement.

Parent step 3 uses `lem-a1-fppf-tensor-model-surjectivity` for exactly its chosen-model criterion and `def-weil-pbc-finite-type-algebra` to read the resulting finite generators. I opened/read its statement after writing: maps C to B agree by the model, the C structure on A factors through P by step 2, the R structure on B is the given composite by phi compatibility, C to D is faithfully flat by step 1, e is the specified A-algebra isomorphism, and the z_j lift all chosen generators by step 2. Its finite-generator hypothesis on P follows from helper 1, so its image generators give the parent's conclusion under exactly the original hypotheses. No definition-only citation is used for an additional theorem, and all three assembly steps are marked non-elementary.

I checked B-E point by point with the sources and cited statements open: new statements introduce all rings/maps and notions, carry source tags and labels, have no embedded proof; searches are actual recorded queries with exact text, not inferred availability; existing nodes and blueprint nodes were searched before creation; there are no clause-restatements or dependencies back to the parent. The parent statement/dependencies are unchanged, no SGA source is used, and no Lean file or compiler is touched. Each parent use has a verbatim quotation in citations.json. No parent step exceeds 2000 characters; its total is below 3000.

Edge cases: n=0 and empty coefficient sets give J empty and P=T, with no requirement of a nonzero generator. A zero tensor permits m_j=0 and z_j=0. C=0 forces A=D=0 and the tensor model remains valid. Non-injective structure maps R to A and C to A do not affect the polynomial evaluation. In the second criterion no faithful flatness of P to A is assumed: it is P to Q that is used. If D=0, faithful flatness forces C=0, hence P=A=B=0. If the generator family b_j is empty, B is generated by R alone, whose image is contained in q, so q is still surjective. For C=D with identity map the comparison reduces to P to A itself. The balancing identity a phi(p) tensor z = a tensor pz verifies the inverse formulas even with zero divisors; no flatness of A over P and no Noetherian property is smuggled in. Applying theta to the base change sends 1 tensor z to q(z), which is the exact map needed for reflection of the complex P to A to 0.

## Preservation of the old arguments

The following text is retained verbatim from the returned/current-main baseline as proof material for the indicated tasks; it is not inserted as a proof in either unsplit node.

### Old step 1 -> existing closed integer-model citation in parent step 1

Apply [lem-a1-fppf-integer-model] to the given faithfully flat finitely presented map $f:A\to B$. Obtain $C,D$, $u:C\to A$, $g:D\to B$ and $e:A\otimes_C D\simeq B$, with $e(a\otimes d)=f(a)g(d)$. In particular $C$ is finitely presented over $\mathbf Z$ and $C\to D$ is faithfully flat. These are exactly the hypotheses required by that model lemma; the finite type hypothesis on $R\to B$ is not used yet.

### Old step 2 -> lem-a1-finite-coefficient-polynomial-lifts

Put $T=R\otimes_{\mathbf Z}C$. The tensor-product universal property [lem-weil-pbc-algebra-tensor-pushout-universal-property] gives $T\to A$, $r\otimes c\mapsto r_Au(c)$, where $r_A$ is the image of $r$ in $A$. A finite presentation [def-weil-pbc-finitely-presented-algebra] supplies finitely many ring generators $c_1,\ldots,c_s$ of $C$. Every $t\in T$ is a finite sum of pure tensors by [def-weil-pbc-module-tensor-product]; writing its $C$-coefficients as integer polynomials in the $c_i$ shows that $t$ is an $R$-polynomial in $1\otimes c_i$. Thus $T$ is finite type over $R$ by [def-weil-pbc-finite-type-algebra]. This is the elementary base-extension part of the general-base reduction in 034Y.

### Old step 3 -> lem-a1-finite-coefficient-polynomial-lifts

Choose $R$-algebra generators $b_1,\ldots,b_n$ of $B$ by [def-weil-pbc-finite-type-algebra]. By [def-weil-pbc-module-tensor-product], write $e^{-1}(b_j)=\sum_{k=1}^{m_j}a_{jk}\otimes d_{jk}$, absorbing module coefficients into the $A$-factors. Introduce one variable $X_{jk}$ for each of these finitely many coefficients and put $P=T[X_{jk}]$. Let $\varphi:P\to A$ extend $T\to A$ and send $X_{jk}$ to $a_{jk}$. The images of $1\otimes c_i$ together with all $X_{jk}$ generate $P$ over $R$: expand the coefficients of each polynomial using the generators of $T$. Consequently $P$ is finite type over $R$ without a Noetherian assumption.

### Old step 4 -> lem-a1-fppf-tensor-model-surjectivity

Form $Q=P\otimes_C D$, where $C\to P$ factors through $T$. Since $C\to D$ is faithfully flat, [lem-weil-pbc-faithfully-flat-base-change] gives that $P\to Q$, $p\mapsto p\otimes1$, is faithfully flat. The tensor-product universal property [lem-weil-pbc-algebra-tensor-pushout-universal-property] gives $q:Q\to B$, $p\otimes d\mapsto f(\varphi(p))g(d)$. Its image contains the image of $R$ and each $b_j=q(\sum_kX_{jk}\otimes d_{jk})$. Since these $b_j$ generate $B$ as an $R$-algebra, writing any element as an $R$-polynomial in them proves that $q$ is surjective.

### Old step 5 -> lem-a1-fppf-tensor-model-surjectivity

The base change of $\varphi:P\to A$ along $P\to Q$ identifies with $q$. Explicitly $\theta:A\otimes_P Q\to B$ sends $a\otimes(p\otimes d)$ to $e(a\varphi(p)\otimes d)$. Its inverse sends $e(a\otimes d)$ to $a\otimes(1\otimes d)$. Both maps are well defined by [lem-weil-pbc-algebra-tensor-pushout-universal-property]; the balancing relation $a\varphi(p)\otimes z=a\otimes pz$ shows their composites fix every pure tensor, hence every element by [def-weil-pbc-module-tensor-product]. Moreover $\theta(1\otimes z)=q(z)$. Thus the complex $P\to A\to0$ becomes exact after tensoring with the faithfully flat $P$-module $Q$, since its first map is the surjection $q$ under this identification. By the exactness-reflection definition in [def-weil-pbc-faithfully-flat-ring-map], $P\to A\to0$ is exact. Its kernel at $A$ is all of $A$, so $\varphi$ is surjective.

### Old step 6 -> lem-a1-fppf-tensor-model-surjectivity

Let $p_1,\ldots,p_N$ be the finite $R$-algebra generators of $P$ obtained in step 3. Given $a\in A$, choose $p\in P$ with $\varphi(p)=a$. Express $p$ as an $R$-polynomial in the $p_i$ and apply $\varphi$. This expresses $a$ as the same polynomial in $\varphi(p_i)$. Hence these finitely many images generate $A$ over $R$, which is the conclusion by [def-weil-pbc-finite-type-algebra].

## Unfinished work

The two new statement-only nodes intentionally await independent stage-1 workers. No part of the parent assembly is deferred. Dry-run and push results are reported by the delivery command.
