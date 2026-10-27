## Worker report

Files written:
- dag/nodes/sec-smooth-purity/lem-pur-line-unbounded-derived-tensor.json: existing item, proof assembly now 1988 characters, unchanged statement, stmt_deps and Lean record.
- dag/nodes/sec-smooth-purity/lem-pur-sheaf-line-evaluation-inverse-pair.json: new statement-only node, unsplit; no complete Mathlib match.
- dag/nodes/sec-smooth-purity/lem-pur-flat-single-derived-normalization.json: new statement-only node, unsplit; no complete Mathlib match.
- citations.json: one verbatim statement quotation for each citation of each assembly step.

Attachments: none. No WANTED source. No statement dispute. No work remains in this one-level stage-1 split; the two new unsplit nodes deliberately leave proofs to other workers.

## Repair of the dedicated handoff

The first local diagnostic preserved the live item unchanged because its status is split and it has an earlier Q46/L review. That was a misreading of this assignment. The dedicated entry in coord/returns/Q63.md, headed lem-pur-line-unbounded-derived-tensor, explicitly reopens it under the human decision of 2026-10-21 applied 2026-10-22. I read the whole entry. It requires at most 3000 characters in the item's assembly and at least two comparable statement-only argument extractions, preserving every existing argument and the statement. These are the three preflight diagnostics repaired here: (1) the item's proof now changes; (2) its assembly is 1988 characters; (3) it cites two new nontrivial argument nodes rather than a single renamed restatement of the whole item. No statement or Lean-record change was made.

The ordinary sheaf argument (old steps 1--3 and the ordinary part of 8) and the arbitrary-flat-single normalization argument (old steps 4--5 and 7) are separate reusable obligations. Neither gives the whole item: the first concerns only ordinary module sheaves on an arbitrary small site, and the second treats any flat sheaf, with no invertibility hypothesis or inverse-equivalence conclusion. The old descent argument in step 6 is supplied by the existing generic exact-derived transformation-pasting node and an explicit shift calculation in assembly step 3. The derived linearity in old step 8 uses the two already existing linear-derived nodes and the scalar-conjugation argument in assembly step 4. These uses are strictly statements of those nodes; they do not use their proofs.

## Searches and provenance

I searched WeilConjectures/ for the exact blueprint tag and for unbounded tensor, inverse tensor and line evaluation. There is no full attachment. The recorded theorem SheafOfModules.LineUnbounded.line_unbounded_derived_tensor in lean/Sheaf/Algebra/Homology/LineUnboundedDerivedTensor.lean:231 ends in sorry and is not a finished proof. I read it through its proof, without running any compiler.

The whole-DAG searches covered ids/titles for line tensor/evaluation, invertible dual, flat single, derived equivalence, and statement patterns for inverse pairs and termwise flat tensor. I also searched all blueprint nodes using tools/blueprint_refs.py search with line tensor, exact functor, locally free rank, inverse equivalence, K-flat, evaluation, flat single, tensor equivalence and termwise. None states either complete new obligation. The nearest ancestor command gives det-def-sp-tate-twist-locally-free; both new nodes have that ancestor with via=[lem-pur-line-unbounded-derived-tensor] and the exact last-two-sentences place of proof (3). I read the current main-20261015 ancestor proof, not the older master snapshot. same_as is empty on both new nodes, with the item's existing empty search result retained.

All new-node Mathlib searches were run with the prescribed msearch.py and are recorded verbatim from searches.jsonl. Each proposed node has two semantic phrasings, Loogle and source grep. LeanSearch for the ordinary-line node returned a rate-limit error and is recorded unavailable. LeanFinder returned free-sheaf/unit-Hom and LightCondensed results, not the specified locally trivial sheaf evaluation inverse pair. The targeted grep of Algebra/Category/ModuleCat/Sheaf for invertibility and evaluation returned no hit. I read Mathlib/Algebra/Category/ModuleCat/Sheaf.lean's module/sheaf and unit API; it does not contain the assertion. The flat-single searches returned Module.Flat exactness for ordinary modules, Tor for projective resolutions, the generic exact-functor mapDerivedCategory API, and HomologicalComplex.leftUnitor; none supplies the fixed sheaf K-flat tensor normalization on arbitrary unbounded inputs. I read Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:25--150: mapDerivedCategory and its factorization, shifts, triangulatedness and linearity are supporting ingredients, but the sheaf-specific tensor comparison is absent. The remote Loogle service also lists names not present in the pinned source; none was declared a Mathlib leaf. Extra exploratory searches for derived inverse pairs are logged but create no third node.

## Existing nearby nodes

lem-sc-invertible-dual is for a curve; lem-pc-tensor-dual-invertible and lem-pc-invertible-sheaf-instance are for structure-sheaf modules on schemes. They do not provide the canonical ordinary inverse-pair data for an arbitrary coefficient ring sheaf on an arbitrary small site.

lem-sf-ringed-kflat-single-tensor-comparison permits any module M but requires the input complex P to be K-flat; the new flat-single node assumes only that its degree-zero fixed factor is flat and applies to every input complex, with an exact-functor, integer-shift and cohomology normalization. lem-trf-site-one-sided-tensor-normalization provides the fixed-factor localization normalization, and lem-weil-pbc-kflat-fixed-tensor-triangulated provides its triangulated structure; neither identifies a flat-single tensor with the termwise exact functor and its specified cycles/boundaries cohomology comparison. They are ingredients, not the complete statement. lem-sfb-locally-free-derived-scalars concerns degree-zero scalar extension along a ring map for locally finite free inputs. lem-pc-kflat-closure supplies K-flatness of a flat single but not the functor comparison. lem-sf-integral-line-tensor-comparison(-representative) concerns completed integral coefficients, resolving inputs and reductions; it does not give this arbitrary-flat unbounded normalization.

lem-sp-exact-derived-transformation-pasting is reused, rather than creating another generic inverse-pair descent node. Its statement passes arbitrary finite composites and whiskerings of ordinary exact-functor cells to the derived categories with the specified composition comparisons. Its hypotheses include exactly the cells a, b and both triangle equations obtained from the first new node. It does not assert shift compatibility, so assembly step 3 separately checks that equality on representatives and uses localization faithfulness.

## Review by Q63

I read Stacks sites-modules.tex, Tag 0B8Q/label lemma-invertible-is-locally-free-rank-1, including the local evaluation argument, and Tag 0B8N/label lemma-invertible, including its tensor-equivalence/exactness paragraph and its specified evaluation inverse. This is the source of the first new node. The omitted computations are precisely the existing local inverse and two triangle calculations carried into its normalized statement and preserved below. I checked both composite types: a:ST→1 and b:TS→1, with unit a^{-1}; the two equations are b_{TM} T(a_M^{-1})=1 and S(b_M) a_{SM}^{-1}=1. No locally ringed assumption is used: the direction rank-one locally free implies invertible works on any ringed topos. The converse is neither used nor asserted. Basis change p'=up has dual u^{-1}p^vee, so the proposed inverse is basis-independent. Tensor is sheafified; the formulas are local, not a false assertion that tensor sections globally equal sectionwise tensors.

For the second new node I read sites-cohomology.tex Tag 06YN/definition-K-flat, Tag 06YT/lemma-derived-tor-quasi-isomorphism-other-side, and the construction preceding Tag 06YU/definition-derived-tor; also derived.tex Tag 015F/lemma-right-derived-exact-functor and homology.tex Tag 010N/lemma-exact-functor. The definition of flatness in the cited DAG node is exactness of sheaf tensor. Hence exact-functor cohomology makes the single K-flat; its only other terms are zero. In Tot(C⊗L[0]) only second degree zero contributes, so the total differential is exactly d_C⊗1; there is no infinite-diagonal convergence issue. Fixed-factor descent applies because L[0] is K-flat AND has flat terms; it allows arbitrary C. Exact-derived factorization and localization compare the two functors, and the first-factor shift comparison is unsigned. Naturality on derived morphisms follows from localization, not just from choosing representatives. No geometric stalk argument, boundedness, completed tensor or flatness of cohomology has entered. The node states a derived functor isomorphism and its cohomology normalization, not a list of per-degree isomorphisms in place of the derived result.

Assembly step 1 cites the first new node for the ordinary dual/evaluation/inverse-pair/exactness data and def-weil-pbc-proetale-site for its small-skeleton size convention. I opened both statements. The small site condition makes Mod(R) abelian in the stated module universe. Step 2 cites the second new node for K-flat singles, the normalized exact functor isomorphisms for all complexes, all shifts/triangles, and natural cohomology. Its hypothesis flat L was obtained for P and its dual in step 1. No K-flatness of the varying representative is assumed.

Step 3 cites both new statements, the existing exact-derived transformation-pasting statement, and lem-weil-pbc-localization-universal-property. I opened the latter two full statements. Pasting gives the specified cells and the two inverse-pair equations, rather than arbitrary equivalences with unspecified evaluations. Naturality at d_C gives chain maps. For shift compatibility, all evaluation components are unchanged under reindexing, the differential acquires only (-1)^n, and the representative comparisons from step 2 commute with that shift. Localization clause (3) says equality after precomposition implies equality on D(R); clause (2) descends the transformations and inverses. Thus there is no invocation of an unstated global derived tensor coherence theorem.

Step 4 cites the first new node for ordinary B-linearity, lem-weil-linear-abelian-derived-category for the linear Q and induced scalar action, and the Mathlib leaf lem-cbc-exact-linear-derived-functor for linear D(T),D(S). I opened each full statement; the latter requires additive finite-limit and finite-colimit preserving B-linear functors, all provided in step 1. The remaining scalar-conjugation calculation is stated in the step: bilinearity of composition carries the scalar through the comparison and its inverse. The localized evaluation components are the images under Q of the specified B-linear sheaf maps. This covers every B→R, without asserting the existence of a global constant-ring trivialization.

Small cases: R=0 and the empty site/scheme give the zero module category and the identities still make sense. For P=R the formulas are the unit tensor maps and both triangles reduce to identities. On an overlap with nontrivial unit u the inverse is unchanged by u·u^{-1}. For the flat-single node L=0 makes both functors zero and L=R makes both the identity; flat noninvertible L is permitted and has no inverse-equivalence conclusion. An arbitrary complex with nonzero terms in both directions is allowed because the fixed factor is supported in degree zero. No unbounded cohomology sum or truncation was used. The original item statement and its Lean record were checked byte-for-byte unchanged. There are no new proofs, hollow definitions, compiler invocations or SGA sources. All new nodes are statement-only, complete and individually searchable. Every assembly step is below 2000 characters and the total is below 3000.

The initial stale-assignment report was corrected after reading the dedicated handoff; it is not part of the final mathematical claim. All remaining validation is the prescribed server dry run, followed by direct delivery after OK.

## Preserved argument inventory

The following is the complete prior eight-step argument, retained as proof guidance in the report rather than proof fields of the new statement-only nodes. Old 1--3 go to the first new obligation; old 4--5 and 7 to the second; old 6 and the derived part of 8 are supplied by already existing generic nodes and assembly steps 3--4. No mathematical argument is discarded or replaced by the phrase “standard”.

### Original step 1

On a slice where $P=Rp$, the definition of sheaf Hom identifies $P^\vee$ with $Rp^\vee$, where $p^\vee(ap)=a$. Evaluation is the balanced map $e:P\otimes_RP^\vee\to R$, $x\otimes\phi\mapsto\phi(x)$; it exists by the tensor definition and is locally $(ap)\otimes(bp^\vee)\mapsto ab$. Its inverse there is $a\mapsto(ap)\otimes p^\vee$. If $p'=up$ on an overlap, then $u$ is a unit and $(p')^\vee=u^{-1}p^\vee$, so $(ap')\otimes(p')^\vee=(ap)\otimes p^\vee$. Thus these inverse maps agree on overlaps and glue uniquely by the sheaf axiom. The two composites are identities locally, hence globally, since equality of sheaf sections is local. This also proves that $P^\vee$ is locally free of rank one. No assertion about geometric stalks is used. Restriction of these tensor and Hom constructions to a slice has the stated formulas simply by their definitions: the objects over a slice object and its covering families are the same in the iterated slice.

### Original step 2

Write $T(M)=M\otimes_RP$ and $S(M)=M\otimes_RP^\vee$. The associators and unitors, followed by $e$ or $e$ after symmetry, give natural isomorphisms $a:ST\to1$ and $b:TS\to1$. On a trivializing slice both send $(x\otimes cp)\otimes dp^\vee$, or $(x\otimes dp^\vee)\otimes cp$, to $cdx$, with inverses $x\mapsto(x\otimes p)\otimes p^\vee$ and $x\mapsto(x\otimes p^\vee)\otimes p$. Naturality follows because a module map sends $cdx$ to $cd$ times its value at $x$. With unit $a^{-1}$ and counit $b$, the first triangle sends $x\otimes cp$ to $((x\otimes p)\otimes p^\vee)\otimes cp$ and then to $cx\otimes p=x\otimes cp$. The second sends $x\otimes dp^\vee$ to $((x\otimes dp^\vee)\otimes p)\otimes p^\vee$ and then to $dx\otimes p^\vee=x\otimes dp^\vee$. Local pure tensors generate the sheaf tensor, so these are identities of sheaf maps. These calculations establish the specified inverse-pair identities, not just the existence of some inverse functors.

### Original step 3

Both $T$ and $S$ are additive by the sheaf tensor structure. Their inverse equivalence from Step 2 makes both exact, as the following universal-property calculation verifies. For any finite diagram $(M_j)$ and test module $N$, the equivalence gives $\operatorname{Hom}(N,T(\lim_j M_j))\cong\operatorname{Hom}(SN,\lim_jM_j)\cong\lim_j\operatorname{Hom}(SN,M_j)\cong\lim_j\operatorname{Hom}(N,TM_j)$, naturally with its projections. Hence $T$ preserves finite limits. Using $\operatorname{Hom}(T(\operatorname{colim}_jM_j),N)\cong\operatorname{Hom}(\operatorname{colim}_jM_j,SN)$ gives the dual calculation for finite colimits. Interchange $S,T$ to obtain both properties for $S$. The module-sheaf category is abelian with the site's stated size convention. Thus the flatness definition applies and proves $P$ and $P^\vee$ flat.

### Original step 4

For $L=P$ or $P^\vee$ put $T_L(M)=M\otimes_RL$. By the total tensor differential, $\operatorname{Tot}(C\otimes_RL[0])^n=C^n\otimes_RL$ and its differential is $d_C^n\otimes1$: only the summand with second degree zero survives. Thus this total tensor is the termwise complex $C(T_L)C$, even when $C$ is unbounded. The exact-functor cohomology isomorphism gives $H^n(C(T_L)C)\cong T_L(H^n(C))$ naturally. If $C$ is acyclic the right side is zero, so the K-flat definition proves $L[0]$ K-flat. Its terms are flat: the only nonzero term is $L$, flat by Step 3, and the zero module is flat because tensoring with zero is the zero exact functor. Consequently $P[0]$ and $P^\vee[0]$ satisfy both the K-flat and flat-term hypotheses of fixed-factor tensor descent.

### Original step 5

Apply fixed-K-flat-factor tensor descent with $A=L[0]$ and use its right-factor version. It supplies a natural representative comparison between $F_L(QC)=QC\otimes_R^LQ(L[0])$ and $Q\operatorname{Tot}(C\otimes_RL[0])$ for every complex $C$, not only for flat or K-flat $C$. Step 4 identifies the latter with $Q(C(T_L)C)$. Independently the exact-functor factorization supplies the termwise induced triangulated functor $D(T_L)$ and the natural comparison $D(T_L)(QC)\cong Q(C(T_L)C)$. The localization universal property, applied to these two factorizations, therefore gives a natural isomorphism $F_L\cong D(T_L)$. Its compatibility with shifts follows on representatives: the first-factor shift of $C\otimes L[0]$ is the termwise identity, since the other factor has degree zero, and both termwise complexes have differential $(-1)^n(d_C\otimes1)$ after shift by $n$. Fixed-factor descent and exact-functor factorization give precisely these shift comparisons. Faithfulness of precomposition with $Q$ proves the shift equation on $D(R)$. Both functors preserve distinguished triangles by the two cited descent statements, including their connecting arrows. The same construction applies to $L=P^\vee$.

### Original step 6

Apply the maps $a_C:C(S)C(T)C\to C$ and $b_C:C(T)C(S)C\to C$ degreewise. They are chain isomorphisms: their naturality for the map $d_C^n$ is exactly the chain-map equation in degree $n$. After the representative comparisons of Step 5, their images under $Q$ are natural isomorphisms on complexes between the pullbacks of $F_{P^\vee}F_P$ and $1$, and of $F_PF_{P^\vee}$ and $1$. The localization universal property extends them and their inverses to natural isomorphisms on $D(R)$; it respects their compositions. Hence the two identities in Step 2 descend, giving the inverse equivalences with those very evaluations. For shift compatibility, $a_C,b_C$ have the same components after every shift and commute with its signed differential, so the descended transformations commute with the shifts by faithfulness. Together with Step 5's triangulated structures this makes them isomorphisms of exact functors, compatible with distinguished triangles. Their representative formulas are the specified sheaf evaluations and inverses of Step 1.

### Original step 7

For any representative $K=QC$, the exact-functor cohomology isomorphism applied to $T$ and Step 5's comparison give $H^i(F_PK)\cong H^i(C(T)C)\cong T(H^i(C))=H^i(K)\otimes_RP$. These isomorphisms are natural in complex maps. Both cohomology functors invert quasi-isomorphisms, so the natural transformation and its inverse descend by the localization universal property; this proves naturality for all derived morphisms and independence of the representative. The construction works for each integer $i$ and did not impose any bound on $C$.

### Original step 8

If $R$ is a sheaf of $B$-algebras, module-sheaf Hom groups are $B$-modules by $(bf)(x)=b f(x)$, using $B\to R$ on every slice. The balanced tensor formula gives $((bf)\otimes1)(x\otimes l)=b(f(x)\otimes l)$ and similarly for sums, so $T,S$ are $B$-linear. The linear derived-category lemma supplies the induced $B$-linear structures and the linearity of $Q$. The exact-linear-derived-functor lemma makes $D(T),D(S)$ $B$-linear. Through Step 5 their naturally isomorphic functors $F_P,F_{P^\vee}$ are also linear: conjugating $D(T)(bf)=bD(T)(f)$ by comparison components preserves the scalar, since composition in a linear category is bilinear. Evaluation and its inverse are $R$-linear sheaf maps on representatives by Step 1's formulas, and their images under the linear $Q$ are $B$-linear. The descended components are those maps after the representative comparisons, so both evaluation isomorphisms are $B$-linear as claimed.

## Not duplicates

lem-pur-sheaf-line-evaluation-inverse-pair vs def-trf-algebraic-space: defines algebraic spaces and line modules on their etale site; it proves no evaluation, exactness or triangle identities.

lem-pur-flat-single-derived-normalization vs lem-sfb-ringed-finite-free-resolution-tensor: computes tensor of degree-zero sheaves using a specified bounded-above finite-free resolution; the new node treats arbitrary unbounded inputs with any flat fixed sheaf and a normalized exact functor comparison.

lem-pur-flat-single-derived-normalization vs lem-weil-pbc-integral-local-reduction-lower-bound: gives a lower bound for adic finite reduction; the new node is about tensor with any flat sheaf and no adic datum.

lem-pur-flat-single-derived-normalization vs lem-weil-pbc-regular-single-reduction: computes single-sheaf finite adic reductions under injective uniformizer action; the new node identifies a flat-single tensor functor on all inputs.

lem-pur-flat-single-derived-normalization vs lem-weil-pbc-alternating-unit-resolution: constructs an alternating unit resolution and computes its nonpositive cohomology; it has no flat-single exact-functor normalization.

lem-pur-flat-single-derived-normalization vs lem-weil-pbc-ringed-tensor-cohomological-bounds: gives upper/lower cohomological bounds under Tor hypotheses, not the specified isomorphism of tensor and termwise exact functors.

lem-pur-flat-single-derived-normalization vs lem-sbc-koszul-tensor-derived-tower: compares a strict dual Koszul tower with its derived tensor; it does not compare a flat single to the termwise exact functor and its cohomology.

lem-pur-flat-single-derived-normalization vs lem-weil-pbc-regular-quotient-self-cohomology: computes two cohomology degrees of quotient self-tensor for a specified unit sequence; the new node requires a flat fixed factor and identifies its entire functor.

lem-pur-flat-single-derived-normalization vs lem-weil-pbc-periodic-quotient-tor: computes periodic quotient Tor from alternating unit endomorphisms; the new node is an exact flat-single termwise comparison.

lem-pur-flat-single-derived-normalization vs lem-weil-pbc-uniformizer-reduction-cohomology: gives one degree of finite reduction from uniformizer injectivity; the new node assumes a flat fixed sheaf and identifies the full exact functor.

lem-pur-flat-single-derived-normalization vs lem-weil-pbc-principal-adjacent-quotient-tor: computes adjacent finite quotient Tor in nonpositive degrees; the new node concerns arbitrary flat sheaves with a natural triangulated termwise normalization.

lem-pur-flat-single-derived-normalization vs lem-sf-cochain-tensor-model-rigidity: gives uniqueness of the tensor bifunctor from flat-term K-flat representatives; the new node identifies a flat-single specialization on every unbounded input with D(T_L) and normalized cohomology.

lem-pur-flat-single-derived-normalization vs lem-exc-intrinsic-resolution-tensor-homology: compares cohomology under finite-coefficient intrinsic realization using a K-flat resolution; the new node has no realization or finite coefficient hypotheses and provides a functor isomorphism.

lem-pur-flat-single-derived-normalization vs lem-sf-finite-comparisons-existence: constructs the FiniteComparisons record for a finite-coefficient open square, not a flat-single tensor functor on a general site.

lem-pur-flat-single-derived-normalization vs lem-pur-line-unbounded-derived-tensor: the parent combines sheaf-line duality with flat-single normalization, evaluation descent and coefficient linearity. This strictly smaller extraction needs no invertibility and gives no inverse pair; the human explicitly requests independent statement-only subarguments.


lem-pur-flat-single-derived-normalization vs def-pc-derived-tensor-cohomology-vanishes: defines a predicate for one cohomology group of a structure-sheaf derived tensor to vanish using a K-flat representative; it does not prove or normalize an exact tensor functor.

lem-pur-flat-single-derived-normalization vs def-pc-derived-tensor-complex-cohomology-vanishes: defines the analogous vanishing predicate with an arbitrary second derived object; it does not compare flat-single tensor to a termwise exact functor.

lem-pur-flat-single-derived-normalization vs def-sc-derived-tensor-augmentation: defines when a derived morphism is represented by a tensor augmentation P tensor J to P; it does not assert exactness or a flat-single functor comparison.

lem-pur-flat-single-derived-normalization vs lem-sc-source-kflat-tensor-left-triangulated: proves shifts and triangles for a K-flat fixed homotopy factor, but gives neither the flat-degree-zero identification with D(T_L) nor its cohomology normalization; it is one ingredient of the new obligation.

lem-pur-flat-single-derived-normalization vs def-pd-section-derived-realization: defines tensor and operation comparisons for a condensed coefficient section-equivalence realization, not flat-single tensor normalization on an arbitrary ringed site.

lem-pur-flat-single-derived-normalization vs def-pd-section-derived-tensor-data: defines the conjugate tensor construction under a section equivalence; the new theorem has no section equivalence or condensed coefficients and proves a flat-single termwise comparison.

lem-pur-flat-single-derived-normalization vs def-weil-pbc-completed-constant-realization-data: specifies adic completion realization and finite-module quotient comparison records; the new theorem has no adic data and concerns arbitrary flat fixed factors.

lem-pur-flat-single-derived-normalization vs def-weil-pbc-tensor-descent-representative-comparison: defines the published tensor representative comparison on pairs of flat-term K-flat complexes; it does not identify flat-single tensor with D(T_L) on nonresolving inputs.

lem-pur-flat-single-derived-normalization vs lem-weil-pbc-completed-constant-derived-tensor-tower: proves derivability of a tensor inverse-sequence diagram and its counit on K-flat inputs; the new theorem uses a flat single, arbitrary inputs and an exact triangulated normalization.

lem-pur-flat-single-derived-normalization vs lem-weil-pbc-completed-constant-resolution-tensor-calculation: compares quotient diagrams on realized bounded-above finite-free resolution sources; the new theorem has no realization/quotient tower or boundedness condition and identifies an entire exact functor.

The duplicate gate listed these ten additional shared-06YU candidates. I opened every full statement, checked the object/hypothesis/conclusion differences above, and found no full match. No node was replaced by a name-only distinction.
