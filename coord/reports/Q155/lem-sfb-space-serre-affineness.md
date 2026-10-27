# Stage-1 report: lem-sfb-space-serre-affineness

## Files written

All node files below are in dag/nodes/sec-six-functors-basics/ in this sandbox.

- lem-sfb-space-serre-affineness.json: item split; original statement and statement dependencies retained; five proof steps follow Stacks 07V6.
- lem-sfb-space-acyclic-affinization-geometry.json: new statement-only node, unsplit; no Mathlib match. Separatedness and universal injectivity of the absolute canonical affinization map under H^1 vanishing (07V4 and 07V5).
- lem-sfb-space-affine-etale-polynomial-generators.json: new statement-only node, unsplit; no Mathlib match. Finite global polynomial generators for an affine etale chart algebra of a space separated over an affine scheme, with quasi-coherent kernel.
- lem-sfb-space-discrete-fibres-locally-quasifinite.json: new statement-only node, unsplit; no Mathlib match. Discrete field-fibre criterion for locally quasi-finite morphisms of algebraic spaces (06RW).

Also written: citations.json (one exact statement quotation per proof-step citation), searches.jsonl (msearch.py log), saved complete search results, and this report. No repository, launcher, Lean source, compiler or git command was used for writing/building.

## Attachments

None. A search of WeilConjectures for the item tag and Serre/affineness terminology finds scheme criteria in AlgebraicGeometry/SerreCriterionAffineness.lean and AlgebraicGeometry/Cohomology/SerreCriterion.lean. They assume a Scheme; they do not prove the algebraic-space item. The new inputs concern algebraic spaces as well. The Mathlib hits are scheme morphisms, etale ring algebras, and ordinary affine scheme instances, and so cannot be substituted for these statements.

## WANTED

None. All sources used are present in literature/stacks-project/. No SGA source is used.

## Corrections and scope

The item was unsplit, with no proof. Its statement is the precise H^1-only assertion of Situation 07UY and Proposition 07V6 and requires no correction. The source's slogan about all higher cohomology is not added as a new clause. The split retains its coefficient convention: additive small-etale cohomology. In the last step, the existing Zariski/etale comparison is explicitly invoked before applying a scheme-module cohomology criterion.

The canonical map to Spec Gamma is absolute; Spec Gamma need not be an S-scheme when S is nonaffine. The new geometry statement and polynomial-generators statement explicitly permit this absolute map. The other geometric tools apply over Spec Z. At the end the original S-structure is recovered by evaluation and naturality of the represented structural map. No extra hypothesis of an affine base S is introduced.

I read the current latest blueprint unit and direct-images proof, and the recorded chapter/unit. This node is a downstream generic affineness input to the recorded alteration support chain; it does not replace any direct-image or alteration step. The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor reports None for this created-node chain. I preserved that result and its detailed inherited place/via chain; new via lists prepend this item. No fabricated blueprint ancestor is supplied. Searches of the whole blueprint for Serre, vanishing, affinization, polynomial generators, discrete, quasi-finite, 07V4, 07V5, 07V6 and 06RW found no blueprint node stating any of the three new results. Existing scheme criteria and space representability tools are cited, not duplicated.

The source proof of Properties of Spaces 03H6 has a final phrase calling its finite-subatlas map finite surjective, although the construction only gives surjective etale (e.g. A^1 minus a point covered along with another affine open, with nonfinite open immersions). The item does not use that phrase: its atlas is constructed from the existing affine-atlas and finite-subatlas statements and the finite coproduct/spectrum isomorphism. The resulting map is only asserted surjective etale, as needed.

## Not duplicates

lem-sfb-space-acyclic-affinization-geometry vs lem-sfb-space-serre-affineness: the former proves existence, separatedness and universal injectivity of the canonical map, not schemehood or affineness; the polynomial-generation, finite-type, quasi-finiteness, schemehood and final scheme criterion remain in the item's proof.

lem-sfb-space-affine-etale-polynomial-generators vs lem-sfb-space-serre-affineness: the new node assumes separatedness and has no cohomology-vanishing hypothesis; it gives a polynomial surjection of module sheaves, not a surjection on global sections, finite type of B over Gamma(X), or affineness. Those deductions remain in the item.

lem-sfb-space-affine-etale-polynomial-generators vs lem-trf-scheme-etale-quasi-coherent-kernel: the existing node gives quasi-coherence of a kernel on a scheme's etale site; it gives neither global finite algebra generators for an affine etale chart of an algebraic space nor the evaluation surjection.

lem-sfb-space-affine-etale-polynomial-generators vs lem-sfb-space-infinitesimal-lift-pseudotorsor: the existing node concerns the torsor of infinitesimal lifts along a square-zero thickening, with Hom of differentials as its acting module; it gives no affine-etale chart algebra or polynomial generators. Both cite 03M1 for quasi-coherence closure properties.

No other existing node shares a source tag with the new nodes in the source-tag scan. The discrete-fibre node generalizes a scheme-only criterion and is not supplied by the existing separated locally quasi-finite representability node, whose input already assumes local quasi-finiteness.

## Review by Q155

I read spaces-cohomology.tex Situation 07UY, the complete proofs of 07UZ, 07V0, the closed-set separation lemma, 07V4, 07V5, and Proposition 07V6. For the geometry node I also read spaces-properties.tex 05Z1, which constructs the canonical absolute morphism via the ring map on sections. The geometric conclusions are strictly before the finite-type argument: 07V4 uses affine base change and closed-point separation, and 07V5 uses an integral scheme cover and the scheme Serre criterion. Neither assumes the algebraic-space affineness proposition being proved. These arguments are left for the new statement-only node to split later, not represented as a proof in that node.

For the polynomial-generators node I read 07V6 from the choice of U through the verification on U, and its cited flat base-change statement 073K, as well as spaces-properties.tex 03M1. With R=U times_X U, separatedness over an affine target makes R a closed affine subscheme of U times_V U. Since R -> U is affine etale its coordinate algebra C is finitely presented over B. The surjection B tensor_A B -> C means finitely many C-generators use finitely many elements s(g_i); thus these g_i can be chosen in B. The flat base-change identification of the chart pullback of the pushforward algebra is exactly what checks the polynomial surjection. Quasi-coherence of the algebra and kernel are included in the new statement, rather than silently assumed by the parent. These claims do not require H^1 vanishing. For the discrete-fibre node I read all of spaces-morphisms.tex 06RW: its necessary hypothesis is local finite type, and the conclusion is chartwise local quasi-finiteness. It is not a theorem that a discrete fibre alone forces finite type.

For item step 1 I opened every cited statement. The new geometry statement supplies exactly the canonical map, closed diagonal, and universal injectivity. The existing affine-atlas node gives a disjoint union of affines; the finite-subatlas node, under precisely quasi-compactness, gives a finite still-surjective etale subatlas; the finite-coproduct-spectrum node identifies this with an affine scheme. I do not take finiteness or affineness of the map U -> X from these statements.

For step 2 the new polynomial statement gives a module-sheaf short exact sequence with quasi-coherent kernel. The vanishing assumption applies to that kernel, not to an arbitrary algebra ideal lacking quasi-coherence. I opened the general derived-functor long-exact statement: its exact segment is Gamma(P) -> Gamma(phi_* O_U) -> H^1(K). The cited sites/cohomology node provides the ambient abelian sheaves with enough injectives and the additive left-exact global-sections functor. Thus the required group surjection follows. Direct-image sections are B by the supplied chart-algebra statement. The universal delta-functor and H^0 comparison in the site definition provide the ordinary sections interpretation.

For step 3 I opened the exact statement of the existing space-cohomology filtered-colimit node. It allows abelian sheaves, arbitrary small filtered categories and q=0, with precisely the item's qcqs hypotheses. The finite subsets of the monomials are a small nonempty directed set. The polynomial module is their colimit of finite sums of O_X. Finite sums of additive sheaves are products, so their sections are the corresponding finite products/sums of A. The colimit identification therefore gives finite polynomial coefficients; the multiplication of the monomial summands gives the ring identification, not just an additive-group isomorphism. This is a routine assembly from that cited theorem, written out as an elementary step. In particular no illicit interchange with an unfiltered colimit is used.

For step 4 I read the scheme finite-type definition and the local-properties-chart-test statement. Spec B -> Spec A has the single affine presentation with finitely generated algebra proved in step 3. The chart-test node then gives local finite type of p. Universal injectivity makes each field fibre empty or a singleton, which is a discrete space. The new 06RW node is now applicable, with all hypotheses supplied, and produces the local quasi-finiteness that the next node actually requires.

For step 5 I opened the separated locally-quasi-finite space representability statement and checked its closed-diagonal hypothesis against step 1 and its chartwise quasi-finiteness against step 4. Its conclusion supplies an actual scheme, without an affine assumption. I read the full statement of the existing quasi-coherent Zariski/etale equivalence, which takes each ordinary quasi-coherent ideal to a site quasi-coherent module. I also read the full cohomology-comparison node: it identifies Zariski module H^1 with additive etale H^1 of that same associated sheaf. Only after that identification do I apply the existing quasi-compact scheme criterion lem-pqf-quasicompact-h1-zero, whose exact statement assumes H^1 vanishing for all quasi-coherent ideals. Representing isomorphisms transport these sites/structure sheaves by inverse equivalences; evaluation at the identity and naturality explicitly recover the map to S. There is no change to the coefficient category or a hidden strengthening of the scheme criterion.

I tested the new statements on X empty (A=0, empty atlas and m=0 permitted), the identity chart of any affine scheme (m=0 suffices), a finite disjoint union of affine charts, nilpotent affine schemes, singleton and empty field fibres, and positive-dimensional affine space. The geometric node does not assert that the original structure map to S is universally injective: it asserts this only for the canonical map to Spec Gamma, so affine lines are not counterexamples. The discrete-fibre criterion would fail without local finite type, which remains explicit. All new statements introduce their own objects and all nonstandard notions cite their defining nodes or are defined inline. They have no proof or proof dependencies. None restates the item or one of its clauses. Every cited node has been opened, and citations.json uses its actual statement text. The five parent steps are each below 2000 characters and hide no separate comparison or descent argument: those are supplied by the cited nodes. The statement and statement dependencies of the item are unchanged; no hollow data, Lean file, compiler, or SGA source is involved.

I checked delivery-errors B1-B10, C1-C8, D1-D5 and E1-E7 against the files and sources. Searches were run only via msearch.py, with two semantic phrasings, Loogle, grep, and LeanSearch per new node; their full actual outputs are retained. The scheme-only hits cannot prove algebraic-space statements by one-line specialization, so all three new nodes remain unsplit rather than being falsely marked Mathlib leaves. Cross-unit nodes are generic tools and each is declared in split_report.tool_uses; no maintainer-owned tool_uses field was set.

## Unfinished work

No unfinished work for this one-level split. The three new statement-only nodes are deliberately left unsplit for the queue, as required. Final validation and delivery results follow below.
