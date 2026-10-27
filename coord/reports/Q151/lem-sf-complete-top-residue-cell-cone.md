## Worker report

Repair of the returned stage-1 split, Q151, 2026-10-22. Only stage 1 was performed: no Lean edits, compiler, Lake or builds. The sandbox initially contained only dispatcher .brief markers, with no retained node, report or searches.jsonl. I therefore copied the current shared node and kept its seven proof steps verbatim in baseline-proof.json and below; I did not treat the missing prior response as invalidating that proof. The current repository has the reviewed Q04 proof, including its correction from one chosen splitting to every splitting. The delivery tool rebases the split fields onto the live server head and retains maintainer-owned fields.

Files written for delivery:

- dag/nodes/sec-six-functors/lem-sf-complete-top-residue-cell-cone.json — original statement unchanged; four assembly steps, 1898 characters total.
- dag/nodes/sec-six-functors/lem-sf-complete-lifted-top-cell-triangle.json — statement, unsplit; no Mathlib match. Integral lifting and completeness argument, without hypotheses on lower residue cohomology.
- dag/nodes/sec-six-functors/lem-sf-prescribed-residue-cell-cone-model.json — statement, unsplit; no Mathlib match. Field-coefficient splitting, all-model map identification, cone model, contraction and restricted tensor calculation, without an integral coefficient ring or completeness assumption.
- report.md and citations.json — author's source review and verbatim statement quotes for every parent step citation.

Attachments: none. The search of lean/WeilConjectures for the item tag, top/residue/cell/basis terminology and cone/splitting terminology found no declaration proving the whole item. lean/Sheaf/Paper/CompleteTopResidueCellCone.lean:264 states the main theorem, whose proof still ends in sorry. That is not an attachment. I also read the closed upstream ChainComplex.nonempty_homotopyEquiv_of_split_identity: it concerns ordinary rank-one module chain complexes and does not state either new sheaf-complex result.

WANTED: none. All source material used is available locally.

The returned fault was proof granularity, not a false statement. Neither the parent's hypotheses nor any conclusion was changed. Both new nodes have empty proof/proof_deps and null proof_origin, so other workers can split them independently. Their self-contained statements have 2213 and 2432 characters, with separately substantial arguments. This is not moving the whole parent into one child: the first node uses only a prescribed top residue basis and constructs an integral complete triangle; the second takes an arbitrary field-valued bounded object and an already supplied top cell/triangle and computes its cone. Each omits a substantial part of the parent's work and has genuinely different hypotheses. The parent's original lower-degree bases are needed only when applying the second node.

## Repair of the returned points

The return contains one substantive request, repeated under compiler attribution: distribute the 5464-character argument among at least two new unsplit nodes of comparable scope, preserve the statement, and keep the assembly at most 3000 characters. I added exactly the two nodes above. Old steps 1-3 form the integral argument (1984 characters before extraction); old steps 4-6 form the residue argument (3006 characters before extraction). Both arguments remain verbatim below as the work briefs. The source-cell K-flat calculation in old step 4 belongs to the first node's canonical source-reduction clause. The residue-zero portion of old step 7 belongs to the second node's a=b clause. Old step 7's integral zero detection is the short application of the existing Nakayama and zero-cone nodes in new parent step 3; its rank-zero and empty-scheme cases are also asserted in both new statements and assembled in parent step 4. Thus no substantive argument was deleted or replaced by a shorter assertion. No extra child proof was written: these are the explicit statement-only work items the human requested.

## Source and search audit

I read literature/stacks-project/proetale.tex, lemma-describe-constructible-complexes (Tag 09C2), and lemma-local-structure-constructible-complex (Tag 09C3), especially the paragraph beginning “If b > a” and the residue-amplitude assertion whose details the source omits. The first new node isolates the finite prescribed-basis specialization of that lift and the complete triangle. The second isolates the omitted residue calculation in the field case; it does not assert that an arbitrary surjective generator map has a shorter cone without being a cohomology basis. I also read derived.tex definition-cone (014E), lemma-morphisms-from-projective-complex (064B), and the existing triangle and completion node statements. The argument follows the permitted Stacks/blueprint route and uses no SGA source.

I read the chapter sec-six-functors and unit sk-rem-sf-pf-done, and the current main-20261015 lem-fix-weil-operations proof paragraph beginning “For an admissible exceptional adjoint”. Its evaluation sentence is the existing blueprint ancestor place for the local projective-model branch. The parent is not a key unit node. Both children's blueprint.from names lem-fix-weil-operations, gives the exact inherited evaluation sentence and extraction place, and has via = [parent, lem-fix-residue-lisse-projective-models, lem-fix-constructible-tensor-completion].

Whole-DAG keyword/title searches covered top residue/cell/basis, split cohomology, identity cones and the source tags. Whole imported-blueprint searches with tools/blueprint_refs.py covered “top residue”, “split complex”, “09C3”, “cohomology basis”, “top summand”, “mapping cone”, “free cohomology” and “lifted”. None states either new lemma; the generic splitting and source-free-completeness nodes are cited tools in the retained arguments. Existing local residue homotopy nodes concern finite free structure-sheaf complexes near a point or cancellation of a split differential, not a prescribed top map in the unbounded category of constant-field module sheaves. The identity-cone contraction already exists as a generic tool (lem-pur-kinjective-cone-contractible); the second new node is substantially more than that contraction.

Every new Mathlib query was run through the mandated batch2/msearch.py, and the exact queries and result names are recorded in searches.jsonl and the new nodes. Both nodes have LeanFinder, LeanSearch, Loogle and source grep; a second phrasing was tried for each. The lifting searches returned ordinary IsAdicComplete lifts, BDeRham completions, and module basis results, not a derived sheaf lift with complete cone. The residue searches returned degreewise-split mapping-cone comparisons and generic cone homotopies, plus a single-projective-object splitting. I read Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean:93 (homotopyToZeroOfId), :537 (complete_distinguished_triangle_morphism), and DerivedCategory/Ext/EnoughProjectives.lean:40 (isSplitEpi_to_singleFunctor_obj_of_projective). These are useful components, not exact matches or one-line specializations of either new statement. I retained all inherited item searches, rather than claiming to have run them this session.

## Review by Q151

I checked the actual parent's statement and all seven original steps against the sources and opened every original proof dependency. The first new statement defines the coefficient sheaf as the inverse limit of constant finite quotient sheaves and defines quotient-tower completeness with the actual quotient transitions and restricted scalars. Its hypotheses are quasi-compactness, exact terminal evaluation, residue Tor interval, and only the top basis. The existing cohomology-bounds node gives precisely H^(b+1)(M)=0 without constructibility. The free-resolution node gives precisely the canonical exponent-one triangle, not a triangle for a different completion convention. The long exact sequence then gives the required epimorphism. The evaluation-exact node applies to any ring sheaf under exactly the assumed set-sheaf hypothesis. The split-model node gives the shifted-free Hom bijection for arbitrary target objects, so it applies with C=B_T even though M's lower cohomology need not be free. This lifts the chosen sections, and naturality of the quotient map fixes their reductions. The free-resolution node also states completeness of the finite free source. The coefficient-limit node identifies B_T with the pulled-back integral ring; the inverse-limit projections are the quotient maps appearing in the completion definition. The Nakayama node explicitly states closure under cones. These are exactly the arguments retained for the first node, not extra unstated conclusions.

For the second node, I removed the integral hypotheses entirely and retained only exact evaluation, bounded residue cohomology, its prescribed finite free bases, and a given triangle whose first map induces the top basis. The existing split-model node gives a zero-differential model. The Hom bijection's injectivity proves equality under every prescribed-cohomology isomorphism phi, rather than claiming this stronger assertion from the node's last sentence about its one displayed model. The cone formula puts the extra source copy in degree b-1, with identity differential to degree b. The homotopy h^b=id satisfies hd=id in degree b-1 and dh=id in degree b. TR3 and triangle-morphism-iso identify any supplied derived cone with that literal model. Restricting the surviving lower model gives a finite sum of free shifts. Its tensor with an acyclic complex is a finite sum of reindexed acyclic complexes (with the standard shift signs); hence it is K-flat, and derived tensor with a degree-zero module is the stated split complex. This computation is on each localized site and never assumes that completeness is preserved by arbitrary restriction. The second statement gives the derived isomorphisms themselves, not merely cohomology-wise comparisons. The a=b case has empty lower sum; r_b=0 has zero identity pair.

The parent assembly was checked citation by citation:

1. The new integral-triangle statement supplies f, its canonical source reduction, H^b(f_1)=theta_b, and a quotient-tower-complete L. All of its hypotheses occur verbatim in the unchanged parent, and it does not require the lower theta_q.
2. lem-pur-derived-change-of-rings explicitly states that scalar extension along a morphism of ring sheaves is an everywhere-defined exact functor, computed on K-flat complexes. It therefore gives the reduced distinguished triangle with third object L tensor^L k_T. The unit test in the Tor definition supplies the required cohomology bound for N=M_1. The new residue-cone node then supplies every model, homotopy, derived cone and local Tor conclusion used. The complete object's source reduction was already normalized in step 1.
3. The new residue-cone statement explicitly says C=0 for a=b. det-prop-sfb-qlbar-colimit-x-integral-limit clause (3) gives the canonical ring identification; sk-def-pe-derived-completion defines the same canonical quotient comparison. det-pe-derived-nakayama-first-reduction explicitly says a complete object with zero first reduction is zero, and lem-kun-distinguished-cone-zero says exactly that the first arrow of a triangle is invertible iff its third object is zero. No boundedness or affine hypothesis was added here.
4. This is elementary substitution in the two new statements: their r=0/r_b=0 and empty-site clauses cover it. All other steps are marked non-elementary; none exceeds 2000 characters.

The small cases checked were a=b=0 with M a finite free integral sheaf, where the residue identity cone contracts and derived Nakayama makes f invertible; b=a+1 with one free copy in each degree, where the remaining cone is the degree-a copy; r_b=0, where the source and identity pair vanish and the cone is the lower model; arbitrary negative b (the identity pair still lies in b-1,b); all ranks zero; and T empty. In the first node lower residue cohomology is allowed to be nonfree and the conclusion claims no lower-cone model. In the second node no integral complete lift is claimed. These checks rule out the hypotheses that would otherwise be silently imported from the parent. The finite dimension assertion uses a field; I did not generalize to arbitrary coefficient rings while still claiming it.

B1-B7: new nodes are statement-only with every object introduced, notions are defined inline or have their definition dependencies, source places use the Stacks tag and label, and TeX is single-escaped in rendered strings. C1/C4: every non-elementary parent inference cites an opened statement that actually says it, and citations.json copies the statements verbatim. D1/D2: this repair deliberately distributes the two distinct arguments requested by the human instead of shifting everything into one node or keeping the old long proof. E: no affine or Noetherian hypothesis is used under a quasi-compact-only assumption, no ordinary tensor is substituted for derived reduction, and no arbitrary section lift is treated as a cohomology basis. I corrected no statement; the repair corrects granularity only. The retained all-model equality correction from the previous independent review is present in the second child and the assembly.

## Not duplicates

lem-sf-complete-lifted-top-cell-triangle vs lem-sf-weakly-contractible-projective: exact evaluation and finite free projectivity alone neither lift the top residue basis of a complete integral object nor compute the cone of a prescribed cell.

lem-sf-complete-lifted-top-cell-triangle vs lem-fix-residue-lisse-projective-models: the existing node gives bounded projective local integral models after a clopen cover on an affine; it supplies neither a prescribed top lift nor a residue-cell cone under every prescribed splitting.

lem-sf-complete-lifted-top-cell-triangle vs def-sf-completed-integral-scalar-action: this defines a scalar natural endomorphism on completed-coefficient complexes; it asserts no basis lift or cone calculation.

lem-sf-complete-lifted-top-cell-triangle vs lem-sf-clopen-lisse-complete-localization: this gives clopen trivialization and completeness-preserving restriction, not a top-cell morphism or its field-coefficient cone.

lem-sf-complete-lifted-top-cell-triangle vs lem-sf-projective-cohomology-split-model: this gives a cohomology splitting and shifted-free Hom bijection. It does not construct an integral lift across reduction with a complete cone, or identify an arbitrary supplied cone, its identity-pair chain model and all restricted derived tensors.

lem-sf-complete-lifted-top-cell-triangle vs def-sf-clopen-restriction-data: this is normalized coefficient/restriction data, not a top-cell or cone theorem.

lem-sf-complete-lifted-top-cell-triangle vs lem-sf-clopen-cover-geometry: this gives clopen refinements of covers and inheritance of exact evaluation, not a derived cell or cone.

lem-sf-complete-lifted-top-cell-triangle vs lem-sf-complete-top-residue-cell-cone: the parent combines integral lift and a fully computed residue cone; the first child requires only the top basis, while the second starts with an arbitrary field-coefficient triangle and assumes no integral lift or completeness. This requested modular re-split is recorded above.

lem-sf-complete-lifted-top-cell-triangle vs lem-sf-completed-coefficient-free-resolution: this gives free quotient resolutions, complete free sources and the uniformizer triangle, but no lift into a given M and no prescribed residue-cell cone.

lem-sf-complete-lifted-top-cell-triangle vs lem-sf-clopen-coefficient-comparison: this gives coefficient restriction isomorphisms on opens; no cell or cone is constructed.

lem-sf-complete-lifted-top-cell-triangle vs lem-sf-clopen-lisse-partition: this trivializes finitely many lisse sheaves on a clopen cover; no derived top map or cone is specified.

lem-sf-complete-lifted-top-cell-triangle vs lem-fix-constructible-flat-cohomology-tor-bound: this proves a Tor bound for an existing residue object; it supplies neither a prescribed integral cell nor the shortened cone model.

lem-sf-complete-lifted-top-cell-triangle vs lem-sf-projective-top-cell-attachment: this starts with an integral triangle and a projective lower model and realizes its connecting map as a chain differential; our first node constructs the triangle, and our second computes its field residue rather than reconstructing an integral model.

lem-sf-complete-lifted-top-cell-triangle vs lem-sf-clopen-derived-compatibility: this concerns restriction of reductions and completeness along a clopen open, not construction of a top basis lift or computation of a cone.

lem-sf-complete-lifted-top-cell-triangle vs lem-weil-pbc-exact-completion-data: this constructs a completion endofunctor/unit with exactness, not a prescribed finite free cell or cone model.

lem-sf-complete-lifted-top-cell-triangle vs lem-weil-pbc-normalized-constructible-local-effectivity: this gives adic-lisse local models for normalized constructible towers on a Noetherian scheme; it neither lifts a specified top basis nor computes an arbitrary field-coefficient cell cone.

lem-sf-complete-lifted-top-cell-triangle vs lem-weil-constructible-coefficient-homology-triangulated: this proves closure of intrinsic constructibility under triangles; it makes no prescribed basis or chain-cone assertion.

lem-sf-complete-lifted-top-cell-triangle vs lem-weil-pbc-uniform-local-model-cohomology: this derives common cohomological bounds from uniform local integral models, not a top-cell lift or residue cone.

lem-sf-complete-lifted-top-cell-triangle vs lem-weil-pbc-uniform-complete-triangulated: this proves closure of a uniformly constructible complete subcategory under triangles, with stronger base hypotheses; it does not construct a prescribed cell or the explicit field cone model.

lem-sf-complete-lifted-top-cell-triangle vs lem-weil-pbc-uniform-reduction-criterion: this characterizes uniform constructible local models via reduction profiles; it neither constructs the integral cell nor computes its cone.

lem-sf-complete-lifted-top-cell-triangle vs def-weil-pbc-uniform-reduction-profile: this defines a reduction cohomology profile and asserts no lifting or cone theorem.

lem-sf-prescribed-residue-cell-cone-model vs lem-sf-weakly-contractible-projective: exact evaluation and finite free projectivity alone neither lift the top residue basis of a complete integral object nor compute the cone of a prescribed cell.

lem-sf-prescribed-residue-cell-cone-model vs lem-fix-residue-lisse-projective-models: the existing node gives bounded projective local integral models after a clopen cover on an affine; it supplies neither a prescribed top lift nor a residue-cell cone under every prescribed splitting.

lem-sf-prescribed-residue-cell-cone-model vs def-sf-completed-integral-scalar-action: this defines a scalar natural endomorphism on completed-coefficient complexes; it asserts no basis lift or cone calculation.

lem-sf-prescribed-residue-cell-cone-model vs lem-sf-clopen-lisse-complete-localization: this gives clopen trivialization and completeness-preserving restriction, not a top-cell morphism or its field-coefficient cone.

lem-sf-prescribed-residue-cell-cone-model vs lem-sf-projective-cohomology-split-model: this gives a cohomology splitting and shifted-free Hom bijection. It does not construct an integral lift across reduction with a complete cone, or identify an arbitrary supplied cone, its identity-pair chain model and all restricted derived tensors.

lem-sf-prescribed-residue-cell-cone-model vs def-sf-clopen-restriction-data: this is normalized coefficient/restriction data, not a top-cell or cone theorem.

lem-sf-prescribed-residue-cell-cone-model vs lem-sf-clopen-cover-geometry: this gives clopen refinements of covers and inheritance of exact evaluation, not a derived cell or cone.

lem-sf-prescribed-residue-cell-cone-model vs lem-sf-complete-top-residue-cell-cone: the parent combines integral lift and a fully computed residue cone; the first child requires only the top basis, while the second starts with an arbitrary field-coefficient triangle and assumes no integral lift or completeness. This requested modular re-split is recorded above.

lem-sf-prescribed-residue-cell-cone-model vs lem-sf-completed-coefficient-free-resolution: this gives free quotient resolutions, complete free sources and the uniformizer triangle, but no lift into a given M and no prescribed residue-cell cone.

lem-sf-prescribed-residue-cell-cone-model vs lem-sf-clopen-coefficient-comparison: this gives coefficient restriction isomorphisms on opens; no cell or cone is constructed.

lem-sf-prescribed-residue-cell-cone-model vs lem-sf-clopen-lisse-partition: this trivializes finitely many lisse sheaves on a clopen cover; no derived top map or cone is specified.

lem-sf-prescribed-residue-cell-cone-model vs lem-fix-constructible-flat-cohomology-tor-bound: this proves a Tor bound for an existing residue object; it supplies neither a prescribed integral cell nor the shortened cone model.

lem-sf-prescribed-residue-cell-cone-model vs lem-sf-projective-top-cell-attachment: this starts with an integral triangle and a projective lower model and realizes its connecting map as a chain differential; our first node constructs the triangle, and our second computes its field residue rather than reconstructing an integral model.

lem-sf-prescribed-residue-cell-cone-model vs lem-sf-clopen-derived-compatibility: this concerns restriction of reductions and completeness along a clopen open, not construction of a top basis lift or computation of a cone.

lem-sf-prescribed-residue-cell-cone-model vs lem-weil-pbc-exact-completion-data: this constructs a completion endofunctor/unit with exactness, not a prescribed finite free cell or cone model.

lem-sf-prescribed-residue-cell-cone-model vs lem-weil-pbc-normalized-constructible-local-effectivity: this gives adic-lisse local models for normalized constructible towers on a Noetherian scheme; it neither lifts a specified top basis nor computes an arbitrary field-coefficient cell cone.

lem-sf-prescribed-residue-cell-cone-model vs lem-weil-constructible-coefficient-homology-triangulated: this proves closure of intrinsic constructibility under triangles; it makes no prescribed basis or chain-cone assertion.

lem-sf-prescribed-residue-cell-cone-model vs lem-weil-pbc-uniform-local-model-cohomology: this derives common cohomological bounds from uniform local integral models, not a top-cell lift or residue cone.

lem-sf-prescribed-residue-cell-cone-model vs lem-weil-pbc-uniform-complete-triangulated: this proves closure of a uniformly constructible complete subcategory under triangles, with stronger base hypotheses; it does not construct a prescribed cell or the explicit field cone model.

lem-sf-prescribed-residue-cell-cone-model vs lem-weil-pbc-uniform-reduction-criterion: this characterizes uniform constructible local models via reduction profiles; it neither constructs the integral cell nor computes its cone.

lem-sf-prescribed-residue-cell-cone-model vs def-weil-pbc-uniform-reduction-profile: this defines a reduction cohomology profile and asserts no lifting or cone theorem.

## Retained arguments for the new work items

The following is the entire old seven-step proof, not a compressed substitute. These are report work briefs only; both new node JSON files intentionally have no proof steps. Steps 1-3 belong to the integral child. Steps 4-6 belong to the residue child except that step 4's free integral source reduction belongs to the integral child. Step 7 is assigned clause by clause in the repair section above. Every old cited dependency is preserved here to make the independent next tasks concrete.

Original step 1:

Apply [lem-sf-complete-residue-cohomology-bounds] to $M$: quasi-compactness, quotient-tower completeness and the stated residue Tor bound give $H^{b+1}(M)=0$. Apply the $n=1$ reduction triangle of [lem-sf-completed-coefficient-free-resolution] and its long exact cohomology sequence [lem-sf-derived-homology-long-exact]. The segment $H^b(M)\to H^b(\operatorname{Res}M_1)\to H^{b+1}(M)$ shows that the canonical reduction map $H^b(M)\to H^b(M_1)$, regarded in $B_T$-modules, is an epimorphism.

Cited nodes: lem-sf-complete-residue-cohomology-bounds, lem-sf-completed-coefficient-free-resolution, lem-sf-derived-homology-long-exact.

Original step 2:

Evaluation at $T$ preserves homology by [lem-weil-pbc-proetale-weakly-contractible-evaluation-exact], under exactly the assumed epimorphism-surjectivity hypothesis; applying it to the epimorphism in step 1 makes the map on sections surjective. Lift each section $\theta_b(e_i)$ to $x_i\in H^b(M)(T)$. The shifted-free Hom bijection of [lem-sf-projective-cohomology-split-model], with $C=B_T$, gives $f:B_T^{\oplus r_b}[-b]\to M$ with generator images $x_i$. After derived scalar extension each generator maps to the reduction of $x_i$, hence $H^b(f_1)(e_i)=\theta_b(e_i)$ and $H^b(f_1)=\theta_b$. If $r_b=0$, the tuple is empty and this is the unique map from zero.

Cited nodes: lem-weil-pbc-proetale-weakly-contractible-evaluation-exact, lem-sf-projective-cohomology-split-model.

Original step 3:

Complete $f$ to a distinguished triangle $P[-b]\to M\to L\to P[-b+1]$, using TR1 of [def-weil-triangulated-category] in the derived category [def-weil-abstract-derived-category]. The source $P[-b]$ is quotient-tower complete by [lem-sf-completed-coefficient-free-resolution]. The canonical ring-sheaf identification $B_T\cong\mathcal O_{E,T}$ of [det-prop-sfb-qlbar-colimit-x-integral-limit] identifies the actual quotient maps, their transitions and the completeness comparison with those of [sk-def-pe-derived-completion]: the maps to the constant finite quotients are the inverse-limit projections. Thus both source and target are complete in the convention of [det-pe-derived-nakayama-first-reduction]. Its closure-under-cones clause makes $L$ complete, and the same identification gives quotient-tower completeness of $L$.

Cited nodes: def-weil-triangulated-category, def-weil-abstract-derived-category, lem-sf-completed-coefficient-free-resolution, det-prop-sfb-qlbar-colimit-x-integral-limit, sk-def-pe-derived-completion, det-pe-derived-nakayama-first-reduction.

Original step 4:

Derived extension along $B_T\to k_T$ is exact by [lem-pur-derived-change-of-rings], so the triangle in step 3 reduces to a distinguished triangle with third term $L_1=L\otimes^L_{B_T}k_T$. The single-term complex $P[-b]$ is K-flat [def-pc-kflat-complex]: its tensor with an acyclic complex is a finite sum of shifts of that complex. Thus its reduction is $k_T^{\oplus r_b}[-b]$, with its actual free generators. The Tor bound implies $H^q(M_1)=0$ outside $[a,b]$ by taking the test module $k_T$. Apply [lem-sf-projective-cohomology-split-model] with $C=k_T$, $N=M_1$, and the given $\theta_q$. It supplies the zero-differential model $V=\bigoplus_{q=a}^b k_T^{\oplus r_q}[-q]$. Let $\varphi:V\xrightarrow{\sim}M_1$ be any isomorphism in the derived category inducing the $\theta_q$, and let $i$ be the top summand inclusion. Then $\varphi\circ i$ and $f_1$ both send the standard generators to $\theta_b(e_j)\in H^b(M_1)(T)$, so by the injectivity of the shifted-free Hom bijection of [lem-sf-projective-cohomology-split-model] (for $C=k_T$, $q=b$, $r=r_b$) $f_1=\varphi\circ i$: under every such model $f_1$ is exactly $i$.

Cited nodes: lem-pur-derived-change-of-rings, def-pc-kflat-complex, lem-sf-projective-cohomology-split-model.

Original step 5:

Put $A=k_T^{\oplus r_b}[-b]$ and $W=\bigoplus_{q=a}^{b-1}k_T^{\oplus r_q}[-q]$. By the cone formula in [def-weil-abstract-derived-category], $C(i)^j=V^j\oplus A^{j+1}$ and $d(v,x)=(i(x),0)$. Splitting $V=W\oplus A$ gives $C(i)=W\oplus D$, where $D$ has $k_T^{\oplus r_b}$ in degrees $b-1,b$ and differential the identity. On $D$ set $h^b=\mathrm{id}:D^b\to D^{b-1}$ and $h^j=0$ otherwise. In degrees $b-1$ and $b$, respectively, $hd=\mathrm{id}$ and $dh=\mathrm{id}$; hence $dh+hd=\mathrm{id}_D$. Projection to $W$ and its inclusion are inverse up to this homotopy and induce cohomology isomorphisms. Therefore $C(i)\cong W$ in the derived category. TR3 [def-weil-triangulated-category] extends the identity on $A$ and the chosen isomorphism $M_1\cong V$ to a morphism from the reduced triangle to the cone triangle of $i$. Its third map $L_1\to C(i)$ is an isomorphism by [lem-sf-triangle-morphism-iso]. This proves the asserted cone model and $L_1\cong W$.

Cited nodes: def-weil-abstract-derived-category, def-weil-triangulated-category, lem-sf-triangle-morphism-iso.

Original step 6:

For any site object $V'\to T$, the model $W|_{V'}$ is the finite sum $\bigoplus_{q=a}^{b-1}k_{V'}^{\oplus r_q}[-q]$ with zero differential. For an acyclic complex $F$, its total tensor with this model is a finite direct sum of reindexed copies of $F$, with differentials $d_F$ or $-d_F$ according to the totalization order, hence is acyclic, so the model is K-flat by [def-pc-kflat-complex]. By [def-weil-derived-tensor] its derived tensor with any degree-zero $k_{V'}$-module sheaf $N$ is therefore the zero-differential complex $\bigoplus_{q=a}^{b-1}N^{\oplus r_q}[-q]$. This has no terms outside $[a,b-1]$. When $a<b$ this proves the required Tor amplitude on every site object, while taking $N=k_{V'}$ gives exactly the constant finite-dimensional cohomology and its stated ranks. Finite sums and shifts here are literal operations on complexes, so the computation uses no preservation-of-completeness under restriction.

Cited nodes: def-pc-kflat-complex, def-weil-derived-tensor.

Original step 7:

If $a=b$, the direct sum $W$ is empty, so step 5 gives $L_1=0$. The complete object $L$ of step 3 is zero by [det-pe-derived-nakayama-first-reduction]. The triangle then makes $f$ an isomorphism by [lem-kun-distinguished-cone-zero]. If $r_b=0$ and $a<b$, $P=0$, $D=0$, and the cone model in step 5 is simply $W$; thus the construction and amplitude argument also cover that case. If $T$ is empty, all module sheaves and all these maps are zero and the same argument applies.

Cited nodes: det-pe-derived-nakayama-first-reduction, lem-kun-distinguished-cone-zero.

## Validation

Required server preflight and delivery are run after writing this report. The final command output is authoritative for the delivered commit; no local DAG/preflight tool or compiler was run.
