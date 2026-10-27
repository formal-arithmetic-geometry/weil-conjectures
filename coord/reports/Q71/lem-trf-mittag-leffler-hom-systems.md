# Q71 repair: lem-trf-mittag-leffler-hom-systems

## Files written

- dag/nodes/sec-trace-formula/lem-trf-mittag-leffler-hom-systems.json: statement unchanged; proof replaced by three assembly steps, using two new nodes, followed by both Hom image inclusions. Proof text totals 1,508 characters, below 3,000.
- dag/nodes/sec-trace-formula/lem-trf-universal-tensor-kernel-witness.json: statement, status unsplit; no Mathlib match after LeanFinder (two phrasings), LeanSearch, Loogle and grep.
- dag/nodes/sec-trace-formula/lem-trf-tensor-witness-eventual-factorization.json: statement, status unsplit; no Mathlib match after LeanFinder (two phrasings), LeanSearch, Loogle and grep.
- citations.json: verbatim statement excerpts for the two citations in the parent proof.
- report.md: this report, including the entire returned argument and its allocation to the new tasks.

Only the sandbox was written. No Lean files, compilers, Lake or builds were used. The server checks and delivery use the authorized launcher scripts.

## Attachments

None. Searched lean/WeilConjectures/ by the exact blueprint tag, hom_images_stabilize, MittagLeffler, and tensor-kernel/witness concepts. No declaration there proves this item. The existing local declaration Module.hom_images_stabilize_of_isMittagLeffler at lean/Sheaf/RingTheory/MittagLefflerHomSystems.lean:69 ends with sorry. Its signature, hypotheses, docstring and all six proof paragraphs agree with the returned node, but it is not a finished attachment. The existing lean and lean_audit fields are retained unchanged. No project declaration states either new witness interface exactly.

## WANTED

None. All mathematical sources used here are present in literature/stacks-project/algebra.tex.

## What was wrong and what was repaired

The human return asks for a genuine redistribution of the 4,398-character proof, at least two new statement-only nodes with comparable workloads, and an assembly below 3,000 characters. No mathematical change to the parent statement was requested or needed. The sandbox initially contained only .brief2 through .brief5, with no retained node, report or search log. I recovered the exact six-step reviewed split and its citations/search records from the current read-only repository into returned-item.json and the item copy. The current item matches the proof described by the return and its named Lean module. This is a new substantive split of that proof, not a re-push.

The first task constructs one universal tensor-kernel witness for an arbitrary map from a finite presentation into a Mittag-Leffler module. It contains the finite-matrix set, the product of all kernel pairs, the product-tensor comparison, vanishing via injectivity, and the isomorphism transport needed to evaluate the witness in every finitely presented test module. The second task starts with any such witness in a supplied directed system, kills it at one stage, obtains all finite tensor-kernel inclusions, presents transition cokernels by an augmented finite matrix, and applies the existing tensor-kernel factorization lemma. Neither new statement mentions Hom-image stabilization; neither assumes the other new node. The two arguments have comparable size: roughly two old proof steps plus transport, versus the remaining three old proof steps. The elementary Hom-composition argument stays in the parent, with its original text except for the changed step number.

An initially tempting extraction of uniform domination would duplicate lem-trf-mittag-leffler-eventual-domination. That node already depends on the present item, so citing it here would also be circular. The delivered interfaces instead separate construction of a witness from use of an arbitrary supplied witness; neither is a specialization of the eventual-domination statement.

## Extracted argument for lem-trf-universal-tensor-kernel-witness

This is guidance for the future worker, not proof steps in the new unsplit node. Its source is Stacks Tag 059M, proposition-ML-tensor, proof of (2) implies (1), through the first product square. I also read Tag 059K, proposition-fp-tensor, proof of (1) implies (2). The existing lem-trf-finite-presentation-tensor-products supplies precisely that bijectivity, for arbitrary set-indexed families.

For f:P→M take B = the disjoint union over finite a,b of matrices R^a→R^b, and Q_t = R^b/im(t). Each Q_t is finitely presented, and every finite presentation is isomorphic to some Q_t, by def-sc-finitely-presented-module. Define A as the set of pairs (t,x) with x in ker(f tensor id_Q_t), put Q_(t,x)=Q_t, and T=∏_A Q_(t,x). These are sets, including all zero-size matrices and the zero presentation. By lem-trf-finite-presentation-tensor-products, the family of coordinates x comes from z in P tensor T. The image of z under f tensor id_T has zero image in every coordinate of the comparison for M. On p tensor (q_alpha), both sides of the comparison square have coordinate f(p) tensor q_alpha; pure tensors generate, as explicitly stated in def-weil-pbc-module-tensor-product. The Mittag-Leffler definition def-trf-mittag-leffler-module makes the comparison for M injective. Hence (f tensor id_T)(z)=0.

For any finitely presented Q and x in ker(f tensor id_Q), choose an isomorphism e:Q→Q_t from its finite presentation. Let x_t=(id_P tensor e)(x). Commutation with f tensor id makes x_t a valid coordinate alpha=(t,x_t) of A. Set q=e^(-1) composed with the alpha-coordinate projection T→Q_t. Then (id_P tensor q)(z)=(id_P tensor e^(-1))(x_t)=x. The two tensor maps induced by e and e^(-1) are inverse: their composites equal the identity on p tensor y and hence on every tensor. This is the explicit isomorphism transfer from returned step 3, now incorporated in the first interface. No choice of a product over a proper class, flatness of M, or finiteness of the family is used.

## Extracted argument for lem-trf-tensor-witness-eventual-factorization

This is guidance for the future worker, not proof steps in the new unsplit node. I read Stacks Tag 059M's product-kernel death argument, Tag 059L, lemma-kernel-tensored-fp, including the directed-colimit proof of death at one stage, and Tag 059E, proposition-ML-characterization, proof of (2) implies (3). For the last inference I read Tags 059C, lemma-domination-fp, and 059D, lemma-domination, and the statement of the existing lem-trf-tensor-kernel-factorization.

Use lem-weil-pbc-tensor-commutes-with-colimits to identify M tensor T with the colimit of M_s tensor T, with the specified maps u_s tensor id_T. Apply lem-weil-pbc-filtered-colimit-modules-elementwise to the supplied z, whose colimit image is zero, and get j≥i with (f_ij tensor id_T)(z)=0. For every finitely presented Q and x in ker(u_i tensor id_Q), choose the evaluation q:T→Q from the hypothesis. The equation
(f_ij tensor id_Q)(x)=(id_M_j tensor q)((f_ij tensor id_T)(z))=0
is checked on m tensor t, where both composites give f_ij(m) tensor q(t), and then by generation of tensors. Thus ker(u_i tensor id_Q) is contained in ker(f_ij tensor id_Q) for every such Q, with a single j independent of Q or x. For k≥j, the cocone equation u_i=u_k composed with f_ik shows ker(f_ik tensor id_Q) is contained in ker(u_i tensor id_Q), hence in ker(f_ij tensor id_Q).

It remains to verify the finite-presentation hypothesis needed for factorization, rather than assume it. Choose finitely many generators p_1,...,p_c of M_i and a finite presentation M_k=R^b/im(D), D:R^a→R^b; def-sc-finitely-presented-module gives both. Choose lifts v_r of f_ik(p_r). The quotient M_k/f_ik(M_i) is R^b modulo im(D)+sum Rv_r, because the image in M_k of an element of R^b is a linear combination of the f_ik(p_r) exactly when that element lies in the displayed submodule. It is therefore the cokernel of (D v_1 ... v_c):R^(a+c)→R^b, so is finitely presented. Now lem-trf-tensor-kernel-factorization, with U=M_i, V=M_k, W=M_j, f=f_ik, g=f_ij, applies: its statement tests only finitely presented Q and assumes exactly the finite presentation of this quotient. It gives h_k:M_k→M_j with f_ij=h_k composed with f_ik for every k≥j. The index j was fixed before k, and no Mittag-Leffler hypothesis on the system or on M is used by this task once its witness is supplied.

## Review by Q71

I checked the item against Stacks Tags 059M and 059E, retaining the arbitrary small directed index set and arbitrary target N. For the first new node I read 059M's set of representatives, all kernel pairs, first comparison square and kernel element, and 059K's product-tensor bijection. Its statement demands the extra evaluation maps explicitly; the construction q=e^(-1) composed with a product projection verifies exactly that demand. For the second new node I read the supplied-system version of the element-death argument in 059L and the finite-cokernel and domination-to-factorization argument in 059E (2) to (3), backed by 059C and 059D. The witness is an explicit hypothesis, not a synonym for being Mittag-Leffler or a restatement of Hom stabilization.

In assembly step 1, the cited universal-witness statement introduces P,M,f and gives exactly T,z, vanishing and every evaluation q used by the step. P=M_i is finitely presented by the unchanged parent hypothesis; M is Mittag-Leffler by that same hypothesis. In step 2, the eventual-factorization statement applies to precisely the parent's small nonempty directed system and its supplied colimit cocone. Its additional T,z hypotheses are the exact output of step 1. Its conclusion is the displayed factorization f_ij=h_k composed with f_ik for all k≥j, which is exactly what step 3 needs. Both quoted passages in citations.json are literal substrings of those statements. Step 3 is elementary: a composed with f_ij=(a composed with h_k) composed with f_ik gives one image inclusion, and f_ik=f_jk composed with f_ij gives the other. No external lemma, exactness assertion, or finiteness of N is hidden in that step.

For the future extracted arguments I opened every reused dependency statement. def-sc-finitely-presented-module gives finite free presentations; lem-trf-finite-presentation-tensor-products is bijective for every set, with no flatness hypothesis; def-trf-mittag-leffler-module gives injectivity for every set of modules; def-weil-pbc-module-tensor-product states generation by pure tensors and functoriality. lem-weil-pbc-tensor-commutes-with-colimits applies to any small category with the supplied colimit and arbitrary tensor factor; lem-weil-pbc-filtered-colimit-modules-elementwise applies to small filtered diagrams and states the needed eventual-zero criterion. A nonempty directed poset is filtered, as def-weil-pbc-category-colimit states. lem-trf-tensor-kernel-factorization tests only finitely presented modules and requires finite presentation only of V/f(U), verified by the augmented matrix above. I did not infer a theorem merely from a definition or borrow a construction from an uncited node's proof.

I tested zero rings, P=0, f=0, injective f with nontrivial tensor kernels, zero-size finite presentations, a singleton index poset, systems with all stages zero, and N=0. For f=0 the product element still exists by finite presentation and M's injective comparison is only used to certify the zero image; for P=0 take the zero witness. Tensor kernels can be nonzero even when f is injective, and both statements quantify over tensor kernels rather than ordinary ker(f). If every test kernel is zero, the zero witness with T=0 is admissible; factorization then follows from the same cited lemma with the finite cokernel, not from ordinary injectivity. In a singleton system the colimit maps are isomorphisms, so the zero witness is valid and h_i=id satisfies the conclusion. No countability, Noetherian, flatness, finite generation of T, or finite generation of N has been added. Products of modules and all finite matrices are set-indexed. Empty generator lists cause no exception to the augmented-matrix calculation.

I checked delivery-errors B–E against the actual node statements and sources. Both new nodes introduce all objects and cite definitions for finite presentation, tensor products, colimits and the module Mittag-Leffler condition where used; their proof/proof_deps arrays are empty and proof_origin is null. Sources include verified Stacks tags and labels, not movable section numbers. Searches were really run through msearch.py, their hits were read, their exact query text and logged records were copied to mathlib_searches, and two semantic phrasings were used for each new statement. The apparent tensorKerEquiv hit assumes a flat tensor factor and describes commuting tensor with a kernel, not a universal witness; directLimitLeft and of.zero_exact are components already covered by existing DAG leaves, not the eventual-factorization theorem. No new node is a one-line Mathlib specialization. Existing related DAG nodes are compared below. I checked the new dependency edges point only to existing definition nodes, so neither new node can lead back to the parent. No SGA source, derived-category replacement, or route change was introduced. The parent has no proof step over 2,000 characters.

## Unfinished work

The two extracted nodes are intentionally statement-only tasks for separate future workers, as the human return requires. There is no unfinished assembly argument and no statement dispute. The inherited chapter and unit remain fixed; the item is not the unit's key node, so no unit realization fields are edited.

## Search and duplicate audit

Before creating the nodes I searched the whole DAG by 059M/059E/059C/059D, Mittag-Leffler, tensor-kernel/witness and factorization concepts, then inspected all related module statements. Blueprint searches included Mittag, tensor kernel, domination, tensor kernel witness and transition factorization. The only blueprint Mittag-Leffler result concerns inverse systems of finite abelian groups, not either new statement. I inspected the project source by the exact item tag and conceptual searches. The logged msearch results for each new node include LeanFinder twice, LeanSearch, Loogle and grep; all five services/queries completed successfully, so none is represented as unavailable. The parent's earlier search records were retained, since its statement and search question have not changed.

## Not duplicates

lem-trf-universal-tensor-kernel-witness vs lem-trf-finite-presentation-tensor-products: the existing node gives bijectivity of a product-tensor comparison for one finite presentation, without constructing a simultaneous kernel witness or giving any finite-stage factorization.

lem-trf-universal-tensor-kernel-witness vs lem-trf-mittag-leffler-hom-systems: the existing item concludes eventual Hom-image equality, and gives neither a universal witness for a single arbitrary map nor a factorization theorem with an arbitrary supplied witness.

lem-trf-universal-tensor-kernel-witness vs lem-trf-countable-projective-faithfully-flat-descent: the existing node descends projectivity along faithfully flat ring maps and requires countability; it does not construct or consume a universal tensor-kernel witness.

lem-trf-universal-tensor-kernel-witness vs lem-trf-coherent-product-flat: the existing statement is Let $R$ be a commutative coherent ring, meaning that every finitely generated ideal of $R$ is finitely presented as an $R$-module [def-sc-finitely-presented-module]. For any set $A$ and family $(Q_a)_{a\in A}$ of flat $R$-modules [def-weil-pbc-flat-ring-map], the product $\prod_{a\in A}Q_a$, consisting of all families with componentwise module operations, is flat over $R$. This differs from the new statement, which constructs one tensor-kernel witness for an arbitrary map from a finite presentation into a Mittag-Leffler module.

lem-trf-universal-tensor-kernel-witness vs lem-trf-flat-mittag-leffler-criterion: the existing node characterizes flat Mittag-Leffler modules by least tensor-support submodules; neither new statement is such a characterization.

lem-trf-universal-tensor-kernel-witness vs lem-trf-ml-countable-colimit: the existing node extracts a countable subsystem with the same colimit, assumes a countably generated Mittag-Leffler module, and gives neither witness interface.

lem-trf-universal-tensor-kernel-witness vs lem-trf-flat-ml-dual-criterion: the existing node assumes a flat colimit of finite free modules and stabilization of dual images and concludes the module Mittag-Leffler property; neither new statement assumes those hypotheses or concludes that criterion.

lem-trf-universal-tensor-kernel-witness vs lem-trf-product-noetherian-flat-mittag-leffler: the existing statement is Let $R$ be a Noetherian commutative ring [def-weil-pbc-noetherian-ring] and let $A$ be any set. The product module $R^A=\prod_{a\in A}R$, with componentwise $R$-module operations, is flat over $R$ [def-weil-pbc-flat-ring-map] and is a Mittag-Leffler $R$-module [def-trf-mittag-leffler-module]. This differs from the new statement, which constructs one tensor-kernel witness for an arbitrary map from a finite presentation into a Mittag-Leffler module.

lem-trf-universal-tensor-kernel-witness vs def-trf-mittag-leffler-module: the existing node defines injectivity of the tensor-to-product comparison; it states no construction or consequence for maps or directed systems.

lem-trf-universal-tensor-kernel-witness vs lem-trf-local-flat-pure-complete-projective: the existing node proves projectivity using local complete-ring and universal-injectivity hypotheses, not either of these witness interfaces.

lem-trf-universal-tensor-kernel-witness vs lem-trf-mittag-leffler-eventual-domination: the existing node is an equivalence between the module property and eventual domination for a whole presentation; it neither provides an actual single witness T,z nor accepts such a witness as input. Its proof depends on the item, so citing it here would be circular.

lem-trf-universal-tensor-kernel-witness vs lem-trf-flat-ml-minimal-support: the existing node constructs a least supporting submodule for one tensor with a flat Mittag-Leffler module, rather than a simultaneous witness for every finite-presentation kernel or a finite-stage factorization.

lem-trf-universal-tensor-kernel-witness vs lem-trf-countable-flat-mittag-leffler-projective: the existing node proves projectivity of a countably generated flat Mittag-Leffler module, with different hypotheses and conclusion.

lem-trf-universal-tensor-kernel-witness vs lem-trf-pure-submodule-mittag-leffler: the existing node concerns preservation of the module property by universally exact submodules, not a single universal kernel element or supplied-witness transition factorizations.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-finite-presentation-tensor-products: the existing node gives bijectivity of a product-tensor comparison for one finite presentation, without constructing a simultaneous kernel witness or giving any finite-stage factorization.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-mittag-leffler-hom-systems: the existing item concludes eventual Hom-image equality, and gives neither a universal witness for a single arbitrary map nor a factorization theorem with an arbitrary supplied witness.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-countable-projective-faithfully-flat-descent: the existing node descends projectivity along faithfully flat ring maps and requires countability; it does not construct or consume a universal tensor-kernel witness.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-mittag-leffler-faithfully-flat-descent: the existing node descends the Mittag-Leffler property under faithfully flat base extension, with neither witness construction nor transition factorization.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-flat-mittag-leffler-criterion: the existing node characterizes flat Mittag-Leffler modules by least tensor-support submodules; neither new statement is such a characterization.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-ml-countable-colimit: the existing node extracts a countable subsystem with the same colimit, assumes a countably generated Mittag-Leffler module, and gives neither witness interface.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-universally-exact-fp-split: the existing node splits one universally exact short exact sequence with finitely presented quotient; it is an ingredient behind tensor-kernel factorization, not either new witness statement.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-flat-ml-dual-criterion: the existing node assumes a flat colimit of finite free modules and stabilization of dual images and concludes the module Mittag-Leffler property; neither new statement assumes those hypotheses or concludes that criterion.

lem-trf-tensor-witness-eventual-factorization vs def-trf-mittag-leffler-module: the existing node defines injectivity of the tensor-to-product comparison; it states no construction or consequence for maps or directed systems.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-local-flat-pure-complete-projective: the existing node proves projectivity using local complete-ring and universal-injectivity hypotheses, not either of these witness interfaces.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-mittag-leffler-eventual-domination: the existing node is an equivalence between the module property and eventual domination for a whole presentation; it neither provides an actual single witness T,z nor accepts such a witness as input. Its proof depends on the item, so citing it here would be circular.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-flat-ml-minimal-support: the existing node constructs a least supporting submodule for one tensor with a flat Mittag-Leffler module, rather than a simultaneous witness for every finite-presentation kernel or a finite-stage factorization.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-tensor-kernel-factorization: the existing node factors a given pair f,g after all finite tensor-kernel inclusions and finite presentation of one cokernel have been verified; it neither constructs the universal witness nor derives a uniform index and those hypotheses from its death.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-countable-flat-mittag-leffler-projective: the existing node proves projectivity of a countably generated flat Mittag-Leffler module, with different hypotheses and conclusion.

lem-trf-tensor-witness-eventual-factorization vs lem-trf-pure-submodule-mittag-leffler: the existing node concerns preservation of the module property by universally exact submodules, not a single universal kernel element or supplied-witness transition factorizations.

## Exact returned proof retained and allocation

No original argument has been dropped. Old steps 1–2 and the final isomorphism-transfer paragraph of old step 3 belong to the universal-witness task. The death-at-one-stage and tensor-coordinate paragraphs of old step 3 and all of old steps 4–5 belong to the eventual-factorization task. Old step 6 is the parent assembly step 3. The complete returned texts, uses and sources are retained below verbatim for future workers.

### Returned step 1

Fix $i\in I$ and write $u_s:M_s\to M$ for the given colimit maps. Form the set $B=\coprod_{a,b\ge0}\operatorname{Mat}_{b\times a}(R)$ and, for $t\in\operatorname{Mat}_{b\times a}(R)$, put $Q_t=R^b/\operatorname{im}(t)$. Every $Q_t$ is finitely presented and every finitely presented $R$-module is isomorphic to some $Q_t$, directly from its finite presentation [def-sc-finitely-presented-module]. Consequently $A=\{(t,z):t\in B,\ z\in\ker(u_i\otimes\mathrm{id}_{Q_t})\}$ is a set. For $\alpha=(t,z)$ put $Q_\alpha=Q_t$ and $z_\alpha=z$, and let $T=\prod_{\alpha\in A}Q_\alpha$, the module of all families. This explicitly supplies the set of test modules used by the source; no product over a proper class is taken.

Cited nodes: def-sc-finitely-presented-module.

Source: literature/stacks-project/algebra.tex, Tag 059M, proposition-ML-tensor, proof of (2) implies (1), choice of the set B and pairs (Q,x).

### Returned step 2

Apply [lem-trf-finite-presentation-tensor-products] to $M_i$ and the family $(Q_\alpha)$ to obtain $z\in M_i\otimes_RT$ whose image under the canonical comparison is $(z_\alpha)_\alpha$. Put $y=(u_i\otimes\mathrm{id}_T)(z)$. Its image under $\theta_{M,(Q_\alpha)}$ is zero: the $\alpha$-coordinate is $(u_i\otimes\mathrm{id}_{Q_\alpha})(z_\alpha)=0$. The comparison square commutes because on a pure tensor $m\otimes(q_\alpha)_\alpha$ both composites have $\alpha$-coordinate $u_i(m)\otimes q_\alpha$; pure tensors generate [def-weil-pbc-module-tensor-product]. The tensor-product Mittag-Leffler hypothesis [def-trf-mittag-leffler-module] makes $\theta_{M,(Q_\alpha)}$ injective. Thus $y=0$.

Cited nodes: lem-trf-finite-presentation-tensor-products, def-weil-pbc-module-tensor-product, def-trf-mittag-leffler-module.

Source: literature/stacks-project/algebra.tex, Tag 059M, proposition-ML-tensor, proof of (2) implies (1), the first commutative square and the kernel element x.

### Returned step 3

By [lem-weil-pbc-tensor-commutes-with-colimits], the maps $u_s\otimes\mathrm{id}_T$ exhibit $M\otimes_RT$ as the colimit of $M_s\otimes_RT$. Since the image of $z$ is zero, [lem-weil-pbc-filtered-colimit-modules-elementwise] gives $j\ge i$ with $(f_{ij}\otimes\mathrm{id}_T)(z)=0$. Project to each $Q_\alpha$. The resulting equality is $(f_{ij}\otimes\mathrm{id}_{Q_\alpha})(z_\alpha)=0$, by the same pure-tensor calculation as in step 2 [def-weil-pbc-module-tensor-product]. In particular, for every $t\in B$ and every $v\in\ker(u_i\otimes\mathrm{id}_{Q_t})$, the coordinate $\alpha=(t,v)$ gives $(f_{ij}\otimes\mathrm{id}_{Q_t})(v)=0$. For any finitely presented $Q$, choose an isomorphism $e:Q\to Q_t$. The maps $1\otimes e$ and $1\otimes e^{-1}$ are inverse and intertwine all these maps: on $m\otimes q$ the commutation identity sends it to $f(m)\otimes e(q)$. Applying this identity and then the inverse transfers the kernel inclusion to $Q$. Therefore, for every finitely presented $Q$, $\ker(u_i\otimes\mathrm{id}_Q)\subseteq\ker(f_{ij}\otimes\mathrm{id}_Q)$. The single index $j$ works for all these $Q$.

Cited nodes: lem-weil-pbc-tensor-commutes-with-colimits, lem-weil-pbc-filtered-colimit-modules-elementwise, def-weil-pbc-module-tensor-product.

Source: literature/stacks-project/algebra.tex, Tag 059M, proposition-ML-tensor, proof of (2) implies (1), killing the universal kernel element; use the given finitely presented directed system directly, as in Tag 059L, lemma-kernel-tensored-fp.

### Returned step 4

Fix $k\ge j$. Since $u_i=u_k\circ f_{ik}$, functoriality of tensor [def-weil-pbc-module-tensor-product] and step 3 give $\ker(f_{ik}\otimes\mathrm{id}_Q)\subseteq\ker(f_{ij}\otimes\mathrm{id}_Q)$ for every finitely presented $Q$. The cokernel of $f_{ik}$ is finitely presented, as the following finite presentation shows. Choose generators $p_1,\ldots,p_c$ of $M_i$ and a presentation $M_k=R^b/\operatorname{im}(D)$ with $D:R^a\to R^b$, with all integers finite [def-sc-finitely-presented-module]. Choose lifts $v_r\in R^b$ of $f_{ik}(p_r)$. Then $M_k/f_{ik}(M_i)$ is the quotient of $R^b$ by $\operatorname{im}(D)+\sum_{r=1}^cRv_r$, hence is the cokernel of the finite matrix $(D\ v_1\ \cdots\ v_c):R^{a+c}\to R^b$. Indeed an element of $R^b$ maps to zero in this quotient exactly when its image in $M_k$ is a linear combination of the $f_{ik}(p_r)$, which is exactly membership in that displayed submodule.

Cited nodes: def-weil-pbc-module-tensor-product, def-sc-finitely-presented-module.

Source: literature/stacks-project/algebra.tex, Tag 059E, proposition-ML-characterization, proof of (2) implies (3), transitivity of domination and finite presentation of the transition cokernel.

### Returned step 5

Apply [lem-trf-tensor-kernel-factorization] with $U=M_i$, $V=M_k$, $W=M_j$, $f=f_{ik}$ and $g=f_{ij}$. Both required hypotheses were verified in step 4: the cokernel of $f_{ik}$ is finitely presented and every finitely presented tensor test gives the stated kernel inclusion. Obtain an $R$-linear $h_k:M_k\to M_j$ with $f_{ij}=h_k\circ f_{ik}$. This applies to every $k\ge j$, with the same $j$ chosen in step 3.

Cited nodes: lem-trf-tensor-kernel-factorization.

Source: literature/stacks-project/algebra.tex, Tag 059E, proposition-ML-characterization, proof of (2) implies (3), application of Tag 059D.

### Returned step 6

Let $N$ be any $R$-module and $k\ge j$. An element of the image of $\operatorname{Hom}_R(M_j,N)\to\operatorname{Hom}_R(M_i,N)$ has the form $a\circ f_{ij}$ for $a:M_j\to N$. Step 5 rewrites it as $(a\circ h_k)\circ f_{ik}$, so it is in the image from $M_k$. Conversely, if $b:M_k\to N$, then $b\circ f_{ik}=(b\circ f_{jk})\circ f_{ij}$ by the directed-system identity $f_{ik}=f_{jk}\circ f_{ij}$. Thus the two images are equal for every $k\ge j$. This proves the required assertion for all $i$ and $N$, without countability or any finiteness condition on $N$.

Cited nodes: .

Source: literature/stacks-project/algebra.tex, Tag 059E, proposition-ML-characterization, (3) implies (4); both image inclusions written explicitly.

## Validation

The server-only review_split check passed before this report was written. The required deliver.py --no-push and final delivery are run after the report is complete; their outputs are recorded below when available.


## Review by Q71: returned landing and current-DAG rebase (2026-10-22)

The new return is the landing refusal, “completed in this project's DAG but not in the live DAG the queue reads (side completion never promoted; L promotes it)”. I continued the retained sandbox, including its two nodes, complete report, returned-item.json, citations.json and searches.jsonl. The first action after reading the brief was the required deliver.py --no-push; it fetched current origin/sheaf-dag, constructed the overlay there, and exited successfully with OK (not pushed) at a48c0c3dda9. This authorized delivery command performs the rebase without any worker git command in the read-only repository.

I compared every field of returned-item.json with the current repository item: they are identical. The retained assembly differs from that current item only in proof, proof_deps and split_report. Thus the historical six-step split is still the base, rather than a reason to discard the human-requested redistribution. The released stage-1 repair note still requires two comparable statement-only tasks and an assembly below 3000 characters. Neither new id exists in the current repository. Current statement dependencies, source, blueprint ancestry, unit, Lean record and maintainer review are retained; the delivery tool preserves current maintainer fields from origin.

I reopened both statements actually cited by the assembly: lem-trf-universal-tensor-kernel-witness gives the exact T,z, zero image and evaluation maps needed in step 1, and lem-trf-tensor-witness-eventual-factorization gives the uniform j and h_k needed in step 2. Neither cited statement has changed since the retained repair; citations.json still copies its conclusion verbatim. Step 3 explicitly proves each Hom-image inclusion by composing h_k or f_jk. I also reopened the current statements of def-sc-finitely-presented-module, def-trf-mittag-leffler-module, def-weil-pbc-category-colimit, def-weil-pbc-module-tensor-product, lem-trf-finite-presentation-tensor-products, lem-weil-pbc-tensor-commutes-with-colimits, lem-weil-pbc-filtered-colimit-modules-elementwise and lem-trf-tensor-kernel-factorization. They still supply precisely the finite presentation, set-indexed comparison, tensor functoriality, small filtered colimit, eventual vanishing and finite-cokernel factorization described in the retained extracted arguments. No changed citation requires a mathematical adjustment.

For this reading I reopened algebra.tex at labels proposition-ML-tensor (059M), proposition-fp-tensor (059K), lemma-kernel-tensored-fp (059L), proposition-ML-characterization (059E), lemma-domination-fp (059C), lemma-domination (059D), and lemma-countgen-projective (059X), and checked their tag mappings. The two extracted arguments follow the same product-kernel, eventual death, finite-cokernel and factorization route. The current lem-trf-mittag-leffler-eventual-domination still depends on this parent and remains unusable as a replacement citation. The searches logged at 06:47–06:49 UTC were read and retained, rather than rerun under an unchanged search question. Their finite-presentation tensor, flat tensor-kernel and individual colimit-zero hits do not state either new interface.

The current project-source search still yields no attachment. In lean/Sheaf/RingTheory/MittagLefflerHomSystems.lean the exact parent theorem still ends in sorry; the WeilConjectures Mittag-Leffler hits concern inverse systems or other conclusions. I checked the chapter and unit records without changing their route. The zero module, zero ring, zero tensor kernels and singleton directed system still satisfy the statements for the reasons in the original Review by Q71. All parent steps are below 2000 characters. This repair adds the current-base comparison and explicit response to the landing return while retaining the substantive two-node redistribution. Final dry run and direct push follow this report update.


### Continuation after the provider interruption (2026-10-22)

The interrupted initial dry run completed: .stage1-ready.json records head 9dfdce335a2, and I verified every recorded input SHA-256 against the retained files before repeating any delivery command. No Q71 delivery process remained active. I compared returned-item.json and the current read-only DAG again: no field changed. The sandbox parent still changes only proof, proof_deps and split_report; both extracted ids remain absent from the current DAG. Thus the substantive repair remains the two new statement-only tasks and their three-step assembly, rather than a rebase-only replacement of the old six-step proof.

I reopened the eight current definition and supporting-lemma statements named in the preceding review, both new interface statements and citations.json, the current chapter/unit records, and algebra.tex at proposition-fp-tensor, proposition-ML-tensor, lemma-kernel-tensored-fp, proposition-ML-characterization, lemma-domination-fp and lemma-domination. In particular, arbitrary products in the first task and small filtered colimits in the second have exactly the required hypotheses; the factorization input is finite presentation of the transition cokernel, not flatness. The two assembly citations remain verbatim, and the assembly step lengths are 480, 469 and 559 characters. The project-source search still supplies no finished attachment, and the recorded Sheaf theorem ends in sorry. The saved Mathlib search results were read and retained because neither new statement nor its search question changed. The zero-module and singleton-system checks in the signed review still apply. No source, route, statement, or dependency correction is required by this current-base comparison. I will run the final dry run after this report update and push through the prescribed delivery tool.


## Review by Q71: current-DAG repair continuation (2026-10-23)

I continued the retained delivery rather than reconstructing its mathematics. The first prescribed dry run exited successfully with `OK (not pushed)` at `819e030c19d`, rebasing the retained overlay onto the delivery tool's current `origin/sheaf-dag`. The return being repaired is the landing refusal recorded at branch head `6024fef2c1a`: side completion had not been promoted to the live queue's DAG. The worker cannot perform that maintainer promotion. This delivery instead supplies the requested current-base repair, retaining the substantive two-task redistribution required by the released stage-1 repair note. It does not restore or merely re-push the old six-step proof.

I compared `returned-item.json` with the current shared item: their bytes have the same SHA-256, `be3e0d65f7f9446a7941f3575463e1df6b4a6224e952c11467691fa9e3bbd114`. The current item still carries the old six-step argument; the sandbox changes only its proof, proof_deps and split_report. Neither extracted id exists in the current shared DAG. I re-read the released repair note, current chapter and unit, and the full statements of both assembly citations and all eight supporting interfaces named in the preceding review. No statement dependency, source hypothesis or conclusion needed by the retained split has changed. The current eventual-domination node still cites this parent, so replacing either task with it would introduce a cycle.

For step 1, the universal-witness node expressly requires the finite presentation of P and the tensor-product Mittag-Leffler condition on M, and supplies T, z, vanishing and every evaluation map; these are exactly the hypotheses and output used with P=M_i and f=u_i. For step 2, the supplied-witness node requires a small nonempty directed poset, a colimit cocone and finitely presented stages, together with precisely that witness. Its conclusion gives the uniform index j and factorizations through every k at least j. Step 3 proves both Hom-image inclusions by composition, with no extra theorem. Both entries of citations.json are still literal substrings of the cited statements, and they account for every assembly citation.

I reopened Stacks algebra.tex at 059C (lemma-domination-fp), 059D (lemma-domination), 059E (proposition-ML-characterization), 059K (proposition-fp-tensor), 059L (lemma-kernel-tensored-fp) and 059M (proposition-ML-tensor). Arbitrary set-indexed products in the first task, eventual zero in the given small filtered colimit in the second, and the augmented finite matrix for the transition cokernel remain justified by the retained full arguments. In particular, the factorization theorem needs the cokernel finitely presented; it does not require a flat tensor factor. Zero modules, the zero ring and singleton systems still pass the explicit checks in the original signed review. The new statements introduce all objects, use single TeX backslashes, have verified tag/label sources, and carry empty proof/proof_deps arrays and null proof_origin. Neither is a clause of the parent's Hom-image conclusion.

I read all 14 retained search-log records and retained the exact five queries on each new node because the statements and search questions are unchanged. The recorded tensor-kernel equivalence concerns flatness, while direct-limit element-zero and tensor-colimit hits provide only ingredients; none states either witness interface. Whole-blueprint searches again found no tensor-kernel node and only the finite-abelian-group inverse-system Mittag-Leffler result. Current project-source searches by the exact tag and by Hom/Mittag-Leffler/witness concepts still supply no attachment: the recorded Sheaf theorem ends in sorry. The earlier duplicate comparisons and extracted arguments remain part of this report. No compiler, Lake, Lean edit or worker git command was used. Assembly lengths remain 480, 469 and 559 characters, totaling 1508. After this dated report and split_report update, I will run the final dry run to completion and deliver through the prescribed tool.
