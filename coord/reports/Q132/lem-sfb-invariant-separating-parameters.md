# Worker report — Q132 repair

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-invariant-separating-parameters.json`: unchanged statement and statement dependencies; three short assembly steps replacing nine steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-semilinear-fixed-field-finite-generation.json`: statement, unsplit; no whole-statement Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-geometric-subfield-scalar-restriction.json`: statement, unsplit; no whole-statement Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-separating-basis-algebraic-diamond.json`: statement, unsplit; no whole-statement Mathlib match.
- `citations.json`: one verbatim statement quotation for each of the three parent steps.
- `report.md`: this signed repair report and the complete retained argument below. `searches.jsonl` is the genuine search-command log; `original-node.json` is an untouched baseline retained only in the sandbox.

## Attachments

None. The item has no matching declaration under `lean/WeilConjectures/`; `lean/Sheaf/FieldTheory/InvariantSeparatingParameters.lean:80` states `Algebra.exists_invariant_separating_parameters` with a `sorry` at the end. Its signature matches the unchanged node: finite generation, geometric integrality, finite compatible possibly nonfaithful actions, and a Fin d invariant independent family giving a finite separable extension. The newly extracted combined statements were also searched by concept in the project sources; the constituent scalar-restriction and separability declarations are existing DAG material, not attachments for these new combined statements.

## WANTED

WANTED: `literature/de-jong-families-curves-alterations-1997.pdf`, Lemma 5.2 proof, printed p.613, for lem-sfb-invariant-separating-parameters and its three extractions. It is absent locally. I read the publisher PDF at https://aif.centre-mersenne.org/item/10.5802/aif.1575.pdf, PDF page 15 (zero-based), and checked the invariant parameter choice in the opening paragraph. The local Stacks sources below provide the algebraic inputs; the fuller algebraic proof remains explicitly agent-authored. No literature was downloaded or repository files changed.

## What was wrong and what was repaired

The return asks for work to be distributed, preserving every argument, with at least two comparable statement-only nodes and at most 3000 characters of assembly in the parent. The sandbox initially contained no node or report, only dispatcher metadata. I copied the current shared node, including its complete existing proof, source, search records and Lean/review metadata, as the repair baseline. No earlier search log was present. The parent statement, its five statement dependencies, and all Lean bindings remain byte-for-byte equal as JSON values.

The nine original steps total 4998 characters. Their ownership is now 1–3 -> semilinear-fixed-field-finite-generation (1654 characters), 4–6 -> geometric-subfield-scalar-restriction (1488), and 7–9 -> separating-basis-algebraic-diamond (1856). These are three genuine arguments, not three restatements of the invariant-parameter conclusion: the first establishes finite generation without any geometric hypothesis; the second is a group-free scalar-restriction/subfield comparison, without finite generation; the third is a group-free separating-basis construction and transfer, assuming the structural properties established by the other two. Each has empty proof and proof_deps and status unsplit, so three workers can start independently. All original proof text and citation/source information is retained verbatim below for those workers; no argument was discarded or blurred. The parent assembly is 1245 characters, with no step longer than 2000 characters. No statement dispute or source error was found.

## What remains unfinished

The three extracted nodes need their own future stage-1 splits. That is intentional and required by the return. I wrote no Lean and ran no compiler, Lake, build, or local project preflight/check_dag/review_split command. Server checks and delivery are run only through the authorized launcher tools.

## Search review

Before creating nodes I searched the entire DAG for Tags 09I3, 09GH, 0C2Y, 030H, 030W, 030Z, 09HB and 037J and for fixed-field, orbit-polynomial, separating-basis, subfield and geometric-reducedness concepts; inspected the near matches listed below; and searched project Lean by the same concepts and the item tag. `tools/blueprint_refs.py search` was run for fixed field, separating, geometrically reduced, semilinear, and transcendence basis. There was no matching imported statement. The ancestor command returns None for this existing imported-via-created chain; I preserved that null ancestor and the detailed existing place, adding the parent at the front of each new node's via list. The chapter and unit records were read; this is not the unit's key node and neither record is changed.

Every new node has actual logged LeanFinder, Loogle, grep and attempted LeanSearch searches, including a second semantic phrasing. The entries reproduce the command's exact tool and query and its log result. LeanSearch was unavailable through rate limiting for the second and third nodes, recorded as unavailable. Successful searches provide the other kinds. I read the hits: `FixedPoints.isSeparable` and the finite-dimensional instance in `Mathlib/FieldTheory/Fixed.lean:287,296` give finite fixed-field extensions; `IntermediateField.fg_of_noetherian` in `Adjoin/Algebra.lean:298` assumes module finiteness over the same base and does not prove the first node's finite-generation descent. `Algebra.IsGeometricallyReduced.of_injective` in `RingTheory/Nilpotent/GeometricallyReduced.lean:78` is same-base descent and uses an algebraic-closure definition; it does not give the second node's separable scalar restriction or its transcendence-degree comparison. The local file explicitly leaves comparison with arbitrary-field base change as a TODO. `FieldTheory/SeparablyGenerated.lean` gives separating bases under perfectness or p-power independence; I read those statements, their assumptions and proofs. They do not supply a basis in a prescribed subfield with the third node's diamond transfer. `Algebra.isSeparable_tower_top_of_isSeparable` at `FieldTheory/Separable.lean:632` gives one constituent used in the retained explicit Bezout argument, not the combined third node. No new node qualifies as a one-line specialization of a single result or one result per independent clause.

## Review by Q132

I read de Jong Lemma 5.2 proof, printed p.613, and the local Stacks algebra/fields sources at their actual labels: 09I3 lemma-galois-over-fixed-field, 09GH lemma-algebraic-finitely-generated, 0C2Y lemma-geometrically-reduced-over-separable-algebraic, 030H lemma-transcendence-degree-tower, 030W lemma-characterize-separable-field-extensions, 030Z lemma-perfect, and 09HB lemma-separable-permanence. I opened and read every statement cited by the original proof, including the definition of separably generated and the algebraic-base-independence leaf; the full source/dependency map is retained with the old steps below. I checked the new statements against those arguments rather than treating the old review as evidence of correctness.

For assembly step 1 the quoted first new statement says exactly that the two fixed fields are nested, that the two extensions over fixed fields are finite separable, and that E and F are finitely generated over k0. Its hypotheses are precisely finite generation of E/k and the two compatible finite actions. Passing to the two automorphism images is essential: the old Galois node assumes faithfulness, whereas the new statement and the item do not. The orbit-coefficient field is contained in F, E is finite over it by 09GH, and a finite basis of the C-subspace F gives the missing finite generation. I checked that no assumption of a faithful action or a perfect base has slipped in.

For assembly step 2 the second new statement explicitly quantifies over all fields L/k0 and gives reducedness of both tensor products and the two transcendence-degree equalities. From the item's domains, reducedness is immediate even when the tensor product has arbitrary dimension. Step 1 supplies separable algebraicity of k/k0 and algebraicity of E/F. Thus 0C2Y applies in the direction down to k0. Tensoring F -> E over k0 with a vector space is injective; the induced map is a ring map with the stated commutative multiplication, so nilpotents vanish by injectivity. The two tower equalities use algebraicity, not equality of k and F; those fields need not be comparable. The original flatness node really states preservation of injectivity and the original tower node really includes the algebraic-zero-transcendence-degree clause. No conclusion of a definition node is being used as a theorem.

For assembly step 3 the third new statement supplies parameters inside F, independence over k, and finite separability over k(t), all explicitly in its conclusion and quotation. Step 1 supplies both finite-generation hypotheses and the two algebraic extension hypotheses; step 2 supplies geometric reducedness and the exact value d. In characteristic p the original 030W node is restricted to prime positive characteristic, so it is used only in that case, with F itself as the finitely generated subextension in the definition; in characteristic zero 030Z supplies the basis. The original tower and finite-generator lemmas give finite separability over B=k0(t). Algebraic-base independence is applicable because k/k0 is algebraic inside E; B is contained in D=k(t). I independently recomputed the old polynomial identity: if P=QR and UP+VP'=1 then 1=Q(UR+VR')+Q'VR, so Q is separable over D. A finite B-spanning family also spans over D. This preserves the full original transfer argument. Membership in F is exactly H-invariance, so the last sentence of the parent is a definition, not another hidden lemma.

I tested the three new statements when H is trivial and when its action has a kernel, when E=k and d=0, and for a wild translation u -> u+1 in characteristic p with fixed element u^p-u (its derivative is -1). I also tested semilinear finite constants k=F_(p^r), E=k(u), with Frobenius on constants and u fixed: k0=F_p, F=F_p(u), and the transferred basis is u. For the group-free second node I tested k=F_(p^r), E=k(u), F=F_p(u^p): E/F is algebraic but inseparable, which is permitted, while F is still geometrically reduced over F_p and the transcendence degrees are one. Removing separability of the scalar restriction would fail for an imperfect base k0 and k=k0(a^(1/p)), E=k; this verifies why that hypothesis must be retained. For the third node a purely inseparable algebraic F/k0 with d=0 fails geometric reducedness and is correctly excluded; a purely inseparable E/F is correctly excluded by its separability hypothesis. All three statements allow empty generating/basis families. No source argument or unit route was replaced.

I checked delivery-errors B–E against the resulting files: the new nodes introduce all four fields and every hypothesis, define tensor multiplication and reducedness inline, cite definitions for fields, separability and transcendence bases, and carry statement-only unsplit records. Sources use the exact Stacks tags and labels read above. Searches were actually executed and unsuccessful services are marked unavailable. The parent uses exactly the three new statement conclusions, with three verbatim quotes in citations.json; its proof_deps is the union of uses. New statement dependencies are existing definition nodes, never the parent, so there is no new dependency cycle. The three work packets are comparable in size, and none alone recovers the invariant-parameter item. All checks requested by the return are substantive repairs, not a rebase or unchanged re-push.

## Not duplicates

lem-sfb-semilinear-fixed-field-finite-generation vs lem-wf-finite-field-action-fixed-degree: the existing result proves degree and Galois properties for one faithful field action; the new finite-generation node treats two compatible possibly nonfaithful actions and establishes finite generation between their fixed fields.

lem-sfb-semilinear-fixed-field-finite-generation vs lem-sfb-invariant-separating-parameters: the parent combines three independent arguments under geometric integrality and a group action; this new node supplies only its named structural argument and does not state the whole invariant-parameter conclusion.

lem-sfb-semilinear-fixed-field-finite-generation vs lem-weil-pbc-distinct-linear-factors-separable: the existing result is about separability of a polynomial with distinct linear factors; the new node constructs and controls finitely generated field extensions, not just a polynomial.

lem-sfb-semilinear-fixed-field-finite-generation vs lem-weil-pbc-algebraic-generators-finite-extension: the existing result gives finiteness after an already-algebraic finite family is specified; the new node must construct the relevant generators or separating basis and verify the field-diamond conditions.

lem-sfb-geometric-subfield-scalar-restriction vs lem-sbc-transcendence-degree-tower: the existing result is only the tower equality; the new node additionally restricts scalars along a separable extension and descends reducedness to a potentially incomparable subfield.

lem-sfb-geometric-subfield-scalar-restriction vs lem-trf-geometric-reducedness-separable-scalar-restriction: the existing result compares reducedness of one algebra over two nested bases; the new node descends to a second subfield and compares the diamond transcendence degrees.

lem-sfb-geometric-subfield-scalar-restriction vs lem-kun-transcendence-degree-tower: the existing result is the tower equality and algebraicity criterion; the new node additionally proves geometric reducedness in the field diamond.

lem-sfb-geometric-subfield-scalar-restriction vs lem-exc-domain-transcendence-degree-tower: the existing result is a transcendence-degree equality for a chain of domains; the new node includes scalar restriction and geometric reducedness of a second subfield.

lem-sfb-separating-basis-algebraic-diamond vs lem-sbc-field-hypersurface-integral-presentation: the existing result supplies a hypersurface presentation of a geometrically reduced affine function field; the new node constructs and transfers a separating basis in a prescribed subfield.

lem-sfb-separating-basis-algebraic-diamond vs lem-zl-separable-permanence: the existing result is composition of two separable algebraic towers; the new node constructs a separating basis and also changes the algebraic base in a diamond.

lem-sfb-separating-basis-algebraic-diamond vs lem-trf-geometric-field-stalk-descent: the existing result is descent of a geometric field stalk of a finite-type algebra to a finite separable residue field; the new node concerns separating bases and two arbitrary subfields of E.

lem-sfb-separating-basis-algebraic-diamond vs lem-pc-finite-extension-tensor-algebraic-closure-reduced-separable: the existing result assumes a finite extension and concludes its separability; the new node has positive transcendence degree allowed and must construct and transfer a separating basis.

lem-sfb-separating-basis-algebraic-diamond vs lem-pc-finite-inseparable-element: the existing result selects an inseparable element of a finite nonseparable extension; the new node proves existence and transfer of separating bases under different hypotheses.

lem-sfb-separating-basis-algebraic-diamond vs lem-pc-inseparable-tensor-nilpotent: the existing result produces a tensor nilpotent from an inseparable element; the new node constructs a separating basis in F and transfers it across E and k.

lem-sfb-separating-basis-algebraic-diamond vs lem-sfb-invariant-separating-parameters: the parent combines three independent arguments under geometric integrality and a group action; this new node supplies only its named structural argument and does not state the whole invariant-parameter conclusion.

lem-sfb-separating-basis-algebraic-diamond vs lem-sfb-finite-field-separable-closure-algebraic: the existing result identifies a separable closure of a finite field as an algebraic closure; the new node is a separating-basis theorem over arbitrary bases.

lem-sfb-separating-basis-algebraic-diamond vs lem-weil-pbc-perfect-field-separating-basis: the existing result assumes a perfect base and supplies a basis in the top field only; the new node allows imperfect bases with geometrically reduced F and must transfer the basis in a diamond.

lem-sfb-separating-basis-algebraic-diamond vs lem-weil-pbc-algclosed-fg-field-separating-basis: the existing result assumes an algebraically closed base and has no diamond transfer; the new node allows arbitrary bases with geometric reducedness and a prescribed subfield.

lem-sfb-separating-basis-algebraic-diamond vs def-weil-pbc-relative-separable-closure: the existing node defines the relative separable algebraic closure and its basic closure properties; the new node is a separating-basis construction and transfer theorem.

lem-sfb-separating-basis-algebraic-diamond vs lem-weil-pbc-algebraic-generators-finite-extension: the existing result gives finiteness after an already-algebraic finite family is specified; the new node must construct the relevant generators or separating basis and verify the field-diamond conditions.

lem-sfb-separating-basis-algebraic-diamond vs lem-weil-pbc-field-char-p-h1-cotangent-vanishing: the existing result is vanishing of cotangent-complex homology over F_p; it does not state the separating-basis field-diamond conclusion.

lem-sfb-separating-basis-algebraic-diamond vs lem-weil-pbc-geometrically-reduced-extension-separable: the existing result in positive characteristic converts geometric reducedness to separable generation of finitely generated subextensions; the new node also handles characteristic zero and transfers a finite separating basis across E/F and k/k0.

lem-sfb-separating-basis-algebraic-diamond vs lem-weil-pbc-separably-generated-separable: the existing result goes from a separating basis to separability of finitely generated subextensions; the new node constructs the basis from reduced tensors and transfers it across the diamond.

lem-sfb-separating-basis-algebraic-diamond vs lem-weil-pbc-p-power-independence-separably-generated: the existing result takes p-power linear independence in positive characteristic; the new node takes geometric reducedness in any characteristic and transfers the resulting basis.

lem-sfb-separating-basis-algebraic-diamond vs lem-weil-pbc-field-char-p-nilpotent-lifting: the existing result lifts field maps across a nilpotent ideal; it does not assert existence or transfer of a separating basis.

lem-sfb-semilinear-fixed-field-finite-generation vs lem-sfb-separating-basis-algebraic-diamond: the first constructs finite generation of invariant fields without geometric hypotheses; the second assumes finite generation and reduced tensors and constructs/transfers a separating basis without a group action.

The nearby curve-separating-parameters node assumes transcendence degree one, a separably closed base and a smooth curve; none of these field-diamond statements follows from it. The geometric-regularity-over-subfields node treats a directed union of bases of a Noetherian algebra, not separable scalar restriction and an arbitrary second subfield. Those were also read and ruled out.

## Retained argument, verbatim, assigned to the three new nodes

The original proof is reproduced without abbreviation. Its node citations remain the future workers' starting material, not premature proof dependencies of unsplit nodes. Each source and cited statement was read as described above.

### lem-sfb-semilinear-fixed-field-finite-generation — former steps 1–3

Original step 1:

Put $k_0=k^H$ and $F=E^H$. Compatibility of the actions gives $k_0\subseteq F$. Apply [lem-wf-finite-field-action-fixed-degree] separately to the finite images of $H$ in $\operatorname{Aut}(k)$ and $\operatorname{Aut}(E)$. Each image acts faithfully and has exactly the original fixed field. Thus $k/k_0$ and $E/F$ are finite separable (indeed Galois). This use of the two images requires no faithfulness of either original action.

Uses: lem-wf-finite-field-action-fixed-degree. Elementary judgment in original: False. Source: literature/stacks-project/fields.tex, Tag 09I3, lemma-galois-over-fixed-field, applied to the automorphism images.

Original step 2:

Choose finitely many field generators of $E/k$ and a finite $k_0$-vector-space spanning family of $k$, possible by step 1. Together they are elements $a_1,\ldots,a_n$ with $E=k_0(a_1,\ldots,a_n)$. For each $i$ form $P_i(T)=\prod_{b\in H a_i}(T-b)$, with each distinct orbit element appearing once. An element of $H$ permutes these factors, so every coefficient lies in $F$. Let $C\subseteq F$ be the subfield generated over $k_0$ by the finitely many coefficients of these polynomials. Since $P_i$ is monic and $P_i(a_i)=0$, all $a_i$ are algebraic over $C$. Also $C(a_1,\ldots,a_n)=E$, since it contains $k_0(a_1,\ldots,a_n)$. Hence [lem-weil-pbc-algebraic-generators-finite-extension] gives $[E:C]<\infty$.

Uses: lem-weil-pbc-algebraic-generators-finite-extension. Elementary judgment in original: True. Source: literature/stacks-project/fields.tex, Tag 09I3, proof, orbit-polynomial construction; Tag 09GH, lemma-algebraic-finitely-generated.

Original step 3:

The $C$-subspace $F\subseteq E$ has a finite spanning family $b_1,\ldots,b_m$: successively choose a vector outside the span until this is impossible; otherwise one would obtain more than $[E:C]$ linearly independent vectors in $E$. Every element of $F$ is a $C$-linear combination of the $b_j$, so $F=C(b_1,\ldots,b_m)$. Since $C/k_0$ was generated by finitely many coefficients, $F/k_0$ is finitely generated. This argument uses only finite-dimensional linear algebra and the explicit coefficient field of step 2.

Uses: def-weil-finite-dimensional-subspace. Elementary judgment in original: True. Source: literature/stacks-project/fields.tex, Tag 09GH together with the explicit finite-dimensional-subspace argument after the orbit-polynomial construction of Tag 09I3.

### lem-sfb-geometric-subfield-scalar-restriction — former steps 4–6

Original step 4:

For every extension field $K/k$, the assumed domain $E\otimes_kK$ is reduced: if $x^n=0$, the absence of zero divisors forces $x=0$. Since $k/k_0$ is separable algebraic by step 1, apply [lem-trf-geometric-reducedness-separable-scalar-restriction] to the $k$-algebra $E$ and the tower $k_0\subseteq k$. It gives that $E\otimes_{k_0}L$ is reduced for every extension field $L/k_0$. Geometric integrality is used here only through reducedness.

Uses: lem-trf-geometric-reducedness-separable-scalar-restriction. Elementary judgment in original: False. Source: literature/stacks-project/algebra.tex, Tag 0C2Y, lemma-geometrically-reduced-over-separable-algebraic, direction from the larger base field to the smaller one.

Original step 5:

Fix any extension field $L/k_0$. Tensor the injective $k_0$-linear inclusion $F\hookrightarrow E$ with $L$. A vector space over the field $k_0$ is free and hence flat, so [lem-trf-flat-tensor-preserves-injection] gives an injection $L\otimes_{k_0}F\hookrightarrow L\otimes_{k_0}E$. Using the tensor flip, this is the ring homomorphism $F\otimes_{k_0}L\hookrightarrow E\otimes_{k_0}L$ given by $f\otimes l\mapsto f\otimes l$. Its target is reduced by step 4. If an element of its source is nilpotent, its image vanishes and injectivity makes the element zero. Thus $F$ is geometrically reduced over $k_0$.

Uses: lem-trf-flat-tensor-preserves-injection. Elementary judgment in original: False. Source: literature/stacks-project/algebra.tex, Tag 030W, lemma-characterize-separable-field-extensions, geometric reducedness condition; tensor-injectivity as in the proof of lemma-generic-points-geometrically-reduced (Tag 07K2).

Original step 6:

By [lem-kun-transcendence-degree-tower], the algebraic extension $E/F$ has transcendence degree zero, and the algebraic extension $k/k_0$ has transcendence degree zero. Applying the tower equality first to $k_0\subseteq F\subseteq E$ and then to $k_0\subseteq k\subseteq E$ gives $\operatorname{trdeg}_{k_0}F=\operatorname{trdeg}_{k_0}E=\operatorname{trdeg}_kE=d$. In particular every transcendence basis of $F/k_0$ has precisely $d$ elements.

Uses: lem-kun-transcendence-degree-tower, def-kun-transcendence-degree. Elementary judgment in original: False. Source: literature/stacks-project/fields.tex, Tag 030H, lemma-transcendence-degree-tower; Tag 030G, definition-transcendence-degree.

### lem-sfb-separating-basis-algebraic-diamond — former steps 7–9

Original step 7:

If $k_0$ has positive characteristic $p$, it has prime characteristic and [lem-weil-pbc-geometrically-reduced-extension-separable], applied to step 5, says that every finitely generated intermediate field of $F/k_0$ is separably generated in the sense of [def-weil-pbc-separable-field-extension] (1). Take that intermediate field to be $F$ itself, which is finitely generated by step 3. If $k_0$ has characteristic zero, apply [lem-weil-pbc-perfect-field-separating-basis] directly to $F/k_0$. In either case there is a transcendence basis $t$ in $F$ with $F/k_0(t)$ separable algebraic. By step 6 and [def-weil-pbc-transcendence-basis], index it as $t_1,\ldots,t_d$. Each $t_i$ is fixed by $H$ because it belongs to $F$.

Uses: lem-weil-pbc-geometrically-reduced-extension-separable, lem-weil-pbc-perfect-field-separating-basis, def-weil-pbc-transcendence-basis, def-weil-pbc-separable-field-extension. Elementary judgment in original: False. Source: literature/stacks-project/algebra.tex, Tag 030W (4) implies (1), lemma-characterize-separable-field-extensions; Tag 030Z, lemma-perfect; Definition 030O, definition-separable-field-extension.

Original step 8:

Set $B=k_0(t_1,\ldots,t_d)$. The extensions $F/B$ from step 7 and $E/F$ from step 1 are separable algebraic. Their tower is separable algebraic by [lem-zl-separable-permanence]. Since $E=k_0(a_1,\ldots,a_n)$, also $E=B(a_1,\ldots,a_n)$. These finitely many generators are algebraic over $B$, so [lem-weil-pbc-algebraic-generators-finite-extension] gives $[E:B]<\infty$.

Uses: lem-zl-separable-permanence, lem-weil-pbc-algebraic-generators-finite-extension. Elementary judgment in original: False. Source: literature/stacks-project/fields.tex, Tag 09HB, lemma-separable-permanence; Tag 09GH, lemma-algebraic-finitely-generated.

Original step 9:

As $k/k_0$ is algebraic, [lem-zl-independence-algebraic-base] applied inside $E$ shows that $t_1,\ldots,t_d$ are algebraically independent over $k$. Put $D=k(t_1,\ldots,t_d)$, so $B\subseteq D\subseteq E$. A finite $B$-spanning family of $E$ also spans over $D$, proving $[E:D]<\infty$. For $x\in E$, let $P\in B[T]$ be its separable minimal polynomial and $Q\in D[T]$ its minimal polynomial over $D$. Division with remainder gives $P=QR$ in $D[T]$. Coprimality of $P,P\prime$ gives $UP+VP\prime=1$ for some $U,V\in B[T]$. Since $P\prime=Q\prime R+QR\prime$, this identity becomes $1=Q(UR+VR\prime)+Q\prime VR$. Thus $Q,Q\prime$ are coprime; $x$ is separable over $D$. This proves the required finite separability for every $x$, including the empty basis when $d=0$.

Uses: lem-zl-independence-algebraic-base, def-weil-pbc-separable-algebraic-extension. Elementary judgment in original: True. Source: literature/stacks-project/fields.tex, Algebraic-base independence: Mathlib Algebra.IsAlgebraic.algebraicIndependent_iff (the existing leaf); finite spanning and the displayed Bezout identity prove passage to an intermediate base directly.

In the third packet, symbols refer to the self-contained new hypotheses: E/k0 finite generation replaces the reference to the earlier choice of generators, and the input trdeg(F/k0)=d replaces the reference to former step 6. Those two quantities were proved by the preceding packets. All computations, characteristic cases, finite-spanning reasoning and the Bezout identity remain assigned to that packet above. The invariant-membership sentence itself is the final definition check in the parent assembly.
