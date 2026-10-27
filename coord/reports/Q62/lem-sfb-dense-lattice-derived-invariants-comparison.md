# Worker report: lem-sfb-dense-lattice-derived-invariants-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dense-lattice-derived-invariants-comparison.json`: repaired split; statement, statement dependencies, provenance, prior review and Lean records retained; five assembly steps, 2458 characters of proof text.
- `dag/nodes/sec-six-functors-basics/lem-sfb-trivial-dense-lattice-restriction.json`: new statement, unsplit; no Mathlib match. The canonical restriction comparison for trivial finite-dimensional representations only.
- `dag/nodes/sec-six-functors-basics/lem-sfb-central-action-derived-vanishing.json`: new statement, unsplit; no Mathlib match. Identity of a central action after ordinary derived invariants and its vanishing consequence.
- `dag/nodes/sec-six-functors-basics/lem-sfb-continuous-section-exact-triangles.json`: new statement, unsplit; no Mathlib match. Exact all-continuous realizations of invariant-subspace sequences, including the connecting square.
- `dag/nodes/sec-six-functors-basics/lem-sfb-commuting-representation-devissage.json`: new statement, unsplit; no Mathlib match. A property criterion for continuous representations, separating dimension induction from the comparison problem.

`citations.json` gives literal statement quotations for every citation of every parent step. `searches.jsonl` is the search command's unchanged log. `search-plan.json` and the four `*-search-results.json` files retain the queries and returned hits (the first trivial-case LeanFinder output was read directly and is recorded in the command log). `returned-proof.json` and the verbatim section below preserve every old argument. All writes are inside this item's sandbox. No Lean, compiler, Lake, repository git command, other node, launcher script, chapter or unit was modified.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, dense-lattice wording, central derived invariants and commuting-representation induction, and read the main and coefficient theorems in `lean/Sheaf/Paper/DenseLatticeDerivedInvariants.lean` at lines 838–919. Both theorem bodies are `sorry`. The source does not supply a finished attachment for this item. Related invariant and representation declarations give only parts of the proposed new statements.

## WANTED

WANTED: an exact reference for the all-continuous norm-topological noncomplete-algebraic-closure trivial-coefficient calculation, already isolated in `lem-sfb-trivial-ladic-derived-exterior`. The new trivial comparison uses that existing obligation; it does not claim it has been proved.

The sources of the four extractions are explicitly agent expansions of paragraph (3) of the current main-20261015 direct-images proof, with their corresponding old proof-step numbers in `source.place`. The blueprint paragraph supplies the tame-boundary context, not proofs of these four lemmas. No invented Stacks tag and no SGA source is supplied. The formal resolution input suggested for the central-action worker is the existing `lem-sp-derived-injective-resolution-naturality`; the topology inputs suggested for the exactness worker are `lem-sfb-continuous-representation-subquotients` and `lem-sfb-finite-dimensional-linear-map-continuous`.

## Repair of the returned delivery

The return requires work to be spread across at least two comparably sized statement-only nodes, an unchanged parent statement, an assembly of at most 3000 characters, and preservation of every argument. I extracted four obligations, carrying old steps 3, 4, 5 and 6, respectively. Those four old steps have comparable argument lengths (roughly 1000 characters apiece); none carries the whole result. The parent now supplies canonical-transformation setup, the two special-case applications, extension closure and application of the independent induction criterion, the sectionwise density proof of the degree-zero identity, and the exact coefficient-pasting square and rank-zero normalization. Its 2458 characters are below the 3000-character limit. Every new node has `status: unsplit`, empty `proof` and `proof_deps`, null `proof_origin`, full standalone hypotheses, blueprint placement and actually executed searches.

The sandbox was empty on arrival, contrary to the generic repair description. I recovered the current merged item and the prior NP report from the read-only repository. Its main and coefficient statements remain unfinished in the live Lean module, matching the return's premise. The initial required dry run on that recovered split stopped because the historical report did not contain `## Review by Q62`; this report supplies a fresh review, rather than relabelling the historical NP review. The historical report is retained below under an explicitly historical heading. There were no prior Q62 search logs to recover.

No parent statement correction or STATEMENT-DISPUTED is needed. The proof route, coefficient topology, coefficient maps and degree-zero normalization are unchanged. The parent’s existing `tool_uses` field is not edited. The current assembly's sole off-unit proof tool is `lem-sf-triangle-two-out-of-three`, declared in `split_report.tool_uses`.

## Repair of landing refusal at a016ae4dabb

The current return is the 2026-10-22 06:35 UTC entry: the reader approved the delivery, but landing refused the side-completion/live-queue discrepancy. This repair retains the approved four child statements, all recorded searches and their results, citations, historical report, and complete returned proof. The required delivery command rebuilds on current origin/sheaf-dag; its initial dry run exited successfully at 8e3d952bced before these final repairs.

I compared every field of the retained parent with the current read-only repository. Only proof, proof_deps and split_report differ; statement, stmt_deps, blueprint, provenance, prior reviews and Lean records agree. None of the four child ids exists in the current repository. The archived returned-proof.json equals the current repository's seven-step proof exactly. The released stage-1 repair note still requires this four-argument extraction, despite the old reviewed record.

I reread all current cited statements, including the restriction calculus, full-fixed-section definition and triangle two-out-of-three, and the subsidiary exterior, resolution-naturality and continuous-subquotient inputs retained for future child workers. All nine citations.json quotations are still exactly their cited statements, so there is no changed hypothesis or map to repair there. I checked the whole-DAG candidates again and found no replacement for the four child statements. The current upstream continuous-comparison declaration concerns discrete integer coefficients and individual cohomology groups, not these internal norm-topological derived objects; the parent and coefficient-square declarations in DenseLatticeDerivedInvariants.lean still contain sorry.

I strengthened assembly step 2's explanation: commutation of T_i-1 with every action operator also gives commutation of its inverse; both extend as continuous finite matrices over E and Omega. Thus the isomorphism is in the action category, exactly as the cited vanishing lemma requires. This clarification changes no statement or route. All steps remain under 2000 characters and the assembly remains under 3000. The small-case checks and source checks signed in Review by Q62 still apply. The final dry run and push follow this update; no Lean or compiler is used.

## Repair of landing refusal at 316353fac04 (2026-10-22 10:41 UTC)

This is the current return in coord/returns/Q62.md, distinct from the earlier a016ae4dabb return retained above. I continued the delivered sandbox rather than recreating any child or search. The first required dry run on the retained files passed on the current server base at 43d18552ae3. The delivery tool rebases by overlaying the split-owned fields on current origin/sheaf-dag and preserving the live maintainer-owned fields; I did not run git or alter the repository.

I compared the retained parent field by field with the current shared repository: only proof, proof_deps and split_report differed. The statement, all eight statement dependencies, blueprint metadata, proof origin, recorded searches, Lean binding, reviewed and reviewed_lean records agreed. None of the four delivered child ids exists in the current live node directory. returned-proof.json still equals the live seven-step proof exactly. Thus the released keep_plan stage-1 repair note applies: this delivery replaces that long proof with the four-child assembly, without treating the old reviewed record as closing the repair.

I opened the current statements of every parent citation: the calculus, full-fixed-section definition, triangle two-out-of-three and all four retained children. The nine existing quotation entries remain verbatim. I also reread both exterior inputs, injective-resolution naturality, continuous subquotients and finite-dimensional linear-map continuity against the complete old arguments retained below. No quoted assertion, coefficient category, group hypothesis, canonical arrow or topology needs replacement. I cannot infer arbitrary cohomology comparisons from their statements: the exterior inputs specify actual derived cup maps, and the calculus specifies the restriction and coefficient-pasting arrows themselves.

The concrete adjustment in this retry is assembly step 3: it now explicitly cites the calculus for shift compatibility before invoking triangle two-out-of-three, with its own verbatim citation entry. The triangle statement requires that hypothesis in addition to the connecting square furnished by the new exact-realization child. This records the hypothesis check at its point of use, instead of leaving it solely in step 1 and the review. The four child statements and their actual Mathlib searches are unchanged. The revised assembly has 2572 characters, with no step above 2000. Its proof dependencies remain precisely the union of the cited uses.

For C4 I checked step 1's normalized arrow and naturality, step 2's trivial comparison and central vanishing (including equivariance and continuity of the inverse matrix), step 3's exact triangles, shift compatibility and three devissage assumptions, step 4's full base-change fixedness and H^0 invariant inclusion, and step 5's exact coefficient-pasting equality and identity normalization. For C1 the non-elementary assertions are those cited statements; the remaining matrix extension, density by congruence representatives, pointwise equality of continuous functions, and substitution of the coefficient map are explicitly the same arguments as in the archived proof. No argument was lost in rebasing.

I rechecked r=0 and V=0, an invertible generator difference on a one-dimensional nontrivial character, and the singular nonzero difference on a two-dimensional unipotent Jordan block. The latter has a one-dimensional stable kernel and quotient and exercises extension closure; r=0 selects no generator. The exact-realization argument uses a nonequivariant E-linear splitting and its finite matrices over Omega, not completeness of Omega. The central lemma at z=1 forces N=0 only when the zero difference is assumed invertible. These checks confirm the hypotheses used by the assembly without asserting completion of the outstanding analytic trivial-coefficient input. No statement dispute, new source attribution or SGA route was introduced. The final server dry run and push are required after this actual proof/report repair.

## Allocation of all arguments

Old step 1 remains assembly step 1: the exact normalized restriction transformation, naturality, additivity and shift/connecting compatibility come from the existing calculus.

Old step 2 remains assembly step 4: congruence representatives prove density, and closed zero sets prove equality of fully fixed sections after every profinite base change. No replacement of the actual coefficient topology is made.

Old step 3 is the independent trivial-comparison obligation. Its intended proof uses the two existing specified coordinate-cup exterior maps, checks their equality after restriction summand by summand using a_i(iota(n)) = n_i, and then passes to all finite-dimensional trivial representations by finite direct sums. Its full argument is retained verbatim below, including the empty subset, ordered products, common complex and zero-dimensional case.

Old step 4 is the independent central-action obligation. The injective-resolution argument belongs to that worker, including the augmentation square, termwise identity after invariants, normalized naturality and the zero-and-invertible argument. The application to both groups and continuity of the inverse E-matrix remain in assembly step 2.

Old step 5 is the independent exact-realization obligation. Its argument retains the continuous subquotients, an E-linear splitting, continuity over complete E, extension by finite matrices to noncomplete Omega, sectionwise surjectivity natural in S, exactness detection in action modules, and the derived connecting square. No equivariant splitting is assumed.

Old step 6 is the independent property criterion. Its intended argument is strong induction on E-dimension: zero; some invertible T_i-1; all T_i-1 zero and hence trivial by density; otherwise a nonzero singular T_i-1 with nonzero proper L-stable kernel. The strict dimension bounds for both kernel and quotient are retained. The criterion assumes extension closure; assembly step 3 proves precisely that hypothesis for the particular property using the new triangle statement and existing two-out-of-three. This separation gives an independently provable representation lemma, not a disguised copy of the full comparison.

Old step 7 remains assembly steps 1 and 5, with the same formula f(v)=1 tensor v and the same derived square c_D b_E = Res(b_Omega) c_L. Naturality is attached to the canonical transformation, not to basis choices made to prove invertibility. Rank zero uses the trivial-group normalization. The following verbatim record is part of this delivery, so no original argument is lost or blurred.

## Verbatim returned proof, for the four new workers and the maintainer

### Original step 1

Use [lem-sfb-condensed-derived-restriction-calculus] for $R=C_F$, $J=L$, $H=D$ and $u=\iota$. This constructs the specified $b_F$ from the inclusion of invariant objects, as a natural transformation of additive triangulated functors $D(\mathcal A_F(L))\to D(\operatorname{Mod}_{C_F})$. In particular it is compatible with the connecting morphism of a short exact sequence of action modules. The map on $H^0$ is the underived invariant inclusion. We will prove that this very transformation is invertible on $V_F[0]$, rather than choose an isomorphism between the two derived objects.

Original cited statements: `lem-sfb-condensed-derived-restriction-calculus`.

### Original step 2

The image of $\mathbf Z^r$ is dense in $\mathbf Z_\ell^r$: every nonempty basic open specifies finitely many residues modulo powers of $\ell$, and each coordinate residue has an integer representative. Let a section $m\in C(S,F\otimes_E V)$ be $D$-fixed after every profinite base change, in the sense of [def-sfb-condensed-action-module]. For every $s\in S$, its value $m(s)$ is fixed by all constant integer elements. The map $x\mapsto x\cdot m(s)-m(s)$ on $L$ is continuous, and its zero set is closed since $F\otimes_E V$ is Hausdorff. Density makes it zero on all of $L$. Thus for every $T\to S$ and continuous $g:T\to L$, one has $g(t)m(t)=m(t)$ at every $t$, so the sections are equal. Hence $m$ is $L$-fixed. The reverse inclusion is immediate by restricting the action. Consequently the inclusion of invariants is literally the identity on their common submodule.

Original cited statements: `def-sfb-condensed-action-module`.

### Original step 3

First consider $V=E$ with trivial action. The two coordinate-cup morphisms of [lem-sfb-trivial-ladic-derived-exterior] and [lem-sfb-discrete-lattice-cup-exterior], with $R=C_F$, have exactly the same source $\mathcal E_{C_F,r}$. Each coordinate character restricts by $a_i(\iota(n))=n_i1_F$. Restriction in [lem-sfb-condensed-derived-restriction-calculus] therefore sends each degree-one connecting class to the corresponding discrete class and preserves ordered cup products and the unit. On every summand $C_F[-|I|]$ this gives $b_F\chi_{F,r}=\chi_{C_F,r}$; the finite biproduct universal property gives the equality on the whole complex. Both $\chi$ maps are isomorphisms, so $b_F$ is one. For a trivial $d$-dimensional $V$, choose an $E$-basis. Its coefficient module is $C_F^d$, since a continuous map into a finite product is exactly a tuple of continuous maps. Additivity and naturality from the calculus identify its comparison with the finite direct sum of the just-proved comparison. This includes $d=0$.

Original cited statements: `lem-sfb-trivial-ladic-derived-exterior`, `lem-sfb-discrete-lattice-cup-exterior`, `lem-sfb-condensed-derived-restriction-calculus`.

### Original step 4

For either $J=L$ or $J=D$, a central element $z\in J$ acts as an equivariant endomorphism on every action module. On an equivariant injective resolution $N\to I^\bullet$ it acts termwise, giving a lift of $z_N$. On $\Gamma_J(I^q)$ that lift is the identity, by the definition of invariants. The normalized injective-resolution naturality of [lem-sp-derived-injective-resolution-naturality], applied to this commuting augmentation square, therefore gives $R\Gamma_J(z_N)=\mathrm{id}$. Such resolutions compute these derived functors by [lem-sfb-condensed-derived-restriction-calculus]. If $z_N-1$ is invertible, its derived image is both invertible and zero (additivity). Thus the identity of $R\Gamma_JN$ is zero and the object is zero. In particular, if any $T_i-1$ is invertible on $V$, its inverse is a finite $E$-matrix, hence extends to an invertible endomorphism on $V_F$; the two derived invariant objects are then both zero. Take $z=\iota(e_i)$ for $L$ and $z=e_i$ for $D$. Their centrality follows from commutativity of these groups.

Original cited statements: `lem-sfb-condensed-derived-restriction-calculus`, `lem-sp-derived-injective-resolution-naturality`.

### Original step 5

If $U\subseteq V$ is $L$-stable, [lem-sfb-continuous-representation-subquotients] gives continuous finite-dimensional representations $U$ and $Q=V/U$ with their usual topologies and continuous equivariant inclusion and quotient. Choose an $E$-linear splitting of the vector-space quotient. Its continuity follows from [lem-sfb-finite-dimensional-linear-map-continuous], since $E$ is complete and nontrivially valued. After extension to either $F$, a matrix and its inverse between finite product spaces are continuous by the topological field operations. Thus $0\to U_F\to V_F\to Q_F\to0$ is split exact on the underlying condensed modules: on every profinite $S$, composition with the continuous splitting lifts every $Q_F(S)$ section. The splitting need not be equivariant; the inclusion and quotient are equivariant, and exactness in the action categories is checked on underlying modules by the calculus. It follows that this sequence gives a distinguished triangle, and step 1 gives a morphism between its two derived-invariant triangles, with components $b_F(U),b_F(V),b_F(Q)$.

Original cited statements: `lem-sfb-continuous-representation-subquotients`, `lem-sfb-finite-dimensional-linear-map-continuous`, `lem-sfb-condensed-derived-restriction-calculus`.

### Original step 6

Fix $r$ and use strong induction on $d=\dim_E V$, for both $F$ separately. Dimension zero is step 3. Write $A_i=T_i-1$. An invertible $A_i$ is settled by step 4. If every $A_i=0$, each integer generator acts trivially; density, using the same closed-zero-set argument as step 2, shows that the $L$-action is trivial, so step 3 applies. Otherwise, with the invertible case excluded, some $A_i$ is nonzero and singular. Then $U=\ker A_i$ is nonzero and proper. It is $L$-stable since all action operators commute with $T_i$. Thus $0<\dim_E U<d$ and $0<\dim_E(V/U)<d$. Apply step 5 and the induction hypothesis to these two representations. The transformation is compatible with shifts by the calculus, so [lem-sf-triangle-two-out-of-three] applies to the displayed morphism of distinguished triangles and proves that $b_F(V)$ is an isomorphism. This exhausts the alternatives: every nonzero $A_i$ is either invertible or singular. No simultaneous diagonalization, semisimplicity, or completeness of $\Omega$ is used.

Original cited statements: `lem-sfb-condensed-derived-restriction-calculus`, `lem-sf-triangle-two-out-of-three`.

### Original step 7

Naturality of $b_F$ for every continuous equivariant $E$-linear map is the naturality of the canonical transformation in step 1; the basis and subspaces used to prove invertibility do not define this transformation. Let $\varphi:C_E\to C_\Omega$ be postcomposition by $E\hookrightarrow\Omega$, and let $f:V_E\to\operatorname{Res}_\varphi V_\Omega$ send a section $v$ to $1\otimes v$. This is equivariant and $C_E$-linear, since both actions use the same matrices over $E$. With $J=L,H=D,u=\iota$, the coefficient-pasting equality in [lem-sfb-condensed-derived-restriction-calculus] reads exactly $c_D\circ b_E=(\operatorname{Res}_\varphi b_\Omega)\circ c_L$, the square requested in the statement. The coefficient transformations there are induced by $f$ and equality of invariants with scalar restriction. Finally, for $r=0$ both groups and the homomorphism are trivial; the normalized transformation is the identity of $V_F[0]$. The identity on $H^0$ for every $r$ was established in step 2.

Original cited statements: `lem-sfb-condensed-derived-restriction-calculus`.

## Not duplicates

lem-sfb-trivial-dense-lattice-restriction vs lem-sfb-trivial-ladic-derived-exterior: the existing node specifies one analytic derived coordinate-cup isomorphism for the trivial rank-one coefficient module; the new node proves the canonical restriction arrow by comparison with the discrete cup model and extends to arbitrary finite dimension. Neither exterior isomorphism alone identifies this arrow.

lem-sfb-trivial-dense-lattice-restriction vs lem-sfb-discrete-lattice-cup-exterior: the existing node treats only the discrete group and an arbitrary condensed coefficient ring, with no continuous-to-discrete restriction arrow. The new obligation compares the two specified exterior models.

lem-sfb-trivial-dense-lattice-restriction vs lem-sfb-discrete-lattice-koszul-resolution: this supplies a discrete-group resolution with degree-zero normalization, not the cup-normalized analytic restriction arrow.

lem-sfb-central-action-derived-vanishing vs lem-sfb-condensed-derived-restriction-calculus: the calculus provides derived functors and restriction/scalar/cup naturality, not the identity of every central action or vanishing for invertible difference.

lem-sfb-central-action-derived-vanishing vs lem-sp-derived-injective-resolution-naturality: generic resolution naturality does not state a group-action identity or its vanishing consequence; it is an input to the old step-4 resolution argument.

lem-sfb-continuous-section-exact-triangles vs lem-sfb-continuous-representation-subquotients: the existing node gives continuous E-representations U and V/U; it does not give exact sequences of all-continuous F-valued internal modules, a parameter-natural splitting, or their normalized derived restriction triangles.

lem-sfb-continuous-section-exact-triangles vs lem-sfb-admissible-scalar-realization-exact: the existing node treats ordinary constant scalar modules tensored with pulled-back coefficients on a scheme's pro-etale site. The new node uses continuous functions into finite-dimensional norm spaces with group actions on the point's coherent profinite site. Identifying those realizations would itself require an additional theorem, and the old node has no group-restriction connecting square.

lem-sfb-continuous-section-exact-triangles vs lem-sfb-flat-scalar-realization-exact: the existing node assumes flatness and a separately specified scalar realization; it does not identify continuous-section representations over noncomplete Omega with that realization, or give the restriction triangle morphism.

lem-sfb-commuting-representation-devissage vs lem-sfb-dc-module-devissage: the existing node uses cohomological truncations to pass from constructible modules to bounded derived objects; it has no kernel argument for operators T_i-1 on continuous finite-dimensional representations.

lem-sfb-commuting-representation-devissage vs lem-sfb-bounded-heart-amplitude-devissage: the latter is an amplitude bound for derived complexes, not an extension-closed property criterion for commuting continuous representations.

lem-sfb-commuting-representation-devissage vs lem-sf-triangle-two-out-of-three: two-out-of-three supplies the extension-closure hypothesis in our application; it does not supply the invariant-kernel dimension induction or the density argument establishing its base alternatives.

I searched all `dag/nodes/` by central-action/invariant, commuting-kernel/representation, exact continuous-section, trivial lattice and devissage concepts; then read the candidate statements above. Whole-blueprint searches included `central`, `commuting`, `dense-lattice`, `realization exact`, `trivial lattice`, `trivial coefficients`, `continuous section`, `dimension induction`, `central invariants`, `commuting representation`, and `continuous exact sections`. Their returned candidates are unrelated algebraic-group centrality, continuous coefficient descent, projectivity, and ordinary derived definitions. No blueprint node states one of the four new obligations. There is no same-Stacks-tag collision because these are agent extractions, not claims attributed to a Stacks lemma. The inherited ancestor command returns None, so the existing null `from.node` and full via chain are retained, prepending this item for each child.

## Mathlib assessment

Each new node has two genuinely different LeanFinder phrasings, one Loogle query, a source grep, and a LeanSearch request made through the prescribed msearch.py command. I read the actual hit signatures. LeanSearch returned results for the trivial case and rate-limit errors for the other three; those three entries say exactly `unavailable`. No nonexistent query or successful no-match response is invented. A further narrower trivial-representation grep in RepresentationTheory is also in the unchanged log.

The trivial-case hits are discrete/locally-constant or solidification functors and continuous cohomology in degree zero; they do not give the specified derived internal-module restriction. Central-action hits include Representation.IntertwiningMap.isIntertwiningMap_of_mem_center and ordinary low-degree cohomology equations, not the identity on the entire condensed derived invariant object. Exactness hits include Condensed.hasExactLimitsOfShape, Condensed.hasExactColimitsOfShape, AB4/AB5 and an ordinary ModuleCat exactness equivalence; these do not give the asserted continuous-section realization or connecting square. Devissage hits include finite-group projectivity, kernel stabilization and Representation.Coinvariants.induction_on, whose motive is a predicate on elements of a quotient, not on representations. None is an exact or one-line generalized match for a complete new statement.

I also read Mathlib/Condensed/Module.lean (CondensedMod is over an ordinary ring), Condensed/AB.lean (limits/colimits of sheaf categories), RepresentationTheory/Homological/ContCohomology/Basic.lean (TopRep cochains and its TODO about exact sequences), and RepresentationTheory/Intertwining.lean (ordinary intertwining maps). These confirm the category and conclusion mismatches. No Mathlib leaf is asserted.

## Review by Q62

I read the current main-20261015 direct-images proof paragraph (3), the item's entire returned proof, the NP report, the node's chapter and unit records, the three-level restrictions in SETUP.md and delivery-errors B–E. The current blueprint routes open direct images through sk-prop-open-coefficients and supplies no analytic calculation itself; all four extracted statements explicitly identify their source as an agent expansion of that context. I read each new node after writing it. The original item statement is retained byte-for-byte, so no finite extension, rank, coefficient category, canonical map, naturality or normalization hypothesis changed. New nodes use exactly the same all-continuous norm topology, including noncomplete Omega, except the central-action statement is a formal general lemma over arbitrary internal coefficients.

Assembly step 1 cites the actual calculus statement saying b_u is induced by invariant inclusion and is natural and compatible with shifts and triangles. It supplies the functors and the actual arrow whose isomorphism property is used as P; invariance under equivariant isomorphisms is conjugation by functorial images, an elementary consequence of that naturality.

Assembly step 2 cites the complete trivial-comparison statement for arbitrary finite-dimensional trivial W, so zero dimension is included. For its other case I checked the central-action statement says both RGamma(z)=id and vanishing when z-1 is an isomorphism in the action category. Here the groups L and D are abelian, and T_i commutes with the entire action. Therefore (T_i-1) inverse commutes too; it is an E-matrix and both it and T_i-1 act continuously on F tensor W by finite sums/products. This checks the stronger action-module-isomorphism hypothesis, not just invertibility on abstract vectors. The two derived objects are zero, so every arrow between them is an isomorphism. This does not assert that a general restriction arrow is invertible before the criterion is applied.

Assembly step 3 uses the new exact-triangle statement with Pi=L, H=D and u=iota. I checked its hypotheses include profiniteness of L and finite-dimensionality over E, and its conclusion includes the connecting square, rather than merely an underived exact sequence. I opened the full statement of lem-sf-triangle-two-out-of-three: it demands compatibility with shifts. That is supplied explicitly by the calculus in step 1; the new triangle statement includes connecting arrows. Consequently P(U),P(W/U) imply P(W). The devissage node has exactly three hypotheses, and steps 1–3 now establish isomorphism invariance and all of them; applying it separately for F=E and F=Omega proves the parent conclusion. The criterion itself has no derived comparison in its statement and cannot conceal the entire item.

Assembly step 4 cites the calculus only for H^0(b)=inclusion and def-sfb-condensed-action-module for full fixedness after every test-set base change. I read that definition: global fixed points alone are insufficient. The proof explicitly passes from constant integer fixedness at each point to all continuous T-to-L sections; Hausdorffness holds for both norm-topological finite products. Density follows coordinate by coordinate from integer representatives of congruence classes, including the empty product. This retains the argument rather than citing a mere definition for density.

Assembly step 5 substitutes the actual scalar-ring map and actual f(v)=1 tensor v into the calculus's displayed coefficient-pasting equality, a verbatim part of its statement. Coefficient-map equivariance follows from the same E-matrices; no basis used in the invertibility proof defines the arrow. The calculus explicitly identifies coefficient invariants with scalar restriction and states its identity normalization for trivial groups. Thus the whole square, naturality and r=0 are proved for the specified comparison in the derived category, not only on cohomology.

For the four child statements I checked B1–B7 separately: each introduces every coefficient ring, group, module, property and morphism it uses; the exact-triangle statement introduces its quotient and H,u; the devissage criterion quantifies P rather than using the parent's P implicitly. All are TeX with single escaping, statement-only and accompanied by definition dependencies that really define those notions. I read def-pod-l-adic-representations clause (2), def-weil-l-adic-coefficient-extension, def-sfb-continuous-map-condensed-ring, def-sfb-condensed-action-module and the triangle definitions. No child relies on the parent's conclusion, and each can be attacked without proving any other new child.

I matched the old subsidiary inputs against the retained argument for future workers: both exterior nodes specify actual derived cup morphisms on the common direct sum, not just cohomology dimensions; the calculus preserves ordered products and the unit. The resolution-naturality node compares a commuting augmentation square already in the derived category; this is exactly the central-action resolution square. The continuous-subquotient node assumes a profinite group and gives the usual E-topologies; these are the hypotheses of the exactness child. The finite-dimensional continuity lemma requires complete, nontrivially valued E, which a finite ell-adic extension is; it is never applied over Omega. After extending a selected E-splitting, continuity over Omega is the explicit finite-matrix calculation in the retained proof. The induction child retains both strict dimension inequalities and invariance of ker(T_i-1) under all commuting action operators.

Small cases checked: W=0 and r=0 in both the trivial and criterion statements; r=1 trivial rank one, where restriction sends the single coordinate class to the integer coordinate; a nontrivial one-dimensional character, where an invertible T_i-1 gives vanishing; a two-dimensional unipotent Jordan block, where the kernel and quotient are both one-dimensional. For central vanishing, z=1 gives the identity assertion and the invertibility hypothesis forces N=0; for the trivial group the statement does not force arbitrary coefficients to vanish. For exactness, U=0, U=V and a nonsplit equivariant extension still have a nonequivariant underlying matrix splitting, so no representation semisimplicity is being assumed. For the criterion at r=0, every representation is trivial and condition (ii) is vacuous; no generator is selected from an empty set. Neither the representation induction nor continuous splitting assumes completeness of Omega or simultaneous diagonalization.

The requested correction is substantive: four new independently claimable obligations replace the four approximately 1000-character arguments. Their statements and all old proofs are retained for the next workers; the parent's proof is 2458 characters and its longest step is below 2000. The initial report-heading diagnostic is repaired by this fresh signed review. The prior NP review is kept as history, not passed off as a Q62 review. There is no unsatisfied mathematical point in the return; the new children intentionally remain unsplit for parallel work.

## What could not be finished

Proving the four children is deliberately left to their subsequent workers, as required by this re-split instruction. The inherited analytic exterior calculation remains a visible existing unsplit obligation. No task within the requested one-level repair is left incomplete.

## Validation

The prescribed dry run is executed after this report and citations are written; its terminal output records check_dag, review_split and preflight. The final push is executed only after the dry run exits successfully. No local substitute for the server checks is run.

## Retained prior report (NP, historical)

The following report predates Q62's re-split and refers to the earlier delivery's three new nodes, now existing dependencies. Its searches and review are preserved verbatim; its seven-step plan is superseded by the repair above.

# Worker report: lem-sfb-dense-lattice-derived-invariants-comparison

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-dense-lattice-derived-invariants-comparison.json`: item, split; statement unchanged, seven proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-condensed-derived-restriction-calculus.json`: statement, unsplit; no Mathlib match. Formal action-category, derived restriction, scalar and cup-product infrastructure; no analytic comparison assertion.
- `dag/nodes/sec-six-functors-basics/lem-sfb-trivial-ladic-derived-exterior.json`: statement, unsplit; no Mathlib match. The specified derived coordinate-cup morphism for the trivial coefficient module is an isomorphism. This is the remaining analytic obligation, explicitly all-continuous for the noncomplete algebraic closure.
- `dag/nodes/sec-six-functors-basics/lem-sfb-discrete-lattice-cup-exterior.json`: statement, unsplit; no Mathlib match. The algebraic coordinate-cup normalization for trivial discrete-lattice invariants over any condensed ring.

`citations.json` contains literal statement quotations for every citation in every item step. Searches are preserved in `searches.jsonl`; full newly run results are in `search-results.json`. No Lean, repository, launcher, unit or chapter file was written.

## Attachments

None. Searches of the project's `lean/WeilConjectures/` by the exact blueprint tag, dense-lattice wording, continuous invariants, and related cohomology notions found no declaration stating this item. The discrete-invariants/continuous-cohomology comparison is for discrete coefficients and does not give this statement. No Mathlib hit gives the derived internal-module comparison.

## WANTED

WANTED: an exact reference or proof for the trivial-representation derived coordinate-cup exterior calculation with all-continuous noncomplete norm-topological algebraic-closure coefficients, for `lem-sfb-trivial-ladic-derived-exterior`. In particular, neither a complete Banach-space theorem nor a sequential closed-embedding colimit statement settles this obligation.

WANTED: an exact ordinary internal condensed-ring reference for the combined normalized restriction/scalar/cup calculus, for `lem-sfb-condensed-derived-restriction-calculus`. The formal ingredients have standard injective-resolution proofs, but the cited blueprint supplies none of this package.

WANTED: an exact internal-module reference for the coordinate-cup normalization of the discrete lattice Koszul calculation, for `lem-sfb-discrete-lattice-cup-exterior`.

I read Bhatt–Scholze, *The pro-étale topology for schemes*, §4.3, especially Definition 4.3.1 and Lemmas 4.3.8–4.3.11, in the obtained arXiv-1309.1198 PDF. These give classifying-topos context and conditional comparison with continuous cohomology; I did not claim they prove the analytic obligation. The hypotheses in Lemma 4.3.9 do not license replacing the topology of Omega by a union topology. I also inspected the Stacks source at Tag 013P, `derived.tex`, `lemma-morphisms-lift`, and Tag 0156, `section-right-derived-functor`, including `lemma-injective-acyclic`. These concern formal resolution computations, not the noncomplete coefficient calculation. I consulted the abstract of Emma Brink, *Condensed Group Cohomology*, arXiv:2512.03648 (https://arxiv.org/abs/2512.03648), only to check scope: its advertised solid-coefficient comparison is not the requested all-continuous analytic theorem. No new literature was downloaded and no SGA source was used.

## What was wrong or missing

The imported item had an empty proof and advertised its exact analytic reference as WANTED. Its mathematical statement is retained verbatim. Its unit record comes from the older six-functors unit, while the item's actual source is main-20261015, paragraph (3) of `sk-thm-sf-ctf-stability-direct-images.proof.md`; I read both the unit/chapter records and that current source, and follow the latter's open-direct-image/tame-boundary route. The current paragraph is context for this analytic input, not a proof of it. The proof origin is therefore honestly `agent`.

The ancestor command returns `None`. I retained the inherited null `blueprint.from.node` and complete inherited via chain, filled the precise places of the new inputs, and searched the whole blueprint. I did not invent an ancestor or edit someone else's metadata.

A tempting but invalid shortcut is to replace every derived internal Hom in `lem-sfb-condensed-derived-invariant-bar` by an underived continuous-function object. Its statement explicitly forbids this substitution. Likewise the discrete finite-coefficient procyclic node has the wrong coefficient category. The split instead isolates a smaller analytic statement on the trivial module and carries the finite-dimensional representation argument itself.

## Proof and why this is a split

For trivial coefficients, restriction sends each continuous coordinate character to the integer coordinate character, and preserves every ordered cup product. Hence it identifies two explicitly specified derived maps out of the same finite zero-differential exterior complex. Their invertibility gives the comparison on trivial representations.

For a general continuous E-representation, induct on its E-dimension. Put A_i=T_i-1. If some A_i is invertible, the central element acts as identity on invariants of an equivariant injective resolution, so the derived image of A_i is both zero and invertible. Both derived-invariant objects vanish. If all A_i vanish, density makes the action trivial. Otherwise a nonzero singular A_i has a nonzero proper kernel U, stable under the entire commuting action. The representations U and V/U have strictly smaller dimension. Their underlying finite-dimensional exact sequence remains exact on all continuous F-valued sections (a linear matrix splitting works even for noncomplete F=Omega). The normalized restriction transformation is a morphism of the resulting distinguished triangles, so the existing triangle two-out-of-three theorem finishes the induction.

The new analytic node does not restate the original comparison: it has no D, no restriction morphism and no nontrivial representation; it computes one fixed trivial-coefficient derived object with specified cup classes. The formal node has no dense-lattice isomorphism claim. The discrete node has no L or analytic coefficients and computes the cup-normalized lattice object over an arbitrary condensed ring. No new node carries the general representation argument; steps 4–6 carry it. Every new node is statement-only. No proof step exceeds 2,000 characters.

## Not duplicates

lem-sfb-condensed-derived-restriction-calculus vs lem-sfb-condensed-product-action-inflation: the latter gives categories and inflation adjunctions only for profinite product projections; the new statement handles restriction along general continuous homomorphisms including discrete-to-profinite maps, the derived restriction transformation, scalar pasting, and cup/character normalization.

lem-sfb-condensed-derived-restriction-calculus vs lem-sfb-condensed-derived-invariant-bar: the existing node gives a derived bar model for profinite groups, not the formal action/restriction/scalar/cup calculus for topological groups including the discrete lattice. Its derived internal Hom terms are not assumed acyclic here.

lem-sfb-condensed-derived-restriction-calculus vs lem-sfb-condensed-product-bar-comparison: product factorization of profinite actions and diagonal-to-iterated totalizations do not give group restriction to a dense discrete subgroup or the cup/character statements.

lem-sfb-condensed-derived-restriction-calculus vs lem-sfb-derived-composition-adjunction-normalization: the existing node derives an isomorphism conjugate to an isomorphism between composites of exact left adjoints. It does not construct the noninvertible-in-general group restriction mate or the internal cup products used here.

lem-sfb-trivial-ladic-derived-exterior vs lem-exc-procyclic-two-term: the latter assumes finite ell-primary discrete coefficients and uses continuous group cohomology; the new node computes an ordinary derived internal condensed-module object for trivial all-continuous E/Omega, with specified coordinate-cup maps, for every r.

lem-sfb-trivial-ladic-derived-exterior vs lem-sfb-tame-inertia-continuous-koszul: the latter is an ancestor which uses this item's comparison for nontrivial representations after prime-to-ell reduction. It cannot be cited downward without a cycle; the new analytic input is only the trivial-representation calculation and has no prime-to-ell group.

lem-sfb-trivial-ladic-derived-exterior vs lem-per-strict-local-snc-kummer-cohomology: the existing node computes etale F_ell cohomology of an algebraic punctured strictly henselian local scheme; it makes no statement about these internal condensed norm-topological coefficient modules.

lem-sfb-discrete-lattice-cup-exterior vs lem-sfb-discrete-lattice-koszul-resolution: the existing Koszul node gives an isomorphism normalized only in degree zero, natural in maps and coefficient restriction. It does not identify degree-one coordinate characters or their ordered cup products with its exterior basis, which is essential for proving that the canonical restriction morphism is invertible. The new node supplies that derived cup normalization, for trivial coefficients only, over arbitrary condensed R.

The DAG searches included tags, coordinate-character/exterior/cup/Koszul wording, central actions and derived restrictions across all nodes. Whole-blueprint searches included `dense lattice`, `procyclic`, `continuous cohomology`, `Fitting`, `Hochschild`, `Breen`, `exterior`, `cup product`, `derived invariants`, `trivial coefficients`, `coordinate characters`, and `restriction calculus`. No identical imported blueprint statement was found. The new nodes cite no Stacks tag as their source, since no Stacks tag states them; there is no same-tag new-node collision.

## Mathlib assessment

For each new node I ran LeanFinder twice with genuinely different formulations, Loogle, LeanSearch, and the prescribed grep command. All services answered in this pass. Every recorded query is exactly a query in the tool log. Full outputs were read, not inferred from the service status.

I inspected Mathlib's `Condensed/Module.lean`: `CondensedMod R` is a sheaf of modules over an ordinary ring, not this internal condensed-ring group-action calculus. I inspected `RepresentationTheory/Homological/GroupCohomology/Basic.lean`: its objects are ordinary Rep, its derived-isomorphism upgrade and profinite cohomology are TODOs. The finite cyclic resolutions do not treat the infinite lattice in internal module objects. The `rightDerived`/`CommShift` hits are relevant formal infrastructure, but not a one-line specialization giving the complete normalized group-action/scalar/cup statement; `Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus.lean` itself notes the triangulated upgrade as TODO. Continuous-cohomology degree-zero results compute another category and only one degree. Mahler-equivalence and period-ring completions do not identify the requested derived objects. Consequently no new Mathlib leaf is asserted.

## Review by NP

I opened the exact current blueprint paragraph (3), the chapter and unit records, the three new node files, the unchanged item statement, and the complete statements of every node used in the proof. The blueprint gives only the tame-boundary context. The three new inputs are explicitly agent-formulated WANTED obligations, not misattributed to a Stacks tag or to Bhatt–Scholze. I checked B–E of delivery-errors in full: new nodes introduce their own rings, sites, groups, actions, derived categories and specified maps, have no proof sketches in the statement, carry real searches, and do not point back to the item.

Step 1 takes precisely the canonical restriction construction, exactness and shift compatibility from the new calculus. Step 2 takes only the definition of being fixed after every profinite base change from `def-sfb-condensed-action-module`; its density proof is explicit, including parameterized group elements rather than just global points. The Hausdorff hypothesis is satisfied by both norm-topological fields. Step 3 reads the actual derived morphisms in the two exterior nodes and the unit/cup/character compatibility in the calculus. The coordinate equality a_i(iota(n))=n_i is written out, so this is not an inference from arbitrarily chosen cohomology isomorphisms. Finite direct sums suffice; no tensor-product flatness or infinite-product preservation is assumed.

In step 4 I checked the resolution-naturality statement: it says the normalized comparison commutes already in the derived category with a commuting augmentation square. The central action gives exactly such a square on the chosen resolution. The termwise invariants force its image to be the identity. Thus subtracting the identity gives zero, and functoriality sends an invertible difference to an isomorphism. This is an explicit short calculation from the cited statements, marked elementary, not an uncited general vanishing theorem.

For step 5 I checked the subquotient lemma's actual profinite-group and continuous finite-dimensional E hypotheses, all satisfied by L. The continuity lemma is applied over complete E only, never over Omega. After scalar extension, continuity of each finite matrix and of the chosen inverse follows from finite sums/products in the given topological field. The underlying exact sequence is sectionwise split; equivariance of the splitting is not required. I corrected the formal node to explicitly state that kernels and cokernels are formed on underlying modules, so the step does not take that claim from a mere action definition. In step 6 the induction is on E-dimension, with a zero base, a trivial-action case and both strict dimension inequalities written down. The kernel is invariant under L because it commutes with T_i. I opened `lem-sf-triangle-two-out-of-three` and verified that the calculus supplies exactly its naturality and shift hypotheses, including the connecting square. It is used as a generic tool, declared in split_report.

Step 7 uses the calculus's exact coefficient-pasting equation with the specified coefficient map f(v)=1 tensor v. Both actions are the extension of the same E-matrices, so f is equivariant. The proof of invertibility does not define b, so no noncanonical subspace or basis choice enters the naturality clause. The r=0 clause follows from the normalized identity group map, not from a rank-only cohomology count.

Small cases: V=0 gives zero on both sides; r=0 gives V_F[0]; trivial V=E gives the empty and degree-one coordinate classes for r=1; a nontrivial one-dimensional character with T-1 invertible gives zero; a two-dimensional unipotent Jordan block uses its one-dimensional kernel and quotient and tests the singular induction branch. For the discrete cup node, r=0 and the zero ring give identities of the corresponding zero/regular objects, and r=2 has two ordered degree-one classes and one degree-two summand (no division by 2, so characteristic 2 is included). The analytic node's r=1 statement is a genuine remaining obligation, not deduced from completeness; no explicit counterexample is known from this review, and it stays unsplit. For the calculus I tested the identity homomorphism, the trivial group, and a noninjective group map: the canonical comparison need not be invertible, and the node does not assert it is.

All off-unit uses are generic tools and listed in the item's split_report.tool_uses. No target, unit route, statement clause or coefficient topology was weakened. There is no STATEMENT-DISPUTED correction, because I found no counterexample to the item itself. The mathematical work completed is its one-level split, not closure of its unsplit analytic descendants.

## What could not be finished

No unfinished work within the requested one-level split. Proving the three new statement-only obligations is subsequent stage-1 work; in particular the all-continuous noncomplete trivial-coefficient calculation remains visible as WANTED rather than being asserted as already proved.

## Validation

The server review_split check passed on the sandbox proof. The required full delivery dry run and final delivery are run after this report is written; their output is the delivery record.
