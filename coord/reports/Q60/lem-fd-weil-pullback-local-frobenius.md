# Stage-1 repair report: lem-fd-weil-pullback-local-frobenius

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-fd-weil-pullback-local-frobenius.json: existing statement, repaired split; statement and statement dependencies unchanged.
- dag/nodes/sec-deligne-laumon-a1/lem-fd-rational-pullback-fibre-comparison.json: statement, unsplit; no exact Mathlib match. Constructs the rational derived fibre isomorphism, its scalar square, and common-stage descent.
- dag/nodes/sec-deligne-laumon-a1/lem-fd-pullback-weil-return-square.json: statement, unsplit; no exact Mathlib match. The morphism/return-transport square, iterated pullback Weil maps, their combination and coefficient compatibility.
- dag/nodes/sec-deligne-laumon-a1/lem-fd-rational-return-block-power.json: statement, unsplit; no exact Mathlib match. Block transport composition, the return recurrence, its power consequence and coefficient compatibility.
- report.md and citations.json are the delivery report and verbatim statement quotations. searches.jsonl is the search command's retained authentic log. Local repair scripts and original-proof.json are sandbox-only working records, not delivery files.

## Attachments

None. Read lean/Sheaf/Paper/WeilPullbackLocalFrobenius.lean: the actual fdWeilPullbackLocalFrobenius theorem still has a whole-proof sorry. Searches of lean/WeilConjectures for the item tag and the notion found no exact theorem on the framework common-stage category. In StalkUpperStar.lean, AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalkAt_of_upperStar is a concrete-category comparison, not an identification with the framework rationalized category. The related concrete stalk/charpoly results are reference material, not an exact attachment.

## WANTED

None. Sources used are present in the read-only repository.

## What was wrong and what changed

The released stage-1 repair note explicitly reopens this split despite the old reviewed and reviewed_lean records. Its sole numbered requirement is to distribute the 6314-character argument into at least two genuinely separate statement-only nodes, preserving the parent statement and route, and retaining at most 3000 characters of assembly. This repair adds three nodes of comparable statement size (2017, 2323, and 2041 characters). Each has status unsplit, proof [], proof_deps [], and proof_origin null. The parent proof now has five assembly steps, all below 2000 characters, totaling 2399 characters. It still carries the heart argument, the residue-field counting argument and the diagonal/eigenvalue calculation. The substantial derived comparison and two independent Frobenius calculations are separately available to future workers. There is no statement dispute and no statement correction.

The sandbox initially contained only dispatcher marker files, no prior report, searches or item copy. I copied the current repository item and compared its eight-step proof and module against the return entry. All pre-existing source, audit, blueprint, Lean and review metadata were retained. The delivery tool rebases split-owned changes over the server's current head and preserves maintainer-owned metadata.

## Review by Q60

I read the stage-1 brief, worker role, stage document, GOAL, SETUP's three blueprint levels, and delivery-errors B through E, including the duplicated historical copy. The chapter is sec-deligne-laumon-a1 and the unit is sk-p-dl-a1-some-weight. I read both records and the current main-20261015 proof lem-fd-realified-kernel-real.proof.md, especially Step 2's alpha^e lambda sentence. This is a local coefficient/Frobenius input to that same Fourier reality route; the unit and chapter are unchanged. No SGA source is used.

For all three new nodes I read that blueprint sentence and the entire old eight-step argument. I also read Deligne Weil II, printed pp. 150-151, (1.1.7)-(1.1.10): geometric Frobenius is the inverse of arithmetic Frobenius, acts on the fibre by transport, and the operator after a finite residue-field extension is a power. The precise rational construction is agent-written, not attributed verbatim to Deligne. For the fibre comparison I additionally read Stacks Tag 0D6D, sites-cohomology.tex, lemma-derived-pullback-composition, and Tag 099N, proetale.tex, lemma-pushforward-Noetherian-case, especially (2),(5). Those give the foundational derived/completed constructions; their simultaneous scalar normalization is taken from the existing realization node, whose full statement I read, not asserted to be a standalone Stacks theorem.

New node 1 introduces the two models, morphism, compatible geometric points, coefficients, point functors and the inverse composition map on the derived category. Its actual scalar square is typed from (J_z f^* M) tensor L to J_x,L(T_Y M). Identity and tower conditions are conclusions, not unstated assumptions. It has no heart or Weil assumption and no Frobenius conclusion, so it is neither the parent nor one of its clauses relabeled.

New node 2 introduces its own data and a positive common return length n; it assumes both scheme return equalities explicitly. I checked the types of c, beta, t and the two iterated Weil maps. The equation c_{G_Y^n M} J_z(beta_n) t_X = t_Y c has target J_x G_Y^n M, and its multiplication by the iterated structure gives c R_X = R_Y c in the derived point category. It does not identify the two closed-point degrees or raise eigenvalues. Its proof task is the two independent inductions/naturality computations of old Steps 4-5, including the factorwise scalar square from old Step 7.

New node 3 fixes one scheme, one point and one positive return length d, not a morphism f. Its block identity is stated with the associative identifications, its recurrence uses r >= 1, and its base case R_d is fixed by the definition. Thus the e = 1 case is literally the initial return and e >= 1 is the induction range; no zero-length transport is silently used. It includes the actual derived operator identity R_ed = R_d^e, not merely a trace equality or a per-degree comparison. Its scalar conjugacy is explicitly part of the statement. This is old Step 6 and its portion of Step 7, separate from node 2's morphism square.

I checked the five parent steps against the exact statements cited, opening every cited node:

1. lem-a1-constructible-pullback-t-exact states t-exactness on the precise E and common-stage categories and the degree-zero point-fibre clause. It applies to the base change f between finite-type k-schemes. lem-trf-integral-pullback-comparison-realization states associative/unital compositors, equality-of-morphisms compatibility, rationalization, no finite Tor restriction and scalar towers. def-weil-derived-pullback-tensor-hom specifies the actual stagewise operation on common-stage morphisms. These give the induced Weil structure as a composite of isomorphisms. I did not cite a definition as proof of a new comparison theorem.
2. lem-kun-closed-point-field(a) states BOTH implications: closed iff finite residue field over the base. The residue embedding is the one induced by the actual f_0. Since kappa(z) is finite-dimensional, its subfield kappa(x) is finite-dimensional; both models are finite type, so the reverse implication applies. Positivity follows from nonzero fields, the tower degree from concatenating field bases, and cardinality from counting coordinate tuples. This elementary counting argument stays written in the parent.
3. def-weil-algebraically-closed-coefficients explicitly identifies Hom as the directed common-field colimit and says representatives agree after enlargement. Finitely many arrows and the two inverse equations can therefore be represented simultaneously. New node 1 supplies the derived c with precisely its normalization and its scalar/identity/tower compatibility; no hidden comparison of coefficient categories is used.
4. New node 2's common return hypotheses hold with n = de by the residue degrees and the return convention of def-weil-local-frobenius-trace. New node 3 applies at x with d positive and e positive. Both use the same specified composition maps and transport normalization, so R_Y,n from node 2 is R_ed from node 3. The product of their equations gives c F_z = F_x^e c. Their explicit scalar statements, together with new node 1, prove equality in the common-stage category. def-weil-local-frobenius-trace defines exactly these returns and the local operators; lem-a1-constructible-pullback-t-exact supplies the heart-stalk identification after H^0. citations.json quotes the defining formulas and the substantive theorem clauses.
5. Retained the old diagonal argument in full. On an algebraically closed field, choose an eigenvector and induct on dimension on the invariant quotient to obtain a triangular basis. The diagonal of a product of upper triangular matrices is the product of the diagonals. Therefore the diagonal of the e-th power is alpha_i^e, the characteristic polynomial is the product of T minus diagonal entries, and a conjugate has the same polynomial. This is a finite-dimensional elementary matrix argument, and does not assume semisimplicity. The zero-dimensional case has empty multiset. Collisions alpha_i^e = alpha_j^e retain both entries.

I checked the new statements on the identity f, coefficient identity E = L, towers E subset L subset H, d = e = 1, zero sheaves, empty X_0 (no closed-point instances), and nonsemisimple matrices. The point-return equality is g^n bar{x} = bar{x} g_s^n, never g^n bar{x} = bar{x}. There is no finite Tor-amplitude hypothesis and no existence assumption for a Weil-stable integral lattice. No new lemma assumes a result of the parent, and no new statement depends on the parent; their created.item/blueprint ancestry is provenance only. New nodes have complete statements, not inline proof sketches. The three non-elementary statements all go beyond two-line consequences: derived/common-stage scalar descent, iterated morphism/transport coherence, and block-return power coherence. Their old arguments are preserved below for their future workers.

## Searches and duplicate audit

Ran the official msearch.py for each proposed node, with its own statement in mind: leanfinder, loogle, grep and leansearch, plus a second semantic phrasing. Read all 15 results. All services responded. Exact query texts and returned names are in the new nodes and authentic searches.jsonl; no unavailable service is described as no match. TopCat.Presheaf.stalkPullbackIso was read at Mathlib/Topology/Sheaves/Stalks.lean:335; it is for ordinary presheaves on topological spaces and does not give the rational derived point functor or its scalar square. The categorical pullbackComp hits concern slices/presheaves of modules, not these normalized completed pullbacks. The regular-category Frobenius hit is a reciprocity morphism. Ring Frobenius powers and Witt isocrystals do not state the rational Weil return identities. No new node is declared a Mathlib leaf.

Searched the whole DAG by statement keywords, common source and relevant Stacks tags, and the whole blueprint with blueprint_refs.py (including stalk pullback, Frobenius transport/power/return, return operator/power, scalar stalk, iterate Weil and pullback scalar). Read the closest statements below. There is no blueprint node with one of these complete statements, so same_as is []. The nearest blueprint ancestor is lem-fd-realified-kernel-real; each new from.place names its Step 2 sentence, and via contains lem-fd-weil-pullback-local-frobenius.

## Not duplicates

lem-fd-rational-pullback-fibre-comparison vs lem-trf-integral-pullback-comparison-realization: the existing node supplies coherent completed scheme pullbacks, not the composite with the point-sections functor and its common-stage derived fibre square.
lem-fd-rational-pullback-fibre-comparison vs lem-weil-point-sections-scalar-extension: the existing node gives scalar extension of sections at s, without a morphism f or the derived pullback fibre comparison.
lem-fd-rational-pullback-fibre-comparison vs lem-per-adic-normalized-fibre-comparisons: the existing node is on PBC coefficient categories and their hearts; the new node is the derived framework rationalized/common-stage comparison. No equivalence of those different coefficient categories is presumed.
lem-fd-rational-pullback-fibre-comparison vs lem-kun-stalk-as-pullback: the existing node identifies the meaning of stalk with inverse image, without the specified rational scalar/coherence equations.
lem-fd-rational-pullback-fibre-comparison vs lem-fd-common-stage-comparison-descent: the existing node descends equivalences BETWEEN framework and PBC coefficient systems assuming comparison data; it does not construct this within-framework geometric fibre comparison.
lem-fd-pullback-weil-return-square vs lem-weil-frobenius-point-transport-natural: the existing node is naturality at the base point s; it does not prove the morphism-f square or induction for the pulled-back Weil structure.
lem-fd-pullback-weil-return-square vs lem-fd-local-frobenius-weil-morphism-naturality: the existing node concerns morphisms of Weil objects on ONE scheme, without comparing geometric pullback along f across two schemes.
lem-fd-pullback-weil-return-square vs lem-fd-local-frobenius-coefficient-extension: the existing node proves a change-of-COEFFICIENT field square on one scheme, not a change-of-SCHEME square at a common return length.
lem-fd-pullback-weil-return-square vs lem-fd-frobenius-fixed-pair-comparison: the existing node assumes an equivalence between two coefficient systems and lifts it to fixed pairs; it does not state a scheme-morphism stalk return comparison.
lem-fd-rational-return-block-power vs lem-trf-frobenius-degree-formula: the existing node is a finite-coefficient trace identity for strict finite-Tor Weil complexes, not an actual rational/common-stage operator power on the full constructible domain.
lem-fd-rational-return-block-power vs lem-trf-fixed-point-stalk-transport-cocycle: the existing node concerns finite A and scheme-Frobenius fixed points; it does not assert rational/common-stage local Weil operator powers or scalar-field compatibility.
lem-fd-rational-return-block-power vs lem-trf-point-transport-composition: the existing node concerns a direct finite-ring point transport at s; the new node concerns rational iterated normalized returns at a point of Y and their composition with Weil maps.
lem-fd-rational-return-block-power vs lem-trf-compact-frobenius-transport-composition: the existing node is finite-coefficient compact-support cohomology with a chosen compactification; the new node is a local rational point operator with no compactification.
lem-fd-rational-return-block-power vs lem-zl-finite-compactification-stalk-return: the existing node is a jointly injective family of evaluation maps for a finite compactification and a pushforward; it does not state the standalone block recurrence for any rational Weil complex.
lem-fd-pullback-weil-return-square vs lem-fd-rational-return-block-power: the former compares two schemes at the same n, the latter compares return lengths on one scheme. Neither restates the parent, whose closed-image, heart, natural stalk isomorphism and eigenvalue clauses still require assembly.

## Preservation of every old argument

This is a complete verbatim archive of the returned proof, with the task that now owns each argument. It is not proof inside an unsplit node: the new nodes contain statements only. Future workers can use both this report and their node's complete statement.

### Old Step 1

Ownership: Retained in parent assembly Step 1.

Apply [lem-a1-constructible-pullback-t-exact] with $h=f$ and $\Lambda=\Qlb$. Its categories, standard heart and derived pullback are precisely those in the item, so $Lf^*\mathcal F$ lies in the constructible heart. The same statement applies at every finite coefficient-field stage and to geometric-point pullbacks. The canonical comparison $\beta_1:Lg_X^*Lf^*\xrightarrow{\sim}Lf^*Lg_Y^*$ comes from $fg_X=g_Yf$ and the composition isomorphisms of [lem-trf-integral-pullback-comparison-realization], rationalized and used stagewise as in [def-weil-derived-pullback-tensor-hom]. Thus the induced Weil structure is $\theta_X=Lf^*(\theta_Y)\beta_1$; it is an isomorphism, so this heart object is a Weil sheaf.

Existing statements used: lem-a1-constructible-pullback-t-exact, lem-trf-integral-pullback-comparison-realization, def-weil-derived-pullback-tensor-hom.

### Old Step 2

Ownership: Retained verbatim in parent assembly Step 2.

Let $z$ be closed and put $x=f_0(z)$. By [lem-kun-closed-point-field](a), $\kappa(z)$ is finite over $k_0$. The scheme morphism gives a $k_0$-embedding $\kappa(x)\hookrightarrow\kappa(z)$, so $\kappa(x)$ is also finite over $k_0$. The converse in that same criterion makes $x$ closed. Set $d=[\kappa(x):k_0]\geq1$ and $e=[\kappa(z):\kappa(x)]\geq1$. A basis in each field extension gives $[\kappa(z):k_0]=de$, and counting coordinate tuples in a basis gives $q_z=q^{de}=(q^d)^e=q_x^e$.

Existing statements used: lem-kun-closed-point-field.

### Old Step 3

Ownership: New lem-fd-rational-pullback-fibre-comparison; the common-field representation argument stays in parent Step 3.

Work over one finite coefficient field $E$ defining $M=\operatorname{For}\mathcal F$, its Weil isomorphism $\theta$ and its inverse. Such a stage exists: represent these finitely many arrows in the Hom colimits of [def-weil-algebraically-closed-coefficients], then enlarge until both inverse equations hold. Choose compatible points $\bar z:s\to X$ and $\bar x=f\bar z:s\to Y$. Write $J_z=\operatorname{Fib}_sL\bar z^*$ and $J_x=\operatorname{Fib}_sL\bar x^*$. The inverse of the composition isomorphism $L(f\bar z)^*\xrightarrow{\sim}L\bar z^*Lf^*$, followed by $\operatorname{Fib}_s$, is a natural isomorphism $c_M:J_zLf^*M\xrightarrow{\sim}J_xM$. Use the canonical families of [lem-trf-integral-pullback-comparison-realization]: they are defined for all derived-complete constructible objects without a finite Tor-amplitude condition, give composition isomorphisms after rationalization, and commute with scalar comparisons. Applying also [lem-weil-point-sections-scalar-extension] shows that $c_M$ commutes with finite coefficient extension, including its identity and tower identifications. Thus $c_M$ defines a natural $\Qlb$-linear comparison on the common-stage category. Its degree-zero map is the desired stalk isomorphism.

Existing statements used: def-weil-algebraically-closed-coefficients, lem-trf-integral-pullback-comparison-realization, lem-weil-point-sections-scalar-extension.

### Old Step 4

Ownership: New lem-fd-pullback-weil-return-square, transport-square clause.

Here is the Frobenius compatibility of this comparison at stage $E$. Put $G_Y=Lg_Y^*$ and $G_X=Lg_X^*$. For $n$ divisible by $de$, both points return: $g_X^n\bar z=\bar z g_s^n$ and $g_Y^n\bar x=\bar x g_s^n$. Let $t^X_{n,N}:J_zN\to J_zG_X^nN$ and $t^Y_{n,M}:J_xM\to J_xG_Y^nM$ be the point transports of [lem-trf-local-frobenius-transport-normalization]. Let $\beta_n:G_X^nLf^*\to Lf^*G_Y^n$ be the comparison from $fg_X^n=g_Y^nf$. Naturality of the iterated point transport applied to $L\bar z^*Lf^*M\cong L\bar x^*M$, followed by the associative composition identifications, gives
$$c_{G_Y^nM}\,J_z(\beta_n)\,t^X_{n,Lf^*M}=t^Y_{n,M}\,c_M.$$
The naturality used here is [lem-weil-frobenius-point-transport-natural](2), iterated $n$ times; the two rebracketings agree by [lem-trf-integral-pullback-comparison-realization]. This constructs the equation in the rational category itself, rather than importing a finite-ring stalk equation.

Existing statements used: lem-trf-local-frobenius-transport-normalization, lem-weil-frobenius-point-transport-natural, lem-trf-integral-pullback-comparison-realization.

### Old Step 5

Ownership: New lem-fd-pullback-weil-return-square, iterated-Weil and resulting-return clauses.

The induced iterated Weil structure is $\theta_X^{[n]}=Lf^*(\theta_Y^{[n]})\beta_n$: induct on $n$, substituting $\theta_X=Lf^*(\theta_Y)\beta_1$ and using naturality and associativity of the composition comparisons in [lem-trf-integral-pullback-comparison-realization]. For $n=de$, the preceding equation and naturality of $c$ for $\theta_Y^{[n]}$ therefore give
$$\begin{aligned}
c_MJ_z(\theta_X^{[n]})t^X_{n,Lf^*M}
&=J_x(\theta_Y^{[n]})c_{G_Y^nM}J_z(\beta_n)t^X_{n,Lf^*M}\\
&=J_x(\theta_Y^{[n]})t^Y_{n,M}c_M.
\end{aligned}$$
By [def-weil-local-frobenius-trace], the left operator is $c_MF_z$ and the right one is the $q^{de}$-return operator at $x$, followed by $c_M$.

Existing statements used: lem-trf-integral-pullback-comparison-realization, def-weil-local-frobenius-trace.

### Old Step 6

Ownership: New lem-fd-rational-return-block-power, block/recurrence/power clauses.

To identify that return operator, keep the point $\bar x$ fixed and put $J=J_x$, $G=G_Y$, $A=\theta_Y^{[d]}:G^dM\to M$, and $t_{rd,N}=t^Y_{rd,N}$. Splitting the defining list of $(r+1)d$ point transports after the first $rd$ entries gives
$$t_{(r+1)d,N}=t_{d,G^{rd}N}\,t_{rd,N}.$$
This equality uses the same return $g_Y^d\bar x=\bar xg_s^d$ and associative comparisons of [lem-trf-integral-pullback-comparison-realization]. Naturality of the $d$-fold transport [lem-weil-frobenius-point-transport-natural] gives $JG^d(\theta^{[rd]})t_{d,G^{rd}M}=t_{d,M}J(\theta^{[rd]})$. Since the definition of iterated Weil structure gives $\theta^{[(r+1)d]}=A\,G^d(\theta^{[rd]})$, we obtain
$$J(\theta^{[(r+1)d]})t_{(r+1)d,M}=(J(A)t_{d,M})(J(\theta^{[rd]})t_{rd,M}).$$
Starting with $r=1$, induction shows that the $ed$-return operator is $(J(A)t_{d,M})^e=F_x^e$, with exactly the geometric-Frobenius convention of [def-weil-local-frobenius-trace].

Existing statements used: lem-trf-integral-pullback-comparison-realization, lem-weil-frobenius-point-transport-natural, def-weil-local-frobenius-trace.

### Old Step 7

Ownership: Distributed factorwise: new fibre-comparison scalar square, new return-square scalar clauses, new block-power scalar clauses; common-stage equality and H^0 assembly in parent Step 4.

The equality just proved is compatible with change of the finite field $E$. Indeed the scalar/composition equation of [lem-trf-integral-pullback-comparison-realization] identifies the two scalar extensions of $c$ and $\beta_n$; the explicit scalar equation in [lem-trf-local-frobenius-transport-normalization] identifies those of $t_{n,M}$; and naturality identifies those of $\theta^{[n]}$. Consequently extension to any common larger field sends every factor in the displayed equations to its corresponding factor. With [lem-weil-point-sections-scalar-extension] these give the same $\Qlb$-linear equation on the common-stage fibres, independently of representatives:
$$c_{f,z}F_{z,f^*\mathcal F}=F_{x,\mathcal F}^{e}c_{f,z}.$$
Taking degree-zero cohomology is legitimate by the point-fibre clause of [lem-a1-constructible-pullback-t-exact].

Existing statements used: lem-trf-integral-pullback-comparison-realization, lem-trf-local-frobenius-transport-normalization, lem-weil-point-sections-scalar-extension, lem-a1-constructible-pullback-t-exact.

### Old Step 8

Ownership: Retained verbatim in parent assembly Step 5.

The two endomorphisms are conjugate after replacing $F_x$ by $F_x^e$. Over the algebraically closed coefficient field choose an upper triangular matrix for $F_x$. Its diagonal lists its eigenvalues with algebraic multiplicity; the diagonal of its $e$-th power lists their $e$-th powers, with repetitions retained even when distinct eigenvalues acquire the same power. Conjugation preserves the characteristic polynomial, proving the asserted multiset formula. The empty diagonal covers the zero sheaf.

Existing statements used: elementary finite-dimensional matrix calculation.

## Tools requested for review

The retained generic tools are lem-a1-constructible-pullback-t-exact (rational heart/fibre t-exactness), lem-kun-closed-point-field (finite-type residue-field criterion), and lem-trf-integral-pullback-comparison-realization (coherent coefficient construction). The newly extracted statements remain in this item's unit. The other old off-unit transport/scalar tools are now source material and statement inputs for the new unsplit nodes, rather than unquoted results hidden in parent steps. Existing maintainer tool_uses were left untouched; split_report lists the prior declarations for review.

## What remains unfinished

The three new nodes are intentionally unsplit, for independent workers to prove. Stage 1 for this parent is the short complete assembly using their statements, as explicitly ordered by the human. No Lean files were changed and no compiler, Lake or build tool ran. The required server dry run exited 0 and printed OK (not pushed) at cd6eaf302c1: preflight passed, including the DAG/split checks. The final report is submitted to the same checks before pushing. Three new nodes, zero Mathlib leaves.
