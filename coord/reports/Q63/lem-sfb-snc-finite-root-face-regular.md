# Q63 returned-delivery repair: lem-sfb-snc-finite-root-face-regular

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-snc-finite-root-face-regular.json`: unchanged statement, four-step proof assembling current DAG statements and explicit face/localization maps.
- `citations.json`: one verbatim current-statement quote per citation occurrence.
- `report.md`: this repair and the complete original seven-step argument below.

There are zero new nodes and zero new Mathlib leaves. The two earlier proposals are preserved under `retained-superseded-nodes/` outside the delivery's DAG, and the earlier report in `prior-report.md`. The actual `searches.jsonl` is unchanged and retained.

## Attachments

None. The blueprint-tag and concept search in `lean/WeilConjectures/` found no complete attachment. I read `lean/Sheaf/AlgebraicGeometry/SNCFiniteRootFaceRegular.lean`: its `AlgebraicGeometry.isRegularRing_snc_finiteRoot_face` ends in `sorry` at the conclusion, so it is not a finished attachment. No Lean was written and no compiler was run.

## WANTED

None.

## Return repaired and current DAG comparison

The return at branch head `da87fbd28c4` says the independent reader approved the delivery, but landing refused the side completion and requests rebasing on the current DAG and rereading changed citations. The delivery tool constructs its commit on current `origin/sheaf-dag`; no worker git command is used. The retained `returned-node.json` and the current repository parent are identical, including the original seven-step proof and statement. The released stage-1 repair note still requires the work to be spread into independently available tasks and the parent assembly below 3000 characters.

The required initial dry run now found newly landed shared-tag nodes, including Q64's `lem-sfb-snc-root-local-presentation` and `lem-sfb-transverse-local-root-family-regular`. I read all four newly reported candidates in full, not just their tags. The current `lem-sfb-snc-finite-root-regular-ring` review explicitly asks this face item to reuse the two Q64 nodes. Its algebra node already states the all-strata/all-partial-root regularity and monomial basis needed here. Its geometry node already supplies Noetherianity and all local coefficient strata. Keeping our overlapping proposals would duplicate those tasks. I removed them from the delivery and substituted the existing nodes; the extra coefficient-quotient and presentation maps in our proposals are explicit elementary maps in the parent or in the retained original argument, not lost claims. This is a substantive repaired split, not an unchanged repush.

The gate explicitly counts previously landed cited tasks for the human re-split order. Both Q64 nodes were created for the same re-split campaign and are directly cited here. Thus the work remains distributed into two statement-only nodes, already available in the current DAG, without creating duplicates. Source and statement dependencies, blueprint fields, searches and maintainer-owned metadata of the parent are retained. Its old tool-use metadata is maintainer-owned and therefore left untouched, although this assembly no longer uses those generic algebra tools directly.

## Sources and searches retained

I reread ILO, Expose IX Proposition 2.1 proof, printed pp.133-134 (the displayed simultaneous root algebra before invariants), and Expose VIII Remark 4.2.2(i)-(iii), printed pp.118-119 (the regular-intersection criterion and the necessary codimension condition). I read Stacks Tag 0BIA, `etale.tex`, label `lemma-strict-normal-crossings`, including the local-ring dimension discussion; and Tag 07PF, `more-algebra.tex`, label `lemma-quotient-regular`. ILO leaves the root regularity details implicit, so the agent proof origin is retained. No prohibited source route is used.

All previous actual Mathlib searches, their returned declarations and unavailable LeanSearch responses remain in `searches.jsonl` and in `prior-report.md`; no unrun search was added. The retained results concern standard smooth/etale presentations, regular sequences and polynomial regularity, not this full face theorem. The parent statement and search question have not changed, so those searches were reused. Whole-blueprint searches for `root.*regular` and `coordinate face` returned no equivalent blueprint node. Current DAG shared-tag searches found the Q64 tasks now reused, together with the labelled-root and root-stage nodes distinguished below. No new statement was created, hence no new Mathlib search was necessary.

## Review by Q63

I checked this repair against delivery-errors B-E with the current source statements open. The original statement has not changed: the branch equations describe distinct reduced irreducible components, n is positive and invertible, and all coordinate faces, including empty and disconnected ones, are included. The extractions previously proposed are superseded by existing tasks, rather than hidden behind differently named duplicates.

Step 1 uses the stated universal property of `def-weil-pbc-mv-polynomial-ring`. The maps kill exactly the J coordinates and impose exactly t_j=0 because n>0; inverse maps fix all coefficients and surviving roots. This is an elementary presentation argument, with no assumption that the stratum is irreducible or nonempty.

Step 2 uses `lem-sfb-snc-root-local-presentation` for A Noetherian and for every localized coefficient stratum with its exact dimension equality and unit equations. That node quantifies over every prime p of A, so it applies to the contraction of a prime of the face E, even though E is not the full cover. It does not assert a face localization comparison, and this proof does not take one from it. The second citation `lem-weil-pbc-finite-type-algebra-noetherian` gives E Noetherian from its actual finite polynomial quotient of A. J is contained in S because each t_j is zero in E. All hypotheses are those of the unchanged parent.

Step 3 uses `lem-sfb-transverse-local-root-family-regular`, whose statement quantifies over all J subsets of S and K disjoint from J, not only the full root family. The chosen K is I minus J. The maximal-ideal index set is the same S because t_i/1 lies in pA_p exactly when t_i lies in p; n maps with its inverse to a unit. Hence it gives precisely the regularity and prime-local regularity of B needed here, under every stated hypothesis. It introduces no henselianity, roots of unity, or field hypothesis.

Step 4 proves the face localization comparison itself by mutually inverse coefficient/root/fraction maps. It uses no comparison hidden inside a cited proof. All denominators from A outside p lie outside q by contraction, and further localization therefore gives E_q isomorphic to B_Q. `def-weil-regular-scheme` states exactly the Noetherian-plus-all-prime-localizations criterion used for E. Ring isomorphisms transport these defining properties. This is elementary assembly after the algebra theorem, not a new regularity theorem smuggled into an elementary step.

I also reopened the thirteen current statements cited by the original seven-step proof. They still supply the affine Noetherianity, quotient/stalk localizations, monic bases, regular-local localization and domain property, single-root regularity at the root, and localization/polynomial/unit-derivative regularity used in the retained induction. Those arguments are assigned to the two existing Q64 tasks as below, and are preserved verbatim for their workers. I reread the newly flagged labelled-root geometry and root-stage statements: both impose positive-characteristic geometric assumptions absent here and neither supplies all the abstract local-stratum data or arbitrary faces. They cannot replace the generic algebra task.

Small cases: with r=0 all presentations reduce to A; with J empty they give the full cover; with J=I they give the ordinary SNC intersection; n=1 gives the same intersection without extra roots. For A=0 or an empty stratum there are no primes, and the presentation is the zero ring. For disjoint branches the same zero case applies. Disconnected intersections are treated prime by prime; for example s and s-t(t-1) in k[s,t] give the two reduced intersection points. For transverse parameters s,t in k[s,t] and invertible n, the full root ring and its faces have the expected polynomial presentations. Nontransverse repeated parameters and three lines through a plane point fail the exact dimension hypothesis of the cited family theorem. No statement dispute or hypothesis correction is needed.

Every cited statement has been read, and each citation occurrence has a verbatim quote in citations.json. Both reused tasks have empty proof dependencies and definition-only statement dependencies, so this replacement introduces no cycle. The proof has no step exceeding 2000 characters and stays under 3000 total. There are no new nodes requiring additional search or source checks. This is the worker's direct self-review; the maintainer supplies independent review.

## Not duplicates

The following pairs document why earlier proposals were removed, rather than asserting artificial distinctions.

lem-sfb-stratified-parameter-root-regular vs lem-sfb-transverse-local-root-family-regular: the existing node already gives the all-strata partial-root regularity and free basis needed by the parent; the proposed node was removed, and the existing node is cited. Its extra generator-preserving presentation comparisons are explicit maps in the retained original argument.

lem-sfb-snc-root-face-local-model vs lem-sfb-snc-root-local-presentation: the existing node gives A Noetherian, all coefficient strata and unit equations at every p. Its full-cover localization comparison does not assert the face comparison; the parent now writes the additional elementary face and fraction maps explicitly. The proposed node was removed and the existing statement is reused only for what it says.

lem-sfb-snc-root-face-local-model vs lem-sfb-snc-labelled-root-algebra-geometry: the latter assumes a positive-characteristic field and states full labelled-cover geometry, not arbitrary face presentations over an arbitrary regular base. The removed proposal is unnecessary after the existing local-presentation lemma and explicit face maps.

lem-sfb-snc-root-face-local-model vs lem-sfb-snc-root-stage-system: the latter assumes a finite-type positive-characteristic chart and supplies a root-stage/Cartier/base-change package, not the arbitrary-base local coefficient-stratum theorem. The removed proposal is unnecessary after the cited generic local-presentation statement.

lem-sfb-stratified-parameter-root-regular vs lem-sfb-snc-labelled-root-algebra-geometry: the latter's field/geometric hypotheses exclude the abstract regular-local setting needed here. Our duplicate algebra proposal was removed in favor of the generic existing transverse-local-root theorem.

## Work retained and unfinished work

Original steps 1, 2 and 7 are now carried by the existing geometric local-presentation task together with the elementary face and fraction maps in this parent. Original steps 3-6 are the existing transverse local-root-family task. The latter statement includes every coefficient stratum and partial root subset, so it retains the simultaneous induction claim, both prime cases and the monomial-basis input. No part of the original argument was discarded; the entire original proof follows verbatim. The two tasks intentionally remain unsplit for their own workers; no required repair work remains beyond delivery validation.

## Retained original argument, verbatim


The following is the exact text of every returned proof step; the ownership map above specifies its new task. These are planning material for the new workers, not proof steps placed in the unsplit node files.

### Original step 1

Fix $J\subseteq I=\{1,\ldots,r\}$ and write $E_J=C_n/(x_j:j\in J)$. Setting precisely these variables to zero gives an isomorphism
$$E_J\cong (A/(t_j:j\in J))[x_i:i\in I\setminus J]/(x_i^n-\bar t_i:i\in I\setminus J).$$
The forward map sends coefficients to their quotient classes, sends each killed coordinate to zero and fixes every remaining coordinate; the reverse map sends coefficients and remaining coordinates to their classes in $E_J$. The root relations for $j\in J$ impose exactly $t_j=0$, since $n>0$, and both composites fix all generators. The affine regular scheme $X$ is locally Noetherian by [def-weil-regular-scheme], so $A$ is Noetherian by [pqf-lem-affine-open-locnoeth]. The finite polynomial presentation makes $E_J$ Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian].

Uses: def-weil-regular-scheme, pqf-lem-affine-open-locnoeth, lem-weil-pbc-finite-type-algebra-noetherian.

### Original step 2

Fix a prime $q$ of $E_J$ and put $p=q\cap A$, $R=A_p$, $S=\{i\in I:t_i\in p\}$ and $d=\dim R$. The root relations give $J\subseteq S$. For every $L\subseteq S$, put $R_L=R/(t_l:l\in L)$. The scheme-theoretic intersection of these branches contains $p$; by [def-trf-strict-normal-crossings-boundary] its local ring at $p$ is regular local and has dimension $d-|L|$, meaning $\dim R_L+|L|=d$. This stalk is indeed $R_L$: [lem-weil-pbc-affine-open-stalk-localization] identifies the affine stalks with prime localizations, and [lem-weil-pbc-localization-at-prime-of-quotient] identifies the localized quotient with $A_p/(t_l:l\in L)A_p$, sending every coefficient and surviving $t_i$ to its indicated image. For $L=\varnothing$ this gives $R$ regular local. If $i\notin S$, then $t_i$ is a unit in $R$ and in every $R_L$.

Uses: def-trf-strict-normal-crossings-boundary, lem-weil-pbc-affine-open-stalk-localization, lem-weil-pbc-localization-at-prime-of-quotient.

### Original step 3

For every $L\subseteq S$ and $K\subseteq I\setminus L$, define
$$B_{L,K}=R_L[x_i:i\in K]/(x_i^n-t_i:i\in K).$$
We prove simultaneously for all such $L$ and $K$ that $B_{L,K}$ is regular, by induction on $|K|$. Every ring displayed is Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian]. Iterating [lem-weil-pbc-monic-quotient-free] gives the free $R_L$-basis $\prod_{i\in K}x_i^{a_i}$ with $0\leq a_i<n$. The iterated one-variable presentation agrees with the displayed presentation in any order: maps fixing coefficients and taking each coordinate to its namesake are well defined on the root relations and are inverse on the generators. For $K=\varnothing$, $B_{L,K}=R_L$ is regular by step 2 and [lem-weil-pbc-regular-local-localization]. This proves the induction base for every $L$.

Uses: lem-weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-monic-quotient-free, lem-weil-pbc-regular-local-localization.

### Original step 4

Assume the induction claim for fewer than $|K|>0$ roots and choose $i\in K$. Put $K'=K\setminus\{i\}$, $D=B_{L,K'}$ and $B=D[T]/(T^n-t_i)=B_{L,K}$, with root $u$. The induction hypothesis makes $D$ regular. Let $Q$ be a prime of $B$ containing $u$. Since $t_i=u^n$, an index $i\notin S$ would make $u$ a unit, a contradiction. Thus $i\in S\setminus L$. The image of $t_i$ in $R_L$ is nonzero: otherwise $R_{L\cup\{i\}}=R_L$, contradicting the dimension equalities $\dim R_L+|L|=d$ and $\dim R_{L\cup\{i\}}+|L|+1=d$ from step 2. The regular local ring $R_L$ is a domain by [lem-sc-regular-local-domain], so multiplication by $t_i$ is injective on $R_L$. It is injective on the free $R_L$-module $D$ as well, coefficient by coefficient in the monomial basis of step 3.

Uses: lem-sc-regular-local-domain.

### Original step 5

Quotienting $D$ by $t_i$ gives $D/(t_i)\cong B_{L\cup\{i\},K'}$. Explicitly, send coefficients from $R_L$ to $R_{L\cup\{i\}}$ and fix the root coordinates; conversely send those quotient coefficients and coordinates into $D/(t_i)$. These are inverse on generators, since the relations on both sides are precisely $t_i=0$ and $x_k^n=t_k$ for $k\in K'$. This is also the coefficient-quotient compatibility in [lem-weil-pbc-monic-quotient-free], iterated over $K'$. By the induction hypothesis this quotient is regular: its root set has size $|K'|<|K|$. Therefore [lem-sbc-root-algebra-regular-at-root] applies with base $D$, equation $t_i$, positive exponent $n$ and prime $Q$ containing $u$. Its Noetherian hypothesis is step 3, its injective-multiplication hypothesis is step 4, and its regular-quotient hypothesis is the preceding induction application. It gives $B_Q$ regular local.

Uses: lem-weil-pbc-monic-quotient-free, lem-sbc-root-algebra-regular-at-root.

### Original step 6

For a prime $Q$ of $B$ not containing $u$, primality and $t_i=u^n$ give $t_i\notin Q$. Set $F=D[1/t_i]$. It is regular by [lem-weil-pbc-localization-of-regular-ring], and $F[T]$ is regular by [lem-trf-polynomial-ring-regular-base]. In $F[T]/(T^n-t_i)$ the class of $T$ is invertible, with inverse $T^{n-1}/t_i$. The image of $n$ remains a unit, since it was a unit in $A$. The derivation $\partial/\partial T$ sends $T^n-t_i$ to $nT^{n-1}$, whose image is thus a unit. By [lem-weil-pbc-hypersurface-derivation-regular], the ring $F[T]/(T^n-t_i)$ is regular. It is $B[1/t_i]$, by maps fixing $D$ and the root coordinate. The prime $Q$ extends to it, and its prime localization is $B_Q$: the inverse fraction maps exist because $t_i$ is already a unit in $B_Q$. Hence $B_Q$ is regular local. Steps 5 and 6 cover every prime of the Noetherian ring $B$, proving the induction step simultaneously for every $L$.

Uses: lem-weil-pbc-localization-of-regular-ring, lem-trf-polynomial-ring-regular-base, lem-weil-pbc-hypersurface-derivation-regular.

### Original step 7

Apply the completed induction with $L=J$ and $K=I\setminus J$. The ring $B_{J,I\setminus J}$ is $(A\setminus p)^{-1}E_J$: use the presentation of step 1 and send a coefficient $a/s$ to the corresponding localized coefficient and each surviving root to its localized class; the inverse evaluates polynomials in those fractions. Both maps respect every displayed relation and are inverse on generators. Every $s\in A\setminus p$ maps outside $q$, so localization further at the prime induced by $q$ gives $(E_J)_q$, with inverse maps on fractions fixing $E_J$. The induction therefore proves $(E_J)_q$ regular local for every prime $q$. Since $E_J$ is Noetherian by step 1, it is regular by [def-weil-regular-scheme]. Its affine spectrum is exactly the coordinate face in the statement, so that face is regular as well. If the intersection $V(t_j:j\in J)$ is empty, its quotient ring is zero and so is $E_J$ by step 1; it has no primes and the conclusion is vacuous. Disconnected intersections cause no change, since $q$ and $p$ were arbitrary. The cases $J=\varnothing$, $r=0$, $A=0$ and $n=1$ are included in the same presentations and induction base.

Uses: def-weil-regular-scheme.


## Delivery validation

The first current dry run exited 1 with shared-tag duplicate findings. Those findings are repaired by reuse of current Q64 statements and removal of both proposed new nodes. The final remote dry run and push follow this finalized report.
