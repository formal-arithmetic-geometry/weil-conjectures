# Repair report: lem-trf-nodal-normalization-adjunction

## Files written

- dag/nodes/sec-trace-formula/lem-trf-nodal-normalization-adjunction.json: existing statement, split; unchanged statement, new short assembly.
- dag/nodes/sec-trace-formula/lem-trf-nodal-adjunction-preparation.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-split-node-component-normalization.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-completed-curve-boundary-geometry.json: statement, unsplit; no Mathlib match.

## Attachments

None. No declaration under lean/WeilConjectures states this item exactly. The existing declaration AlgebraicGeometry.nodal_normalization_adjunction in lean/Sheaf/AlgebraicGeometry/NodalNormalizationAdjunction.lean:153 ends in sorry, so it is not an attachment. The normalization source contains general normalization facts but none of the three complete new statements.

## Wanted sources

WANTED: literature/temkin-stable-modification-arXiv-0707.3953v3.pdf, §1.2(b), pp. 2–3, for lem-trf-nodal-normalization-adjunction. The PDF named by the historical source is absent locally. I used the available Stacks sources and kept proof_origin.by=agent. No download or repository edit was made.

## What was wrong and what changed

The return required work distribution, not a new mathematical route: eleven proof steps totalled 11138 characters. There were no retained JSON files, report or searches in this sandbox, only dispatcher brief markers. I recovered the complete split from the current read-only repository and retained its source, statement, metadata and historical search records. No statement or Lean signature is changed. Three new nodes are statement-only with empty proof/proof_deps, so future workers can start them independently; none depends on another new node or the parent.

The old proof is preserved verbatim below, with an explicit allocation. Adjunction preparation owns reducedness and old steps 2–3; branch algebra owns steps 4–6; completed-curve geometry owns normalization in step 1, step 7 and the Cartier-boundary part of step 8. The parent still performs the rational smooth-locus identification of step 8 and the actual local differential calculation, completed-lattice test and unique gluing of steps 9–11. No argument was removed by shortening its description.

## Unfinished work

The three new statements are intentionally unsplit; proving them is the parallel work requested by the human. All former proof arguments needed for their next split are preserved below. No unhandled mathematical objection to the parent statement was found.

## Review by Q94

I read Stacks curves.tex at lemma-2-branches-delta-1, remark-trivial-quadratic-extension, lemma-split-node (0CBW), lemma-nodal-lci (0C4E), lemma-facts-about-nodal-curves (0E37), and the full proof of lemma-closed-subscheme-nodal-curve (0E38). I read varieties.tex at normalization-same-after-completion (0C3V), normalize-noetherian-dim-1 (0C45), and the adjacent prepare-delta-invariant statement. For the adjunction calculation I read the existing formal-plane-adjunction-lattice statement and its proof, whose separate completed conormal comparison is the source of the formal compatibility; 0E9Z itself is not cited as a theorem asserting compatibility with completion. I checked the chapter and sk-i-curve-zero unit and the current local-term-locality proof: this is a re-split of the existing auxiliary algebraic geometry input and does not replace a unit step. No SGA source is used.

New adjunction preparation is the old reducedness/lci/Fitting argument: field flatness, finite presentation and quasi-separatedness of a Noetherian scheme, codimension n−1 regular sequences and geometric fibre dimension are all conclusions explicitly requested in its statement. It does not assume separatedness or properness. New branch algebra states both the concrete normalization and all completed maps needed downstream; faithful flatness prevents two different component primes from acquiring the same completed ideal. Its total quotient and product-of-component-normalizations assertions preserve the old monic-polynomial argument, not just the cardinality two. New completed-curve geometry is for an arbitrary marked integral proper curve with the two specified completed local types; it does not assume an ambient nodal scheme or an adjunction conclusion. It includes smoothness at marked regular points, nonsmoothness at the formal node, finiteness/properness/connectedness of normalization, and the reduced boundary ideal. These are different proof obligations of comparable size.

Parent step 1 uses exactly the new preparation statement for reducedness, the finite singular set and the smooth normalization of the adjunction line. Step 2 uses the branch statement for the explicit completed maps, the component partition and localization compatibility; its local rings are reduced essentially finite type and one-dimensional by step 1 and the nodal hypothesis. Step 3 applies completed-curve geometry to the finite set of ambient singular points on the proper reduced component; away from this set the smooth-normal node gives normality, uniqueness of the local component and equality with that component after deleting others. The partition required by that new statement is supplied by step 2. It produces the geometry and divisor without proving the adjunction clause.

Parent step 4 checks every hypothesis of formal-plane-adjunction-lattice: a reduced pure-dimensional finite-type lci affine chart from preparation, a closed node with residue k, a normalized branch DVR on the smooth normalization, the completed equation uv and one of the two maps from step 2. Its partial derivative is t on the relevant branch and is nonzero; no derivative is asserted invertible in k[[t]]. The comparison is with continuous formal differentials, never the whole algebraic differential module of k((t)). The divisor-line definition gives the inverse maximal ideal, and completion-regular-local explicitly says the completed maximal ideal is its extension. Thus the two compared lattices are identical under the same generic map. Parent step 5 uses the exact valuation decomposition and section injections in smooth-connected-curve-local-rings; the remaining stalk-unit and overlap argument is elementary and is written out. Every node in each uses list was opened; citations.json copies its statement verbatim, so no use takes a fact from a node's proof.

I tested the empty singular set (empty boundary and the usual smooth identification), a crossing of two components (one point on each normalization and a smooth component point), an irreducible self-node (two normalization points but one component), and characteristic two (the minus sign remains a unit). Nonproper/nonseparated ambient schemes cause no added assumption; only Z is proper. The new geometric node allows marked regular points, which is essential for ambient intersection nodes. I checked that none of the new nodes cites the parent in stmt_deps and that their only relationship to it is provenance. Every parent step is below 2000 characters; the total is recorded below.

## Mathlib searches and duplicate search evidence

The exact msearch.py calls and digests are in searches.jsonl; full hits are retained in mathlib-hits.txt. Each new node has two different LeanFinder phrasings, Loogle, source grep and LeanSearch. Two LeanSearch calls were rate-limited and are recorded unavailable. I read the returned signatures and the relevant Mathlib source: standard smoothness/cotangent criteria, integral-closure base change and relative normalization. NormalizationPullback under smooth base change is not smoothness of a normalized curve, and Weierstrass division is not the normalization of uv=0. No new node is a Mathlib leaf. The DAG/blueprint searches are retained in dag-blueprint-searches.txt; nodal, split-node and all relevant Stacks tags gave no blueprint duplicate. The normalization matches were general definitions/properties or constant-sheaf assertions, none the complete marked formal-geometry statement.

## Not duplicates

lem-trf-nodal-adjunction-preparation vs lem-sfb-nodal-family-regular-affine-presentations: the existing node assumes flatness, finite presentation and reduced nodal geometric fibres and produces regular affine presentations over a locally Noetherian base; preparation derives reducedness, flatness and finite presentation from field-curve completions, identifies the finite reduced Fitting singular scheme, and establishes the canonical adjunction line and smooth-locus identification, which the existing statement does not assert.

lem-trf-nodal-adjunction-preparation vs lem-trf-depth-fitting-quadratic-lci: the existing node starts with depth one and a specified Fitting stalk at a single maximal ideal and produces a quadratic completed equation and one lci neighbourhood; the new node starts with nodal completions globally and proves reducedness, finiteness of the singular scheme, all adjunction hypotheses and the normalized line.

lem-trf-nodal-adjunction-preparation vs lem-trf-field-curve-fitting-smooth-preparation: the existing node identifies the Fitting complement and lci charts only at smooth points of an arbitrary equidimensional curve; it does not provide nodal lci charts, reducedness, a finite singular scheme or adjunction applicability.

lem-trf-nodal-adjunction-preparation vs lem-trf-lci-unramified-singular-nodal-recognition: the existing node assumes flatness, geometric lci fibres and unramified singular subscheme to recognize nodal completions; the new node proves these preparation properties from nodal completions and supplies the adjunction line.

lem-trf-nodal-adjunction-preparation vs lem-trf-nodal-limit-lci-pure-stage: the existing node descends flatness and lci fibre properties along a qcqs inverse limit; it neither identifies a finite singular scheme of a field curve nor supplies normalized adjunction presentations.

lem-trf-split-node-component-normalization vs lem-sfb-nodal-completed-normalization-model: the existing node assumes a proper global nodal curve and describes its normalization and equal-constant-term completed model; the new node applies to a local essentially finite-type algebra without a proper global model and additionally identifies extended component primes as zero or (u),(v), the completed component quotients, and the allocation of branches to algebraic components.

lem-trf-split-node-component-normalization vs lem-trf-finite-dvr-branch-completion: the existing node starts with an already finite injective algebra whose branch localizations are DVRs and proves the product formula for completion; it does not identify that algebra as the normalization of a node, compute its two explicit formal branch maps or partition minimal primes.

lem-trf-split-node-component-normalization vs lem-trf-flat-birational-normalization-comparison: the existing node compares finite birational algebras under flat base change, with normality as an extra hypothesis; it does not compute the integral closure of uv=0, its maximal ideals or the completed component-prime partition.

lem-trf-split-node-component-normalization vs lem-trf-nagata-normalization-dvr-branches: the existing node proves finite componentwise normalization and DVR localizations for arbitrary reduced local Nagata curves; it does not compute the nodal completed normalization, its two projection maps, or which extended component prime is zero, (u) or (v).

lem-trf-split-node-component-normalization vs lem-sfb-nodal-graph-cone-fibre: the existing node identifies a projectivized graph conormal algebra with a normalization fibre, including its two geometric points; it does not describe full completed normalization rings, their two parameter maps, or extended minimal component ideals.

lem-trf-nodal-adjunction-preparation vs lem-trf-nodal-curve-lci-criterion: gives the lci/unramified-Fitting equivalence, but not global finite singular scheme, reducedness and applicability of the normalized adjunction construction.

lem-trf-nodal-adjunction-preparation vs lem-trf-nodal-geometric-fibres-reduced: proves geometric reducedness from hypotheses on every geometric extension, not the finitely presented lci adjunction presentations and finite singular scheme here.

lem-trf-nodal-adjunction-preparation vs lem-trf-nodal-point-local-criterion: characterizes a single node by lci and its Fitting stalk, not the global reducedness, finite singular scheme and adjunction applicability.

lem-trf-nodal-adjunction-preparation vs lem-sfb-nodal-relative-dualizing-line: requires proper families and constructs a Serre-duality line, whereas preparation allows nonproper nonseparated curves and identifies the determinant adjunction line and its presentations.

lem-trf-split-node-component-normalization vs lem-trf-nodal-generic-component-closure: assumes a proper flat family over a valuation base and a smooth generic component, and proves flat closure/boundary constancy; it does not give this local algebra or marked-normalization statement.

lem-trf-split-node-component-normalization vs lem-trf-stacks-nodal-closed-subcurve: gives nodality and smoothness of intersections for an ambient subcurve, but neither completed normalization maps/component-prime partition nor the marked-normalization Cartier boundary.

lem-trf-split-node-component-normalization vs lem-trf-curve-normalization-completion: identifies integral closure after completion for general reduced local algebraic curves, but does not calculate the uv normalization, its component ideals or the two branch maps.

lem-trf-split-node-component-normalization vs lem-trf-nodal-point-finite-separable-splitting: produces a separable extension splitting a nodal point over an arbitrary field; it does not compute completed branch maps and the algebraic component partition.

lem-trf-split-node-component-normalization vs lem-trf-nodal-curve-normalization-euler: assumes smooth component normalizations and proves an Euler-characteristic formula, not branch algebra or marked normalization geometry.

lem-trf-split-node-component-normalization vs lem-trf-complementary-pure-subcurve-components: describes complementary unions of components for arbitrary reduced Noetherian schemes, not completed normalization maps or formal smoothness and boundary on normalization.

lem-trf-split-node-component-normalization vs lem-trf-nodal-normalization-quotient: assumes a proper ambient nodal curve and gives the structure-sheaf normalization quotient, not the local completed component maps or marked normalization criterion.

lem-trf-split-node-component-normalization vs lem-trf-nodal-subcurve-boundary: computes the intersection of complementary ambient subcurves, rather than the branch partition on normalizations or the marked Cartier divisor on a smooth normalization.

lem-trf-split-node-component-normalization vs lem-sfb-nodal-branch-double-cover: constructs a relative etale cover recording two branches, but does not identify their completed rings/maps or partition them among local component primes.

lem-trf-split-node-component-normalization vs lem-sfb-nodal-local-tangent-normalization: identifies the quadratic normalization residue algebra with tangent Proj; it does not compute full completed normalization rings and component quotients.

lem-trf-completed-curve-boundary-geometry vs lem-trf-nodal-generic-component-closure: assumes a proper flat family over a valuation base and a smooth generic component, and proves flat closure/boundary constancy; it does not give this local algebra or marked-normalization statement.

lem-trf-completed-curve-boundary-geometry vs lem-trf-stacks-nodal-closed-subcurve: gives nodality and smoothness of intersections for an ambient subcurve, but neither completed normalization maps/component-prime partition nor the marked-normalization Cartier boundary.

lem-trf-completed-curve-boundary-geometry vs lem-trf-complementary-pure-subcurve-components: describes complementary unions of components for arbitrary reduced Noetherian schemes, not completed normalization maps or formal smoothness and boundary on normalization.

lem-trf-completed-curve-boundary-geometry vs lem-trf-nodal-subcurve-boundary: computes the intersection of complementary ambient subcurves, rather than the branch partition on normalizations or the marked Cartier divisor on a smooth normalization.

lem-trf-completed-curve-boundary-geometry vs lem-sc-normalization-properties: gives general normalization finiteness/smoothness, but not formal smooth/nodal locus classification or the reduced marked boundary divisor.

lem-trf-completed-curve-boundary-geometry vs lem-sc-point-cartier: starts with a smooth connected curve and one closed point, not the completed local criterion and construction of the normalized marked curve.

## Complete allocation of the returned proof

### Old step 1: lem-trf-nodal-adjunction-preparation (reducedness), lem-trf-completed-curve-boundary-geometry (integral proper smooth normalization)

The finite-type scheme $C$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. At a nodal point its local ring injects into its completion by [lem-weil-pbc-local-completion-faithfully-flat] and [lem-weil-pbc-faithfully-flat-universally-injective], so it is reduced: a nilpotent maps to zero in $k[[u,v]]/(uv)$, which embeds in $k[[u]]\times k[[v]]$. At a smooth point choose a smooth affine curve neighbourhood; [lem-sc-smooth-normal] makes its local ring normal, in particular reduced. Thus $C$ is reduced. The reduced irreducible component $Z$ is integral, finite type, proper and one-dimensional. Apply [lem-sc-normalization-properties]: $\nu$ is finite, $\bar Z$ is proper and one-dimensional, and it is smooth since the algebraically closed field $k$ is perfect. The normalization is integral, since its affine rings are integral closures of domains inside their fraction fields; hence it is nonempty and connected. Properness gives separatedness, so it is a smooth proper connected curve in the stated sense.

Cited nodes: lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-local-completion-faithfully-flat, lem-weil-pbc-faithfully-flat-universally-injective, lem-sc-smooth-normal, lem-sc-normalization-properties.

### Old step 2: lem-trf-nodal-adjunction-preparation

By [lem-trf-nodal-curve-lci-criterion], $C$ has a local-complete-intersection affine cover. The base is the Noetherian scheme $\operatorname{Spec}k$, the structure map is flat because vector spaces over $k$ are free, and it is locally of finite presentation by [pqf-lem-lft-fp-locnoeth]. A Noetherian scheme is quasi-compact and its open intersections are quasi-compact, giving the quasi-separatedness required here. On each nonempty global-complete-intersection chart, its defining equations have length $n-1$, since the chart is pure one-dimensional. They form a regular sequence at every prime by [lem-weil-pbc-global-complete-intersection-local-regular-sequence]; by [lem-exc-regular-sequence-principal-neighbourhood] they spread to neighbourhoods and give the regular-immersion presentations of [lem-trf-flat-lci-canonical-adjunction]. Geometric fibres are pure one-dimensional by [lem-trf-flat-dense-generic-fibre-pure-dimension], applied over $\operatorname{Spec}k$ whose generic fibre is $C$ itself. Thus the cited adjunction theorem applies with $d=1$: $K_{C/k}$ exists, is invertible, and agrees canonically with $\Omega^1_{C/k}$ on the smooth locus. No properness or separatedness of $C$ was used.

Cited nodes: lem-trf-nodal-curve-lci-criterion, pqf-lem-lft-fp-locnoeth, lem-weil-pbc-global-complete-intersection-local-regular-sequence, lem-exc-regular-sequence-principal-neighbourhood, lem-trf-flat-lci-canonical-adjunction, lem-trf-flat-dense-generic-fibre-pure-dimension.

### Old step 3: lem-trf-nodal-adjunction-preparation

Let $T$ be the first-Fitting singular subscheme of $C$. With the flatness, local finite presentation and geometric dimension checked in step 2, [lem-trf-dth-fitting-smooth-locus] says $|T|$ is exactly the nonsmooth locus and its complement is open. By [lem-trf-nodal-curve-lci-criterion], $T\to\operatorname{Spec}k$ is unramified. Therefore [lem-trf-unramified-field-fibre-decomposition] expresses $T$ as a disjoint union of spectra of finite separable extensions of $k$, all equal to $k$. As a closed subscheme of the Noetherian scheme $C$, $T$ is quasi-compact, so this union is finite. In particular every singular point is one of the nodes in the hypothesis, the smooth locus contains every generic point, and its inverse image in $\bar Z$ is the complement of finitely many closed points.

Cited nodes: lem-trf-dth-fitting-smooth-locus, lem-trf-nodal-curve-lci-criterion, lem-trf-unramified-field-fibre-decomposition.

### Old step 4: lem-trf-split-node-component-normalization

For the complete node $R=k[[u,v]]/(uv)$, the map $a(u,v)\mapsto(a(u,0),a(0,v))$ identifies $R$ with the pairs of series having equal constant term. Put $N=k[[u]]\times k[[v]]$. The idempotent $e=(1,0)$ satisfies $e^2-e=0$, and $N=R+Re$, so $N$ is finite and integral over $R$. Both power-series factors are integrally closed domains by [lem-weil-pbc-power-series-normal-domain] applied to the field $k$. The total fraction ring of $R$ is $k((u))\times k((v))$: $u+v$ is a non-zero-divisor, and $u/(u+v)=(1,0)$ splits its two fraction-field factors. Any element of that product integral over $R$ is integral over $N$ and belongs to $N$ by the factorwise integrally closed property. Consequently $N$ is precisely the integral closure of $R$. Its two local factors have residue field $k$.

Cited nodes: lem-weil-pbc-power-series-normal-domain.

### Old step 5: lem-trf-split-node-component-normalization

For a reduced Noetherian local curve ring $A$ with minimal primes $P_i$, [lem-weil-pbc-reduced-noetherian-total-ring-fractions] identifies $Q(A)$ with $\prod_i\operatorname{Frac}(A/P_i)$. Its integral closure is the product of the integral closures $B_i$ of the $A/P_i$: projecting a monic equation proves one inclusion. For the other, given a tuple $b_i\in B_i$, lift the coefficients of a monic equation for each $b_i$ to $A$; the product of these monic polynomials annihilates the tuple, since in component $i$ its $i$-th factor vanishes. Thus the tuple is integral over $A$. By [lem-weil-pbc-integral-closure-commutes-localization], this description agrees with the localizations of scheme normalizations on affine charts. Consequently normalization of the reduced local ambient curve is the disjoint union of the normalizations of its components, and each of its points is attached to exactly one component. This verifies the local/scheme identification used in the following branch calculation.

Cited nodes: lem-weil-pbc-reduced-noetherian-total-ring-fractions, lem-weil-pbc-integral-closure-commutes-localization.

### Old step 6: lem-trf-split-node-component-normalization

Fix an ambient node $x$ and put $A=\mathcal O_{C,x}$. Apply [lem-trf-curve-normalization-completion] to $A$. Step 4 and [lem-weil-pbc-completion-finite-extension] identify the completed local rings of its normalization above $x$ with the two factors $k[[u]]$ and $k[[v]]$, one factor per point. Their residue fields are $k$. To track a particular component through $x$, let $P$ be its minimal prime in $A$. Apply the same normalization-completion lemma to the reduced one-dimensional domain $A/P$. By [lem-weil-pbc-completion-finite-module-tensor], its completion is $\widehat A/P\widehat A$; it is reduced and one-dimensional. Its kernel in $R$ is therefore the intersection of a nonempty subset of the two minimal primes $(u),(v)$. Thus the component uses either one branch or both. Distinct component ideals have distinct completed ideals, since faithful flatness contracts $P\widehat A$ back to $P$. If one completed ideal is zero, its contraction is zero, so $A$ is a domain and has just that one minimal prime. Otherwise the only possibilities are $(u)$ and $(v)$, with disjoint branch sets. Every branch occurs: the product of all minimal primes in reduced $A$ is zero; its extension is zero, so each minimal prime of $R$ contains at least one completed component ideal. It follows that a node on two distinct components contributes one point on each normalization; a node on a single component contributes two points on that component's normalization. Applied to $Z$, this proves the asserted branch counts, including self-nodes.

Cited nodes: lem-trf-curve-normalization-completion, lem-weil-pbc-completion-finite-extension, lem-weil-pbc-completion-finite-module-tensor, lem-weil-pbc-local-completion-faithfully-flat.

### Old step 7: lem-trf-completed-curve-boundary-geometry

If $x\in Z$ is smooth in $C$, an open normal affine curve neighbourhood of $x$ by [lem-sc-smooth-normal] has a unique component through $x$; after removing the other finitely many components, $Z$ and $C$ agree there. If an ambient node lies on two components, step 6 gives the completed local ring of $Z$ at $x$ as $k[[u]]$ or $k[[v]]$. This ring is regular by [lem-weil-pbc-power-series-field-cohen-regular-complete], so the local ring of $Z$ is regular by [lem-weil-pbc-completion-regular-local]. Its residue field is $k$, a separable extension of itself; [lem-weil-pbc-regular-local-separable-residue-smooth] makes $Z$ smooth at $x$. If the node has both branches on $Z$, its completed local ring is $R$, whose maximal ideal has two independent generators modulo its square and whose dimension is one, so it is not regular. The same regularity and smoothness criteria show $Z$ is not smooth there. These are exactly its self-nodes. Finally, on the smooth locus of $Z$, [lem-sc-smooth-normal] gives normality and [lem-sc-normalization-properties](b) gives that $\nu$ is an isomorphism. This includes its smooth points over ambient intersection nodes.

Cited nodes: lem-sc-smooth-normal, lem-weil-pbc-power-series-field-cohen-regular-complete, lem-weil-pbc-completion-regular-local, lem-weil-pbc-regular-local-separable-residue-smooth, lem-sc-normalization-properties.

### Old step 8: lem-trf-completed-curve-boundary-geometry (Cartier boundary), parent step 3 (rational map)

By steps 3 and 6 the set of points of $\bar Z$ over the singular locus of $C$ is finite, with two distinct points for each self-node and one for each intersection branch belonging to $Z$. Each is a reduced closed point on the smooth connected curve $\bar Z$. By [lem-sc-point-cartier], their sum $B_Z$ is an effective Cartier divisor, and [def-pc-divisor-line-bundle] gives its associated invertible module. Outside $B_Z$, step 7 identifies $\nu$ with an isomorphism onto the part of $Z$ in the ambient smooth locus. Hence [lem-trf-flat-lci-canonical-adjunction] gives a canonical identification of $L:=\nu^*(K_{C/k}|_Z)$ with $M:=\Omega^1_{\bar Z/k}\otimes\mathcal O_{\bar Z}(B_Z)$ there, using the canonical trivialization of $\mathcal O(B_Z)$ off its divisor. This determines a rational isomorphism $\alpha:L\dashrightarrow M$.

Cited nodes: lem-sc-point-cartier, def-pc-divisor-line-bundle, lem-trf-flat-lci-canonical-adjunction.

### Old step 9: parent step 4 (formal-plane residue)

Let $p\in B_Z$ lie over a node $x$. Use the formal presentation $\widehat{\mathcal O}_{C,x}=k[[u,v]]/(uv)$ from the hypothesis. By step 6 its map to the completion at $p$ is one of $u\mapsto t,v\mapsto0$ or $u\mapsto0,v\mapsto t$, after choosing the branch parameter. The ring at $p$ is a discrete valuation ring by [lem-sc-smooth-connected-curve-local-rings]; it is the local ring of the normalization of the reduced algebraic curve at $x$, is essentially of finite type, and has residue field $k$. Step 2 supplies the local complete intersection and the adjunction line. Thus all hypotheses of [lem-trf-formal-plane-adjunction-lattice] hold with $f=uv$. On the first branch $f_v=u$, giving the generator $\mathrm dt/t$; on the second $f_u=v$, giving $-\mathrm dt/t$. Each is nonzero and has precisely one simple pole. These are calculations in continuous formal differentials as specified by the lemma, not an identification with the entire algebraic differential module of $k((t))/k$.

Cited nodes: lem-sc-smooth-connected-curve-local-rings, lem-trf-formal-plane-adjunction-lattice.

### Old step 10: parent step 4 (target Cartier lattice)

At the reduced point $p$ the divisor ideal is the maximal ideal of the discrete valuation ring $D=\mathcal O_{\bar Z,p}$. For a uniformizer $z$ it is $(z)$; the definition [def-pc-divisor-line-bundle] therefore realizes $\mathcal O(B_Z)_p$ as $z^{-1}D$ in its fraction field. Under completion $z$ still generates the maximal ideal, by [lem-weil-pbc-completion-regular-local], and in the parameter of step 9 it is $t$ times a unit. The regular-differential comparison in [lem-trf-formal-plane-adjunction-lattice] identifies the completed target $M_p$ with $k[[t]]\,\mathrm dt/t$. Step 9 identifies the completed image of $L_p$ under the same rational smooth-locus map with this identical lattice; the minus sign on the second branch is a unit, including in characteristic two. Therefore the rational isomorphism $\alpha$ has order zero at every point of $B_Z$.

Cited nodes: def-pc-divisor-line-bundle, lem-weil-pbc-completion-regular-local, lem-trf-formal-plane-adjunction-lattice.

### Old step 11: parent step 5 (DVR unit and gluing)

To spell out the extension in step 10, choose local generators of $L_p,M_p$ and write $\alpha$ as multiplication by $a\in k(\bar Z)^*$. By [lem-sc-smooth-connected-curve-local-rings], $a=wz^n$ with $w\in D^*$ and $n\in\mathbf Z$. In the completion $z=t$ times a unit, so equality of the two completed lattices forces $n=0$; hence $a\in D^*$. A unit in the stalk is represented by a unit on some neighbourhood of $p$, so $\alpha$ extends to an isomorphism there. At points outside $B_Z$ it was already an isomorphism by step 8. The extensions agree on overlaps: they agree at the generic point and, on the integral curve, local regular functions inject into the function field by the same cited lemma. They therefore glue to $L\cong M$ on $\bar Z$. The isomorphism is canonical because it is the unique extension of the prescribed smooth-locus identification; in particular formal coordinates, branch ordering and local generators introduce no choice in the result.

Cited nodes: lem-sc-smooth-connected-curve-local-rings.

## Size and scope

Parent proof text: 2647 characters. New statement sizes: lem-trf-nodal-adjunction-preparation: 1833, lem-trf-split-node-component-normalization: 2380, lem-trf-completed-curve-boundary-geometry: 1583. Three new unsplit nodes, zero new Mathlib leaves. Only the sandbox was written; no git command, Lean edit, compiler or local preflight/check_dag/review_split invocation was run.

## Repair of live-DAG promotion return (2026-10-22)

The retained delivery head was bbf2a116e90, recorded by the successful earlier readiness record. The return was a landing/promotion failure, not a mathematical rejection: the side completion had not been promoted to the live queue DAG. I compared all four retained node files against the current shared DAG before making changes. The three new ids are absent there. For the parent, only proof, proof_deps, proof_origin and split_report differ; its statement, statement dependencies, source, blueprint provenance and all other metadata agree. All eleven current old proof steps are still present verbatim in this report. The released stage-1 repair note still requires three independently stated new nodes and an assembly of at most 3000 characters; the retained assembly is 2647 characters.

I reread all six existing proof dependencies in the current DAG: divisor-line-bundle, smooth-connected-curve-local-rings, smooth-normal, flat-lci-canonical-adjunction, formal-plane-adjunction-lattice, and completion-regular-local. Their current statements still give the exact ten quotations in citations.json, with no changed quotation or missing hypothesis. In particular the formal-plane node compares the lattice through the generic smooth-locus map, and completion-regular-local explicitly identifies the completed maximal ideal with its extension. Thus the residue calculation and DVR extension remain valid without changing the proof route. I also reread the three retained new statements and their Stacks source passages (curves.tex 0C4E, 0E37, 0E38, 0CBW and varieties.tex 0C3V, 0C45); the crossing-component, self-node, empty-boundary and characteristic-two checks in the signed review above still apply. I added the two completion/power-series definition dependencies already explicitly named in completed-curve-boundary-geometry's unchanged statement.

The first new dry run identified nine additional same-tag nodes now present on the base. I opened every statement and added the nine pairwise distinctions under Not duplicates. In particular the closest completed-normalization model assumes a proper ambient curve and does not state the minimal-prime partition needed here; the general Nagata and completion comparison nodes do not compute that nodal partition either. No new node is deleted or replaced, and no new search query or unrun search is claimed. I reread the retained search results; because the statements and search questions have not changed, those logged searches are reused. The split_report now records this rebase repair, and the delivery tool will construct the new commit on the current DAG rather than repush the old head.

## Final current-base verification (Q94, 2026-10-22)

The retained repair was resumed, rather than reconstructed or replaced. The required first dry run completed successfully on the current server base: `OK (not pushed) deliver/Q94/lem-trf-nodal-normalization-adjunction at f1312206e42: preflight passed`. This follows the earlier repair work recorded above and confirms that its definition-dependency corrections and same-tag distinctions are present in the rebased delivery.

I independently reread the current six existing cited statements. The formal-plane comparison still uses the generic smooth-locus map, the Cartier-line definition gives the dual ideal, and the regular-local completion statement identifies the extended maximal ideal; therefore the two branch generators and the valuation-zero extension require no mathematical change. The smooth-normal statement is applied only to smooth affine curve neighbourhoods. All ten step/node pairs have exact verbatim quotations, the proof-dependency union agrees with the uses lists, and all eleven live proof arguments remain verbatim above. The parent statement and statement dependencies are unchanged. The three new ids remain absent from the shared DAG.

Current statement fingerprints (SHA-256), for identifying any later dependency changes:

- def-pc-divisor-line-bundle: `d2fb738c73c9f3c60942a1257d5718b46c3f6a4e5d1217e379ce91862bab97cd`.
- lem-sc-smooth-connected-curve-local-rings: `58fc53e4e7266279a63fbabc037969727505083e7942bbedd3b4eabd18fb86e3`.
- lem-sc-smooth-normal: `ab138ad648a7398ab2891655073f46a1ab717d4ce7383a1792e19e5c2eaf746f`.
- lem-trf-flat-lci-canonical-adjunction: `5dab6067a3707d6f654a7a5e0399d91cbc22d3a90c0a902edeca9f76a4b826e3`.
- lem-trf-formal-plane-adjunction-lattice: `c6c6ce24163a972bb4428ba0cd88d798c412403378e7bdaab44d251949f3aa31`.
- lem-weil-pbc-completion-regular-local: `1e8b041d875a45959d09cf5fe64a61d1ce53b03c9d791c68f3e01d620bb56189`.

I reread the retained search-result signatures and did not invent or rerun any searches: the three new statements and the search questions are unchanged. The local Stacks split-node, nodal-lci, reducedness, closed-subcurve and normalization/completion passages still support the source allocation. The empty boundary, ordinary crossing, irreducible self-node and characteristic-two cases remain consistent. This report update records the completed verification; the final dry run and push use the delivery tool on the current server base.


## Rebase repair and signed current-base review (Q94, 2026-10-23)

The promotion return was repaired against the current shared DAG, retaining the delivered three-node split, all eleven original arguments above, citations and logged searches. The required initial dry run exited successfully: `OK (not pushed) deliver/Q94/lem-trf-nodal-normalization-adjunction at 54eb854eacf: preflight passed`. The three new node ids are still absent from the shared DAG. The parent differs from the current node only in its replacement proof, proof dependency union, proof origin and split report; its mathematical statement and statement dependencies remain identical. The released stage-1 repair note still requires this re-split and at least three new obligations, so the older reviewed long proof does not supersede the repair.

I opened every existing proof dependency again. All six statements have exactly the SHA-256 fingerprints listed in the preceding verification, so none has changed since that reading. Preparation still supplies step 1's reducedness, finite singular set and normalized adjunction line; local branch algebra supplies step 2's projections and component partition. Step 3 uses smooth-normal only on smooth affine curve neighbourhoods and applies the marked-curve geometry to the proper integral component, allowing marked regular intersection points. The canonical smooth-locus identification is explicitly in flat-lci-canonical-adjunction. For step 4, formal-plane-adjunction-lattice explicitly compares the completed source lattice and regular differentials through this same generic identification, divisor-line-bundle is the dual of the Cartier ideal, and completion-regular-local explicitly gives the extended maximal ideal. Step 5 uses the valuation decomposition and function-field injections of smooth-connected-curve-local-rings; the unit and gluing argument is written in the step. I verified all ten step/node quotations against these current statements and the three new statements.

I reread the local Stacks sources: curves.tex split-node (0CBW), nodal-lci (0C4E), facts-about-nodal-curves (0E37), closed-subscheme-nodal-curve (0E38), and varieties.tex normalization-same-after-completion (0C3V), normalize-noetherian-dim-1 (0C45). The essentially finite-type hypothesis supplies the Nagata setting in the local normalization comparison; the smooth branch criterion uses the algebraically closed base. The three new obligations retain the source's lci preparation, completed component algebra, and marked normalization geometry separately. Empty marked set, two distinct components, a self-node and characteristic two still satisfy the stated conclusions. The source PDF remains WANTED as already recorded; no SGA route or alternative unit route was introduced.

I checked B4 on the decoded proof strings: the backslashes are single TeX backslashes; the apparent doubling was output encoding, so no TeX repair was needed. The final dry run on the next current base detected an additional same-tag node, lem-sfb-nodal-family-regular-affine-presentations. I opened its whole statement: it assumes flatness, finite presentation and reduced geometric nodal fibres and supplies regular affine presentations, but gives neither the derived preparation hypotheses nor the finite reduced singular scheme nor the canonical adjunction identification. I added the precise pairwise distinction under Not duplicates. No mathematical content, citation or dependency list changed. Each step remains below 2000 characters and the full assembly remains below 3000. The statement-only nodes are unchanged. I read the retained Mathlib hit signatures and unavailable-service results; no new mathematical statement or search question requires repeating those searches. The final dry run and push will create the delivery on the current server DAG through the authorized delivery tool.


## Review by Q94 — promotion-return retry, 2026-10-23

I resumed the retained delivery, including its three statement-only obligations and all eleven old arguments, rather than replacing it. The required first dry run exited zero and printed `OK (not pushed) deliver/Q94/lem-trf-nodal-normalization-adjunction at aa6d5223297: preflight passed`. The delivery tool rebased the sandbox files onto the current server DAG. In the shared read clone the three new ids remain absent; the parent differs only in proof, proof_deps, proof_origin and split_report. Its statement, statement dependencies, Lean metadata and blueprint provenance agree with the current parent. The released repair order still requires the three-node re-split; the old side completion is not treated as a live completion.

I opened all six current existing proof-input statements and compared their SHA-256 fingerprints with the recorded previous reading: all six are identical. I also opened the three retained new statements. Step 1 uses preparation for reducedness, the finite singular locus, regular-sequence presentations and normalized adjunction; step 2 uses the local branch algebra for the two completed maps and their component partition, with reducedness already supplied. Step 3 applies the marked geometry to the proper integral component and uses smooth-normal only in smooth affine neighbourhoods; the canonical differential identification is explicitly in flat-lci-canonical-adjunction. In step 4 the formal-plane statement explicitly supplies both lattices through that same generic identification, the divisor definition supplies the dual ideal, and completion-regular-local supplies the extended maximal ideal. Its derivative denominators are nonzero on their selected branches, including in characteristic two. Step 5 uses the curve-local-ring statement's valuation decomposition and injections into the function field; equality of lattices forces valuation zero, and the written stalk-unit and overlap argument gives the unique gluing. All ten uses/step pairs are present in citations.json and every quotation remains verbatim in its current statement. No changed citation needed substitution.

For the source check I reread curves.tex at split-node (0CBW), nodal-lci (0C4E), facts-about-nodal-curves (0E37), and the full closed-subscheme-nodal-curve proof (0E38), together with varieties.tex normalization-same-after-completion (0C3V) and normalize-noetherian-dim-1 (0C45). The local comparison applies in the essentially finite-type/Nagata setting; the marked geometry is over the algebraically closed field and only the component is required proper. These passages still support the three obligations' allocation. Empty boundary gives the smooth formula; an ordinary crossing gives one marked smooth point on each component normalization; a self-node gives two points on one normalization. No source or statement correction was necessary.

I reread the retained search log and Mathlib signatures: smoothness criteria, relative normalization, integral-closure base change and Weierstrass division do not give any complete new statement, and the two unavailable LeanSearch responses remain recorded as unavailable. Since the statements and questions are unchanged, the searches are reused without invented or repeated queries. All three new nodes retain empty proof and proof_deps; none cites the parent or its other new siblings. The decoded proof strings have no doubled TeX backslashes. Every step is below 2000 characters and the assembly totals 2647 characters. This retry updates the signed report and split report with the actual current-base comparison; the final dry run and push construct a fresh current-base delivery, rather than repushing an old head. The maintainer still performs the live promotion identified in the return; no live queue or repository file was changed here.
