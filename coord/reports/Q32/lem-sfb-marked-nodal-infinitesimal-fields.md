# Repair report: lem-sfb-marked-nodal-infinitesimal-fields

## Files written

- Item: statement unchanged, five assembly steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-completed-normalization-model.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-nodal-derivation-local-descent.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-derivation-zero-divisor.json: statement, unsplit, no Mathlib match.

## Attachments

None. The project module Sheaf.AlgebraicGeometry.MarkedNodalInfinitesimalFields contains sorry at the identification, vector-field bounds, and stability declarations (lines 209, 260, 293). The WeilConjectures search by blueprint tag and nodal/vector-field/derivation terminology found no declaration proving this item or any new node. No compiler was run.

## WANTED

None: all mathematical sources are locally present.

## Return repaired and comparison

The sandbox initially contained only dispatcher markers, no delivered JSON, report, citations or search log. I copied the current read-only repository node, which includes the maintainer's prior fix, and ran the required initial dry run. It stopped because report.md was absent. I retained every current field outside the worker-owned proof/report fields, including the unchanged statement, Lean records, blueprint metadata and existing searches. There was no retained local attempt to overwrite. The delivery tool rebases the changed worker-owned fields against the current server main.

The human requested at least three comparable statement-only jobs and an assembly of at most 3000 characters. The three new statements assign old steps 2--3 (2906 characters), 4--6 (2957 characters), and 8--9 (2207 characters). Their proof/proof_deps are empty and status is unsplit. Steps 1, 7 and 10 remain explicit in the short assembly. The full old argument follows verbatim below, so none of its calculations or source corrections disappears. New local-descent hypotheses are supplied by the new geometric model; neither node depends on the parent, and the tangent-divisor job is independent of both.

## Source error retained

Stacks curves.tex Tag 0E68 (lemma-nodal-vector-fields), proof, asserts an exact sequence using the product of the two uncompleted normalization branch stalks and treats branch uniformizers as elements of the original nodal local ring with product zero. For an irreducible nodal cubic the original local ring is a domain, so two nonzero elements cannot have product zero. Its integral closure in the fraction field is a semilocal domain, not that product. This is a source proof error, not a dispute with the unchanged theorem. The new model and local-descent jobs retain the repair: use the product only after completion, and descend membership via injectivity after faithfully flat completion. This also avoids division by two in characteristic two.

## Not duplicates

- lem-sfb-nodal-completed-normalization-model vs lem-trf-curve-normalization-completion: the existing statement concerns Normalization and completion of a reduced local algebraic curve; the new statement also requires the explicit equal-constant completed nodal model together with finite global branch/component geometry.
- lem-sfb-nodal-completed-normalization-model vs lem-sfb-marked-nodal-infinitesimal-fields: the new node is normalization geometry and the explicit completed ring model, with no automorphisms, derivation correspondence, zero bounds or stability conclusion.
- lem-sfb-nodal-completed-normalization-model vs lem-weil-pbc-fraction-field-lift: the existing statement concerns An injective ring map from a domain to a field extends to an embedding of its fraction field; the new statement also requires the explicit equal-constant completed nodal model together with finite global branch/component geometry.
- lem-sfb-nodal-completed-normalization-model vs lem-weil-pbc-laurent-series-field: the existing statement concerns Laurent series over a field form a field; the new statement also requires the explicit equal-constant completed nodal model together with finite global branch/component geometry.
- lem-sfb-nodal-completed-normalization-model vs def-weil-pbc-laurent-series: the existing statement concerns Formal Laurent series in one variable; the new statement also requires the explicit equal-constant completed nodal model together with finite global branch/component geometry.
- lem-sfb-nodal-completed-normalization-model vs lem-weil-pbc-power-series-normal-domain: the existing statement concerns A power series ring over a Noetherian normal domain is a Noetherian normal domain; the new statement also requires the explicit equal-constant completed nodal model together with finite global branch/component geometry.
- lem-sfb-nodal-derivation-local-descent vs lem-sfb-marked-nodal-infinitesimal-fields: the new node is a local ring statement with given completed normalization data; it supplies membership descent and the two local maps, with no global curve, marked automorphism group, or genus bounds.
- lem-sfb-nodal-derivation-local-descent vs new-lem-weil-pbc-finite-model-formal-fiber-derivation-extension: the existing statement concerns Extending finite-model derivations to the generic formal fibre; the new statement is the two-direction ideal-preserving derivation correspondence and faithful-flat membership tests for an uncompleted nodal ring.
- lem-sfb-nodal-derivation-local-descent vs lem-weil-pbc-derivation-extends-finite-type-extension: the existing statement concerns A multiple g^N D of a derivation extends along a finite type extension that is an isomorphism after inverting g; the new statement is the two-direction ideal-preserving derivation correspondence and faithful-flat membership tests for an uncompleted nodal ring.
- lem-sfb-nodal-derivation-local-descent vs lem-weil-pbc-derivation-extends: the existing statement concerns A derivation extends to adic completions and to localizations; the new statement is the two-direction ideal-preserving derivation correspondence and faithful-flat membership tests for an uncompleted nodal ring.
- lem-sfb-nodal-derivation-local-descent vs lem-weil-pbc-another-helper-g-ring: the existing statement concerns Formal fibres of A[x] over nonzero primes above (0), A complete local domain of characteristic p; the new statement is the two-direction ideal-preserving derivation correspondence and faithful-flat membership tests for an uncompleted nodal ring.
- lem-sfb-nodal-derivation-local-descent vs lem-weil-pbc-derivation-away-finite-type-core: the existing statement concerns Restriction of a localized derivation to a finite type algebra; the new statement is the two-direction ideal-preserving derivation correspondence and faithful-flat membership tests for an uncompleted nodal ring.
- lem-sfb-nodal-derivation-local-descent vs lem-weil-pbc-another-helper-g-ring-noetherian-component: the existing statement concerns Noetherian component of polynomial formal fibre; the new statement is the two-direction ideal-preserving derivation correspondence and faithful-flat membership tests for an uncompleted nodal ring.
- lem-sfb-nodal-derivation-local-descent vs lem-weil-pbc-polynomial-complete-local-nonzero-fibre-char-zero: the existing statement concerns Nonzero polynomial formal fibres in characteristic zero; the new statement is the two-direction ideal-preserving derivation correspondence and faithful-flat membership tests for an uncompleted nodal ring.
- lem-sfb-nodal-derivation-local-descent vs lem-weil-pbc-another-helper-g-ring-geometric-component: the existing statement concerns Geometric component of polynomial formal fibre; the new statement is the two-direction ideal-preserving derivation correspondence and faithful-flat membership tests for an uncompleted nodal ring.
- lem-sfb-nodal-derivation-local-descent vs lem-weil-pbc-helper-g-ring-char-p: the existing statement concerns Formal fibres over the generic point of k[[x]][y] in characteristic p are geometrically regular; the new statement is the two-direction ideal-preserving derivation correspondence and faithful-flat membership tests for an uncompleted nodal ring.
- lem-sfb-nodal-derivation-local-descent vs lem-weil-pbc-derivation-away-transport: the existing statement concerns Transport of a derivation across an away-localization isomorphism; the new statement is the two-direction ideal-preserving derivation correspondence and faithful-flat membership tests for an uncompleted nodal ring.
- lem-sfb-smooth-derivation-zero-divisor vs def-sc-rational-section-divisor: the existing statement concerns Rational sections of an invertible module on a smooth curve and their divisors; the new statement identifies ideal preservation with tangent-section zeros and realizes their multiplicities as a divisor of degree 2-2g.
- lem-sfb-smooth-derivation-zero-divisor vs lem-sc-rational-section-order: the existing statement concerns Orders of a rational section: independence of the generator and finiteness; the new statement identifies ideal preservation with tangent-section zeros and realizes their multiplicities as a divisor of degree 2-2g.
- lem-sfb-smooth-derivation-zero-divisor vs def-sfb-curve-vector-fields-fixing-points: the existing statement concerns Sheaf derivations preserving specified point ideals; the new statement identifies ideal preservation with tangent-section zeros and realizes their multiplicities as a divisor of degree 2-2g.
- lem-sfb-smooth-derivation-zero-divisor vs lem-sfb-marked-nodal-infinitesimal-fields: the new node gives the tangent-section dictionary and its effective divisor with multiplicities; the parent performs the numerical zero bounds and combines them with nodal automorphisms.
- lem-sfb-smooth-derivation-zero-divisor vs lem-a1-uniformizer-differential-basis: the existing statement concerns A uniformizer generates the differentials at a separable smooth curve point; the new statement identifies ideal preservation with tangent-section zeros and realizes their multiplicities as a divisor of degree 2-2g.

- lem-sfb-nodal-completed-normalization-model vs lem-sfb-quadratic-series-integral-closure: the quadratic-series node gives only an abstract completed quadratic ring and its integral closure after a coordinate choice; it has no original local ring, comparison with its finite normalization, or finite global normalization geometry. The old equal-constant calculation remains allocated to the new model; its future worker can reuse the quadratic-series result if useful.
- lem-sfb-nodal-completed-normalization-model vs lem-sfb-nodal-local-tangent-normalization: the existing statement identifies tangent Proj with the quadratic normalization residue scheme; it does not assert the whole completed normalization model or global component geometry.
- lem-sfb-nodal-completed-normalization-model vs lem-trf-nodal-normalization-quotient: the existing statement identifies the finite-length quotient sheaf and its Euler characteristic, not the canonical completed normalization ring and its embedding.

## Preserved arguments and allocation

The following are the full returned proof steps, copied from the current repository head, including every cited node. They are worker guidance in this report, not proof steps or proof sketches inside the new statement-only node files.

### Old step 1 -> parent assembly

Put $k=\Omega$ and $R=k[\epsilon]/(\epsilon^2)$. On each open of $C$ its constant thickening has ring $\mathcal O_C\oplus\epsilon\mathcal O_C$. Every $R$-algebra automorphism reducing to the identity has the unique form $a+\epsilon b\mapsto a+\epsilon(b+D(a))$. Multiplicativity is precisely $D(ab)=aD(b)+bD(a)$, and fixing $R$ says that $D$ is $k$-linear. Conversely this formula for any sheaf derivation is multiplicative, compatible with restrictions, and has inverse given by $-D$. It gives local ring maps since reduction is the identity and nilpotents do not change the underlying space. Composing the formulas adds $D$'s. At a marked point $p$, evaluation of this formula along the constant section is unchanged exactly when $D(a)(p)=0$ for every local function $a$. Since $D$ kills $k$, this is equivalent to $D(\mathcal I_p)\subseteq\mathcal I_p$. Thus the group in the statement is additively the space of derivations on $C$ preserving the marked ideals.

Cited prerequisites: def-sc-dual-numbers.

Source: literature/stacks-project/more-morphisms.tex, Tag 02H5 (lemma-action-by-derivations), direct verification for the split dual-number thickening; curves.tex section-vector-fields, definition of fixes.

### Old step 2 -> lem-sfb-nodal-completed-normalization-model

If $C$ is empty, both sides are trivial; assume $C$ nonempty. The scheme $C$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]: proper implies finite type and a field is Noetherian; so its local rings are Noetherian. The normalization is finite with finitely many smooth proper connected components by [lem-trf-reduced-curve-normalization-genus]; those components are projective by [lem-sc-proper-dim-one-projective]. By [lem-trf-normalization-singular-skyscraper], the set $S$ of non-smooth points of $C$ is a finite set of closed points, which by the hypothesis is the set of nodes, and there is an exact sequence $0\to\mathcal O_C\to\nu_*\mathcal O_{\widetilde C}\to Q\to0$ with $Q$ supported on $S$. So $\mathcal O_U\cong(\nu_*\mathcal O_{\widetilde C})|_U$ on $U=C\setminus S$. Since $\nu$ is finite, hence affine [def-weil-finite-integral-morphism], for every affine open $V\subseteq U$ the inverse image $\nu^{-1}(V)$ is the spectrum of $(\nu_*\mathcal O_{\widetilde C})(V)=\mathcal O_C(V)$; thus $\nu^{-1}(U)\to U$ is an isomorphism. At a node $x$, put $A=\mathcal O_{C,x}$ and let $B$ be its integral closure in $Q(A)$, the localization at the non-zero-divisors; by the same node [lem-trf-normalization-singular-skyscraper], $B$ is the stalk $(\nu_*\mathcal O_{\widetilde C})_x$, a semilocal ring, not a product of the uncompleted branch stalks. By [lem-trf-curve-normalization-completion], $B$ is finite over $A$ and $B\otimes_A\widehat A$ is the normalization of $\widehat A$. The hypothesis applies: $A$ is reduced and essentially of finite type over $k$; also $\dim A=\dim\widehat A=1$ by [lem-weil-pbc-completion-dimension]. Indeed every prime of $k[[u,v]]/(uv)$ contains $u$ or $v$, and a one-variable power-series ring has only the primes $(0),(t)$ since each nonzero series is $t^n$ times a unit. The node has exactly two normalization points by [lem-trf-ordinary-point-delta-branches], which also gives normalization defect one. As $S$ is finite and $\nu$ has finite fibres over it, each $E_a$ is finite.

Cited prerequisites: lem-trf-reduced-curve-normalization-genus, lem-trf-normalization-singular-skyscraper, lem-trf-curve-normalization-completion, lem-trf-ordinary-point-delta-branches, lem-weil-pbc-finite-type-over-noetherian, lem-weil-pbc-completion-dimension, lem-sc-proper-dim-one-projective, def-weil-finite-integral-morphism.

Source: literature/stacks-project/curves.tex, Tag 0E68 (lemma-nodal-vector-fields), normalization setup; varieties.tex Tag 0C3V (lemma-normalization-same-after-completion); completed replacement of the uncompleted stalk assertion.

### Old step 3 -> lem-sfb-nodal-completed-normalization-model

Write $\widehat A=k[[u,v]]/(uv)$. The map $h\mapsto(h(u,0),h(0,v))$ identifies this ring with the pairs in $P=k[[u]]\times k[[v]]$ having equal constant terms: every such pair is uniquely $c+uf(u)+vg(v)$. Its total fraction ring is $k((u))\times k((v))$: inverting the non-zero-divisor $u+v$ produces the idempotents $(1,0)=u/(u+v)$ and $(0,1)$ and then the two Laurent-series fields. Moreover $P=\widehat A[(1,0)]$, an integral extension since the adjoined element is idempotent. Both factors of $P$ are integrally closed by [lem-weil-pbc-power-series-normal-domain] applied to the field $k$; integral closure in the product of fraction fields is checked coordinatewise. Thus $P$ is the normalization of $\widehat A$, so step 2 identifies $B\otimes_A\widehat A=P$. By [lem-weil-pbc-completion-finite-module-tensor], this is also the $\mathfrak m_AB$-adic completion of $B$.

Cited prerequisites: lem-weil-pbc-power-series-normal-domain, lem-weil-pbc-completion-finite-module-tensor.

Source: literature/stacks-project/curves.tex, Tag 0E68 (lemma-nodal-vector-fields), completed node calculation; varieties.tex Tag 0C3V and algebra.tex Tag 0BI0 (lemma-power-series-over-Noetherian-normal-domain).

### Old step 4 -> lem-sfb-nodal-derivation-local-descent

Here is the membership test used below. The map $A\to\widehat A$ is faithfully flat by [lem-weil-pbc-local-completion-faithfully-flat]. By [lem-weil-pbc-faithfully-flat-universally-injective], the map $N\to N\otimes_A\widehat A$ is injective for every $A$-module $N$. Taking $N=Q(A)/B$ shows that an element of $Q(A)$ whose image belongs to $B\otimes_A\widehat A=P$ already belongs to $B$. Taking $N=B/A$ shows that an element of $B$ whose image in $P$ belongs to $\widehat A$ already belongs to $A$. These assertions follow by taking the class modulo the indicated submodule and using injectivity; tensoring the quotient gives the corresponding quotient of the tensor product. Flatness ensures that the inclusions into $Q(A)\otimes_A\widehat A$ remain inclusions.

Cited prerequisites: lem-weil-pbc-local-completion-faithfully-flat, lem-weil-pbc-faithfully-flat-universally-injective.

Source: literature/stacks-project/algebra.tex, Tags 00MC (lemma-completion-faithfully-flat) and 05CK (lemma-faithfully-flat-universally-injective), applied to the two quotient modules.

### Old step 5 -> lem-sfb-nodal-derivation-local-descent

For a derivation $D:A\to A$, [lem-weil-pbc-derivation-extends] gives its continuous extension $\widehat D$ to $\widehat A$ and its unique extension to $Q(A)$, with $D(a/s)=D(a)/s-aD(s)/s^2$. In the completed node, $0=\widehat D(uv)=v\widehat D(u)+u\widehat D(v)$. Writing the two branch coordinates shows $\widehat D(u)\in(u)$ and $\widehat D(v)\in(v)$: the $v$-coordinate of the first and the $u$-coordinate of the second must vanish, including their constant terms. Consequently $\widehat D(u)=uf(u)$ and $\widehat D(v)=vg(v)$. Its extension to $P$ is the pair of continuous derivations $uf(u)\partial_u$ and $vg(v)\partial_v$. The formulas agree with $\widehat D$ first on polynomials and then on power series by continuity. Both derivations preserve the respective maximal ideals. Localizing these formulas agrees with the extension of $D$ on $Q(A)$ by the displayed quotient rule. For $b\in B\subset Q(A)$, its derivative therefore has image in $P$. Step 4 implies $D(b)\in B$. Thus $D$ extends uniquely to $B$, and the residue at either branch of every $D(b)$ is zero, so the extended derivation fixes both branch points.

Cited prerequisites: lem-weil-pbc-derivation-extends.

Source: literature/stacks-project/curves.tex, Tag 0E68 (lemma-nodal-vector-fields), forward implication computed in completed rings; more-algebra.tex Tag 07PE (lemma-derivation-extends), parts (1) and (2).

### Old step 6 -> lem-sfb-nodal-derivation-local-descent

Conversely let $D'$ be a derivation on the normalization fixing the two branch points above $x$. It induces a derivation of $B$. Extend it to the $\mathfrak m_AB$-adic completion $P$ by [lem-weil-pbc-derivation-extends]. The two residue evaluations are continuous (their kernels contain $\mathfrak m_AB$), so their composites with the extended derivation are zero, as they already are on the dense subring $B$: for $b\in B$, subtract its residue in $k$ and use ideal preservation and $k$-linearity. A derivation kills an idempotent $e$, since $D'(e)=2eD'(e)$ implies, after multiplying by $e$ and subtracting, $eD'(e)=0$ and then $D'(e)=0$, in every characteristic. Hence the derivation on $P$ acts separately on the two factors and has zero residue in each. It therefore takes every equal-constant pair to a pair with both constants zero, and preserves $\widehat A$. For $a\in A$, $D'(a)\in B$ has image in $\widehat A$, so step 4 gives $D'(a)\in A$. This descends $D'$ to a derivation of $A$. The two procedures are inverse by uniqueness of extension to fractions.

Cited prerequisites: lem-weil-pbc-derivation-extends.

Source: literature/stacks-project/curves.tex, Tag 0E68 (lemma-nodal-vector-fields), reverse implication with completed membership descent; more-algebra.tex Tag 07PE (lemma-derivation-extends).

### Old step 7 -> parent assembly

These constructions glue to sheaf derivations. Indeed the extension on every localization is uniquely given by the quotient rule of [lem-weil-pbc-derivation-extends]; thus local constructions restrict to the same maps in the rational-function rings. Regularity was proved at nodes in steps 5--6, and elsewhere normalization is an isomorphism by step 2. This also proves uniqueness and additivity. At every smooth marked point that isomorphism identifies its ideal with the ideal of its unique preimage, so the fixed-marked-ideal conditions of step 1 become precisely the remaining conditions in $E_a$. A sheaf map on a disjoint union is a tuple of sheaf maps on its open-and-closed components; there are finitely many components by step 2, so their product of additive groups is their direct sum. We obtain the stated canonical additive identification.

Cited prerequisites: lem-weil-pbc-derivation-extends.

Source: literature/stacks-project/curves.tex, Tag 0E68 (lemma-nodal-vector-fields), globalization; section-vector-fields, fixed-point definition; more-algebra.tex Tag 07PE for restriction uniqueness.

### Old step 8 -> lem-sfb-smooth-derivation-zero-divisor

Let $X$ now be any smooth proper connected curve over $k$. It is integral by [lem-sc-smooth-connected-curve-local-rings]. Every closed point has residue field $k$: by [lem-kun-closed-point-field] it is finite over $k$, and an algebraically closed field has no proper finite field extension. By the universal property of [def-sc-relative-differential-sheaf], its derivations are the maps $\theta:\Omega^1_{X/k}\to\mathcal O_X$. By [lem-sc-canonical-sheaf] and [lem-pc-tensor-dual-invertible], these maps are global sections of the invertible sheaf $T=(\Omega^1_{X/k})^\vee$. At any closed point $q$, [lem-a1-uniformizer-differential-basis] applies, since $\kappa(q)=k$ is separable over $k$, and gives a basis $dt$ for a uniformizer $t$. The ideal of $q$ is locally $(t)$, so the Leibniz formula $D(th)=tD(h)+hD(t)$ says $D((t))\subseteq(t)$ exactly when $D(t)\in(t)$. But $D(t)=\theta(dt)$, so this condition is exactly vanishing of the corresponding section of $T$ at $q$. The assertion for the ideal sheaf follows stalkwise, since the ideal is the unit ideal away from $q$.

Cited prerequisites: def-sc-relative-differential-sheaf, lem-sc-canonical-sheaf, lem-pc-tensor-dual-invertible, lem-a1-uniformizer-differential-basis, lem-sc-smooth-connected-curve-local-rings, lem-kun-closed-point-field.

Source: literature/stacks-project/curves.tex, Tag 0E67 (lemma-smooth-vector-fields), universal derivation and fixed-point calculation; Tag 0C1E (lemma-uniformizer-works).

### Old step 9 -> lem-sfb-smooth-derivation-zero-divisor

Let $g$ be the genus. The degree homomorphism [def-sc-pic0] and [lem-sc-canonical-degree] give $\deg T=-(2g-2)=2-2g$. For completeness, the usual bound on zeros follows directly from the existing divisor statements. The curve is integral by [lem-sc-smooth-connected-curve-local-rings]. A nonzero global section $s$ of $T$ is a nonzero rational section: locally it is a function times a basis, and the local-to-generic maps are injective. By [def-sc-rational-section-divisor], $Z=\operatorname{div}(s)$ has at $q$ the valuation of that local coefficient. These integers are nonnegative because the coefficients are regular, and are positive exactly where $s$ vanishes. By [lem-sc-line-bundle-rational-section], $T\cong\mathcal O_X(Z)$, whence [def-sc-pic0] gives $\deg Z=\deg T=2-2g$. By step 8 all closed points have residue field $k$, so each distinct zero contributes at least one to this sum. If $g\ge2$ its right side is negative, impossible for a nonzero section. If $g=1$ it is zero, so there is no fixed point. If $g=0$ it is two, so there are at most two fixed points. Step 8 translates all three conclusions to derivations.

Cited prerequisites: def-sc-pic0, lem-sc-canonical-degree, lem-sc-smooth-connected-curve-local-rings, def-sc-rational-section-divisor, lem-sc-line-bundle-rational-section.

Source: literature/stacks-project/curves.tex, Tag 0E67 (lemma-smooth-vector-fields), degree argument; Tag 0BS6 (lemma-rr); divisors.tex Tags 02SF and 0BE6, divisor of a rational section.

### Old step 10 -> parent assembly

Finally $2g(C_a)-2+\#E_a>0$ forces $\#E_a\ge3$ for $g(C_a)=0$ and $\#E_a\ge1$ for $g(C_a)=1$. In those cases step 9 excludes any nonzero derivation fixing $E_a$; for $g(C_a)\ge2$ it excludes all nonzero derivations already. Every summand in step 7 is therefore zero, so its additive identification makes the infinitesimal marked automorphism group trivial. No markings are required in the construction: when $n=0$, $E_a$ consists only of node preimages, and when there are no nodes the normalization identification is the identity.

Cited prerequisites: none.

Source: literature/stacks-project/curves.tex, Tag 0E67 and Tag 0E68, arithmetic consequence for marked curves.

## Review by Q32

I read the item against curves.tex section-vector-fields, including the full statements and proofs of 0E67 (lemma-smooth-vector-fields) and 0E68 (lemma-nodal-vector-fields), and more-morphisms.tex 02H5 (lemma-action-by-derivations). For the completed normalization job I read varieties.tex 0C3V and the statements of the existing reduced-normalization, singular-skyscraper, ordinary-branches, dimension-of-completion, projectivity, completion-tensor and normal-power-series nodes. The finite-type hypothesis comes from properness; reducedness and dimension one are explicit, so the curve-normalization/completion theorem applies. The new node states the canonical maps and two residue maps needed downstream, rather than an arbitrary abstract isomorphism. It retains old step 2's local-to-global setup and step 3's equal-constant, fraction-ring and integral-closure calculations.

For local descent I read 07PE and the existing local-completion faithful-flat and universally-injective module statements. The hypotheses include the actual compatible finite normalization and completion model, not a product assertion for uncompleted stalks. Old step 4 tests classes in Q(A)/B and B/A; old steps 5 and 6 compute both directions, continuous extensions and their residue maps. Uniqueness follows from the quotient rule. A derivation of a product kills its idempotents in every characteristic; no characteristic-zero assumption has entered. This job explicitly includes the membership tests and completed formulas, so it does not hide those parts as unstated technical facts.

For the tangent-divisor job I read curves.tex 0E67 and 0C1E, the existing relative differential universal property, canonical invertibility/degree, tensor-dual, smooth-connected local-ring, closed-point field, rational-section-divisor and line-bundle-rational-section statements. The smooth proper curve is integral, each residue extension is trivial over the algebraically closed field, and dt is a basis at a uniformizer. Hence ideal preservation is exactly vanishing of the section. Nonzero generic germ and the divisor isomorphism justify effectivity, positive multiplicities at fixed points, and degree 2-2g. The new node stops at the divisor calculation; the parent itself proves the three numerical cases and the stability consequence.

For each assembly citation I opened the cited statement: step 1 uses only the actual split dual-number ring of def-sc-dual-numbers; step 2 uses all the finite geometry and compatible completed data stated by the new model; step 3 uses that model, both directions and uniqueness in the new local-descent statement, and the existing derivation extension lemma's quotient rule for overlaps. The smooth marked ideals are identified on the normalization-isomorphism locus, and finite many components turn product into direct sum. Step 4 takes the effective divisor, exact degree and fixed-point support literally stated in the tangent-divisor node. Step 5 is the elementary numerical inequality applied to steps 3 and 4. citations.json quotes each of these cited statements verbatim.

I checked B--E of delivery-errors: self-contained objects and definitions; statement-only new jobs; source tags and labels; searches run and actual log records retained; no claimed Mathlib match from analytic or manifold hits; no whole-item restatement; no parent-to-child cycle; no unsupported inference from another node's proof. Blueprint searches for vector fields, normalization completion, nodal, rational section and derivation gave no statement equal to a new node (the rational-section result is reused as future proof guidance). Small cases: the empty curve is separated before the nonempty model; disconnected reduced curves are allowed by that model; a smooth curve has no local node obligations; zero markings are allowed. The completed split node has two branches including characteristic two. At a self-node B may be a semilocal domain, which the new statement allows. P1 with zero through three special points has the expected zero bounds; genus one has a nowhere-vanishing nonzero field; negative tangent degree in genus at least two is incompatible with any nonzero section. No hypothesis or clause of the parent statement changed.

The retained old step longer than 2000 characters is now assigned to a separate statement-only job. Every new parent step is below 2000 characters, and the total assembly is 2485 characters. During self-review I clarified that completed extensions have the displayed formal shape; arbitrary formal coefficients are not asserted to algebraize. I also wrote scheme Noetherianity as quasi-compact plus locally Noetherian, so it supplies Noetherian local rings rather than merely a topological chain condition. No Lean file, repository file, or launcher script was written; no agents, compiler, Lake or local DAG checker was started.

## Unfinished work

None in this authorized repair: the three new unsplit statements are deliberately future workers' proof jobs.
