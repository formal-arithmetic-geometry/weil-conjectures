# Repair delivery: lem-pur-proetale-support-global-boundary

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-proetale-support-global-boundary.json — existing statement, unchanged; three assembly steps, 1813 proof characters.
- dag/nodes/sec-smooth-purity/lem-pur-support-injective-exact-models.json — statement, unsplit; no Mathlib match. Exact support/restriction rows and injective derived models (old steps 1–3).
- dag/nodes/sec-smooth-purity/lem-pur-derived-injective-cone-comparison.json — statement, unsplit; no Mathlib match. Generic right-derived-unit comparison of entire cone/quotient triangles (old steps 4–5).
- dag/nodes/sec-smooth-purity/lem-pur-injective-cone-boundary-descent.json — statement, unsplit; no Mathlib match. Generic positive-sign cone boundary, choice independence and descent to all derived morphisms (old steps 6–8).
- citations.json — verbatim statement excerpts for every citation of every parent step.
- report.md — this review, including the complete retained arguments for the future workers.

## Attachments

None. A notion and blueprint-tag search of lean/WeilConjectures found no complete project declaration for this item. I also read the actual existing module lean/Sheaf/AlgebraicGeometry/ProEtaleSupportGlobalBoundary.lean: supportGlobalTriangleComparison (line 220), supportGlobalComparisonNatural (line 274), and supportGlobalBoundaryNormalization (line 331) all end in sorry. They are not attachments. No Lean file was written and no compiler or build was run.

## WANTED

None: all sources needed for this re-split are present locally.

## What was wrong and how the return was repaired

The returned proof had eight steps and 5521 characters. It was mathematically reviewed previously, but the human now requires its work to be spread among independently claimable nodes. The provided sandbox was empty when this repair started, so I copied the current repository item, which contains the returned eight-step proof and all prior review/Lean metadata. No retained report or search log existed to overwrite. I preserved its statement, statement dependencies, source, origin, historical Mathlib searches, blueprint provenance, and Lean records. The current repository is the returned baseline available without git; the eight proof-step lengths agree with the return. This is a substantive three-node re-split, not an unchanged re-push or a prose abbreviation. The three new statements have comparable size (1756, 1917, and 1997 characters). Each has an empty proof and proof_deps, null proof_origin, status unsplit, complete hypotheses, source tags/labels, and its actual logged searches.

The parent keeps the support localization and supported long-exact-sequence interfaces, and instantiates the new generic lemmas. No new node restates the entire parent: the first has no boundary or triangle comparison, the second has no support/site or cocycle-boundary assertion, and the third has no geometric support model or derived-global triangle comparison. They expose three separate arguments for parallel future work. Every argument of the old proof is retained verbatim below, allocated to a new node, including the elementary calculations embedded in those arguments.

## Review by Q131

I read coord/brief-stage1.md, stages/1-dag.md, delivery-errors B–E in full, GOAL.md, the chapter and unit records, and SETUP.md's three levels. The current main-20261015 unit sk-prop-a1 still uses the localization triangle to pass from the Kummer class to the supported fundamental class. Its separate global assertion concerns modules. The orientation-uniqueness source, proof steps 1 and 3, is the nearest blueprint ancestor through the existing retracted-support comparison. The repair changes no chapter, unit route, coefficient category, or target statement.

For the item and the first new node I read Stacks etale-cohomology.tex, Tag 09XP, section-cohomology-support: injective restriction is surjective, its kernel is Gamma_Z, and this produces the global triangle. I read the adjacent Tag 09XQ, lemma-sections-with-support-acyclic, and the ringed-site module form in sites-cohomology.tex, Tag 093X, lemma-restriction-along-monomorphism-surjective. The latter assumes an injective module over a commutative ring sheaf and an actual monomorphism in the site, not an injective underlying abelian sheaf. U→X meets that hypothesis in the small pro-etale site. I retain quasi-compactness of j for the canonical supported-sheaf comparison and the sheaf support row. Thus the new exact-model statement does not infer surjectivity on global sections from a sheaf epimorphism. Exact j_!, i^* and j^* give the appropriate injectivity via their right adjoints; the existing injective support global-model node supplies i^!_0I and its kernel identification. All operations are ordinary module-sheaf operations; there is no completion or condensed-coefficient substitution.

For the second new node I read derived.tex, definition-cone and Tag 014Z, section-canonical-delta-functor. The cone is F^n ⊕ E^{n+1} with differential (db+u(a),−da), and the quotient is q(b,a)=v(b); Stacks uses −projection composed with inverse(q). I also read Tag 05TH, lemma-injective-acyclic, and the next existence lemma. The hypotheses explicitly include enough injectives in the source, bounded-below termwise injectivity of all three row complexes, and short exactness after T. These are verified by the first new node when T is global sections. The statement pins all three object comparisons by the inverse derived units, and explicitly includes the shift comparison and naturality at q; an arbitrary isomorphism of the three derived objects would not suffice. The finite-sum injectivity argument and the preservation of the cone differential, inclusion, negative projection and shifted differential are retained in the allocated argument below. This is an isomorphism of triangles in the derived category, not merely per-degree cohomology isomorphisms.

For the third new node I read Tag 014Z's negative projection and functoriality, homology.tex Tag 0117, lemma-long-exact-sequence-cochain (the snake construction and its naturality), and derived.tex Tags 070I and 070J, lemma-K-injective and lemma-bounded-below-injectives-K-injective. I recomputed d(b,−a)=(db−u(a),da)=0 and −projection(b,−a)=a: both minus signs are essential. Changing b by u(t) changes a by dt; changing c by dg and lifting g to h permits b+dh and leaves a unchanged. This yields the actual A-linear snake boundary, not just an unspecified natural transformation. The existing derived-injective-boundary statement explicitly normalizes the derived maps against this snake map. A chain map gives the displayed cone map and the boundary square because d(F(h)b)=F(h)(db). Bounded-below injective representatives and the K-injective Hom bijection allow every derived morphism. For a common homotopy H of representative maps, the induced cone homotopy has components (F(H),−S(H)) on the unshifted and shifted summands; naturality of u cancels the off-diagonal terms. Thus descent and changes of resolutions do not require F(I), S(I), or G(I) themselves to be injective modules.

I opened and read the statement of every node cited in the parent: step 1 also cites lem-pur-module-restriction-kernel-comparison for its explicit assertion that module sheaves on any small ringed site form an abelian category with enough injectives; then it uses the new exact-model statement for both rows, injectivity, representing objects, direct-image section formula, and the natural kernel comparisons; step 2 uses the new generic cone comparison for all arrow squares and the existing support-localization statement for the specified cone triangle and its counit/unit interpretation; step 3 uses the new functor-row boundary/descent statement for all integer degrees, positive sign, and derived naturality, and thm-pur-with-support-exactness for the supported cohomology long exact sequence. The latter is the long exact sequence of the same kernel/restriction construction, not an assertion that its bare existence alone fixes a sign: the normalization is supplied explicitly by the new cone-boundary lemma and its cited derived-injective-boundary interface. I repaired the inherited implicit use of enough injectives by citing that general ringed-site statement directly; the etale-only module-sheaves-enough-injectives lemma would not suffice here. The parent has the finite coefficient and quasi-compactness hypotheses needed for every specialization. citations.json quotes statements verbatim; no argument hidden inside an old proof is cited as though it were its statement.

I separately read the old proof's cited statements: support-exact fixes the first map as the supported-kernel inclusion; ringed-open-closed gives exact j_! and its adjunction; right-adjoint-preserves-injectives has the exact-left-adjoint hypothesis; injective-support-global-model gives i^!_0I and its derived/global kernel identification; right-derived-plus-injective clause (2) gives the unit isomorphisms; ringed-site-injective-mono-restriction is genuinely for module sheaves; cone-short-exact-quasi-iso gives both quotient quasi-isomorphisms; complex-ses-long-exact-naturality gives the boundary square; dplus-injective-representative clause (2) and kinjective-hom-derived give the resolution descent. These facts are work ingredients for the newly queued statements; they have not been silently assumed in an elementary parent step.

Edge cases: Z=X gives C=0 and the identity first map; Z empty gives E=0 and the identity restriction; A=0 makes all models zero. In all cases the boundary formula is zero as required. The two generic nodes allow zero complexes, identity rows, and arbitrary lower bounds; n ranges over all integers, including negative n, so there is no hidden nonnegative-index truncation. The generic boundary lemma assumes exactness only on injectives, and does not assert exactness on arbitrary objects. The cone-comparison lemma assumes its T-image row exact rather than incorrectly treating every additive functor as exact. The target statement itself needed no correction, so no STATEMENT-DISPUTED claim is introduced.

The search log contains distinct leanfinder, loogle, grep and leansearch calls for each new statement, and a second semantic phrasing for each. I read the hits. The sheaf hits concern local injectivity of morphisms, not injective objects or the support row. The cone hits triangleOfSES, triangleOfSESIso and mapTrianglehIso do not compare a right-derived functor with the termwise functor via its units. The homologySequenceδ_triangleh lemma in Mathlib/Algebra/Homology/HomotopyCategory/ShortExact.lean:84 is a useful ingredient, but it does not state descent for a row of functors exact on injectives and its all-representatives normalization. I read it and the derived-category short-exact triangle implementation at ShortExact.lean:45–110. No claimed absence is based on a service outage, and no unrun query is recorded. All new nodes remain unsplit.

B–E review: the new statements introduce every object and use TeX once, source tags with labels, and definition dependencies; contain no proof sketches or steps; and have complete logged searches. Duplicate searches covered the whole DAG (tags and concepts), blueprint_refs search (cone, cone quotient, injective support, boundary, derived connecting), and project Lean source. The closest comparisons are discussed below. The parent is below 3000 characters and has no long hidden argument. New proof dependencies do not point back to the parent, and no new definition is introduced. No SGA source is used. Only the sandbox is written; the server tools perform the required checks and git delivery.

## Preserved argument allocation

These are the full returned arguments, retained for the workers who will split the three new nodes. They are report material, not proof steps inside the statement-only new nodes.

### Old step 1 → lem-pur-support-injective-exact-models

Write $\mathcal E=i_*i^!_0I$, $\mathcal B=I$, and $\mathcal C=j_*j^*I$. The supported-kernel comparison identifies $\mathcal E$ with $\ker(\mathcal B\to\mathcal C)$, and the injective support exactness lemma gives $0\to\mathcal E\xrightarrow{u}\mathcal B\xrightarrow{v}\mathcal C\to0$ degreewise. The first map is the kernel inclusion under this comparison, not an arbitrarily scaled map. The support localization theorem identifies its associated cone triangle with the triangle of the statement, with first arrow the support counit and second arrow the open unit.

Cited ingredients: def-pur-flasque-support, lem-pur-support-exact, lem-pur-support-localization-triangle.

### Old step 2 → lem-pur-support-injective-exact-models

The ringed open-closed lemma supplies the exact left adjoint $j_!$ of $j^*$. Thus $j^*I$ is termwise injective by the right-adjoint injectivity lemma. Exactness of $j^*$ shows that it represents $j^*K$. Both $i_*$ and $j_*$ preserve injectives by the same lemma, since their left adjoints $i^*,j^*$ are exact. The injective support global model says that $i^!_0I$ is termwise injective and represents $SK$. Therefore $\mathcal E,\mathcal B,\mathcal C$ are bounded-below complexes of injectives on $X$. The derived-unit comparisons for such complexes compute $R\Gamma(X,-)$ by ordinary sections; they compute $R\Gamma(U,j^*K)$ by $\Gamma(U,j^*I)$ and $R\Gamma_Z(X,K)$ by $\Gamma_Z(X,I)$.

Cited ingredients: lem-weil-pbc-proetale-ringed-open-closed, def-weil-pbc-proetale-operations, lem-sp-right-adjoint-preserves-injectives, lem-pur-proetale-injective-support-global-model, lem-weil-pbc-right-derived-plus-injective, def-pur-support-cohomology.

### Old step 3 → lem-pur-support-injective-exact-models

On the chosen small model of the pro-etale site, the complementary open $U\to X$ is a monomorphism into the terminal object. Apply the ringed-site injective restriction lemma to each $I^r$, with the constant ring sheaf $A_X$: $I^r(X)\to I^r(U)$ is surjective. This uses injectivity as an $A_X$-module, without asserting injectivity of the underlying abelian sheaf. Set $E=\Gamma_Z(X,I)$, $F=I(X)$, and $G=\Gamma(U,j^*I)$. Sections preserve the kernel in step 1, so $0\to E\xrightarrow{u_X}F\xrightarrow{v_X}G\to0$ is degreewise short exact. The equality $\Gamma(X,j_*j^*I)=\Gamma(U,j^*I)$ is the defining section formula for direct image, and identifies $\Gamma(X,v)$ with restriction.

Cited ingredients: lem-pur-ringed-site-injective-mono-restriction, def-pur-flasque-support, def-weil-pbc-proetale-operations.

### Old step 4 → lem-pur-derived-injective-cone-comparison

Let $P=\operatorname{Cone}(u)$ with the convention of the statement. Its terms $I^r\oplus\mathcal E^{r+1}$ are injective: given a map from a subobject into this finite direct sum, extend each component by injectivity and pair the two extensions. Thus $P$ too is a bounded-below injective complex. The derived-unit comparisons consequently identify $R\Gamma(X,P)$ with $\Gamma(X,P)=\operatorname{Cone}(u_X)$, since sections preserve finite direct sums and the displayed differential matrix. They identify the cone inclusion with the inclusion of $F$ and the third map with $-\operatorname{pr}_E$, including the shift: sections sends the shifted differential $-d$ to $-d$. The first term is $E$ by the sectionwise supported-kernel comparison. Hence these comparisons identify the entire derived-global cone triangle and its first two arrows, not just its three objects.

Cited ingredients: def-pur-support-triangle, def-weil-abstract-derived-category, lem-weil-pbc-right-derived-plus-injective, lem-pur-proetale-injective-support-global-model.

### Old step 5 → lem-pur-derived-injective-cone-comparison

The cone-to-quotient lemma applies to the sheaf sequence of step 1 and the module sequence of step 3. Their comparison maps are respectively $q:P\to\mathcal C$, $(b,a)\mapsto v(b)$, and $q_X:\operatorname{Cone}(u_X)\to G$, $(b,a)\mapsto v_X(b)$, and both are quasi-isomorphisms. The derived-unit comparisons are natural for $q$, so $R\Gamma(X,q)$ is identified with $\Gamma(X,q)=q_X$ between the injective models. Inverting these maps identifies the global third arrow with $(-\operatorname{pr}_E)\circ q_X^{-1}:G\to E[1]$. Together with step 4 this gives the asserted identification of the whole support triangle with the global supported-cohomology triangle and the direct-image/sections comparison on its third object.

Cited ingredients: lem-pc-cone-short-exact-quasi-iso, lem-weil-pbc-right-derived-plus-injective, def-weil-abstract-derived-category.

### Old step 6 → lem-pur-injective-cone-boundary-descent

Fix any integer $q$ and a cocycle $c\in G^q$. Step 3 gives a lift $b\in F^q$. Since $v_X(db)=dc=0$, there is a unique $a\in E^{q+1}$ with $u_X(a)=db$. Then $u_X(da)=d^2b=0$ and injectivity of $u_X$ gives $da=0$. In the cone, $d(b,-a)=(db-u_X(a),da)=0$ and $q_X(b,-a)=c$. The third arrow is minus projection, so it sends this cocycle to $a$. Thus the induced boundary sends $[c]$ to $[a]=[db]$ under the kernel identification. Both minus signs are necessary: one in $(b,-a)$ and one in the third arrow.

Cited ingredients: def-pur-support-triangle, def-weil-abstract-derived-category.

### Old step 7 → lem-pur-injective-cone-boundary-descent

The result is independent of choices: another lift $b+u_X(t)$ changes $a$ to $a+dt$, and replacing $c$ by $c+dg$ permits the lift $b+dh$ for any lift $h$ of $g$, leaving $a$ unchanged. Addition and $A$-linearity follow by adding and scaling lifts. This is exactly the usual cochain snake construction for the short exact sequence in step 3. The derived injective boundary normalization identifies that snake boundary with the natural derived supported-cohomology boundary, whose long exact sequence is the one in the support exactness theorem. The kernel functor used there is precisely $\Gamma_Z$, so the map just computed is $\partial$ with no sign change.

Cited ingredients: lem-pur-derived-injective-boundary, def-pur-support-cohomology, thm-pur-with-support-exactness.

### Old step 8 → lem-pur-injective-cone-boundary-descent

For a chain map $f:I\to I\prime$, restriction and the kernel inclusion give a morphism of the short exact sequences of steps 1 and 3. On cones it is $(b,a)\mapsto(fb,fa)$; this commutes with $q_X$ and minus projection. On cocycles, $fb$ lifts $fc$ and $d(fb)=f(db)$, giving the boundary square explicitly; the general long-exact-sequence naturality lemma gives the same square. Finally each bounded-below injective complex is K-injective, and morphisms into a K-injective are computed in the homotopy category. Thus every derived morphism between the represented objects is given by such a chain map, uniquely up to homotopy. All additive functors here carry a homotopy to its termwise image, so the comparisons and squares are independent of that representative and natural in $K$, including comparison between two injective resolutions.

Cited ingredients: lem-weil-pbc-complex-ses-long-exact-naturality, lem-weil-pbc-dplus-injective-representative, lem-weil-pbc-kinjective-hom-derived, lem-pur-support-localization-triangle.

## Not duplicates

The same-tag comparison below includes source-tag collisions and the especially close conceptual hits. Shared Stacks tags are not assertions of equal statements. Existing statements remain available as ingredients when these new tasks are split; no existing node is edited.

lem-pur-derived-injective-cone-comparison vs lem-pur-derived-injective-boundary: The existing “Normalized derived connecting maps from sequences exact on injectives” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-pur-derived-representable-transport: The existing “Derived transport of represented left exact functors through injective comparisons” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-pur-etale-injective-support-sequence: The existing “Degreewise-injective ordinary etale support sequence” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-pur-kernel-shifted-cone-boundary: The existing “The shifted cone boundary agrees with the kernel connecting map” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-pur-module-restriction-kernel-comparison: The existing “Forgetting constant module coefficients compares derived restriction kernels” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-pur-normalized-comparison-augmented-resolution: The existing “A normalized derived comparison on a common augmented resolution” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-pur-proetale-injective-support-global-model: The existing “Injective model for global sections of the closed support object” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-pur-proetale-support-global-boundary: This is the parent assembled from three smaller arguments: the new statement omits the other two arguments and therefore cannot prove the complete parent by itself.

lem-pur-derived-injective-cone-comparison vs lem-pur-ringed-site-injective-mono-restriction: The existing “Injective modules on a ringed site restrict surjectively along monomorphisms” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-pur-support-exact: The existing “The exact sequence of supported sections for injective objects” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-pur-support-pair-chain-coherence: The existing “Adjoint chain maps on restriction kernels: maps and homotopies” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-sc-derived-lower-truncation-unit-bridge: The existing “Bottom derived unit through good lower truncation” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-sc-p1-ext-resolution-derived-connecting: The existing “Injective-resolution and derived connecting maps agree” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-sc-p1-right-derived-triangle-connecting: The existing statement derives a single left-exact functor on a short exact sequence of objects via horseshoes; the new comparison derives an additive functor on an existing exact row of bounded-below injective complexes.

lem-pur-derived-injective-cone-comparison vs lem-sp-derived-functor-single-identification: The existing “The derived functor on an object placed in degree 0 computes the classical right derived functors” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-weil-pbc-complex-ses-connecting-formula: The existing “Formula for the connecting morphism of a split short exact sequence of complexes” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-weil-pbc-complex-ses-homology-long-exact: The existing “Long exact cohomology sequence of a short exact sequence of cochain complexes” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-weil-pbc-complex-ses-long-exact-naturality: The existing “Naturality of the long exact cohomology sequence of short exact sequences of complexes” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-weil-pbc-dplus-injective-representative: The existing “Every object of D^+ is represented by a bounded below K-injective complex of injectives” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-weil-pbc-exact-functor-ses-triangle-image: The existing statement assumes the functor exact and a sequence of objects in degree zero; the new statement allows a nonexact additive functor and arbitrary bounded-below injective complexes, pinning its total-derived-unit comparison.

lem-pur-derived-injective-cone-comparison vs lem-weil-pbc-kinjective-hom-derived: The existing “Morphisms into a K-injective complex are computed in the homotopy category” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-weil-pbc-resolution-pullback-augmentation: The existing “Exact pullback and localized resolution augmentations” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-weil-pbc-right-derived-injective-sequence: The existing “Long exact derived sequence for a short exact sequence of additive functors” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-weil-pbc-right-derived-pair-sequence: The existing “Natural long exact sequence from a pair sequence exact on injectives” has its specified objects or functor comparison; the new statement pins the inverse derived units on all components of an arbitrary injective exact row and its cone quotient, with a potentially nonexact additive functor.

lem-pur-derived-injective-cone-comparison vs lem-weil-pbc-right-derived-plus-injective: The existing statement constructs derived functors and units on injective complexes, but does not compare cone/quotient triangle arrows or their signs.

lem-pur-injective-cone-boundary-descent vs lem-cbc-kinjective-derived-mapping-complex: The existing “K-injective targets compute enhanced derived mapping complexes” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-kun-right-derived-single-h0: The existing “Zeroth homology of the canonical right-derived single augmentation” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-pc-abelian-cech-augmentation-boundary-squares: The existing “The alpha and beta augmentation boundary squares” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-pc-abelian-cech-comparison-boundary: The existing “Boundary compatibility for canonical augmentation quotients” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-pc-abelian-cech-ext-section-boundary: The existing “The Ext boundary is the prescribed horseshoe section boundary” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-pc-abelian-cech-horseshoe-total-boundary: The existing “Total boundary naturality for a prescribed horseshoe” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-pc-bounded-exact-term-hom-quasi-iso: The existing “Bounded exact-term Hom preserves quasi-isomorphisms” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-pc-stupid-tail-hom-short-exact: The existing “Natural short exact Hom sequences for a stupid source tail” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-pur-derived-injective-boundary: The existing statement supplies snake-normalized natural cohomology transformations; the new statement identifies an explicit cone roof with them, gives the elementwise positive lift formula, and descends the cone maps themselves.

lem-pur-injective-cone-boundary-descent vs lem-pur-etale-injective-support-sequence: The existing “Degreewise-injective ordinary etale support sequence” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-pur-kernel-shifted-cone-boundary: The existing statement compares a shifted cone of restriction with its kernel in a fixed abelian category; it does not construct the functor-row derived boundary or its all-injective-representatives normalization.

lem-pur-injective-cone-boundary-descent vs lem-pur-module-restriction-kernel-comparison: The existing “Forgetting constant module coefficients compares derived restriction kernels” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-pur-module-supported-hom-transport: The existing “Exact transport of module-valued normalized supported Hom” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-pur-proetale-injective-support-global-model: The existing “Injective model for global sections of the closed support object” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-pur-proetale-support-global-boundary: This is the parent assembled from three smaller arguments: the new statement omits the other two arguments and therefore cannot prove the complete parent by itself.

lem-pur-injective-cone-boundary-descent vs lem-pur-ringed-site-injective-mono-restriction: The existing “Injective modules on a ringed site restrict surjectively along monomorphisms” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-pur-support-exact: The existing “The exact sequence of supported sections for injective objects” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-pur-support-pair-chain-coherence: The existing statement concerns site-change evaluation/kernel diagram maps of abelian sheaves, without signed cone boundaries or arbitrary additive module-valued functor rows.

lem-pur-injective-cone-boundary-descent vs lem-sbc-ambient-operations-scalar-linearity: The existing “Scalar linearity of ordinary unbounded ringed pro-etale operations” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sbc-unbounded-exact-adjunction-square: The existing “Constant towers and evaluations preserve the unbounded derived adjunctions of a ringed morphism” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sc-boundary-horseshoe-representative: The existing “Global horseshoe representative of the cohomology boundary” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sc-localized-complex-qc-homology-extension: The existing “Extension closure of quasi-coherent cohomology on a localized open site” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sc-p1-ext-resolution-derived-connecting: The existing statement is specific to Ext in a fixed argument and a sequence of objects; the new statement is for arbitrary additive module-valued functor rows exact on injectives.

lem-pur-injective-cone-boundary-descent vs lem-sc-p1-nat-complex-derived-boundary: The existing “Nonnegative complex boundaries agree with derived triangle boundaries” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sc-p1-rhom-hom-derived-roof: The existing “Natural RHom comparison with the cocycle roof formula” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sc-p1-rhom-hom-derived-roof-shift: The existing “Unit-shift coherence of a roof-normalized natural RHom comparison” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sc-p1-rhom-hom-derived-roof-shift-injective-cocycle: The existing “Shift coherence on a single cocycle in an injective representative” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sc-p1-rhom-injective-cocycle-bijective: The existing “Bijectivity forced by the injective cocycle formula” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sc-p1-rhom-natural-cocycle-map: The existing “Natural additive RHom map normalized on injective cocycles” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sc-p1-right-derived-triangle-connecting: The existing “Right-derived connecting maps agree with the derived triangle” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sf-exact-localization-derived-triangle: The existing “Natural derived triangle of an exact localization sequence” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sfb-independent-bounded-exact-term-hom: The existing “Bounded exact-term internal Hom comparison at independent universes” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sfb-kinjective-hom-scalar-telescope: The existing “Functorial K-injective Hom and scalar telescopes agree on every leg” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sfb-ordinary-proetale-direct-image-plus-comparison: The existing “Ordinary intrinsic pro-étale direct image: K-injective and bounded-below comparison” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sfb-scalar-hom-telescope-evaluation: The existing “Scalar localization internal-Hom comparison with every telescope leg and evaluation” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sp-exact-pullback-derived-adjunction: The existing “Normalized derived adjunction of exact module pullback” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-sp-levelwise-kinjective-tower-image: The existing “Levelwise K-injective towers compute additive functors applied levelwise” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-trf-filtered-hom-complex-invariance: The existing “Homotopy and graded quasi-isomorphism invariance of the shift-filtered Hom complex” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-trf-proetale-unit-leray-chain-formula: The existing “Chain representative for ordinary pro-etale module cohomology pullback” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-kinjective-total-derived-linear: The existing “K-injective total right derived functors preserve scalar linearity” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-complex-ses-connecting-formula: The existing statement assumes a degreewise split row and specified sections/retractions; the new boundary statement assumes only exactness on injectives and includes derived descent without such splittings.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-complex-ses-homology-long-exact: The existing statement gives a long exact sequence of a fixed complex row, not the derived functor-row cone transformation and its normalization for all injective representatives.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-complex-ses-long-exact-naturality: The existing statement gives naturality for a fixed morphism of exact complex rows; it does not descend a functor-row cone roof to D^+ or fix its elementwise sign.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-derived-exchange-bounded-comparison: The existing “The bounded below exchange comparison equation” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-derived-exchange-module-termwise: The existing “K-injective representative of the module derived exchange mate” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-derived-exchange-unbounded-transport: The existing “Transport of the exchange equation to arbitrary K-injective representatives” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-dplus-injective-representative: The existing statement supplies bounded-below injective representatives and their K-injectivity; the new statement concerns functorial cone roofs and their normalized boundary on those representatives.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-exact-functor-ses-triangle-image: The existing “An exact functor carries the triangle of a short exact sequence to the triangle of the image sequence” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-flat-restriction-derived-mate: The existing “FlatRestrictionDerivedMate” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-free-sheaf-derived-sections: The existing “Free sheaf shifted Hom computes derived module global sections” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-horseshoe-delta-functor: The existing “The connecting maps of right derived functors computed from horseshoe resolutions are well defined and natural” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-kinjective-exact-square-comparison: The existing “Normalized right-derived comparison for a K-injective-preserving exact square” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-kinjective-hom-derived: The existing statement identifies Hom sets after localization; the new one uses that fact to descend specific functor-row cone roofs and their normalized boundary maps.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-kinjective-pullback-abutment: The existing “K-injective representative of the unit--Leray abutment map” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-kinjective-unit-leray: The existing “Unit--Leray computation on K-injective complexes” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-right-derived-binary-product: The existing “Binary product comparison for right derived functors” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-right-derived-injective-sequence: The existing statement asserts an exact sequence for R^n on objects and natural n, not the cone roof on D^+, its all-integer lift formula, or changes of injective models.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-right-derived-pair-sequence: The existing statement concerns a four-functor difference-map row on objects and natural n; the new one concerns a three-functor cone boundary on all bounded-below derived objects with explicit sign and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-right-derived-plus-injective: The existing “Right derived functor on bounded below derived categories, computed on bounded below complexes of injectives” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs lem-weil-pbc-sequential-tower-evaluation-full: The existing “Compatible derived evaluations lift to a strict derived tower map” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs stage3-boundary-global-lift: The existing “Global lift and cycle in a compatible horseshoe” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-injective-cone-boundary-descent vs stage3-boundary-identification: The existing “Horseshoe representative and canonical boundary comparison” treats its specified cohomology or derived comparison; the new statement constructs the signed cone-roof transformation for an arbitrary additive module-valued functor row exact on injectives, with its lift formula and homotopy descent.

lem-pur-support-injective-exact-models vs def-per-canonical-etale-supported-pullback: The existing “Canonical etale pullback on closed-supported sections and its derived map” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs def-per-closed-support-plus-adjunction: The existing “Bounded-below closed-support right adjoint and its fixed adjunction” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs def-pur-coordinate-germ-cohomology-classes: The existing “CoordinateGermCohomologyClasses” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs def-pur-coordinate-germ-concentration-data: The existing “CoordinateGermConcentrationData” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs def-pur-etale-coordinate-support: The existing “Ordinary etale sheaf support and normalized supported germ maps” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs def-pur-etale-supported-kernel: The existing “Sheaf-valued supported kernel and supported closed inverse image” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs def-pur-supported-class-normalizations: The existing “Shared derived localization and elementary normalizations of supported signed-twist classes” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs def-pur-supported-localization-comparisons: The existing “Canonical open-product and support comparisons for localization” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-per-etale-closed-sheaf-internal-adjunction: The existing “Closed support kernel and internal sheaf adjunction over an arbitrary ring” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-per-etale-godement-supported-exact-model: The existing “Etale Godement model exact on supported coefficient terms” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-per-finite-coefficient-coinduction-locality: The existing “Locality of derived finite-coefficient coinduction” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-per-ind-etale-closed-support-base-change: The existing “Ind-etale base change for the closed etale support right adjoint” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-affine-coordinate-support-stalk-continuity: The existing “Affine continuity for coordinate-supported geometric stalks” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-concentrated-support-etale-transfer: The existing “Etale transfer of a concentrated supported normal-slice comparison” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-derived-injective-boundary: The existing “Normalized derived connecting maps from sequences exact on injectives” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-etale-injective-support-sequence: The existing statement is on the etale site and lacks the global exact row; the new statement is on the ordinary pro-etale module sites and includes that row and its injective computations.

lem-pur-support-injective-exact-models vs lem-pur-etale-supported-kernel-adjunction: The existing “Closed etale support kernel and its exact left adjoint” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-exact-derived-mate: The existing “Mates of exact unbounded derived squares on complex models” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-finite-type-coordinate-support-orientation: The existing “Ordinary etale finite-type coordinate support orientation and field normalization” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-kernel-shifted-cone-boundary: The existing “The shifted cone boundary agrees with the kernel connecting map” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-module-restriction-kernel-comparison: The existing statement compares module and underlying-abelian supported kernels under scalar forgetting, rather than constructing the support/open injective sheaf models.

lem-pur-support-injective-exact-models vs lem-pur-proetale-injective-support-global-model: The existing statement identifies i^!_0I and supported global sections but does not give the open restriction model, injectivity of all three X-models, or both exact rows.

lem-pur-support-injective-exact-models vs lem-pur-proetale-support-global-boundary: This is the parent assembled from three smaller arguments: the new statement omits the other two arguments and therefore cannot prove the complete parent by itself.

lem-pur-support-injective-exact-models vs lem-pur-relative-support-bottom-descent: The existing “Descent in the bottom supported degree of a smooth pair” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-relative-support-coordinate-model: The existing “Geometric normal-slice comparison for supported cohomology” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-relative-support-vanishing: The existing “Lower supported-degree vanishing for a smooth pair” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-ringed-site-injective-mono-restriction: The existing statement gives surjective restriction for one injective module on a site; it does not construct the support sheaf row or identify all three derived models.

lem-pur-support-injective-exact-models vs lem-pur-support-comparison-boundary: The existing “Site comparison preserves the support localization boundary” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-support-comparison-section-model: The existing “The common section model represents the specified support comparisons” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-support-exact: The existing statement gives the sheaf support row only; it does not give surjectivity of global restriction or all injective/global models.

lem-pur-support-injective-exact-models vs lem-pur-support-pair-chain-coherence: The existing “Adjoint chain maps on restriction kernels: maps and homotopies” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-support-site-comparison: The existing “Etale-proetale comparison for supported sections and their exterior products” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-supported-affine-line-homotopy: The existing “Affine-line invariance of finite supported cohomology” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-supported-coefficient-derived-open-mate: The existing “Derived open support coefficient mate on homotopy models” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-supported-coefficient-open-mate-quotient: The existing “Ordinary open support mate preserves the constant coefficient quotient” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-supported-coefficient-open-tensor: The existing “Supported coefficient tensor comparison under first-variable open restriction” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-supported-coefficient-second-open-tensor: The existing “Supported coefficient tensor comparison under second-variable open restriction” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-supported-cup-functoriality: The existing “Pullback and symmetry of supported Kummer cup products” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-supported-exterior-product-boundary: The existing “Supported exterior products commute with connecting maps in both variables” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-supported-exterior-product-support-maps: The existing “Supported exterior products are natural in normalized support maps” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-supported-product-localization: The existing “Supported exterior products respect localization triangles” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-supported-product-localization-first-map: The existing “Component maps extend to a triangle morphism (first variable)” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-supported-product-localization-second-map: The existing “Component maps extend to a triangle morphism (second variable)” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-supported-product-support-congruence: The existing “The supported product is invariant under equality of closed supports” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-pur-supported-tensor-comparison-naturality: The existing “Derived coefficient tensor comparisons are natural in coefficient maps” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-sc-p1-ext-resolution-derived-connecting: The existing “Injective-resolution and derived connecting maps agree” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-sc-p1-right-derived-triangle-connecting: The existing “Right-derived connecting maps agree with the derived triangle” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-weil-pbc-complex-ses-connecting-formula: The existing “Formula for the connecting morphism of a split short exact sequence of complexes” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-weil-pbc-complex-ses-homology-long-exact: The existing “Long exact cohomology sequence of a short exact sequence of cochain complexes” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-weil-pbc-complex-ses-long-exact-naturality: The existing “Naturality of the long exact cohomology sequence of short exact sequences of complexes” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-weil-pbc-dplus-injective-representative: The existing “Every object of D^+ is represented by a bounded below K-injective complex of injectives” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-weil-pbc-exact-functor-ses-triangle-image: The existing “An exact functor carries the triangle of a short exact sequence to the triangle of the image sequence” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-weil-pbc-injective-sheaf-mono-restriction: The existing “Injective abelian sheaves restrict surjectively along monomorphisms” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-weil-pbc-kinjective-hom-derived: The existing “Morphisms into a K-injective complex are computed in the homotopy category” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-weil-pbc-right-derived-injective-sequence: The existing “Long exact derived sequence for a short exact sequence of additive functors” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-weil-pbc-right-derived-pair-sequence: The existing “Natural long exact sequence from a pair sequence exact on injectives” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

lem-pur-support-injective-exact-models vs lem-weil-pbc-right-derived-plus-injective: The existing “Right derived functor on bounded below derived categories, computed on bounded below complexes of injectives” concerns its stated support comparison or auxiliary site construction; the new statement simultaneously gives the pro-etale injective sheaf row, exact global restriction row, and all their derived models, not that comparison.

## What remains

The three new statement-only nodes require future workers' proofs, as expressly required by the re-split return. There is no missing work in this stage-1 parent split. The delivery dry run and push are performed after this report is written; their authoritative results are the delivery-tool output.
