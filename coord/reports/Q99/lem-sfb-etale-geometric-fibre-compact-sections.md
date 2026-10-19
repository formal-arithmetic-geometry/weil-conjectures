# Q99: lem-sfb-etale-geometric-fibre-compact-sections

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-geometric-fibre-compact-sections.json`: statement node, now split into seven steps; no exact Mathlib match.
- `citations.json`: one verbatim cited statement for each of the 18 step/node pairs.
- `searches.jsonl`: five searches actually executed with the required msearch command, including a second semantic phrasing.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The sandbox also holds the worker's local JSON-writing script; it is not a delivered project file.

## Attachments

None. A whole-project search for the exact blueprint tag found no declaration. The notion searches under WeilConjectures/SixFunctors and WeilConjectures/AlgebraicGeometry found finite geometric fibre geometry and derived compact-support constructions, but no declaration with all clauses of this item, including the specified graph-generator germ formula. In particular the derived proper comparison in SixFunctors/Etale/Derived/LowerShriekToLowerStar.lean contains a sorry and does not state this result for arbitrary quasi-compact separated etale morphisms. No upstream master sorry declaration was treated as finished.

## WANTED

None. All sources used are present under literature/stacks-project.

## Corrections and scope

The existing item was an unsplit statement with no proof or audit. Its statement is correct, and is preserved verbatim, together with all original searches and blueprint ancestry. The new proof fills the finite-component calculation needed by its parent lem-sfb-quasifinite-compact-support-exact. The unit sk-lem-geo-affine-local, proof (2), uses exact sum extension to identify the final Hom groups; this calculation supplies the geometric fibre part of that comparison. Neither the unit nor the chapter route is changed.

The graph section is evaluated along the explicit map a=(r, w-bar q) from the geometric fibre to V times_T W. Spelling out this map removes any ambiguity in the phrase 'pullback to the fibre'. No finite-coefficient, Noetherian, finite-base-type, or constructibility hypothesis is used: A is an arbitrary commutative ring and F an arbitrary constant-A module sheaf. 'Constant-A module sheaf' means a module over the constant ring sheaf, not that F is a constant sheaf.

## Not duplicates

No new nodes. The DAG/tag and whole-blueprint searches found the existing general 09Z9 node sbc-lem-etale-over-normal, and the existing clopen-product, geometric-point-sections, inverse-image-germ and clopen-section nodes, so all were reused. The finite geometric point coproduct cohomology node was also read; the proof instead cites its existing underlying degree-zero ingredients so the restriction map and its germ normalization remain explicit. No new restatement of any clause of this item was introduced.

## Mathlib searches

Inherited searches were retained. Five new logged searches covered leanfinder (two phrasings), loogle, grep of AlgebraicGeometry, and leansearch. All services returned normally. Loogle and grep returned no hits. Semantic hits concern scheme structure-sheaf sections, affine scheme coproducts, topology-sheaf gluing, and formally etale algebras. Their printed types have those different objects, so none states the present result for arbitrary etale module sheaves, proper support and the graph map. No Mathlib leaf is claimed from those partial hits.

## Review by Q99

I read the item source in etale-cohomology.tex, Tag 09Z9 (lemma-normal-scheme-with-alg-closed-function-field), including the statement and its proof. For the section calculation I read Tag 03Q1 (lemma-stalk-pullback), especially the direct colimit proof of (3), Tag 03QT (theorem-equivalence-sheaves-point), and the finite-disjoint-union reduction at the beginning of the proof of Tag 0A5B (lemma-constant-smooth-statements). For the generator I read the graph construction in Tag 0F4L (lemma-shriek-into-star-separated-etale) and the statement and proof of more-etale.tex Tag 0F4Y (lemma-separated-etale-shriek). For support I read coherent.tex Tag 0CYR (lemma-union-closed-proper-over-base). These are Stacks sources; no SGA source is used. The assembled proof is honestly marked agent-written, since the exact combined formulation is not a single quoted theorem.

Step 1 uses exactly the clauses of lem-weil-pbc-etale-base-change-finite-limits, lem-weil-pbc-separated-base-change and lem-weil-pbc-qcqs-morphism-permanence that preserve etale, separated and quasi-compact morphisms under arbitrary base change. I opened their statements; none imposes Noetherian or finite-type conditions on the base-change scheme. I checked the source labels 02GO in morphisms.tex, and 01KU and 01K5 in schemes.tex. The extra hypotheses of the normal-base decomposition are verified here: a field is an integrally closed domain and is its own fraction field, and Omega is algebraically closed.

Step 2 uses the actual statement of sbc-lem-etale-over-normal, not its proof, to obtain disjoint open immersions. Its hypotheses were verified in step 1. The finite-subcover argument proves finiteness rather than assuming it; the fibre-product universal property in def-pc-fibre-product identifies the indexing set with precisely the Omega-valued lifts in the item. No claim that an arbitrary set-theoretic image determines a factorization of schemes is used: the components are open immersions and the source is the one-point Spec Omega, so the factorization is through an open subscheme. The structural isomorphism on a component forces the unique Omega-morphism.

Step 3 uses the global-sections clause of lem-weil-pbc-etale-sheaf-clopen-product, the actual degree-zero germ-map clause of lem-weil-pbc-geometric-point-cohomology, and both the isomorphism and germ-compatibility clauses of lem-weil-pbc-inverse-image-stalk-germ. I read all three statements. They apply to underlying abelian sheaves without a finiteness condition on the ring or the modules. The inverse-image lemma is applied to both the component inclusion and r; its direction gives the displayed map to F_v, rather than an unspecified abstract isomorphism. Naturality for multiplication by every a in A proves A-linearity.

Step 4 checks the support and its scheme structure. The geometric-point node allows every algebraically closed overfield, so a nonzero component section has a nonzero geometric germ at every geometric point on that component. The reduced-induced-closed-subscheme node states uniqueness for a reduced closed subscheme with a fixed support; Spec Omega is reduced. I checked that the finite-union node's statement uses properness of closed subsets in the reduced-support convention, not properness of an arbitrary subscheme structure. Its locally-finite-type hypothesis follows from the componentwise identity description in step 2. Each component is proper by the definition of a proper morphism, because its morphism to Spec Omega is an isomorphism. The empty support is handled separately, without silently assuming the union lemma requires a nonempty family.

Step 5 is elementary finite module algebra, with the inverse product-to-sum map and both composite checks written down. It introduces no lemma or hidden comparison. It preserves the component germ coordinates and hence the claimed naturality.

Step 6 reuses the base-change nodes to check every hypothesis of lem-weil-pbc-etale-section-clopen-immersion. The graph is a section of P to W, which is separated and etale even if W is not quasi-compact. That node explicitly states that the section is an isomorphism onto a clopen subscheme. The clopen-product node applies to the two-piece partition (graph and complement); it requires a finite number of pieces, not quasi-compact pieces. Its sheaf recovery/gluing clause supplies the section with z and zero. This is a construction of an actual sheaf section, not an objectwise identification of sections with the sum-extension presheaf.

Step 7 uses the pointed-neighbourhood colimit in def-weil-pbc-geometric-stalks and the full representative/germ formula of lem-weil-pbc-inverse-image-stalk-germ. These statements were opened and quoted verbatim in citations.json. The point of P is (v-bar,w-bar); it belongs to the graph precisely for v-bar=t w-bar. Restriction along the graph identifies the surviving germ with the given representative z. Restriction to the complement gives zero. This proves equality of the specified maps, not merely existence of some stalk isomorphism.

I checked delivery-errors B through E against the written node. There are no new nodes or leaf claims to audit for self-containedness or duplicate tags. Every non-elementary step cites existing statements supplying the facts it takes; no step uses an internal proof construction of a cited node. The newly used off-unit statements are general scheme or sheaf tools, declared in split_report.tool_uses with individual reasons; they do not replace the unit's adjunction route. No proof step exceeds 2000 characters (all are below 1200). I tested the empty fibre, a one-point fibre, two distinct points with one nonzero coordinate, the zero sheaf, the zero ring, a nonconstant sheaf with different modules on the two components, an arbitrary larger geometric residue field, and non-quasi-compact W. The decomposition, support argument and generator formula have the asserted behavior in all of these cases. No statement dispute or unfilled proof gap was found.

## Unfinished work

None within this one-level split. The existing cited nodes retain their own proof obligations. No new unsplit work is introduced.
