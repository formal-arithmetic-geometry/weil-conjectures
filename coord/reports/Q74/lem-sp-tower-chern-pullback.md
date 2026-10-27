# Q74: lem-sp-tower-chern-pullback

## Files written

- dag/nodes/sec-smooth-purity/lem-sp-tower-chern-pullback.json: statement preserved, status split, seven complete proof steps, refreshed actual Mathlib searches, blueprint provenance and declared generic tool uses.
- citations.json: 22 literal quotations, one per cited node per proof step, checked against the current repository statements.
- report.md: this report.

New nodes: 0. Mathlib leaves: 0. The scalar/geometry comparison required here already exists as lem-pur-algebra-diagram-pullback-extension-coherence. No new node is needed for the explicit gluing map or the two-term kernel calculation.

## Attachments

None. I searched WeilConjectures for the blueprint tag, tower/Chern combinations, Kummer, and the concrete Chern pullback declarations. AlgebraicGeometry.Scheme.Pic.chernClassRootsOfUnity_map (WeilConjectures/EtaleCohomology/Purity/Smooth/KummerChernClass.lean:43) concerns ordinary etale cohomology at a single exponent. AlgebraicGeometry.Etale.leftDerivedUpperStar_map_chernClass (WeilConjectures/EtaleCohomology/Purity/Smooth/ExtendScalarsCohomologyPullback.lean:362) concerns a fixed coefficient ring on the ordinary etale site. Neither states an equality in the varying-ring tower derived category of the item. I did not treat these as attachments or use their proofs as axiomatic tower inputs.

## WANTED

None. All literature needed for this split is present.

## Corrections and scope

No statement dispute or statement change. The item was unsplit and the sandbox initially contained no item or previous split. Its statement already carefully distinguishes actual tower-derived morphisms from their finite evaluations; the proof preserves that distinction. There is no appeal to evaluation being faithful on arbitrary derived morphisms and no deduction of coefficient-linear equality from forgetting scalars.

The blueprint's classes paragraph (2) compresses the coefficient-linear realization into an unsupported 'since' if read alone. The reviewed det-sp-tower-classes statement supplies the actual scalar-extension construction, which I use. I do not use the blueprint's phrase to assert that every integral class with torsion target lifts uniquely to a module-derived class.

The chapter and tower-geometric unit remain unchanged. The split serves the classes-and-integration step and the base-change-of-projective-line-trace sentence of det-sp-tower-p1-adjunction. Generic homological and diagram tools from other units are declared in split_report.tool_uses; they implement that route rather than replace it.

## Searches and duplicate checks

I ran tools/blueprint_refs.py ancestor for the item and searched all blueprint nodes for Kummer and Chern. I searched the whole DAG for inverse-image/scalar-extension comparisons, extensions and their naturality, root tower pullback, concentrated derived objects and successive scalar extension. In particular, I read the statements of lem-pur-algebra-diagram-pullback-extension-coherence, lem-pur-quotient-system-flat-models, lem-sfb-normalized-scalar-boundary-naturality and lem-sfb-divisible-extension-derived-reduction. The last two fixed-multiplication lemmas do not directly cover the varying n tower, so the split uses the genuine whole-diagram lemma and the explicit simultaneous resolution instead. The item's nearest blueprint ancestor is det-sp-tower-p1-adjunction; no blueprint statement duplicates this arbitrary-line-bundle tower assertion.

The five fresh searches are logged in searches.jsonl and appended verbatim by tool/query in the node: Loogle "Chern" returned matcher-name declarations; Mathlib/AlgebraicGeometry grep returned no Chern/Kummer hits; LeanSearch returned ordinary presheaf naturality, module pullback and a snake-lemma identity; the two differently phrased LeanFinder queries returned ordinary module pullback/composition, quasicoherent presentations, cohomology definitions and local-cohomology diagrams. I read the returned types. These are neither the whole-system Kummer realization nor its naturality. Historical searches already present on the item were retained.

## Not duplicates

No new nodes, so there are no new/existing same-tag pairs. The gluing and kernel calculations are steps rather than redundant lemmas. Existing generic coherence statements are cited directly.

## Review by Q74

I read the current latest blueprint classes proof in full, the latest tower-p1 proof's reduction paragraph, the smooth-purity chapter record and the complete tower-geometric unit record. I read the statement and first eight construction steps of det-sp-tower-classes to verify the explicit extension, scalar realization, root normalization and coefficient transitions. This proof is marked agent-written: it expands geometric naturality of that construction, supported by the following Stacks sources and the existing DAG tools; it is not attributed to a nonexistent numbered theorem about coefficient towers.

For the homological sources I read Stacks derived.tex, Tag 0152 (lemma-derived-canonical-delta-functor), including its explicit cone-map proof of naturality and delta=-p q^{-1}; Tag 06XV (lemma-ext-1), together with its pointer to Tag 06XU (lemma-yoneda-extension); and the truncation construction at Tag 08J5 (remark-truncation-distinguished-triangle). In sites-cohomology.tex I read Tag 03AJ (lemma-torsors-h1), including the pushout extension giving the class, and Tags 07A4 (lemma-pullback-tensor-product) and 0G7E (lemma-pullback-K-flat). The latter explain the K-flat models used by the existing whole-diagram scalar comparison. I also checked the source descriptions of lem-pur-derived-change-of-rings (06YT, 06YU, 06YY) and the existing statement giving its K-flat computation. No SGA source is used.

Step 1: I opened def-weil-proetale-inverse-image, lem-coef-semilinear-derived-sections, det-prop-sfb-cartesian-coefficients-twists and det-sp-coefficient-towers-abelian. They give the actual pro-etale inverse image, exact whole-system module inverse image, root/constant-coefficient identifications with Kummer transitions, and levelwise exactness. The statement of the root node permits arbitrary scheme morphisms. I explicitly form the componentwise geometric morphism on system topoi; the index category is the small category of positive integers with reversed order. No smallness theorem is applied to an unbounded or large index category. The coefficient identifications are those in the item, not a completed integral coefficient comparison.

Step 2: I read lem-sc-line-bundle-torsor and lem-sc-torsor-h1 in full. Both allow arbitrary schemes and explicitly cover the Zariski site, so no unjustified pro-etale Picard theorem is invoked. The gluing rule is written out on a Zariski trivializing cover and used unchanged to define the pro-etale extension; its fibre at 1 is the frame torsor. The extension classification statement identifies its connecting class and gives exact-functor transport. det-sp-tower-classes(2) states exactly that its coefficient-linear construction starts with this line-bundle morphism. I checked the sign: e_b=g_ab e_a makes the pair (u,m)_b correspond to (g_ab^m u,m)_a, so this is L and not its dual.

Step 3: I read the statements of lem-weil-pbc-exact-functor-ses-triangle-image and lem-weil-pbc-complex-ses-triangle. The former transports the specified signed boundary by an exact functor, while the latter states naturality for a morphism of short exact sequences. Those are different tasks; merely citing an existence-of-triangle statement would not justify this equation. The map (u,m)->(a(u),m) commutes with gluing and has exactly the endpoints used. The map on units is not assumed invertible. Exact inverse image preserves the source short exact sequence regardless of flatness of X->Y.

Step 4: I read the complete statement of lem-pur-algebra-diagram-pullback-extension-coherence. It permits any small diagram of commutative algebras over a constant base ring, so J=N_{>=1}^{op} and base Z meet its hypotheses even though the quotient exponents vary. It supplies an actual natural module-derived comparison, its scalar-unit equation and compatibility with algebra-diagram maps. I apply it separately to R and A. This avoids treating the fixed-Z/n result lem-sfb-divisible-extension-derived-reduction as a varying-n theorem. Source comparison at the coefficient unit follows from its stated unit normalization.

Step 5: I checked the supplied K-flat scalar-change theorem applies on a small presentation of the system topos, the Kummer exactness is exactly det-sp-tower-classes(1), and the concentrated-object statement applies in the module-system abelian category with r=-1. The coefficient resolution has transition (ell,1), since ell^n ell=ell^{n+1}; the tensor target has the power transition in degree -1 and identity transition in degree 0. The displayed homotopy h^0=1 has components i and the power map, giving j^{-1}b=-pv^{-1}. Thus the positive kernel identification and the shifted Kummer boundary use the same sign on both schemes. The sign convention is stated by the exact-functor boundary node and by Stacks 0152, not guessed.

Step 6: I checked that the balanced comparison in the whole-diagram lemma fixes both generators of the coefficient resolution. The map on its two tensor terms is consequently (a,a); its kernel map is the specified roots-of-unity map. I read lem-pur-torsion-sheaf-constant-module: it really gives uniqueness of the quotient-ring action and linearity of sheaf maps, not a derived forgetful-faithfulness assertion. I use lem-weil-pbc-derived-single-fully-faithful only within the R-module system derived category after the target has been identified with a shifted single module object. Its statement permits every abelian category; shifting both objects reduces to its degree-zero assertion. This proves the comparison equation for whole shifted sheaves. It does not infer equality of degree-two Chern classes from their cohomology.

Step 7: I read the full statements of lem-sfb-successive-derived-quotient-normalization and det-def-sp-tate-twist-locally-free. The former is stated for sheaves of rings on any small site, hence for a small presentation of the system topos; it identifies successive scalar extension and its units without a flatness hypothesis. Only clause (1) of the latter is needed: compatible roots trivialize the entire root tower and give flatness by levelwise exactness. An auxiliary algebraic closure containing E can be chosen as required by that lemma. The tensor-root target is then the degree-zero tower named in the item. I checked its map and its transition explicitly as u tensor b -> r(u) tensor b and u tensor b -> u^ell tensor bar b. Naturality and coefficient-map compatibility give the final equality with precisely theta^0 and theta^1.

Small cases: for the trivial bundle the extension has its global split, its connecting class and both Chern maps vanish; for f=id all comparisons and the extension map reduce to identities; for empty schemes the same categorical construction and equality apply. At n=1 the resolution and kernel give the usual finite Kummer map with the same sign. Nilpotent schemes or nonflat maps change the units map but not its multiplicativity or compatibility with powers, which are the only properties used. Ramification of E is harmless: coefficients are O_E/ell^n exactly as in the item, not O_E/varpi^n, and no quotient-map flatness is assumed. I checked every cited statement and verified literal quotations in citations.json. All seven non-elementary steps have length below 2000 characters. A local dependency traversal found no route from the main generic comparison or the homological inputs back to this item. The server checks, rather than local check scripts, are used below.

## Unfinished work

None in the stage-1 split. This delivery adds no Lean and runs no compiler, Lake or build command. Server dry-run and delivery outcomes are recorded by the delivery command.
