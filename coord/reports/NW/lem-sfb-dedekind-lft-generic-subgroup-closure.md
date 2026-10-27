# Worker report

1. Files written:
   - dag/nodes/sec-six-functors-basics/lem-sfb-dedekind-lft-generic-subgroup-closure.json: item split in seven steps, statement unchanged.
   - dag/nodes/sec-six-functors-basics/lem-sfb-dedekind-torsionfree-module-flat.json: statement, Mathlib leaf, Module.Flat.instOfIsDedekindDomainOfIsTorsionFree (Mathlib/RingTheory/Flat/TorsionFree.lean:143; equivalent criterion at :138).
   - citations.json: one verbatim statement quotation for every proof-step citation.
2. Attachments: none. Searched WeilConjectures by the exact blueprint tag and schematic-closure/generic-subgroup notions; no project declaration states the item. Upstream Hopf-algebra Zariski closure concerns field-valued matrix groups and does not give this relative scheme-theoretic result.
3. WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models, 10.1 Proposition 4 proof (printed p.291) and 7.1 Corollary 6 (printed p.175), for the item. The PDF named by the inherited source is absent locally. No download or source-file modification was made. The replacement explicit proof is marked agent-written and uses local Stacks material.
4. The inherited item was statement-only. Its hypotheses are sufficient; no statement dispute or statement change. No imported blueprint ancestor exists (blueprint_refs ancestor returns None); retained that provenance and named the precise subgroup-closure subargument in the new leaf. The latest blueprint unit and chapter were read; this is a lower-level trait-extension input, with no change to either route. Mathlib searches for the item return flatness criteria, torsion-free flatness, and ordinary topological subgroup closure, none of which supplies all its clauses. Existing recorded searches were preserved, and new executed queries added. The new node records only its four executed dedicated searches, including source grep at lines 138 and 143.
5. Nothing unfinished mathematically. Required server dry run exited 0 and printed OK (not pushed) at 69443c9cece, preflight passed. The push command follows that successful final dry run.

## Review by NW

I read delivery-errors B–E in full against the files. For the construction I read local Stacks morphisms.tex, Tags 01R6 (lemma-scheme-theoretic-image) and 01R8 (lemma-quasi-compact-scheme-theoretic-image), including the quasi-compactness warning immediately preceding 01R8. For the new leaf I read more-algebra.tex, Tag 0AUW (lemma-dedekind-torsion-free-flat), part (1), and Mathlib/RingTheory/Flat/TorsionFree.lean, especially the instance at line 143 and criterion at 138. I also read the local proof of Tag 0538 and the affine criterion of Tag 01U5. The absent BLR PDF is reported rather than claimed to have been read. The proof is an explicit affine proof based on these sources.

Step 1 uses lemma-nagata-scheme-image-ideal-qc for its closed image, factorization, and full quasi-coherent kernel under quasi-compactness. I checked its statement, which specifies that kernel, not only a topological closure. The quasi-compactness hypothesis follows here because every affine inverse image is closed in the affine generic base change. This is valid for locally finite-type M without assuming M quasi-compact. The cited closed-immersion definition gives the quotient affine charts.

Step 2 uses only those quotient charts and the base-change definition. Its contraction-extension calculation is written out: b/t in K implies b/1 in K. The injected quotient is torsion-free because every nonzero D-scalar is a unit in the E-algebra. This works even when a generic chart is empty (zero quotient), and when J is nonreduced. No argument replaces scheme-theoretic equality by equality of sets.

Step 3 uses exactly the new Dedekind module leaf, then lem-weil-pbc-flat-local-ring-maps for D_p to (B/I)_q, then the pointwise definition of scheme-flatness. I checked each of these statements. The domain D is Noetherian, normal and one-dimensional as required; the new leaf allows dimension at most one, matching Mathlib and including fields. Arbitrary modules are allowed: coordinate rings need not be finite D-modules. Localization of this flat ring map is the precise conclusion of the cited existing localization node, so no affine-cover locality theorem is silently assumed.

Step 4 uses lem-weil-pbc-flat-morphism-affine-criterion to get flatness of every affine coordinate algebra of X over the affine base, and lem-trf-flat-module-torsionfree-domain to get nonzero-scalar injectivity. The latter statement is for every domain, not only a valuation ring. Vanishing after localization means some nonzero denominator kills the section; torsion-freeness kills it already. Quotient maps give local lifts, and the surjective sheaf map plus subspace description in def-weil-closed-immersion gives uniqueness and gluing. In particular this proves the required factorization on arbitrary flat X, not just finite-type test objects. As a small-case necessity check, without flatness take D a DVR, M additive, J the zero generic subgroup and X the special-fibre affine line mapped by its coordinate: generic factorization is vacuous but the map does not land in the zero closure. The hypothesis is used in exactly the necessary place.

Step 5 uses lem-weil-pbc-flat-morphism-base-change for the product projection and lem-pc-flat-compose for its structure morphism. I opened both nodes: one asserts arbitrary base change of a flat morphism, the other asserts composition. Thus Step 4 applies to the identity, inverse, and product; their generic images lie in J by the supplied subgroup structure. def-sc-group-scheme only states the field-base diagrams, and I use it only for those diagrams, with the base-general version explicitly defined in the item. I do not take any relative closure theorem from that definition.

Step 6 verifies every group law by composition with the closed inclusion and cancellation; it uses the actual multiplication, identity and inverse already constructed in Step 5. This is an elementary diagram argument, not a new group-closure node that would merely restate the item. Step 7 derives local finite type by images of algebra generators. It proves closed-immersion base change directly on quotient charts, identifies the inverse image of the ambient diagonal with C using monomorphy, and obtains separatedness. I checked the definitions cited in both steps: they give exactly quotient charts, group diagrams and base change. These elementary facts therefore remain steps, as B–E requires.

All seven steps are below 2000 characters. The new node is statement-only and genuinely smaller: it concerns arbitrary modules over Dedekind domains, not group schemes. The zero module, non-finitely-generated torsion-free modules, fields, and nonprincipal Dedekind domains fit its Mathlib instance. The item also passes the tests J=M_E (closure removes vertical torsion if M is not flat), the identity subgroup, nonreduced J, and infinitely many ambient components. A group scheme itself cannot be empty, but empty affine generic intersections were explicitly checked. No finite-type conclusion for the entire closure is asserted; only local finite type is proved.

The DAG and whole blueprint were searched for schematic closure, torsion-free modules, Dedekind rings, flatness and flat morphisms, and all existing tools above were reused. No SGA source or alternate unit route is used. citations.json copies actual node statements, preserving the distinction between the cited statement and stronger claims one might find in a proof. No source, live repository, Lean, compiler or launcher file was changed.

## Not duplicates

lem-sfb-dedekind-torsionfree-module-flat vs lem-sfb-scalar-finite-free-resolutions: requires finite presentations over a DVR or field and constructs finite free resolutions; the new leaf allows arbitrary modules and every Dedekind domain and asserts only flatness.

lem-sfb-dedekind-torsionfree-module-flat vs lem-sbc-root-normalization-generic-stalk-flat: is a geometric normalization/stalk theorem with ramified polynomial and regularity assumptions; it does not assert arbitrary Dedekind module flatness.

lem-sfb-dedekind-torsionfree-module-flat vs lem-sc-dvr-fg-torsionfree-free: requires a DVR and a finitely generated module and concludes finite freeness; the new leaf has neither restriction and only concludes flatness.

lem-sfb-dedekind-torsionfree-module-flat vs lem-sfb-dvr-projective-complex-matrix-model: constructs finite matrix models of complexes over a DVR; it does not state the arbitrary-module flatness implication.

lem-sfb-dedekind-torsionfree-module-flat vs lem-sfb-finite-sum-lattice: concerns a finite sum of full lattices in a local coefficient field and constructs a basis; it does not state arbitrary Dedekind module flatness.

lem-sfb-dedekind-torsionfree-module-flat vs lem-sfb-flat-trait-pinching-base-change: concerns pushout schemes over a DVR and compatibility with base change; it is not a module-flatness criterion.

lem-sfb-dedekind-torsionfree-module-flat vs lem-weil-pbc-pid-torsion-free-module-flat: restricts the ring to a PID; nonprincipal Dedekind domains are allowed in the new Mathlib leaf, so the existing statement does not cover it.

lem-sfb-dedekind-torsionfree-module-flat vs lem-pur-twist-integral-basis: constructs a specific integral coefficient-ring basis over p-adic integers; it does not state arbitrary Dedekind module flatness.

lem-sfb-dedekind-torsionfree-module-flat vs lem-sp-integral-local-model-finite-matrix-reduction: concerns coefficient sheaves and finite matrix reduction, not arbitrary modules over any Dedekind domain.

The projective DVR flat-closure node requires an ambient projective closed subscheme over a DVR and proves a geometric closure assertion; it does not cover the present arbitrary separated lft ambient group over a Dedekind domain, or the standalone arbitrary-module leaf. The topological matrix-group closure nodes similarly concern field-valued groups.
