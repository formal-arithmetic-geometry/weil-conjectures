# Worker report: lem-per-flat-maximal-dominance-base-change

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-flat-maximal-dominance-base-change.json: statement item, now split into five steps; not a Mathlib leaf as a whole.
- citations.json: verbatim statement quotations for every node cited by every proof step.
- report.md: this report. No new DAG nodes, no unit changes, no Lean files.

## Attachments

None. Searches in /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the exact blueprint tag and maximal-dominance terminology found no declaration stating this item. The flat-product image declarations in AlgebraicGeometry/GroupScheme/Image.lean concern quasi-compact scheme-theoretically dominant maps, so they neither attach this item nor cover its hypotheses. The item has no inherited Lean declaration or open sorry frontier to recover.

## WANTED

None for this split. ILO refers to EGA IV2 2.3.7(ii), but I do not use that unexpanded reference as a proof: the explicit argument below uses locally available Stacks facts and the universal property of fibre products.

## Problems found and corrections

The item statement is correct and is unchanged. I read ILO Expose II 1.1.1--1.1.5, printed p.23, PDF p.29. Example 1.1.3 gives the first clause and Proposition 1.1.5 gives exactly the second without any Noetherian, finite-type, reducedness or surjectivity hypothesis. The source only points to EGA for the latter, so proof_origin.by is agent and the actual fibre argument is supplied in the item.

The specialization wording of lem-weil-pbc-flat-generalizations-lift is correct: “v specializing to f(t)” means that v generalizes f(t), and the output t-prime specializing to t is a generalization of t. I initially misread this wording during drafting, then checked it against Tag 03HV and removed the erroneous report claim before delivery. Step 2 now cites that existing node directly. This avoids creating another generalization-lifting node or redoing its ring-going-down proof. No existing node has been changed.

The chapter and unit records were read. This is an auxiliary node below lem-per-artin-gabber-affine-curve, not the unit's key node; its inherited from/via route remains intact. The proof supports exactly the flat maximal-dominance calculation used in the alteration-generator argument. It uses no step of the trace formula or Poincare duality, and no SGA source.

## Searches and reuse

No earlier sandbox item or report existed. I retained all five Mathlib searches already in the repository item and read their reported hits; the sandbox searches.jsonl records five additional searches made with the required msearch.py command, all successful: LeanFinder (two phrasings), Loogle, grep in AlgebraicGeometry/Morphisms, and LeanSearch. Their exact tool names and query text are appended to mathlib_searches.

The returned Flat.generalizingMap (Mathlib/AlgebraicGeometry/Morphisms/UniversallyOpen.lean:134) gives the flat-map component; Flat.isStableUnderBaseChange and the projection instances (Morphisms/Flat.lean:81--90) give flatness of projections. I inspected those source ranges. IsDominant describes dense image rather than images of all component-generic points; genericPoint_eq_of_isOpenImmersion imposes open-immersion and irreducibility hypotheses. None states the complete second clause. The existing component-cover, scheme-sobriety, flat-generalization-lifting, field-extension-flatness and flat-base-change nodes already supply the tools, so no new node was created for any of them.

I searched the whole DAG for maximal dominance, generalizing/generizing maps, going down, minimal primes, fibre topology and the candidate Stacks tags. I ran tools/blueprint_refs.py search for flat, generaliz and maximal and its ancestor command. No blueprint node states this item in another form; same_as stays []. No search not actually run is recorded.

## Not duplicates

No new nodes. The scheme-lifting node is reused rather than duplicated. Step 2 applies its existing statement; steps 1 and 5 are short deductions from their cited statements. No parent clause has been moved into a newly named lemma.

## Review by Q71

I checked the mathematics against ILO II p.23 and opened every cited node's statement before using it. For the generic-point criterion I read Stacks topology.tex Tag 004W (lemma-irreducible), parts (3) and (4), and schemes.tex Tag 01IS (lemma-scheme-sober). For the flat-map argument I read morphisms.tex Tag 03HV (lemma-generalizations-lift-flat), and also checked its ring-going-down background at algebra.tex Tag 00HS (lemma-flat-going-down) and morphisms.tex Tag 01U5 (lemma-flat-characterize). For base change I read morphisms.tex Tag 01U9 (lemma-base-change-flat), and schemes.tex Tags 01K0/01K1 (definition-fibre and lemma-fibre-topological). The relevant tag-to-label correspondences were checked in tags/tags. No new node needs a separate source review.

Step 1 uses def-weil-irreducible-components for maximality, lem-sc-irreducible-components-cover for a component through an arbitrary point, and lem-sc-scheme-sober for the unique generic point of that component. All three statements have exactly those clauses, with no Noetherian hypothesis. The argument explicitly proves both implications of the no-proper-generalization criterion and uses uniqueness, rather than silently assuming T0.

Step 2 uses lem-weil-pbc-flat-generalizations-lift. Its precise statement says that for v specializing to f(t), a point t-prime specializing to t exists over v. In the proof, b1 specializes to u(a), so it is exactly this v, and the returned a1 specializes to a, so it generalizes a. The flatness hypothesis is the only one required by the cited node and is explicitly present. Step 1 gives a1=a, hence b1=u(a), and then genericity of u(a). The statement says exactly what this step takes; no finite presentation or surjectivity was inserted.

Step 3 uses def-pc-fibre-product for p, q and fp=hq, and lem-weil-pbc-flat-morphism-base-change for p, with the flat map h as the map being pulled back along f. The prior step applies to this p, so x is component-generic. The original maximal-dominance hypothesis on f, not any dominance theorem about dense images, makes y generic.

Step 4 uses def-pc-scheme-fibre, whose statement includes the homeomorphism onto the fibre subspace (not merely the definition of the pullback), for both unique points w and t and the injectivity W -> Z. It uses def-weil-residue-field for kappa(y) -> kappa(x), def-pc-fibre-product for the explicitly described isomorphism W = T times Spec kappa(x) over Spec kappa(y), lem-pc-field-extension-flat for the flat field-spectrum map, and lem-weil-pbc-flat-morphism-base-change for W -> T. Their statements give every one of these clauses. The point w is shown to have no proper generalization using continuity and injectivity, so no assertion about generizations being preserved by an arbitrary set bijection is needed. Flatness of W -> T then gives genericity of t by step 2. The isomorphism is a routine reassociation of pullbacks; its inverse maps and their compatibility are explained by the same universal property, not an unproved comparison lemma.

Step 5 uses only the homeomorphism clause of def-pc-scheme-fibre and earlier steps. Every generalization of y' stays over y because y has no proper generalization, and specialization inside a subspace is explicitly computed as ambient singleton closure intersected with the subspace. This checks the passage from genericity in T to genericity in all of Y'. The conclusion is the original projection, not the other projection or a reduced fibre product.

For delivery-errors B I checked that there are no new statement-only obligations, no hollow definitions, no missing object hypotheses, and no changed source or blueprint metadata. For C I checked all cited statements as above; citations.json uses verbatim full statements. proof_deps is precisely the union of uses. All off-unit generic facts are Mathlib leaves and additionally explained under split_report.tool_uses. For D the argument is in the item's own steps, not moved into a restatement node, and no step relies on the proof of a cited node. For E I checked all flatness hypotheses at the two applications of base change, the field-extension direction, the point identifications, and all specialization directions, including the initial drafting misreading corrected above.

Small cases checked: an empty source or empty pullback makes the corresponding universal claim vacuous; the identity base change reduces to the original map; identity f gives the identity projection; a disjoint union of components need not be irreducible; Spec of a nonreduced zero-dimensional local ring still has the same generic-point criterion; arbitrary transcendental residue extensions are flat; infinite-component/non-Noetherian schemes are allowed by 004W and 01IS. The proof never identifies a generic point's local ring with a field, which would fail for nonreduced schemes. No proof step exceeds 2000 characters; the longest is the single pullback/fibre argument, and each non-elementary input there is already a cited node.

## Unfinished work

None in the one-level split. Server validation and direct delivery are performed with the required tools; no Lean or compiler is run.
