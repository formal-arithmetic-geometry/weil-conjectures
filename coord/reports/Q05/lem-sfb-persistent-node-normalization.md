## Worker report

Files written:

- dag/nodes/sec-six-functors-basics/lem-sfb-persistent-node-normalization.json: split into ten steps; statement retained verbatim; added the existing componentwise-normalization definition to statement dependencies.
- dag/nodes/sec-six-functors-basics/lem-sfb-dvr-nodal-etale-local-form.json: statement, unsplit; Stacks 0CDD; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-componentwise-normalization-smooth-pullback.json: statement, unsplit; Stacks 07TD; no exact Mathlib match for absolute componentwise normalization.
- dag/nodes/sec-six-functors-basics/lem-sfb-affine-closed-pinching-pushout.json: statement, unsplit; Stacks 0ET0; no Mathlib match.
- citations.json: a verbatim statement quotation for every citation of every proof step.

Attachments: none. Searches of lean/WeilConjectures for the item's blueprint tag, persistent-node terminology, nodal normalization, absolute reduced normalization and the cited local inputs found no declaration giving this item with a completed proof. The existing project normalization file treats relative normalization, not this statement.

WANTED: none. All primary source texts needed for this split are present in the Stacks checkout.

The statement needs no correction. The main danger in the seeded source was treating xy=pi^n like a persistent node, or using excellent-normalization finiteness over an arbitrary DVR. The split instead separates the xy=0 branches and leaves xy=pi^n unchanged. Finiteness follows from explicit finite chart normalizations and fpqc descent. It also distinguishes absolute componentwise normalization (07TD) from the relative normalization comparison in Mathlib. No target or unit statement is changed.

The item's inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor lem-sfb-persistent-node-normalization returns None. Its created.item chain ends without an imported blueprint node. I retained this truthful ancestry, the existing via chain and the precise det-thm-sf-ctf-stability-direct-images proof-(3) route description. Whole-blueprint searches for persistent node, nodal family, normalization smooth, etale local at worst nodal, integral closure, pushout schemes, fibre product rings, surjection rings and 0ET0 found no equivalent imported statement. The unit and chapter records were read and not changed.

Nothing in the assigned one-level split remains unfinished. The three new nodes deliberately carry statements and searches only; they remain stage-1 items. No Lean was written and no compilation was run.

## Not duplicates

lem-sfb-dvr-nodal-etale-local-form vs lem-trf-nodal-family-etale-local-model: the latter gives uv=h over an arbitrary etale base scheme V. The new Stacks 0CDD input additionally gives an etale extension R' that is itself a DVR and replaces h by 0 or an actual uniformizer power. Shrinking an etale base to such a DVR uses the Dedekind-algebra argument in the proof of 0CDD; it is not asserted in the older statement.

lem-sfb-dvr-nodal-etale-local-form vs lem-sfb-point-blowup-fibre-defects: the latter assumes a regular surface and states blowup multiplicities and fibre defects. It does not supply common pointed etale DVR charts for an arbitrary nodal family.

lem-sfb-dvr-nodal-etale-local-form vs lem-sfb-persistent-node-normalization: local equations for an arbitrary, possibly nonproper family are an input to the item. The new node asserts no global normalization, conductor, finiteness or reconstruction clause of the item.

lem-sfb-componentwise-normalization-smooth-pullback vs lem-sbc-relative-normalization-smooth-base-change: the existing node normalizes a base in a supplied qcqs source. The new node compares absolute normalizations of X and Y; relating these absolute objects to a relative construction is the content of 07TD.

lem-sfb-componentwise-normalization-smooth-pullback vs lem-trf-conductor-smooth-base-change: the existing theorem assumes finite type over Q and asserts a conductor-annihilator formula. Here arbitrary locally Noetherian schemes, including mixed characteristic and nonexcellent traits, are needed; no conductor formula is part of the new statement.

lem-sfb-componentwise-normalization-smooth-pullback vs lem-trf-normalized-blowup-calculus: the existing normalization comparison is restricted to schemes of finite type over Q and accompanies a normalized blowup. The new 07TD statement is the unrestricted locally Noetherian absolute comparison.

lem-sfb-affine-closed-pinching-pushout vs lem-trf-relative-nodal-point-pinching: the existing theorem pinches finitely many smooth k-points on curves over an algebraically closed field. The new theorem treats arbitrary rings and arbitrary maps T to D, and is needed on mixed-characteristic trait charts.

lem-sfb-affine-closed-pinching-pushout vs lem-sfb-trait-etale-branch-pinching: the existing theorem assumes a projective nodal trait family and etale rank-two branches. The new 0ET0 ring theorem has none of these hypotheses, and directly identifies the affine ring whose spectrum is the pushout. Its statement is not the global projective pinching assertion.

lem-sfb-affine-closed-pinching-pushout vs lem-sfb-persistent-node-normalization: the new result is the general affine closed pinching theorem, independent of normalization or curves. The item's proof still computes its normalization and conductor and establishes the fibre-product ring identity and descent to every open; it is not an application of a renamed reconstruction clause.

lem-sfb-affine-closed-pinching-pushout vs lem-sc-dual-number-scheme-pushout: the latter concerns a finite wide pushout of dual-number spectra over a field, not arbitrary conductor rings over a DVR.

## Review by Q05

I read models.tex, lemma-etale-local-at-worst-nodal (0CDD), its full proof reducing 0CBY to etale DVR extensions, and the statement and proof of curves.tex, lemma-etale-local-structure-nodal-family (0CBY). I read more-morphisms.tex, lemma-normalization-and-smooth (07TD), including its finite-component hypothesis, and lemma-basic-example-pushout (0ET0), including the passage from a ring fibre product to a universal property for arbitrary target schemes. I also read proposition-pushout-along-closed-immersion-and-integral (0E25) and its Situation: the affine 0ET0 theorem is sufficient here and avoids having to establish additional global gluing hypotheses. For the explicit algebra I checked the affine componentwise normalization statements (035P/0CDV) and the polynomial-normality statement. The existing 0CDD arithmetic blowup-calculus node supplies the separate normality assertion for xy=pi^n; its blowup clauses are not used.

For the new local-form node I checked every hypothesis against 0CDD: flat and locally finitely presented, pure one-dimensional reduced nodal geometric fibres, and a special-fibre point; connectedness and properness are unnecessary. For the new absolute comparison I checked the locally Noetherian hypothesis implies finitely many irreducible components on every quasi-compact open. Its empty and nonreduced cases are expressly covered by the source proof. For the new affine pushout, I used precisely surjectivity A to D and an arbitrary T to D. The source does not require finiteness. All three nodes have no proof or proof dependencies.

I opened and read the statement of every node cited in the proof, and compared the quotations in citations.json with those statements:

1. The finite-type-over-Noetherian node supplies Noetherianity. The new 0CDD input supplies only the special-fibre charts; the existing 0CBY node supplies generic charts. Flatness gives the written injection into A[1/pi], proving reducedness without assuming normality or excellence.
2. The polynomial-normality node is applied to the DVR R', whose integral closedness is justified by the valuation comparison in the text. The affine componentwise-normalization node gives the product of the two integral closures. I checked D=A[e], the conductor ideal, both quotients and the fibre-product ring equality explicitly. This is an elementary calculation from the two cited statements, not an omitted normalization lemma.
3. The arithmetic chart node says that xy=pi^n is normal for all n>=1. The new 07TD comparison applies to both etale arrows of the common chart. Componentwise properties give restriction to opens. Finiteness descends along a finite affine etale cover of the Noetherian X, exactly the covering assumed by the finite-descent node.
4. The closure calculation is the kernel on an affine ring and therefore commutes with the flat etale chart tensor product, as written. Smoothness descends through the existing etale-source-smoothness theorem, and its dimension-zero characterization gives etaleness. The composition-of-etale-maps node applies to the chart base R'/R. The closed-immersion-composition node gives the required projective embedding of N. Its fibres are finite, so the projective-finite-fibres node applies with the Noetherian base S. For the complement isomorphism, the single flat surjective quasi-compact cover in the cited descent statement is the finite disjoint union of the chosen affine charts.
5. The existing nodal-source-locality theorem includes flatness and local finite presentation; it does not require connected fibres. The smooth-source-locality theorem applies to the generic fibre. The componentwise-properties node supplies surjectivity. The finite-over-projective theorem specifically supplies a projective-space embedding over an affine Noetherian base, which S is. Quasi-compactness and separatedness then upgrade local finite presentation to finite presentation.
6. The finite-permanence node supplies finite base change and the finite-composition node gives B finite over S. The same smoothness locality theorem gives etaleness and the relative smooth-locus assertion from the two branch origins. The module-descent node really does reflect finite local freeness of rank two; it is not being cited just for effectivity. No global branch ordering is chosen.
7. The new affine pushout statement gives a pushout for arbitrary target schemes. The exact sequence in the proof shows why its ring identity persists under the flat etale chart map. It is not a claim that Spec converts all ring limits into scheme colimits.
8. The representable-fpqc-descent node is used to glue actual maps U to Z, after uniqueness on affine refinements of double overlaps. Repeating this on charts over any open V proves the open-restriction clause. Neither an arbitrary-base-change stability claim nor a properness assumption on the target Z is used.
9. The absolute comparison handles the generic open immersion; the field-version conductor calculation identifies the generic square. The finite-etale-generic-components node really identifies each component with the normalization of S in its generic field. Applying it separately to N and B gives the requested integral closures; a generic algebra map preserves integral elements, which gives the asserted uniqueness of the extended map.
10. The finite-etale-components statement gives the local domain property. I checked the residue quotient is a field at every closed point, so the maximal ideal is generated by the original pi. Flatness keeps it nonzero. The DVR equivalence is part of the cited definition, and the dimension-one node gives its dimension; a one-generated maximal ideal in dimension one gives regularity. The empty case is included explicitly.

I tested a smooth family (N=B empty and normalization the identity), the split constant node xy=0, the smoothing node xy=pi, the normal but nonregular surface xy=pi^n for n>1, nonsplit branches (only etale-local ordering), residue characteristic two, and disconnected normalizations. These checks do not use completeness, perfect residue fields or excellence. No step exceeds 2000 characters. The external-unit citations are declared generic tools in split_report.tool_uses; the common-nodal-model route remains unchanged.

The Mathlib searches were all run through msearch.py and the recorded answers were read. Each new node has semantic, Loogle and source-grep searches, with a second semantic phrasing. The apparent normalization hit is the relative comparison in Mathlib/AlgebraicGeometry/Normalization.lean:588-611, which I read; the apparent pushout hits in Pullbacks.lean convert a ring pushout to a scheme pullback. Neither matches the new statements.

Validation repair: the first dry run rejected the affine-pushout matrix row separators as doubled TeX escapes, and did not recognize its grouped reference. I replaced the matrix by the four canonical morphisms written individually and gave each definition reference its own brackets. The mathematical statement and proof route are unchanged.
