# Stage-1 report: lem-sp-fullcd-ambient-adjoint

## Files written

- `dag/nodes/sec-smooth-purity/lem-sp-fullcd-ambient-adjoint.json`: repaired split of the existing statement.
- `dag/nodes/sec-smooth-purity/lem-sp-clopen-section-component.json`: new statement-only obligation; no Mathlib match.
- `citations.json`: verbatim statement quotes for every citation in every item proof step.

## Attachments

None found. The relevant slopmaster2 declaration `AlgebraicGeometry.ProEtale.HasAmbientExceptionalRightAdjoint.isLeftAdjoint` in `WeilConjectures/SixFunctors/ProEtale/ExceptionalAdjoint.lean:151` has proof `sorry`; it is not an attachment. Its conclusion also does not itself supply every coherence clause of this item.

## WANTED:

None. The proof route uses the existing blueprint and DAG statements; the extracted obligation is recorded as unsplit nodes for later work.

## What was repaired

The returned delivery identified item step 6 as a 2359-character non-elementary step hiding several lemmas. I retained the item statement, its Lean record, all other proof steps, hypotheses, and the compactification/Brown route. I replaced that step by two concise steps. The first cites the existing unbounded ringed-projection restriction statement together with the existing proper-open section and extension-by-zero base-change nodes. The second cites the new statement-only node for the clopen component calculation, together with the existing K-injective resolution and total-derived-image nodes. No new node restates the item: each is a strictly smaller obligation used only in the refinement comparison. I searched the DAG and blueprint for the extracted clopen obligation; no existing node states it. No SGA source is used.

## Not duplicates

- `lem-sp-clopen-section-component` vs `lem-weil-pbc-proper-open-identification`: the new node supplies the K-injective/clopen component calculation on the full unbounded pro-etale category, while the existing node states the bounded-below etale comparison-map identification.

- `lem-sp-clopen-section-component` vs `lem-weil-pbc-clopen-section-direct-image`: the existing node gives a derived identity on bounded-below etale complexes; the new node states the pro-etale sheaf/complex equivalence, unbounded K-injective insertion and ordinary section formula.
- `lem-sp-clopen-section-component` vs `lem-pur-finite-clopen-derived-decomposition`: the existing equivalence assumes a finite-type scheme over the fixed algebraically closed finite field and the fixed coefficient system; this item uses arbitrary scheme bases and the new node also identifies direct image along the section's retraction.
- `lem-sp-clopen-section-component` vs `lem-weil-pbc-etale-sheaf-clopen-product`: the existing node concerns abelian etale sheaves and global sections, rather than pro-etale module complexes and K-injectivity.
- `lem-sp-clopen-section-component` vs `lem-weil-pbc-disjoint-open-direct-image-retract`: the existing node gives an etale direct-image retract; it gives neither the pro-etale equivalence nor the unbounded computation.
- `lem-sp-clopen-section-component` vs `lem-weil-pbc-open-section-clopen`: the existing node proves the geometric decomposition, not the sheaf and complex calculations.

- `lem-sp-clopen-section-component` vs `lem-exc-proetale-cartesian-open-injective-acyclic`: the existing node assumes a proper map with finite cohomological dimension and proves acyclicity of an open extension; the new node concerns a clopen section and proves the product/K-injective/section formulas without those assumptions.
- `lem-sp-clopen-section-component` vs `lem-exc-proetale-proper-open-sheaf-comparison`: the existing node is a Cartesian proper/open sheaf comparison, not the component-category or K-injective insertion statement.
- `lem-sp-clopen-section-component` vs `lem-weil-proetale-weakly-etale-localization`: the existing node identifies a localized site and its coefficients, not the product for a clopen cover, K-injective insertion or retraction direct image.
- `lem-sp-clopen-section-component` vs `def-cbc-finite-constant-coefficient-transport`: the existing node defines finite-coefficient scalar transport and its comparison maps; it makes no clopen product or K-injective assertion.
- `lem-sp-clopen-section-component` vs `def-cbc-strict-tower-open-extension`: the existing node defines open extension on strict coefficient towers and its normalized adjunction, not a clopen component equivalence of module-sheaf categories.
- `lem-sp-clopen-section-component` vs `lem-cbc-strict-tower-proper-open-calculus`: the existing node treats normalized proper/open mate calculus on strict towers and invertibility under etale-origin hypotheses; it does not state the sheaf product and K-injective component lemma on arbitrary inputs.
- `lem-sp-clopen-section-component` vs `def-cbc-strict-constant-tower-operations`: the existing node defines termwise strict-tower operations and compositors, not a clopen decomposition theorem.
- `lem-sp-clopen-section-component` vs `def-cbc-strict-tower-proper-open-arrows`: the existing node defines proper/open comparison arrows and clopen projection by adjunctions; it does not give the component equivalence or K-injective insertion claimed here.

## Review by Q58

I read the returned item in `dag/nodes/sec-smooth-purity/lem-sp-fullcd-ambient-adjoint.json`, the unit record `dag/units/sk-prop-sf-existence.json`, and the source route `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-existence/_section.md`. Steps 1–5 still use exactly the existing Grothendieck-category, FullCD, condensed-continuity, K-injective, coproduct, exact-open, and Brown statements listed in their `uses`; I checked each cited node's statement rather than relying on its proof. The first repaired refinement step uses the existing proper-open section statement for the clopen section and identity projection, the existing unbounded ringed-projection restriction statement for `j_e^*Ru_*N ≅ Rq_*b^*N`, and the existing Cartesian extension-by-zero base-change statement for `b^*j_{d!}K ≅ s_!K`. Its hypotheses are the refinement data already fixed in the item and the finite coefficient ring in the item statement. The second repaired step uses the existing K-injective-resolution existence, localized restriction K-injectivity, K-injective definition, extension-by-zero adjunction and exactness, plus the new clopen component statement; these statements together say precisely why the restriction is computed on a K-injective model and why the component calculation yields the normalized `λ_u`. Steps 8–11 retain the existing direct-image composition, K-injective preservation, cofiltered compactification, adjunction-transport, and ambient-datum statements, and their uses remain unchanged. I verified every citation quote in `citations.json` is a verbatim statement sentence or formula and that `proof_deps` is the union of step uses. I checked the new statements on the identity refinement and on an empty complex: both give the identity/zero comparison, so no extra hypothesis was silently introduced. The former long step is gone; the remaining steps are below the 2000-character review threshold.

## What could not be finished

The one new clopen-component obligation is intentionally a statement-only stage-1 node for subsequent splitting. The open-restriction obligation is supplied by an existing node.

## Resumed repair review by Q58

I compared the retained sandbox with the current shared item: its statement and entire Lean record agree exactly. Only the proof, its dependency union, split report and split status differ. The returned head's 2359-character step contains two arguments: unbounded open localization of derived direct image, now cited from `lem-weil-pbc-ringed-projection-restriction`, and the clopen component calculation, now `lem-sp-clopen-section-component`. The former's statement explicitly supplies the natural unbounded direct-image isomorphism without a cohomological bound. The latter is strictly smaller than the item: it assumes a clopen section and asserts no FullCD consequence, Brown adjoint or compactification coherence. The remaining item steps have lengths at most 1702 characters.

For the new node I read the current blueprint's `sec-proetale-coefficients/sk-def-sf-operations/lem-weil-pbc-clopen-section-direct-image.md` and `.proof.md`, as well as Stacks 09AE (`proetale.tex`, `definition-extension-zero`). The blueprint theorem is etale and bounded below, so the new pro-etale unbounded clause is explicitly agent-formulated, rather than incorrectly attributed to it. The disjoint-cover argument works for objects of the pro-etale site: their pullbacks to the two opens cover with empty intersection. Componentwise acyclicity and Hom-complexes give the unbounded K-injective clause. The case of empty complementary open gives the identity equivalence; when X is empty every inserted complex is zero, and for V=X disjoint union Z the pushforward formula discards the Z component. No properness, finite type, or etale-origin hypothesis is needed for this component lemma.

I checked steps 1–5 against their complete cited statements: the finite bound applies to all source sheaves; the continuity theorem accepts a common degree-zero bound and a small filtered finite-subset category; sums of injectives are used only as pushforward-acyclic objects; the acyclic-complex theorem accepts unbounded complexes with the finite bound; and Brown takes a Grothendieck source and an exact coproduct-preserving functor in a common universe. Step 6 uses the geometric clopen section, the localized pro-etale site identification, unbounded restriction and Cartesian extension-by-zero, each as explicitly stated. Step 7 uses the new component lemma, Grothendieck K-injective existence, exact extension and the K-injective computation theorem. Step 8 uses the existing ambient support statement and the open adjunction. Step 9 cites composition with its identity/associativity clauses and the explicit K-injective preservation under both direct image and localized restriction. Step 10 uses cofilteredness with an already given compactification over an arbitrary base. Step 11's displayed unit/counit equations are exactly those of the ambient-datum definition after substitution of the common right adjoint. Thus no etale-only or bounded-below statement is substituted for an unbounded pro-etale claim.

I read the retained search log before reusing it and inspected the Mathlib sheaf-disjoint-product hit (`Topology/Sheaves/SheafCondition/PairwiseIntersections.lean:428`): it is a section product for sheaves on a topological space, not the claimed pro-etale module-category and K-injective assertion. The recorded semantic hits concern complex-shape extension and scheme structure sheaves, not this statement. I corrected one inherited grep record that had appended its subdirectory to the query text: it now records the exact logged query `K-injective|KInjective`; the earlier result and date are retained. All 42 step/node citation pairs have verbatim statement quotes, with no missing or stale quote. No statement dispute was introduced, no Lean file was written and no compiler was run.

The new node records `blueprint.from.via = [lem-sp-fullcd-ambient-adjoint]`, since its parent is itself created under `cor-exc-base-change-open-immersion-general`; this preserves the full ancestry rather than treating the parent as an imported blueprint node.
