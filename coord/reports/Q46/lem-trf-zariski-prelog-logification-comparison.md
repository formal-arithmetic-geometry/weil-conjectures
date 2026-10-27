## Files written

- `dag/nodes/sec-trace-formula/lem-trf-zariski-prelog-logification-comparison.json`: statement unchanged; nine proof steps, explicit universal-property comparison, two stalk computations, reflection of units, characteristic quotients and open restriction.
- `dag/nodes/sec-trace-formula/lem-trf-filtered-varying-prelog-pushout.json`: one new statement-only algebraic input; unsplit, no Mathlib match. Both the prelog monoids and rings vary in the filtered diagram.
- `citations.json`: every step's cited statements copied verbatim. Search records are preserved in `searches.jsonl` and item/new-node metadata.

## Attachments

None. Searches in `lean/WeilConjectures/` for the exact blueprint tag and for logification, PreLog, LogStructure and associatedLog returned no declaration. General stalk declarations do not assert this item. No Lean was written or compiled.

## WANTED

WANTED: K. Kato, Logarithmic structures of Fontaine–Illusie (1988), section 1, for the associated-log conventions referenced by ILO VI 1.1 and the existing prelog nodes. This is already wanted by their source records. The proof here is explicitly agent-written; I did not attribute the detailed argument to that unread source.

## Corrections and scope

No statement correction or STATEMENT-DISPUTED finding. ILO VIII opening of section 3 (printed p.97) and 3.3.2 (p.106) were read from the PDF converted inside this sandbox. They set the Zariski/etale convention and assert the associated-prelog comparison in the monoscheme-chart case. The imported item's arbitrary sheaf formulation is an explicit generalization whose proof must be supplied; it is not an exact quoted theorem of ILO and has no exact Stacks tag. The same remains true after this split.

The current `literature/blueprint/latest` ancestor `lem-trf-local-term-locality` and its proof were read, as were the current chapter and unit and their DAG records. The latest ancestor uses Varshavsky's contracting correspondence argument. The assigned node is a historical alteration/log-resolution auxiliary. Its ancestry is retained and this delivery does not change the chapter or unit route or claim that the new blueprint still contains the historical log-chart branch. Blueprint searches for logification, associated log, prelog, pre-log, pushout, filtered, stalk and units found no blueprint equivalent of the item or the new algebraic lemma. All same_as fields remain empty.

The existing etale prelog lemmas are deliberately applied only to the etale site. Their statements do not authorize applying them on the Zariski site. The Zariski quotient, log axiom and universal mapping bijection are written explicitly in steps 2–3. Likewise `lem-trf-filtered-ring-log-pushout` has a *fixed* monoid R; it cannot be cited for the varying monoid sheaf in step 6. That is why there is one new algebraic node. The new node is not a clause of the item: it concerns arbitrary filtered ring/monoid diagrams, no scheme, site, log sheaf, comparison morphism or point.

## Review by Q46

I read the item and every quoted node's actual statement. I checked delivery-errors B–E against these files rather than treating tags or neighboring proofs as statements. The new node is a complete algebraic proposition with its own small category, coefficient universe, diagrams, maps, presentations and comparison; it contains no proof and no proof dependencies. Its notions of filteredness and quotient congruence are written out; its universe and colimit notions cite their definition nodes. Its source is Stacks categories.tex, Tag 04AX, `section-directed-colimits`, whose eventual-equality paragraph after the filteredness definition was read. It is an agent-formulated consequence of that paragraph, not a falsely attributed Stacks logarithmic theorem.

For step 1, the inclusion-morphism node explicitly states epsilon_* as restriction and epsilon^-1 as its adjoint; the presheaf-pullback node gives the indexing category and left exactness. For this inclusion, maps U→V over X exist exactly when image(U)⊂V. The monoid-sheafification node gives the underlying set compatibility. I wrote why multiplication and identity transfer under the adjunction, rather than citing an abelian-sheaf inverse-image theorem for monoids.

For step 2, the prelog-log-axiom node really allows arbitrary monoid presheaves on the *etale* site, not only constant charts. The general local-sections theorem is for any small site; its lifting and equality assertions justify the separate Zariski unit-locus calculation. For beta(p)u invertible, beta(p) is invertible because u is, without cancellation in P. This is the only algebraic observation needed for the Zariski log axiom. Monoid sheafification supplies the structural extension and the underlying set interpretation.

For step 3, the hom-extension node explicitly gives the etale Hom bijection and automatic unit compatibility. The Zariski version is proved by the displayed quotient formula and sheafification adjunction, and the definition of a log structure supplies the inverse unit map. In particular, I did not cite that definition as a theorem about sheaf colimits. Every generated congruence is killed because the displayed map is a homomorphism killing its generators.

For step 4, I checked that restriction of an etale log structure to open subschemes is a Zariski log structure: the inverse-unit isomorphism is evaluated on exactly the same open subschemes, with the same regular functions. The four Hom sets are over their respective structure sheaves. The comparison is given inverse maps; both composite identities follow from uniqueness on the original prelog sheaf, not from an unsupported claim that inverse image alone preserves log structures. The etale construction/universal-property nodes apply also to epsilon^-1 L_Zar, which is a genuine prelog monoid sheaf.

For step 5, the etale definition gives flatness and local finite presentation, and the cited openness theorem states exactly that this makes U→X open. The raw inverse-image formula reduces to F(image U). Both stalk maps on representatives are written, including the pointed map U→image U which proves the inverse identity. The cited cofiltered-neighborhood theorem and set-colimit elementwise theorem justify the index and eventual equality. The sheafification-stalk node is set-valued, and the monoid-sheafification node explicitly identifies underlying set sheafification; no abelian-only result is used.

For step 6, I checked the Zariski index is a small directed poset of opens containing x and that the etale index can be replaced by small representatives in the fixed universe. The etale cofilteredness node is cited; no colimit is taken over an uncontrolled large category. The new lemma allows both diagrams to vary and therefore applies to sections of an arbitrary P, including nonconstant sheaves. The site local-lifting theorem proves the Zariski stalk/sheafification bijection directly; the set-valued geometric-stalk theorem supplies the etale version. The new lemma with trivial monoid also identifies unit germs with units of the ring stalk.

For step 7, the existing constant-monoid filtered lemma *does* state the required unit representative assertion, and it is used only for that assertion with the trivial monoid. The geometric-point and residue-field definitions give compatible evaluations into Omega. The basic-open-function theorem states precisely the invertibility criterion and the open neighborhood D(a) on which the function is a unit. Thus nonunits cannot become units, and the same E_x is valid in both stalk pushouts. The local-ring argument identifies nonunits in the etale stalk as the kernel of evaluation; it does not assume unproved faithful flatness or an unquoted strict henselization theorem.

For step 8, quotient by the units is the orbit congruence: a unit factor and the one equality witnessing an orbit relation are finite data. The unit-lift assertion and the set-colimit eventual-equality assertion are exactly the two cited facts. Local lifting/equality or the geometric sheafification-stalk theorem handles final sheafification. I marked this short representative calculation elementary, with all non-elementary ingredients cited.

For step 9, the slice-sheafification node is used in its *sets* case, not an invented monoid-valued clause. The monoid-sheafification node and local representatives show its set isomorphism respects multiplication and identity. The raw inverse-image open-neighborhood systems are cofinal after intersection with W. The comparison restricts because its extension is unique, and all stalk maps are the same representative maps. This proves the claimed compatibility, not merely an assertion of naturality.

Every step is below 2000 characters (lengths 1009, 922, 870, 1052, 1042, 1149, 1206, 759, 924 at the initial write); I checked that none hides a separately named standard comparison. The single new algebraic lemma isolates the finite-witness subargument that genuinely needs further work. Its proof idea, retained here for its future worker, is to lift a monoid element and a unit representative to one common stage, and to lift each inverse witness and each finite chain of generating pushout relations to a common later stage. Equality in a generated congruence is a finite chain, not necessarily one generator. Filteredness equalizes parallel arrows, so the argument does not presume the index is a poset. Conversely each stage relation remains a relation in the colimit; these maps are inverse on pair representatives. The existing constant-monoid proof and Stacks 04AX provide the finite-witness model but do not state the varying conclusion.

Small cases tested: the trivial monoid (output is the units sheaf); beta entirely in units (the associated log structure is the trivial log structure); a noncancellative monoid (none of the arguments cancels); a nonconstant Zariski monoid sheaf; X empty (no points, constructions terminal on the empty open); the zero ring on the empty open (its units group is the singleton, so the unit-locus calculation still works); one-object filtered diagrams; localization k[t]→k[t,t^-1], where a chart element becomes invertible only later; noninjective transition maps and parallel arrows. Neither finite generation, fs, cancellation, integrality nor normality was silently added. The scheme hypotheses needed are present, and local Noetherianity is available for the reused etale prelog lemmas. No SGA source is used.

No part of the item is left unfinished. The algebraic input is intentionally statement-only, as required for a one-level stage-1 split. Server diagnostics and final delivery status are appended below.

## Not duplicates

`lem-trf-filtered-varying-prelog-pushout` vs `lem-trf-filtered-ring-log-pushout`: the latter fixes R and beta_i on a constant monoid; the new lemma permits arbitrary transition homomorphisms M_i→M_j and compares with colim M_i. It cannot be applied to the varying-monoid diagram by a one-line specialization.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-trf-associated-log-universal-stalks`: that node constructs a log sheaf from a fixed global monoid chart on a locally Noetherian scheme; the new lemma is algebraic, with varying monoids, and contains no sheaf universal property.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-trf-zariski-prelog-logification-comparison`: the item concerns two sites, their logification universal properties and comparison; the new lemma only computes an arbitrary filtered algebraic pushout system used for the stalks.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-a1-directed-ring-cocone-recognition`: this gives elementwise recognition or representatives for ring colimits, not the monoid-unit pushout comparison.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-a1-ring-inverse-image-underlying-sets`: this identifies underlying sets of a ring sheaf inverse image along a continuous map, not filtered varying prelog pushouts.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-sfb-filtered-two-colimit-diagonal-equality`: this concerns morphism equality or representatives in a categorical two-colimit, not varying prelog monoids and unit-adjoining pushouts.

`lem-trf-filtered-varying-prelog-pushout` vs `def-sfb-simultaneous-root-tower`: this defines a particular simultaneous-root ring diagram; it asserts no general unit-adjoining monoid pushout comparison.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-sfb-filtered-two-colimit-common-stage-images`: this concerns morphism equality or representatives in a categorical two-colimit, not varying prelog monoids and unit-adjoining pushouts.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-pc-filtered-colimit-commrings-elementwise`: this gives elementwise recognition or representatives for ring colimits, not the monoid-unit pushout comparison.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-filtered-colimit-sets-elementwise`: this gives set-colimit representatives and eventual equality, without any ring, inverse-unit submonoid or pushout conclusion.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-colimit-constant-connected-diagram`: this concerns constant diagrams on a connected category; the new lemma allows varying monoids and rings and asserts a different pushout comparison.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-colimit-site-abelian-stage-image-refinement`: this refines finite additive expressions of site sections at a common stage, not a monoid-unit pushout comparison.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-filtered-colimit-algebras-elementwise`: this gives ring-element representatives in a filtered colimit of fixed-base algebras, not a varying monoid or an inverse-unit pushout.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-filtered-colimit-categories`: this concerns objects, arrows, finite diagrams or operations of a categorical filtered colimit, not the quotient of a monoid times ring units.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-etale-limit-affine-stage-eventual-zero-tail`: this is a cohomological limit-stage or reindexing assertion with etale sheaves, not an algebraic pushout comparison.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-etale-limit-reindex-transition-coherence`: this is a cohomological limit-stage or reindexing assertion with etale sheaves, not an algebraic pushout comparison.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-finite-type-ring-map-factors-filtered-colimit`: its statement has no varying prelog monoids over varying rings or comparison of their inverse-unit pushouts.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-filtered-colimit-category-list-equality`: this concerns objects, arrows, finite diagrams or operations of a categorical filtered colimit, not the quotient of a monoid times ring units.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-filtered-colimit-finite-iso-lift`: this concerns objects, arrows, finite diagrams or operations of a categorical filtered colimit, not the quotient of a monoid times ring units.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-filtered-colimit-fiber-operations`: this concerns objects, arrows, finite diagrams or operations of a categorical filtered colimit, not the quotient of a monoid times ring units.

`lem-trf-filtered-varying-prelog-pushout` vs `def-weil-pbc-filtered-colimit-hom-fibers`: this concerns objects, arrows, finite diagrams or operations of a categorical filtered colimit, not the quotient of a monoid times ring units.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-etale-limit-affine-stage-tail-colimit`: this is a cohomological limit-stage or reindexing assertion with etale sheaves, not an algebraic pushout comparison.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-filtered-colimit-modules-criterion`: this is an R-module colimit recognition criterion with a fixed scalar ring, not a monoid-unit pushout comparison.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-filtered-colimit-category-structure`: this concerns objects, arrows, finite diagrams or operations of a categorical filtered colimit, not the quotient of a monoid times ring units.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-etale-limit-affine-stage-eventual-zero`: this is a cohomological limit-stage or reindexing assertion with etale sheaves, not an algebraic pushout comparison.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-filtered-colimit-category-iso`: this concerns objects, arrows, finite diagrams or operations of a categorical filtered colimit, not the quotient of a monoid times ring units.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-filtered-colimit-fiber-laws`: this concerns objects, arrows, finite diagrams or operations of a categorical filtered colimit, not the quotient of a monoid times ring units.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-filtered-colimit-category-finite-lift`: this concerns objects, arrows, finite diagrams or operations of a categorical filtered colimit, not the quotient of a monoid times ring units.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-colimit-site-finite-kan-arrow-lift`: this concerns objects, arrows, finite diagrams or operations of a categorical filtered colimit, not the quotient of a monoid times ring units.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-filtered-colimit-category-finite-functor-lift`: this concerns objects, arrows, finite diagrams or operations of a categorical filtered colimit, not the quotient of a monoid times ring units.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-weil-pbc-filtered-colimit-category-descent`: this concerns objects, arrows, finite diagrams or operations of a categorical filtered colimit, not the quotient of a monoid times ring units.

`lem-trf-filtered-varying-prelog-pushout` vs `def-weil-directed-colimit-abelian-groups`: this defines directed colimits of abelian groups, not varying prelog monoids over rings or their unit pushouts.

`lem-trf-filtered-varying-prelog-pushout` vs `lem-sfb-diagonal-tensor-colimit-hom-ext`: the latter tests equality of arrows from a tensor square using diagonal cocone legs in an arbitrary monoidal category under colimit-preservation hypotheses. It asserts neither a units-colimit comparison nor a monoid-unit pushout computation.

`lem-trf-filtered-varying-prelog-pushout` vs `def-weil-pbc-filtered-colimit-smooth-algebras`: the latter defines a fixed-base algebra being a filtered colimit of smooth algebras, with no conclusion about varying prelog monoids or units.

`lem-trf-filtered-varying-prelog-pushout` vs `def-coef-bounded-filtered-subcategory-system`: the latter defines a small poset of bounded subcategories and an iterated colimit comparison, with no inverse-unit or prelog-pushout assertion.

## Server checks

The preliminary server `review_split` passed. The first full dry run stopped before preflight because three further existing nodes shared source Tag 002V. I opened their complete statements and added the three comparisons immediately above. None supplies this algebraic lemma or a generalization of it. This was a report repair only; the mathematical split did not change.

The full dry run exited successfully with preflight passed at 4e63bed7a94. Final self-review added the explicit project size-convention citation to step 1 (the universe choice was already in the text), and corrected “group of sections” to “monoid of sections” in step 5. No statement or proof argument changed. The final dry run below validates this exact revision before pushing.
