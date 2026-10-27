# Stage-1 delivery: lem-trf-geometric-irreducibility-generic-dichotomy

## Files written

- dag/nodes/sec-trace-formula/lem-trf-geometric-irreducibility-generic-dichotomy.json: existing statement, now split in four steps; not a Mathlib leaf.
- citations.json: seven entries, one for every cited node in every proof step, copied verbatim from the statements read.
- searches.jsonl: five searches actually run through msearch.py, retained without alteration.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The existing general component-count generic-constancy theorem supplies the substantial geometric input; making a new 055A node would duplicate it.

## Attachments

None for this item. Searched lean/WeilConjectures for the exact blueprint tag, geometric irreducibility, generic fibres and dichotomy. The generic-component splitting, generic geometric-irreducibility shrinking and geometric-cover spreading declarations cover other inputs, not every clause of this item. The existing AlgebraicGeometry.isIrreducible_preimage_of_isSepClosed_extension belongs to lem-sbc-subset-geometric-irreducibility, whose record already names it; no attachment change is requested.

## WANTED

None. All mathematical sources used are available locally in literature/stacks-project/. No SGA source is used.

## Corrections and source comparison

No statement correction or STATEMENT-DISPUTED issue. The item's finite type hypothesis is sufficient: Stacks 055A assumes finite type, although the stronger local constructibility statement 055B assumes finite presentation. This split uses precisely 055A and the level-one consequence in the second paragraph of 055B. It does not apply the constructibility theorem to a merely finite type morphism.

The sandbox initially contained no node or prior split. Copied the current repository item, preserving all imported statement, ancestry and prior-search fields. The new proof reuses lem-trf-geometric-component-count-generic-constancy, already present with exactly the point-closure formulation and without Noetherian or flatness assumptions. Its hypotheses were read from its statement, not inferred from its proof. The item remains an independent predicate-valued specialization, not a new node duplicating the numerical theorem.

Read the current latest blueprint chapter, unit, and lem-trf-local-term-locality statement and proof. Their current route is the contracting-correspondence theorem. This auxiliary item is on the inherited flattening/05FH branch recorded by its ancestry; proving this existing auxiliary item does not replace a chapter or unit step. No chapter or unit file was edited. Searched the whole DAG by tags 055A/055B and geometric-component/generic-dichotomy wording, and searched blueprint_refs for geometrically irreducible, generic point and component count. No blueprint node states this dichotomy in another form, so same_as remains [].

## Mathlib searches and results

All five queries ran with the required msearch.py command, and the exact queries and results are appended to the node and logged in searches.jsonl. LeanFinder was tried with both the more general numerical statement and the predicate on an arbitrary irreducible closed subset. LeanSearch returns finiteness of irreducible components for a Noetherian scheme, finite fibres, and generic-point facts. Loogle with GeometricallyIrreducible and LocallyOfFiniteType returns no hit. The grep hits were read in Mathlib/AlgebraicGeometry/Geometrically/Irreducible.lean: irreducibleComponentsEquiv assumes an already geometrically irreducible open morphism, while this item asserts existence of a generic open for an arbitrary finite type morphism, including the failure alternative. Neither it nor the other hits specializes in one line to the item. All services used answered successfully; no unavailable service is recorded as absence.

## Review by Q19

I read coord/delivery-errors.md B through E and checked the proof against the actual cited node statements and the Stacks source text. No new statement-only lemma, duplicate, or clause relabelled as a lemma is introduced. The statement dependencies are the original definitions; the item statement has not changed. Every proof dependency is used, every use has its quote, and no proof step exceeds 2000 characters.

Step 1 uses lem-sc-scheme-sober, whose statement explicitly supplies a unique generic point of every irreducible closed subset, to obtain eta with closure Z. I read Schemes 01IS, label lemma-scheme-sober. The numerical theorem lem-trf-geometric-component-count-generic-constancy explicitly applies to every point of the base of a finite type morphism and gives a nonempty relatively open subset of its closure with a constant finite nonnegative integer count. Its hypotheses are exactly the ones here, so it applies directly to f and eta, without reduction, flatness or a Noetherian assumption. I read More on Morphisms 055A, label lemma-nr-geom-irreducible-components-good, and the second paragraph of 055B, label lemma-nr-geom-irreducible-components-constructible. The definition def-pd-separable-closure explicitly fixes a separable closure for each field and says it is separably closed; the step needs exactly that clause and no assertion about its filtered colimit.

Step 2 uses the explicit covering clause of lem-sc-irreducible-components-cover, not just the definition of a component. I read Topology 004W, label lemma-irreducible, parts (3)-(4), and def-weil-irreducible-components. A sole component covers the whole space and is nonempty by its irreducibility; conversely a nonempty irreducible whole space contains every component and maximality forces equality. The empty-space case follows since no subset of an empty space is nonempty. This is an elementary consequence of the cited covering statement and maximality, so it stays a step, not a new lemma.

Step 3 uses the defining quantification over all field extensions in def-pc-geometrically-irreducible for the forward direction. For the reverse direction I read lem-sbc-subset-geometric-irreducibility in full and its existing source declaration. Its statement allows an arbitrary scheme over k and arbitrary subset A, with no finiteness or closedness hypothesis. Set k equal to the residue field, Omega equal to its fixed separable closure, and A equal to the entire fibre. The inverse image of the whole space is the whole base-changed space. Thus its hypothesis is exactly the irreducibility and nonemptiness of W_t obtained from Step 2, and its conclusion gives both properties for every field extension E/k. This is precisely the geometric irreducibility the item defines. I read Varieties 054P, label lemma-geometrically-irreducible-check-after-extension; 020J, label lemma-separably-closed-irreducible; and the separable-closure test 038I, label lemma-characterize-geometrically-irreducible. The cited subset lemma is a general field-extension tool from another unit, recorded in split_report.tool_uses; it replaces no unit route. In particular geometric connectedness or ordinary irreducibility of the unextended fibre is never substituted for geometric irreducibility.

Step 4 performs the case distinction on the single constant integer n, using the equivalence already proved pointwise. When n=1 all points satisfy the predicate; when n is different from 1 none do. A chosen point of the nonempty V proves exclusivity. This is elementary logic and needs no additional cited fact.

I checked small cases: an empty total space has n=0 and yields the second alternative; an irreducible single-point base has V equal to that point and the geometric-irreducibility test decides the alternative; a disjoint union of two copies of the base has n=2; a purely inseparable field extension has n=1 while a nontrivial separable extension can split into several components, so the proof correctly counts after separable closure. Reducibility with components meeting is covered because the proof counts irreducible, not connected, components. Nilpotents are harmless since the argument only uses underlying-space irreducibility and actual field base changes. No separation, flatness, finite presentation, reducedness or Noetherian hypothesis is added.

The quoted statements supply all non-elementary facts used. In particular neither the covering of a space by its components nor the field-extension test is treated as a consequence of a mere definition. I checked the dependency direction: the constancy theorem, sobriety, covering and field-extension tool do not depend on the present dichotomy, so this proof does not invoke the parent constructibility theorem or introduce its cycle.

## Not duplicates

No new node is created. The already existing lem-trf-geometric-component-count-generic-constancy is cited directly as the stronger numerical input.

## Unfinished work

The mathematical split and local self-review are complete. Required server dry run and delivery follow; no Lean files or compilers have been used.
