## Files written

- dag/nodes/sec-six-functors-basics/def-sfb-dc-hom.json — definition, split; no exact Mathlib match. The generic full-subcategory lift is in Mathlib and the elementary construction is written out here.
- citations.json — one verbatim statement quotation for each node used by each of the three construction checks.

0 new nodes; 0 new Mathlib leaves. Searches are recorded exactly in the item and in searches.jsonl. No Lean was written and no compiler, Lake or build tool was run.

## Attachments

None. Searches for the blueprint tag, boundedConstructibleHom, boundedConstructible_derivedHom and the derived-Hom notion throughout WeilConjectures in /home/ubuntu/weil-src-slopmaster2 found no exact declaration. AlgebraicGeometry.ProEtale.derivedHom in SixFunctors/ProEtale/Derived/Hom.lean:71 is an ambient layer-A functor, not the restriction for condensed module coefficients. The finite-coefficient etale stability declarations likewise do not state this definition.

The upstream master reference has AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructibleHom in WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/BoundedConstructible.lean:349 and boundedConstructibleHomObjCompatibility at :367. Its preservation lemma at :331 is sorry (:338), and master is not a finished-proof source. They are not attachments. Its definition correctly confirms the opposite first variable and uses the generic ObjectProperty.lift construction.

## WANTED

None. The item's current blueprint document and unit and chapter section texts are present locally.

## What was wrong or incomplete

The imported definition had no direct dependencies for the words “setting”, “commutative condensed ring”, and “bounded constructible”. Those existing definition nodes, and the separate finite-subextension definition of the algebraic-closure coefficient, are now cited explicitly. The original preservation hypothesis and examples are retained, with no extra hypothesis or weakened conclusion. The first dry run rejected the shorthand “in the setting of”; I expanded it to distinct primes l,p, a characteristic-p field k, and a separated finite-type k-scheme X, exactly the hypotheses of sk-def-sfb-dc-setting. The pulled-back coefficient ring is now also named explicitly before its module category. The restriction's object and morphism maps and identity comparison are now explicit. This is a definitional expansion, not a statement dispute.

There is no dag/chapters/sec-six-functors-basics.json or dag/units/sk-def-sfb-dc-restricted-functors.json in this snapshot; the imported item also has no chapter/unit metadata. I read the corresponding current-blueprint _section.md files instead, and did not create or edit maintainer-owned metadata. This item is a constituent definition, not the key unit node, so no unit realization record is part of this delivery.

The existing lem-sfb-dc-hom-preserves has an imported proof citing a source forbidden by the current route lock and an identification that needs its own justification. That node is not edited or certified by this delivery. Only its exact statement supplies the already-listed coefficient examples; the construction is conditional on preservation for general Lambda. The second-reader/maintainer should retain the existing preservation node as work to be audited on the permitted route. This delivery does not introduce that forbidden source or use its proof.

## Unfinished work

Nothing in this one-level split remains unfinished. The separate preservation theorem remains an existing DAG obligation; it has not been relabelled as a new lemma or treated as Lean-closed.

## Not duplicates

No new nodes were created. Whole-blueprint searches for “internal hom”, “restricted internal”, and “RHom.*D_”, and whole-DAG searches for full subcategories and the restriction terminology were inspected. sk-def-sfb-dc-restricted-functors is the larger parent definition that explicitly uses this item; it is not a dependency (which would cycle). Its Hom clause agrees with this item, but the full statement defines five operations and their structure, so it is not listed as a same_as duplicate. def-sfb-derived-hom-modules defines the ambient operation, not its restriction; def-sfb-dc-tensor defines the tensor operation, not Hom. Thus blueprint.same_as is [].

## Review by Q50

I read the current main-20261015 def-sfb-dc-hom.md, the full sk-def-sfb-dc-restricted-functors/_section.md, and the six-functors-basics chapter _section.md. The route asks for restriction of the ambient module-object functor, not a new derived construction. I opened all six statement-dependency nodes, including the ambient derived tensor/Hom definition, the bounded-constructible full-subcategory definition, the setting, both coefficient definitions, and the preservation statement. They define the notions actually used. In particular the algebraic-closure coefficient means the finite-subextension sheaf of sk-def-sfb-qlbar-condensed, not all continuous maps to the topological algebraic closure.

Step 1 takes only the conclusion of lem-sfb-dc-hom-preserves: for the specified three coefficient rings and a scheme of the stated setting, pairs of bounded constructible objects have bounded constructible ambient Hom. I checked that its ambient operation and coefficient categories match this item's module-object layer B, and that E is finite over Q_l. For every other coefficient ring, preservation is an explicit input hypothesis. The entire quoted theorem statement in citations.json includes all those hypotheses. No reduction, completeness or finiteness argument is being inferred from the definition of constructibility.

Step 2 takes bifunctoriality from the internal-Hom paragraph of sk-def-sfb-derived-tensor-hom and the fact that morphisms are computed in the ambient derived category from sk-def-sfb-bounded-constructible. These are literal assertions of their statements; citations.json quotes them. The first variable is contravariant: a map K' -> K sends H(K,L) to H(K',L). For a second pair K'' -> K', L' -> L'', the written composition equation has u composed with u' in the first variable and v' composed with v in the second. The identity and composition equations are exactly those of the existing bifunctor and require no theorem about resolutions, adjunctions, exactness or constructibility. I checked the order explicitly rather than calling it transport.

Step 3 uses the same full-subcategory statement, and evaluates both composite functors on each object L and map v. They have identical ambient images. The comparison and inverse have identity components, whose naturality reduces to the two category identity equations written in the step. This is an elementary verification, not an unproved compatibility theorem. The sole cited statement is again quoted verbatim. There is no appeal to the proof of any cited node, and proof_deps is the union of the step citations.

For the small cases I checked identity maps in both arguments, two successive contravariant maps, either argument the zero complex, the empty scheme, and the case where the full subcategory is the whole ambient category. Restriction uses the same maps in all of them; no nonemptiness or finite-Tor condition has been assumed. For arbitrary Lambda the preservation hypothesis cannot be dropped, and was not dropped.

I checked delivery-errors B through E against the final files: there are no new statement-only obligations, tag-sharing duplicates, unsupported literature facts, or moved clauses. All non-elementary input is the existing preservation statement. The elementary full-subcategory argument remains in the item instead of becoming a node. I read Mathlib/CategoryTheory/ObjectProperty/FullSubcategory.lean:159 (lift) and :165 (liftCompιIso) after the actual Loogle, LeanFinder and grep hits; these confirm the generic construction. The semantic searches for the coefficient-specific statement returned ambient condensed and derived-category APIs rather than this definition. I recorded both phrasings and the actual results without inventing a search or treating a generic supporting API as an exact coefficient-specific match. The item and every cited node already exist, and the parent unit is deliberately not cited, avoiding the obvious cycle. No new source is taken from the forbidden SGA route.

## Second reading by Q50

- Item statement: checked against `def-sfb-dc-hom.md` and the setting, coefficient, bounded-constructible, derived-Hom, and algebraic-closure definition nodes; all hypotheses and the three coefficient instances are present, with no weakened conclusion.
- Step 1: checked against the full statement of `lem-sfb-dc-hom-preserves`; it uses exactly its preservation conclusion under the same coefficient and scheme hypotheses.
- Step 2: checked against the bifunctor clause of `sk-def-sfb-derived-tensor-hom` and the full-subcategory morphism clause of `sk-def-sfb-bounded-constructible`; the identity and composition calculations are elementary from those statements.
- Step 3: checked against the same full-subcategory morphism clause; the two inclusion composites have identical objects and maps, so identity components give the natural isomorphism and its inverse.
- New nodes: none; therefore B1--B7 and duplicate checks introduce no additional node obligations.
- Edge cases: the zero object, identity maps, successive maps in the contravariant argument, the empty scheme, and the whole ambient category were checked; the definition imposes no nonemptiness or extra finiteness hypothesis.

No mathematical or metadata repair was needed. The existing search log, citations, explicit setting expansion, and preservation hypothesis were rechecked against delivery-errors B--E; the report and item remain within the stage-1 scope.
