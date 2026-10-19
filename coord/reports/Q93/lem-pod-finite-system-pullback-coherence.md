## Worker report

Item: lem-pod-finite-system-pullback-coherence. Group: Q93. Stage 1 only.

The item is split into seven steps, with no new nodes and no new Mathlib leaves. Its statement and statement dependencies are unchanged. I preserved all inherited provenance, searches and blueprint fields. The proof is explicitly agent-written: Stacks 0D6D does not itself state the varying-coefficient strict-system theorem. The proof constructs the comparison in the abelian category of strict systems using adjunctions, establishes associativity there, applies the construction termwise to complexes, and descends natural transformations by ordinary localization. No equality of arbitrary derived-system morphisms is inferred from equality of their evaluated morphisms.

The sandbox originally contained only dispatcher markers. There was no prior item, report or split to recover. I read the current repository item, its chapter and unit records, the current main-20261015 local Frobenius definition and the cited dependency statements. The item is a technical child, not the key statement of sk-lem-finite, so there is no unit-record change.

## Attachment and duplicate searches

I searched WeilConjectures in the read-only slopmaster2 checkout for the exact item id and the notions finite systems, semilinear systems, pullback composition and coherence. The pro-etale UpperLowerStar/Coherence.lean file supplies ordinary sheaf-valued pullback coherence, but no declaration found supplies every clause for ordinary unbounded derived categories of strict systems over varying rings. It therefore does not attach this item. No master sorry declaration was treated as a finished proof.

I searched the entire DAG for pullback-composition, associativity, coefficient-compatibility, module-adjunction and localization statements. I used blueprint_refs.py ancestor and search on “pullback composition”, “strict systems” and “semilinear”. The ancestor is def-weil-local-frobenius-trace. No imported blueprint statement found equals this item; the existing ordinary module-comparison, adjunction-coherence and localization nodes cover its tools. In particular I reused lem-pur-proetale-module-pullback-composition and lem-trf-adjoint-composition-coherence instead of creating wrappers for their statements. There are no new-node/existing-node pairs to distinguish.

## Mathlib searches

I ran the mandated msearch.py leanfinder, loogle, grep and leansearch commands, and a second semantic phrasing. Their actual results are in searches.jsonl. The first semantic query found SheafOfModules.pullback_assoc and Scheme.Modules.pseudofunctor_associativity_assoc among eight results. Loogle found six pullback_assoc results. Grep located pullbackComp and pullback_assoc at PullbackContinuous.lean:167,177,180,193,194; I read the surrounding declarations. LeanSearch returned eight results including the underived sheaf theorem and unrelated image/composition identities. The second semantic query returned eight module-localization/cotangent results, with no strict-system theorem. These services were available. I also read DerivedCategory/ExactFunctor.lean:27-58. Exact-functor descent and ordinary module coherence are relevant infrastructure but do not alone constitute the item's entire assertion. Existing Mathlib-leaf nodes already supply generic localization and adjunction associativity.

## Sources and route

I read sites-modules.tex at lemma-adjoint-push-pull-modules (03D3), lemma-adjoint-pullback-pushforward-modules (03D7), and lemma-push-pull-composition-modules (03D8); sites-cohomology.tex at lemma-derived-pullback-composition (0D6D); and categories.tex at lemma-transformation-between-functors-and-adjoints (0B65). The last has the adjoint correspondence; the precise associativity identity is the cited existing Mathlib-leaf node, not an extra assertion attributed to that tag. The strict-system extension is the argument supplied here. No SGA source is used.

The blueprint place remains the iteration sentence in the first paragraph of def-weil-local-frobenius-trace. The split supplies finite-system reassociation below lem-pod-integral-pullback-composition. The off-unit citations declared in split_report.tool_uses are generic sheaf, adjunction and exactness/resolution tools; they do not replace the finiteness or Frobenius route of the unit.

## Route-pivot audit and repair comparison

I read the complete current route-pivot snapshot in
`coord/route-pivot-dropped.txt`.  It contains 1,336 dropped node IDs; the
first is `def-cbc-bounded-representable-hypercover` and the last is
`lem-pur-system-section-suspension`.  Its SHA-256 is
`83fac6f3b3671df63e67b4872ba55fe82c1555081606091c8a7b60355c66e0bc`.
I also read the companion exact Lean-module inventory
`coord/route-pivot-dropped-modules.txt`, which contains 1,172 module names
and has SHA-256
`9ab2be3566883a26315dfd7710f31504275145c64b45d9b05987a2c11299e159`.
I compared the item ID, every `stmt_deps` and `proof_deps` entry, every
proof-step `uses` entry, the blueprint `via` entry, and every declared
`split_report.tool_uses` entry with the dropped-node inventory.  The
intersection is empty.  The item's only blueprint `via` node is
`lem-pod-integral-pullback-composition`; it is not in either dropped list.
The proof route uses ordinary strict-system adjunctions, exact termwise
functors, K-flat resolutions, and ordinary localization, so it introduces
none of the dropped infinity/dg/model-category or Zariski-gluing machinery.

I searched the available `coord/repair-notes/` snapshot and found no
item-specific note for `lem-pod-finite-system-pullback-coherence`.  The
applicable repair instruction is the F1 entry for this item in
`coord/returns/Q93.md`: record the exact dropped-list check, the applicable
repair note, and the historical comparison.  Since that entry is itself the
repair handoff and no item-specific note exists, there is no additional
node-specific route change to apply.

For the historical comparison I used the returned delivery recorded in that
entry at branch head `11991e059f` (the only historical identifier available
without git or live-tree access).  The retained historical split is the same
seven-step strict-system construction described above: no new node, no
statement change, and no dropped machinery.  The current sandbox node is the
repaired seven-step record (SHA-256
`ae5806f24a590dea11df6f0b8910c9cb0ba89a8536eeedff1d39acfb24af0403`); this
repair adds the missing route-pivot evidence to the report and does not claim
an unverified historical file hash.

## Review by Q93

I checked B–E with the node statements and the cited source passages open. No statement dispute was found and no hypotheses or conclusions were changed. There are no new nodes, so no unsplit proof sketches, added notions, duplicate wrappers or uncertified Mathlib leaves are introduced. citations.json quotes the actual statement of every node used by every proof step. None of the seven steps exceeds 2000 characters.

Step 1 uses the constant-sheaf sheafification definition, the specified constant-section structure map and its isomorphism, and lem-trf-constant-coefficient-composition's actual ring-map equality. Naturality in the coefficient ring is proved by sending a constant a to r(a) in the two adjuncts, not taken from the ring-map node, which only asserts the fixed-ring isomorphism. This verifies both scalar compatibility and the required normalization for composites.

Step 2 uses the ringed-topos module adjunction, plus geometric-module-transport's explicit assertion that its bijection agrees with the underlying sheaf adjunction. That second citation is needed: naturality in a fixed-ring module category alone would not justify semilinear transition compatibility. The written equation for t_n is the adjunction transpose of the written equation for s_n, using the same underlying sheaf adjunction at the two indices. The inverse bijection proves the converse. Thus the Hom bijections restrict to compatible families and give an actual adjunction on strict systems. Constant-exact states exactness of the module inverse image; semilinear-derived-sections states that exactness in the system category is componentwise. These are precisely the two inputs for system exactness. No flatness of coefficient maps is used.

Step 3 cites the actual direct-image section formula in def-weil-proetale-inverse-image and the universal property in def-pc-fibre-product. It writes the fibre-product identification, checks transitions by naturality of restriction, and checks the two triple-composite identifications by their projections. This is the elementary step: it does not assume a general coherence theorem hidden in a definition. Module scalars agree because both maps preserve the same constant sections, as checked in Step 1.

Step 4 uses the existence and uniqueness in conjugate-iso-unit-equation and the ordinary canonical module comparison of lem-pur-proetale-module-pullback-composition. The latter explicitly uses the specified constant-section maps and is normalized as a comparison of left adjoints to the stated right-adjoint identification. Evaluating the system unit equation therefore identifies the two module comparisons by uniqueness. Transition compatibility follows at the underived system level, before evaluating any derived morphisms. No new node merely restates this clause.

Step 5 applies lem-trf-adjoint-composition-coherence with the four strict-system categories and all six adjunctions. This node allows nonidentity right-adjoint comparison maps, unlike the older strict-right-adjoint version. Its hypothesis is exactly the projection calculation in Step 3. Inverting its conclusion gives the displayed equality in the item's direction, with the canonical associator included.

Step 6 uses exact-functor-derived-factorization for the termwise functors and localization-universal-property for natural-isomorphism descent, compatibility with composition, and equality of descended natural transformations. Naturality against differentials establishes the chain maps explicitly; equality of system maps is carried degreewise to equality of chain maps. This proves the required before-localization assertion as well as the derived one.

Step 7 uses the evaluation statement of semilinear-derived-sections, K-flat-resolution existence, and the exact representative normalization explicitly stated by proetale-derived-pullback-composition. That composition node applies because its composite ring identification agrees with the canonical one by Step 1. On a flat-term K-flat resolution both comparisons have exactly the same component; exactness carries its quasi-isomorphism to a quasi-isomorphism for every leg, giving the identification for every complex by naturality. This uses the statement of the composition node, not an unstated property of its proof.

I tested the construction on identity scheme maps, zero systems, complexes concentrated in one degree, the empty source scheme, constant coefficient towers, zero transition maps, and the nonflat quotient maps Z/4 to Z/2. Underived operations apply inverse image to the semilinear transitions; no tensoring with a coefficient quotient is introduced. Empty-source coefficient sheaves are the zero ring sheaf as the ring-map node explicitly permits. No boundedness, normalization, finite-type condition or coefficient-flatness is needed. I checked the dependency closures of the main reused system and adjunction nodes and found no path back to the item. The main correction to the imported empty proof is to construct a comparison of whole systems before localization, with explicit unit normalization, rather than infer it from evaluated comparisons.
