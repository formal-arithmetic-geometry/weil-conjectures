## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-zero-support-retraction-triangle.json`: statement unchanged; seven proof steps, status split. Mathlib verdict: no match for the complete pro-etale assertion.
- No new nodes or Mathlib leaves. The existing geometry, coefficient, support and derived-functor nodes suffice.
- `citations.json`: one verbatim quotation for every proof-step citation.

## Attachments

None. I searched the live `lean/WeilConjectures/` for the item id and for zero support, retraction, localization and zero-section terminology. The support declarations in `SixFunctors/OpenClosed/Supports.lean` and `SupportsDerived.lean` concern the etale-site support triangle, not the full ordinary pro-etale statement including its geometric hypotheses and retraction. They are not attachments for this item.

## WANTED

None. The assembly follows the available blueprint and existing DAG statements. No new local-field result is asserted: finiteness follows directly from the existing finite Kummer level statement.

## Problems corrected

The item was statement-only, with no proof. I retained its statement, source, inherited searches, created record and blueprint ancestry. The new proof supplies every asserted clause, with explicit formulas for the transported arrows. In particular, triangulatedness is cited as a theorem, rather than inferred from the definition of derived image; the first arrow is identified with the actual support counit by the kernel-adjunction lemma. No statement dispute was found, and no coefficient category or exceptional-functor transport was substituted.

## Unfinished work

None for this one-level split. The existing unsplit prerequisite nodes keep their own queue status; they were read for their statements and are used as black boxes.

## Blueprint and duplicate searches

I read the chapter and unit records `sec-smooth-purity` and `sk-prop-a1-kummer`, the current main-20261015 `lem-pur-gysin-structure.proof.md`, and the support-localization and finite-Kummer proofs. The item realizes exactly the first paragraph before any Kummer cohomology computation. `blueprint_refs.py ancestor` gives `lem-pur-gysin-structure`. Whole-blueprint searches for retraction, localization triangle, support localization, composition of derived images and affine-line, and whole-DAG statement/title searches found the existing prerequisites used here. No blueprint node states this complete retracted-support assertion in another form, so same_as stays empty. No new node was needed, hence no new-node duplicate pairs arise.

## Mathlib searches

The required command logged grep, LeanSearch, Loogle and two differently phrased LeanFinder requests in `searches.jsonl`. All completed successfully. LeanSearch returned generic retracts, localization triangles and `CategoryTheory.Functor.mapDerivedCategoryFactors`. Loogle returned generic triangulated-functor declarations, including map_distinguished. LeanFinder returned Zariski scheme localization and affine-limit results rather than pro-etale support or retraction theorems. I read the exact-functor localization source in `Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean`; it supplies a generic ingredient already covered by an existing DAG node, not the complete item. The grep search found no support-localization declarations in Mathlib. The item retains the earlier Q159 searches as inherited research, and appends only searches actually run by Q133.

## Review by Q133

I checked delivery-errors B--E against the node and the sources. There are no new nodes to hide a clause, introduce an undefined object, duplicate a prior result, or omit a search for. Every proof dependency is the union of the step uses; every citation has a literal extract from the current cited statement in citations.json. No step exceeds 2000 characters. I checked the actual mathematical interfaces as follows.

Step 1 uses the explicit finite free module description in `lem-pur-finite-kummer-level`, whose statement I opened in full and checked against the current blueprint proof. The input has e dividing n, n positive and ell different from the characteristic, so N is a positive integer and the displayed finite Cartesian power is genuinely finite. This avoids relying on a definition that merely calls the quotients finite. Step 2 uses precisely the conclusions of the already reviewed `lem-pur-affine-line-support-geometry`: finite type of X and U, Noetherianity of all three schemes, and quasi-compactness of j. Its field and finite-type hypotheses hold; separatedness is stronger than it requires. I checked its sources Stacks 01T6, label lemma-finite-type-noetherian in morphisms.tex, and 01OW/01OX, labels lemma-locally-Noetherian and lemma-immersion-into-noetherian in properties.tex.

Step 3 uses `lem-exc-proetale-closed-exact` with the now verified quasi-compact complement and finite constant coefficient ring. I read Stacks 09BM, label lemma-closed-immersion-complement-retrocompact-exact in proetale.tex; without that complement hypothesis a general pro-etale closed pushforward could not be used here. I read both exact-derived statements cited: one identifies the termwise functor with the ordinary derived functor, and the other explicitly gives shift commutation. Stacks 015F, label lemma-right-derived-exact-functor in derived.tex, checks the termwise computation. The cohomology formula is then the written kernel-image-quotient calculation, valid also for unbounded L. It uses no constructibility or finite-Tor hypothesis.

Step 4 uses the full statement of `lem-pur-support-localization-triangle`: the input is bounded below, the coefficient ring is finite, and the complement is quasi-compact. Its functor is the same derived supported kernel named in the item, rather than a separately transported exceptional functor. I also opened `def-pur-support-triangle`, whose definition specifies the supported-kernel inclusion and the open unit, and `lem-sf-ringed-closed-kernel-adjoint`, whose statement says verbatim that the inclusion is the sheaf counit and that the derived counit is induced by it. These statements justify the asserted first arrow; an abstract existence of a triangle would not do so. This was an explicit C4 check and correction to the initially shorter assembly.

Step 5 uses `prop-pur-kinjective-resolutions-exist` on the small models of the pro-etale sites already required by the project size convention. Its actual statement supplies K-injective resolutions for all sheaf-module complexes. `lem-weil-proetale-module-direct-image-left-exact` explicitly supplies additivity, and `lem-pc-right-derived-functor-triangulated` applies to any additive functor with these resolutions. I read the source `lean/WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/Triangulated.lean` through its two final instances: the maps use the canonical shift comparison, so the triangle has a specified last arrow. No compilation was run.

Step 6 reads the affine datum and the finite Kummer level statement literally: they give the same p,s,j,pi, and the twist comparison is compatible with base change, in particular restriction to U. All schemes are over k, so ell is invertible. `lem-weil-derived-direct-image-composition` explicitly covers all ordinary finite-level pro-etale derived objects, not only constructible ones. Its natural comparison has direction R(gf)_* to Rg_*Rf_*, so the proof uses its inverses for alpha and beta; the identity comparison and ps=id give the first identification. No integral or rational clauses are used. Step 7 is elementary transport by those specific isomorphisms: I wrote u, r and delta as composites, including the shift comparison, and cited the isomorphism axiom for distinguished triangles. Naturality follows by substitution into these formulas from the already cited functorial support triangle and natural comparisons, without choosing a completion of a triangle morphism.

For edge cases, Y empty gives three empty schemes and the zero triangle; a point gives the usual affine/punctured-line pair; a nonreduced finite-type base is allowed by the geometry and support statements. Ramified coefficients with n=e are included (N=1), and unramified n=1 is included. Negative cohomological degrees and arbitrary unbounded L in the exact-pushforward clause use the same degreewise kernel and quotient calculation. None of the reasoning uses regularity, smoothness of Y, or geometric stalk conservativity. No prohibited SGA source is used.

The off-unit citations declared in split_report.tool_uses are generic exactness, derived-functor, resolution and kernel-adjunction tools; they do not replace the unit's affine-line Kummer route. I have not changed top-level tool_uses or any unit or chapter record.
