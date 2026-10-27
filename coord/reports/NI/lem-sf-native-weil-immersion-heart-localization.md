# Stage-1 delivery: lem-sf-native-weil-immersion-heart-localization

## Files written

- dag/nodes/sec-six-functors/lem-sf-native-weil-immersion-heart-localization.json: statement, split into ten proof steps; no Mathlib match for the complete theorem.
- citations.json: one entry for each step/node citation, quoting the complete verbatim statement to include all clauses actually used.

New nodes: 0. Mathlib leaves: 0. Existing statement, statement dependencies, provenance, source and blueprint breadcrumbs are retained. The report and search log are in this sandbox. No Lean file was written, no compiler was run, and the shared repository was read only.

## Attachments

None for this item. A search for its blueprint tag in lean/WeilConjectures found no declaration. I also read the relevant native declarations in WeilSheaf/Category.lean, OpenImmersion.lean, UpperStarLowerStarAdjunction.lean, Triangle.lean and UpperStarExact.lean, and Adic/UpperStar.lean, Module.lean, Constructible.lean, ClosedImmersion.lean, GeometricFrobenius.lean, ExchangeMate.lean and OpenImmersion.lean. Several components exist, including coefficient pullback and exact pullback/open extension, but these do not give every clause of the item as one finished attachment. In particular the ordinary short-exact-to-triangle construction does not assert this localization sequence. I did not treat the broader derived existence assertions as finished proofs.

## WANTED

None. All sources used for this assembly are present. The blueprint gives the general recollement route, and the native sheaf-level assembly is explicitly agent-authored.

## Errors and scope

No statement dispute was found. No hypothesis or conclusion was changed. The item's old source field names WeilSheaf/Category.lean and WeilSheaf/OpenImmersion.lean without their full prefix; the actual files are under lean/WeilConjectures/WeilSheaf, not SixFunctors/ProEtale/WeilSheaf. The named coefficient and immersion-exactness sources are under SixFunctors/ProEtale/Adic as recorded.

Two tempting shortcuts were rejected during source checking. The native pullback/Frobenius-mates node assumes separated source and target schemes, while this item assumes only qcqs schemes locally of finite type. It is therefore not cited. Instead step 5 uses the general equivalence/adjunction theorem and the actual section-reindexing definitions. Similarly, the continuous-module localization and supported-constructibility nodes use the all-continuous coefficient ring; I did not substitute that ring for the locally finite continuous B used here. The finite-coefficient immersion theorem is not applied to B either.

## Unfinished work

None in the one-level split. All dependencies already exist in the DAG. Their future proof work remains on their own nodes.

## Not duplicates

There are no new nodes and hence no new/existing same-tag pairs. Whole-DAG keyword and tag searches found the existing generic ring-sheaf localization, native pullback, native constructible abelian category, exact open extension and finite-stratification nodes used below. Whole-blueprint searches for open closed, locally finite, fixed pairs, recollement and ring-sheaf found no blueprint node stating this entire native fixed-pair theorem. The existing common-stage derived Weil recollement statement has a different coefficient and derived realization, so it is not recorded as same_as. blueprint_refs.py ancestor reports None; the inherited from.node=null and via breadcrumb are retained.

## Review by NI

I read coord/delivery-errors.md B through E in both copies of that document, the stage-1 contract, the three blueprint levels in SETUP.md and GOAL.md. I checked the current unit and chapter records and read the latest prop-functor-package proof clause (3), lem-zl-morphism-open-closed-reduction proof Part 1 and det-sf-open-closed-sequence-ring-sheaf proof (1)-(4). This split supplies the ordinary heart input to the existing open-closed derived route. It changes neither the chapter nor the unit route. The proof origin says agent, since the native-coefficient and fixed-pair assembly is not a theorem stated verbatim in Stacks.

For the mathematical source I read proetale.tex at lemma-closed-immersion-complement-retrocompact-exact (09BM), lemma-ses-associated-to-open (09AH) and their surrounding extension-by-zero and restriction statements. The quasi-compact open complement is essential to both uses and is present here. I checked the native section formula in the framework: functions live on the whole underlying site object and are locally of finite coefficient span. Step 2 uses the existing native coefficient isomorphism, not an assertion about a discrete constant ring or about arbitrary all-continuous functions.

I opened the statement of every cited DAG node. Step 1 takes only the base-change immersion and qc assertions from the three geometric permanence nodes. Its finite affine-cover argument uses the finitely generated field-algebra Noetherian theorem with the base-changed coordinate algebras, so no separatedness is required. Closed charts are arbitrary quotients, including nonreduced ones. This also verifies the qcqs and Noetherian hypotheses used later.

Step 2 takes the coefficient map isomorphism, exact native pullback and composition comparisons from lem-sf-native-adic-pullback-exact-lisse. The precomposition formula shows multiplicativity and the Frobenius square directly. I checked the isomorphism-inverse-image node's reindexing statement; its sheaf-level conclusion is used for the site objects and step 2 supplies the native scalar identification. The module actions are therefore preserved, without claiming the constant-ring clause already covers B.

Step 3 uses the stated exact conservative forgetful functor of lem-sf-native-weil-constructible-abelian. Reflection of exactness is written out using the quotient of kernel by image and the end kernel/cokernel. This avoids importing the stronger small-limit hypotheses of a different fixed-pair theorem without checking them. All categories here are the ambient abelian hearts, so no input constructibility is assumed.

Step 4 uses each of (1)-(3) of det-sf-open-closed-sequence-ring-sheaf for the actual ring B_X after the coefficient isomorphisms. Its statement allows any ring sheaf; it supplies exact closed image, the invertible closed counit, disjoint restriction and the sequence with the actual maps. The closed pullback/direct-image adjunction is separately supplied by lem-weil-pbc-ringed-topoi-module-adjunction with exactly the precomposition structural map. I checked that this cited node states the tensor formula and the Hom bijection, rather than merely defining module sheaves.

In step 5 the generic equivalence-square-inverse-mate-coherence theorem (1) applies with the Frobenius equivalences of step 2, and the same specified ordinary adjunction on either side. I checked the actual native definitions: geometric Frobenius direct comparison is composition of direct images; open extension comparison is defined by conjugateIsoEquiv (Adic/OpenImmersion.lean, lines 299ff.). The direct-image Hom transpose commutes with the displayed object reindexing and its scalar map, as written in the step, so it is the normalized comparison, not an arbitrary isomorphism of right adjoints. Thus the named generic theorem identifies the actual comparisons as inverse mates. No separatedness hypothesis is introduced.

Step 6 applies lem-sf-fixed-pair-adjunction-lift to those mates, and its statement explicitly says that the carrier components are the original unit and counit. I read the native lift formula and the module IsoAlgebraAdjunction definition and carrier lemmas. The proof writes the two actual fixed-pair commuting equations. This is the needed compatibility; it does not simply assert that an underlying isomorphism transports an adjunction.

Step 7 uses carrier exactness from step 4, exact conservative forgetting from step 3 and the native exact-open-extension theorem. It explains finite preservation by the finite-product/kernel and finite-coproduct/cokernel descriptions, including additivity. Step 8 takes arbitrary native constructible pullback from lem-sf-native-adic-constructible-pullback and the actual equivariant extension-by-zero preservation from lem-sf-native-weil-open-exact-constructible. Both statements use exactly the native lisse condition, with finite rank allowed to vary with the covering member.

For step 9, lem-sf-native-adic-qcqs-stratification has both qc and qs hypotheses; step 1 provides them for the geometric closed scheme. I use only the first geometric paragraph of lem-sf-closed-partition-module-test to extend its finite partition across the closed immersion in the Noetherian geometric scheme. That paragraph has no coefficient restriction. Its later finite-ring module clauses are not invoked. The ring-sheaf localization node supplies the closed counit and zero open restriction, while the native pullback-composition statement identifies restrictions to each old stratum. Hence old strata are lisse and the additional stratum is rank zero for B itself.

Step 10 takes the short exact carrier sequence from the generic ring-sheaf node, with the actual maps identified by step 6, and reflects it by step 3. Naturality is naturality of these same units and counits. I checked U empty, Z empty, X empty, rank zero and arbitrary nilpotent closed thickenings. The empty sequences become identities at the remaining supported term; empty strata can be discarded. No nonreduced complement was replaced by its reduction.

For B1-B10: no new node or hidden proof was placed in a new statement; existing metadata and mathematical statement are preserved. All searches run through the required msearch helper are recorded, including the second semantic phrasing. The grep hit algEquivIsoAlgebraIso was read at Mathlib/Algebra/Category/AlgCat/Basic.lean:243; it concerns ordinary algebra isomorphisms and is not this theorem. LeanSearch returned generic ShortComplex results, and the second LeanFinder query returned ordinary scheme-module and condensed-module facts, not native localization. No unavailable service was counted as an absence result.

For C1-C8 and D1-D5: citations.json uses the exact existing statement text for every citation. No step borrows a construction from a cited proof in place of its statement. The actual reindexing comparison is checked explicitly against its defining formula and then the normalized generic theorem is applied. No new node restates a clause of the item; in fact there are no new nodes. I traversed all proposed dependency closures before writing the split and found no path back to this item. Off-unit generic tools are declared in split_report.tool_uses for maintainer judgment.

For E1-E7: all finiteness, qcqs, complement and coefficient hypotheses are accounted for as described above. The native category is not identified with fixed pairs in another derived category. Every non-elementary step is under 2000 characters; the longest is the explicit reindexing/mate argument (1477 characters). It applies an existing generic adjunction theorem, rather than concealing a new source-specific comparison lemma.
