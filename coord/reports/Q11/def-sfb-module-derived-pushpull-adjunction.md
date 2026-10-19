# Worker report: def-sfb-module-derived-pushpull-adjunction

## Files written

- `dag/nodes/sec-six-functors-basics/def-sfb-module-derived-pushpull-adjunction.json`: existing definition, now split; no exact Mathlib match.
- `citations.json`: verbatim statements for every step citation.
- `report.md`: this report. No new nodes or Mathlib leaves.

The statement and its three statement dependencies are unchanged. The six proof steps replace the imported compressed argument. All dependencies are existing nodes. `blueprint.same_as` is empty: the unit statement contains this adjunction together with the entire derived-functor construction, but does not state precisely this standalone definition. No unit realization is appropriate: this is not the unit's key node. This newly imported node has no chapter/unit fields or matching new chapter/unit JSON records in the current shared repository; I read the current blueprint chapter and unit `_section.md` directly and preserved the maintainer's metadata.

## Attachments

None. Searches by the exact blueprint tag, the full declared name, and derived-adjunction names in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` find the finite-coefficient/generic coefficient category construction, not the condensed-ring module-object construction. The master reference has `AlgebraicGeometry.ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction` in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/UpperLowerStar.lean:242`, defined from `.derivedAdjunction`; under the brief this master source is reference material, not evidence of a finished proof. No attachment claimed.

## WANTED

None.

## Problems found and corrected

The statement is faithful to the current main-20261015 blueprint. No statement dispute or statement correction.

The imported proof compressed the derivation of adjunctions and checked only preservation of K-flat quasi-isomorphisms. The existing `sk-def-sfb-derived-categories` statement already contains precisely the needed general derived-adjunction theorem. I use that statement instead of creating a duplicate general lemma or copying its proof. The split also checks its structural hypotheses for the actual module categories.

The blueprint proof of the unit cites `sk-prop-sfb-module-category`, which is present as a blueprint section but is absent as a DAG node. Its smaller facts, including module Grothendieck structure and functorial flat resolutions, already have DAG nodes. The proof assembles those statements instead of citing the absent aggregate. This keeps the unit route: derive the complete module functors directly, without deriving the abelian-sheaf factors separately.

Mathlib's `CategoryTheory.Adjunction.derived`, read at `Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:144`, requires the additional derived-composition/absoluteness instances. It does not by itself state the module-category and resolution prerequisites. The item is therefore split, not marked Mathlib. All Mathlib searches recorded are exactly those run by msearch.py, and both a general adjunction phrasing and the actual condensed-module phrasing were tried. The latter returned underived sheaf pullback adjunctions; those do not supply the total derived adjunction.

## Unfinished work

None in this one-level split. Existing prerequisites remain work for their owners. This worker does not push; the second reader receives the sandbox after the dry run.

## Not duplicates

No new nodes. Existing general derived adjunction, module structure, flatness and resolution statements are reused. The broad blueprint search `derived adjunction` found the existing general definition and the distinct finite-coefficient, scalar-change and restricted-adjunction nodes; none calls for another node here.

## Review by Q11

I read the current chapter `_section.md`, the derived-pushpull unit `_section.md`, the item's statement and proof file, and Parts 3–4 of the module-category blueprint proof. The latter supplies the free-sheaf construction that I expanded. I opened the statements of every cited DAG node; `citations.json` contains their exact text, not text from their proofs. There are no new-node sources to check.

Step 1 uses the actual pro-etale size convention, the sheaf tensor statement (including its closedness and colimit assertion), and the arbitrary-ring-sheaf Grothendieck theorem. The last theorem applies to the constant ring Z on the small representative, so this is not an unjustified application of an etale constant-coefficient theorem to a pro-etale condensed coefficient system. Abelian sheaves and Z-module sheaves have the same objects and morphisms by the repeated-addition action.

Step 2 takes flatness of the sheafified representable free sheaf from `lem-weil-pbc-free-sheaf-flat`, with P=Z. That node explicitly allows an arbitrary essentially small site and A=Ab. I wrote the functor on the indices (U,s), the evaluation epimorphism and its naturality. Tensor commutes with coproducts by the cited sheaf-tensor statement; sums of exact sequences are filtered colimits of finite sums, so the cited exact-filtered-colimit assertion proves their exactness. Thus this step constructs a functorial flat resolution, rather than assuming one or confusing a K-flat resolution with a flat object.

Step 3 applies the module-object Grothendieck and flat-resolution statements only after establishing their base-category hypotheses in steps 1–2. Commutativity is already part of the coefficient-ring hypothesis and the module-object convention. I checked the symmetric relative tensor and internal Hom statements: they give the symmetric monoidal structure and its right adjoints, respectively. I additionally cite `lem-weil-pbc-left-adjoint-preserves-colimits` for preservation of colimits by the relative tensor functors. Grothendieck exact filtered colimits imply the exact integer-indexed colimits needed in the existing derived-functor theorem. No missing aggregate module-category node is used.

Step 4 cites the upper-star and lower-star statements specifically for additivity and the underived module-adjunction statement for the actual adjunction. In particular the right adjoint includes restriction of scalars, and the left includes extension of scalars; neither is identified with the abelian-sheaf functor.

Step 5 cites the K-flat quasi-isomorphism preservation statement exactly as written. The right- and left-derived-functor clauses of `sk-def-sfb-derived-categories` then give the total functors using the hypotheses already checked. Its statement explicitly says every Grothendieck abelian category has K-injective resolutions, so this assertion is not borrowed from an uncited proof.

Step 6 specializes the explicit Derived adjunctions clause of the same node. This is an elementary specialization, not an unsupported general derived-adjunction argument: the cited statement itself says Lf is left adjoint to Rg under precisely the hypotheses established. It defines the chosen adjunction without using a theorem about the object it defines. The existing general theorem is not a new node restating this item.

I tested the construction on the identity morphism, on the zero condensed ring, and on zero or empty complexes. The identity gives the derived identity adjunction; the zero ring gives the zero module categories, and no step assumes a nonzero ring, nonempty scheme or nonzero section. The free resolution includes the zero-section indices, whose evaluation maps are zero; this does not affect epimorphy or functoriality. Indexing sums are small in the chosen universe. All non-elementary claims are cited; the explicit finite-sum and evaluation arguments are kept in the proof, not promoted to unnecessary nodes. I checked B–E: no new-node schema/duplicate issues, no unquoted citation, no use of a cited proof as its statement, no changed coefficient category, no SGA source, and no new route replacing the unit's argument.


## Second reading by Q11

- Item statement: compared every hypothesis and clause with main-20261015 `def-sfb-module-derived-pushpull-adjunction.md`, its separate `.proof.md`, and the derived-pushpull unit statement/proof. PASS: arbitrary schemes and morphism, commutative condensed coefficients, unbounded categories, K-flat source resolutions and K-injective target resolutions all agree; the statement is unchanged.
- Step 1: opened `def-weil-pbc-proetale-site`, `sk-def-sfb-sheaf-tensor` and `lem-weil-pbc-ring-sheaves-grothendieck`; checked the last against Stacks 079Q (`remark-existence-D`) and 079B (`definition-grothendieck-conditions`) in `injectives.tex`. PASS: the small representative is taken in the larger working universe, and constant-Z modules are exactly abelian sheaves, so the arbitrary-ring-sheaf Grothendieck statement applies.
- Step 2: opened all three cited statements, compared the construction with module-category proof Part 4 and Stacks 03EV (`lemma-j-shriek-flat`) in `sites-modules.tex`. PASS after making finite-limit preservation plus right exactness imply flatness explicitly: the flatness node allows A=Ab and P=Z; the element-indexed evaluation maps exist by the free-presheaf/sheafification definitions, are natural, and hit every section. Exactness of the sum follows from exact finite sums and exact filtered colimits; no additional lemma node is needed.
- Step 3: opened all eight cited statements, including the added `sk-def-sfb-pulled-back-coefficients`, and their main-20261015 source statements; compared with module-category proof Parts 3–4 and Stacks 0038 (`lemma-adjoint-exact`) in `categories.tex`. PASS after repair: commutativity of the pulled-back ring is now explicitly cited, coequalizers exist in the abelian base, the closed tensor preserves colimits, its additivity is explained using diagonal/codiagonal, and the filteredness of the integer poset is written out. The functorial flat-resolution statement requires precisely the natural flat epimorphism constructed in step 2.
- Step 4: opened both functor definitions and the underived adjunction statement. PASS: all three explicitly give the functors, additivity, and their adjunction; extension/restriction of scalars are included. Elementary specialization only. Corrected the source path to the actual `.proof.md`.
- Step 5: opened `lem-sfb-module-upper-star-kflat-quasi-iso` and the left/right derived-functor clauses of `sk-def-sfb-derived-categories`. PASS: the former applies to the same module pullback and the latter explicitly supplies K-injective resolutions for the Grothendieck target category. No assertion was borrowed from a cited proof. Corrected the source path to the actual `.proof.md`.
- Step 6: reread the Derived adjunctions clause of `sk-def-sfb-derived-categories` against every hypothesis established in steps 1–5 and the item's source proof. PASS: direct specialization defines exactly the induced adjunction, without asserting an uncited localization theorem or deriving the two factors separately. Corrected the source path to the actual `.proof.md`.
- New nodes: none; no new-node source, duplicate, definition-dependency, search or Mathlib-leaf repairs are required (B1–B9, C5, D1–D2). The existing general derived-adjunction statement is broader than this module specialization and already supplies the needed conclusion.

Independent searches: ran msearch.py with the new LeanFinder phrasing "For sheaves of modules on ringed sites, the inverse image derived using flat complexes is left adjoint to the direct image derived using injective complexes" (eight underived module-pullback/pushforward hits), Loogle `CategoryTheory.Adjunction, "IsLeftDerivedFunctor"` (zero hits), and grep `adjunction|IsLeftAdjoint|derived` under `Condensed` (free/forgetful and discrete/underlying adjunctions). The actual results remain in searches.jsonl. Read `CategoryTheory.Adjunction.derived` at Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:144–150: its composite-derived-functor instances do not supply the module structures and derivability hypotheses here. The item remains split, with zero Mathlib leaves. Slopmaster2 has the general coefficient-category pro-etale adjunction, whereas the exact condensed-module declaration occurs only in the read-only master reference at UpperLowerStar.lean:242; no closed-proof attachment is claimed.

Small cases: identity on Spec(k), with k a field and any permitted coefficient ring, specializes to the identity adjunction. The zero coefficient ring gives zero module categories. For the empty scheme the abelian sheaf and module categories are zero; evaluation remains an epimorphism even though every section is zero. Zero complexes and complexes concentrated in degrees 0 or 1 impose no boundedness or nonzero hypothesis. The functorial flat cover need not send the zero sheaf to zero, and no step claims that it does. Indexing sums stay small in the chosen working universe.

Changes made: added the existing coefficient-commutativity citation in step 3; explained flatness from finite-limit preservation and right exactness in step 2; explained tensor additivity and integer-indexed exactness in step 3; corrected step 4–6 and proof_origin source paths to the separate proof file; fixed the doubled TeX slash in the item's title; regenerated citations.json from the exact cited statements. No statement, statement dependency, unit route, first-worker report section, or existing prerequisite was changed. Checked that the added coefficient node has no dependency path back to this item (125-node closure). The `split_report.tool_uses` entries are worker proposals under the documented review_split.py convention, not maintainer-owned top-level `tool_uses`; the maintainer judges these at merge. No SGA source is used.
