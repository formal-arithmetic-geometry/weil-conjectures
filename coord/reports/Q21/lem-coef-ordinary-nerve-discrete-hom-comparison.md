# Stage-1 report: lem-coef-ordinary-nerve-discrete-hom-comparison

## Files written

- `dag/nodes/sec-six-functors/lem-coef-ordinary-nerve-discrete-hom-comparison.json`: statement, split; no Mathlib match. Eight proof steps; statement unchanged; original source, blueprint ancestry and earlier search records retained. No new nodes and no new Mathlib leaves.
- `citations.json`: verbatim excerpts of the statements cited in every step, with both the projection and mapping-resolution conclusions quoted for step 3.
- `searches.jsonl`: five actual new searches through the required launcher command (LeanFinder twice, Loogle, LeanSearch, grep). `write_split.py` is an item-local preparation script, not a project change.

## Attachments

None. Searched the whole `WeilConjectures/` source tree of slopmaster2 by the item id and by rigidification/coherent-nerve terminology. The hits involving rigidification concern algebraic sheaves, not enriched simplicial categories. There is no declaration of the project giving this statement. The read-only upstream master category-theory tree likewise has no matching declaration; master sorry declarations are not evidence of completion.

## Wanted sources

WANTED: archival copy of Jacob Lurie, *Higher Topos Theory*, Section 2.2.4 opening calculation and Proposition 2.2.4.1, Section 2.2.2 Q-resolution, and Section 5.1.3 pp. 319–320, for this item. Read the relevant passages online at https://www.math.ias.edu/~lurie/papers/HTT.pdf .

WANTED: archival Kerodon extracts 03N6/03N7 (strict Hom model), 0142/03X7 (singular-realization unit and weak-equivalence convention), 03PJ/00TN (mapping-homotopy invariance and Kan exponentials), and 01DK (componentwise detection), for this item. Read these online; the web reader timed out on 03PJ, then curl successfully retrieved and displayed the proposition and proof. These are Kerodon identifiers, not Stacks tags. No Stacks source supplies this enriched infinity-category comparison.

## Audit findings and changes

The unsplit item correctly distinguishes the discrete ordinary Hom family from the concrete singular-realization rigidification family. No statement dispute or hypothesis repair was needed. Its original Kerodon 03N7 reference supplies the strict Hom model but does not, by itself, identify the particular augmentation from the project's concrete rigidification. I retained that source record and gave the proof its own agent-origin record explaining the additional comparison.

The split uses the existing `lem-coef-pinched-rigidification-resolution`, not a new lemma restating the item's first clause. For an ordinary nerve the right-pinched mapping set is literally constant Hom. On each copy of Q^n in the coend, the augmentation after theta and the projection p are both the constant final arrow. This proves the map-level comparison, rather than merely the equality of its components. Unit naturality then gives the singular version. I used the existing Kan-target testing criterion for cancellation; an argument only checking homotopy groups at basepoints in the image of theta or of the unit would need an additional basepoint-transport explanation. The testing argument avoids that gap.

A family of weak equivalences alone does not give a coherent transformation. Steps 5–6 establish enriched naturality and then construct the mixed simplices of an actual map K × Delta^1 to the space category. Step 7 turns component weak equivalences into inverse-triangle witnesses before using pointwise detection. Step 8 checks the identity vertex and its unit simplex, restriction, universe inclusion, and empty cases.

Read the chapter record `sec-six-functors` and unit `sk-prop-sf-biduality-general`. The current chapter record points at main-20261017 and the unit retains historical master metadata; neither record was altered. The blueprint ancestor is `prop-coef-integral-exceptional-adjoint`; I read its main-20261015 proof, especially paragraph 2's derived coefficient adjunction mapping calculation. This foundational item serves the existing ancestry below that calculation. It does not replace the geometric or coefficient route of the chapter/unit and is not the unit key node. Historical mentions of excluded literature in the chapter/unit are not used as sources of this split.

## Mathlib and duplicate checks

The original item has eight older search records, retained verbatim. This attempt ran five more recorded searches, including two different semantic phrasings. Read the hits and their sources: `CategoryTheory.nerve.homEquiv`, `Mathlib/AlgebraicTopology/SimplicialSet/Nerve.lean:168–173`, concerns edges only; `CategoryTheory.nerveAdjunction.isIso_counit`, `NerveAdjunction.lean:409–415`, concerns the ordinary homotopy-category adjunction; `CategoryTheory.Nerve.quasicategory`, `Quasicategory/Nerve.lean:29–32`, gives only the ordinary-nerve horn condition. Read `SimplicialNerve.lean:14–35`, whose project list explicitly leaves the locally Kan nerve/space-category results open. None gives this item or a one-line specialization of it, so this is not a Mathlib leaf.

Searched the whole DAG for rigidification, the cited identifiers, and pointwise/realization terminology; read all cited node statements. Ran blueprint search for rigidification, discrete Hom, pinched, and ordinary nerve and the ancestor command. No blueprint node states this item in another form. Every candidate needed for the proof was already a DAG node. A read-only traversal of the existing statement/proof dependencies confirms that the proposed citations do not depend on this item.

## Not duplicates

No new nodes: there are no new/existing pairs to distinguish. In particular the Q-resolution, unit theorem, testing criterion, Kan mapping invariance and pointwise detection are reused under their existing ids.

## Review by Q21

I checked B–E of `coord/delivery-errors.md` against the statement, the proof, the definitions and the sources, rather than treating the imported references as an accepted proof. This is a split with eight arguments, not eight renamed clauses or an appeal to a new comparison node. No unsplit auxiliary statement, new definition, Mathlib leaf or Lean attachment is introduced.

For step 1 I read `def-coef-infinity-category-of-spaces`: it states the simplex colimit, image-of-subsets action and union composition used to construct epsilon. `def-cbc-enhanced-diagrams-cones` supplies the ordinary nerve convention. The map to an ordinary arrow is independent of the subset, respects union by composition, and also respects noninjective ordinal maps and identity arrows. Thus the colimit map and its naturality are justified from the definitions.

For step 2 I checked the full initial-face condition in `def-cbc-enhanced-diagrams-cones`, not just equality of initial vertices. It forces all initial arrows to be identities, so every operator fixes the final arrow f. Inner-horn fillings are the ordinary composition/associativity calculation, with the two-dimensional case included. No groupoid or invertibility hypothesis is needed on C.

For step 3 I read the entire statement of `lem-coef-pinched-rigidification-resolution`. It gives both p for every simplicial set and the specified theta for a quasicategory, together with its action on each copy of Q^n. The hypothesis holds by step 2. I checked epsilon theta = p on those copies using their actual final arrow, not a noncanonical comparison. `lem-cbc-realization-weak-equivalence` gives both directions of the Kan-target testing criterion, so cancellation of the bijections proves exactly the declared realization-based weak equivalence. These two statements are quoted in the citations file; no Quillen-equivalence counit theorem is implicitly invoked.

For step 4 the same testing criterion cancels the characteristic-simplex unit. `lem-cbc-realization-singular-unit-weak` explicitly imposes no Kan or nonemptiness condition, so it applies to B(c,x). The definition of the space category explicitly proves Sing(T) is Kan by horn extension. I checked that Sing of the realization of a constant set is that same constant set and that its unit is literally the identity under this identification. Consequently the map proved weakly equivalent is exactly Sing|epsilon|, as requested.

For steps 5–6 I read the precise reflected-subset formula of `def-coef-infinity-presheaf-yoneda` and the product comparison/composition formula of `def-coef-infinity-category-of-spaces`. Applying the enriched epsilon to precomposition and postcomposition gives the displayed naturality identity in all degrees. The mixed-simplex construction uses that identity for the two possible mixed label triples, and both unmixed triples use the already specified actions. Restriction along ordinal maps respects reflection and subset images. This establishes a genuine edge of the full functor simplicial set, not just independent one-variable equivalences. These are direct calculations from the cited constructions, so they are marked elementary; they hide no independent lemma with additional hypotheses.

For step 7 `lem-cbc-kan-mapping-homotopy-invariance` states that the two functor spaces are Kan and that weak-equivalence precomposition induces a bijection on components. Applying this first with target P gives g; applying it with target Q cancels precomposition to obtain fg homotopic to the identity. Kan horn fillings join or reverse paths; the resulting homotopies give the enriched Delta^2 inverse witnesses. The definition's equivalence-edge convention is therefore met before `lem-coef-infinity-pointwise-equivalences` is applied. That node allows every small simplicial indexing set; here K is small because C is V-small and the value category is formed in a containing ambient universe. The target is the declared infinity category of V-small spaces. The three smooth-purity-unit tools are declared in `split_report.tool_uses` as generic foundational tools; no result of a different geometric unit is used to replace this unit's route.

For step 8 I checked identities at the enriched, singular and coherent-simplex levels, so the unit homotopy is retained. Restriction and universe inclusion use the very same maps; no inverses are chosen functorially. Small-case checks: empty C gives an empty indexing simplicial set; an empty Hom set forces the source enriched Hom empty by its augmentation; a discrete category gives identity/empty comparisons; the terminal category gives a point; a category with parallel arrows keeps the arrows in distinct fibers; a category with nontrivial automorphisms still has discrete right-pinched Hom, since the entire initial face is constant. Degenerate strings give identities and do not introduce a missing nondegeneracy assumption.

Every step has fewer than 2,000 characters. I inspected the coend identification and the mixed-simplex construction anyway: each is a direct specialization or defining equation using cited statements, not a hidden general comparison theorem. The statement and every new recorded search are genuine; every quoted citation is a contiguous verbatim excerpt of the corresponding node statement. No project/launcher file, Lean source or literature file was written, and no git command, compiler, Lake tool, local DAG checker, or sub-agent was used.

## Unfinished work

None in the stage-1 split. Independent second reading and actual delivery are reserved for the next worker. Dry-run status is recorded below after the server checks complete.

## Dry run

`tools/review_split.py` via the required server wrapper: PASS, 0 new nodes; all three off-unit citations accepted as declared tool uses.

Full required `deliver.py Q21 lem-coef-ordinary-nerve-discrete-hom-comparison --no-push`: printed `OK (not pushed)` with preflight passed (temporary delivery commit b666b3d0fc). No delivery was pushed. The final report and the refined per-step verbatim citations are submitted once more with the same no-push command so the second reader receives the accepted final sandbox.

## Second reading by Q21

- Statement: I reread the item against Kerodon Construction 8.3.6.1 (03N6) and Proposition 8.3.6.2 (03N7), the explicit rigidification definitions, and the stated Q-resolution; the ordinary nerve, right-pinched convention, augmentation, weak-equivalence conclusion, coherent two-variable comparison, identity, restriction, universe, and empty cases all have the hypotheses and clauses written in the node. Kerodon 03N6/03N7 supplies the strict Hom-functor framework; the augmentation comparison itself is supplied by the explicit steps below.
- Step 1: Checked against the simplex-colimit and subset-poset definitions in `def-cbc-enhanced-diagrams-cones` and `def-coef-infinity-category-of-spaces`; the constant composite map respects identities, union composition, degeneracies, ordinal images, and the colimit relations. Verdict: correct and elementary.
- Step 2: Checked against the full initial-face right-pinched definition and the ordinary nerve horn fillers; a constant initial face forces every initial arrow to be an identity, leaving exactly one final arrow in every degree and preserving it under all operators. Verdict: correct and elementary.
- Step 3: Checked the exact statements of `lem-coef-pinched-rigidification-resolution` and `lem-cbc-realization-weak-equivalence`; on each Q-copy both maps are the same constant final-arrow map, and cancellation is applied in the correct contravariant order. Verdict: correct; no hidden basepoint or Kan hypothesis.
- Step 4: Checked the realization quotient, singular/Kan construction, `lem-cbc-realization-singular-unit-weak`, and the testing criterion; realization of a discrete simplicial set and its singular complex are identified explicitly, and the unit naturality equation supplies the required cancellation, including the empty case. Verdict: correct.
- Step 5: Checked the reflected-subset and enriched-composition formulas in `def-coef-infinity-presheaf-yoneda` together with the singular-realization enrichment; the displayed identity is exactly the pre/postcomposition naturality needed for both variables. Verdict: correct and elementary.
- Step 6: Checked the coherent-nerve and functor-simplicial-set definitions; the monotone label sequences give all mixed simplices, with the two mixed composition cases equal by Step 5 and restriction compatible. Verdict: correct and elementary; this constructs an actual transformation rather than a family of unrelated maps.
- Step 7: Checked `lem-cbc-kan-mapping-homotopy-invariance` and `lem-coef-infinity-pointwise-equivalences`; surjectivity and injectivity give the two inverse homotopies in the right order, Kan composition/reversal supplies single witnesses, and pointwise detection applies to the resulting edge. Verdict: correct.
- Step 8: Checked identity preservation, restriction, containing-universe inclusion, and empty cases against the three definition nodes; the singular identity and degenerate simplices are preserved and no nonemptiness assumption is introduced. Verdict: correct and elementary.
- New nodes: none. I searched the whole DAG for the rigidification, pinched, discrete-Hom, and pointwise claims and found the cited existing nodes; the recorded LeanFinder, Loogle, LeanSearch, and Mathlib grep searches were reread and none gives this enriched comparison. There are therefore no B1–B7 new-node records to repair.
- Changes: none to the node, citations, or search log. I added this independent source-and-step audit only; the worker’s report and `## Review by Q21` remain intact.
