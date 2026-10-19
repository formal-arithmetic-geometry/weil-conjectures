# Stage-1 report: lem-coef-corepresented-equivalence

## Files written

- `dag/nodes/sec-six-functors/lem-coef-corepresented-equivalence.json`: the existing statement-only node, now split into four sourced proof steps; no new child nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotes for every cited node in every step.
- `searches.jsonl`: the four Mathlib searches run for this item.

## Attachments

None. I searched both read-only source checkouts for the exact item id, the explicit corepresented construction, rigidification and equivalence terminology. No sorry-free project declaration states this item exactly.

## WANTED:

- An archival copy of Lurie, *Higher Topos Theory*, Section 5.1.3 (printed pp. 319–320), Section 1.2.3 and Proposition 1.2.4.1, for the rigidification, homotopy-category and equivalence-edge route.
- An archival copy of Kerodon Subsection 4.6.8 (01PF), especially Propositions 4.6.8.11–4.6.8.12 and 4.6.8.19, for enriched composition and coherent-nerve compatibility.

These infinity-categorical sources were read online; no SGA or Stacks substitution gives this statement.

## What was wrong or incomplete

The imported node was statement-only. Its statement and the two definition dependencies are correct and were preserved. The proof needed to expose the previously inline rigidification/precomposition argument: the coherent natural transformation, the inverse-triangle homotopies, the componentwise equivalence, and the pointwise promotion. The four steps now carry those arguments explicitly. No statement dispute arose, and no dependency was added or removed. Step 3 declares `lem-cbc-simplicial-homotopy-equivalence-weak` as a generic off-unit tool because the biduality unit has no replacement for this Kan-space homotopy criterion.

## Not duplicates

- `lem-coef-corepresented-equivalence` vs `def-coef-infinity-category-of-spaces`: the definition fixes the Sing-realization model of each covariant corepresented functor but expressly does not state equivalence invariance.
- `lem-coef-corepresented-equivalence` vs `lem-coef-infinity-hom-bifunctor-functoriality`: that node gives an abstract coherent Hom bifunctor identified with right-pinched mapping spaces; it does not identify its choices with the explicit Sing-realization functors fixed here.
- `lem-coef-corepresented-equivalence` vs `lem-coef-space-transport-classification`: transport classifies abstract mapping bifunctors and fibrations, without the explicit rigidification model or this precomposition transformation.
- `lem-coef-corepresented-equivalence` vs `lem-coef-infinity-mapping-composition`: that node supplies composition, units and inverse-edge criteria for right-pinched mapping spaces, while this item constructs the coherent equivalence between the explicit Sing-realization functors.
- `lem-coef-corepresented-equivalence` vs `lem-coef-infinity-pointwise-equivalences`: the pointwise node only promotes already-given component equivalences; it does not construct the components or their inverse homotopies.

## Review by Q49

I read `AGENTS.md`, `SETUP.md`, `GOAL.md`, `coord/dag-sync.md`, `coord/brief-stage1.md`, `stages/1-dag.md`, and delivery-errors B–E. I read the current item node and the retained Q18 report, including the exact statement, its two definition dependencies, the imported Mathlib-search verdict, and the blueprint ancestry. I also read `def-cbc-enhanced-diagrams-cones`, `def-coef-infinity-category-of-spaces`, `lem-coef-infinity-mapping-composition`, `lem-cbc-simplicial-homotopy-equivalence-weak`, and `lem-coef-infinity-pointwise-equivalences` in full; every citation quote in `citations.json` is copied verbatim from those statements.

Step 1 uses the explicit `H_c` construction: the definition says its values are `Sing|A(c,x)|` and its action is postcomposition in `A^{top}`. The enhanced-diagrams definition supplies coherent functors and natural equivalence edges, so applying the coherent nerve to the simplicial enriched action gives the displayed edge with all higher naturality data. I checked that the component has source `h_a(x)=Sing|A(a,x)|` and target `h_g(x)=Sing|A(g,x)|`, with the direction determined by composition with `e:g→a`.

Step 2 uses the inverse edge `e'` and the two inverse-triangle 2-simplices. The mapping-composition statement explicitly identifies pre/postcomposition as restrictions of the canonical composition class and characterizes equivalence edges by inverse edges with those 2-simplex boundaries. Applying the enriched composition, realization and Sing functors preserves the corresponding simplicial homotopies; the construction is parameterwise in `x`, so the homotopies are coherent natural transformations rather than only component-set equalities.

Step 3 checks the small target cases and the equivalence mechanism. For `C` a point and `e` an identity, both maps are identities. For the nerve of a two-object groupoid, the inverse maps exchange the two objects and the two triangle witnesses give the required homotopies. A noninvertible arrow in `Δ¹` is excluded by the stated equivalence-edge hypothesis. The homotopy-inverse maps satisfy the hypotheses of `lem-cbc-simplicial-homotopy-equivalence-weak`; the coherent-nerve definition of `S_V` retains the same inverse maps and endpoint homotopies as equivalence data.

Step 4 applies the pointwise-equivalence criterion, whose statement exactly says that an edge of a functor simplicial set is an equivalence iff every vertex component is. The component formula and inverse transformation were already constructed in Step 1 and Step 2, so this final step proves all clauses of the item without adding a colimit or accessibility hypothesis.

I checked the item’s source and blueprint place against the extracted Step 6 argument in `lem-coef-infinity-presheaf-presentability`; its route is the explicit HTT/Kerodon rigidification route. The Mathlib searches were actually run for Q49: LeanFinder and LeanSearch returned only ordinary-category/Yoneda or cocone declarations, Loogle reported no quasicategory identifier match, and the focused quasicategory grep returned no hits. I read those returned signatures and retained the no-match verdict; no Mathlib leaf is claimed. No new definition was introduced, no step restates the item, no SGA source is used, and all proof dependencies are the union of the cited uses. The off-unit tool declaration is limited to the generic homotopy-inverse criterion in Step 3.

## What I could not finish

No mathematical work remains in this one-level split. The required server dry run and delivery are the remaining validation gates; this report does not claim a push before those commands succeed.
