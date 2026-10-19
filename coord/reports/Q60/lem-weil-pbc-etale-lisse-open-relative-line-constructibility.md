# Q60 stage-1 report

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-lisse-open-relative-line-constructibility.json` (item; repaired split).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-lisse-filtration-devissage.json` (new statement-only node; Mathlib searches found no exact match).
- `citations.json` (verbatim statement quotes for every cited node and proof step).

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id, its Lean declaration keywords, and the constructibility/lisse terms; no sorry-free declaration states this item exactly.

## WANTED

None.

## Not duplicates

- `lem-weil-pbc-etale-lisse-filtration-devissage` vs `lem-sbc-cohomology-in-weak-serre-subcategory`: the existing node proves that all derived objects whose cohomology already lies in a weak Serre class form a triangulated subcategory; the new node instead transfers constructibility from the successive quotient objects of a finite filtration in the source abelian category through a specified triangulated functor.
- `lem-weil-pbc-etale-lisse-filtration-devissage` vs `thm-constructible-serre`: the existing node gives closure of constructible sheaves under kernels, cokernels and extensions; the new node is the derived finite-filtration induction that invokes that closure.
- `lem-weil-pbc-etale-lisse-filtration-devissage` vs `lem-sp-finite-filtration-induction`: the existing node is the filtered-object five-lemma isomorphism criterion, while the new node concerns cohomology of derived images and Serre closure.

- `lem-weil-pbc-etale-lisse-filtration-devissage` vs `lem-sc-p1-split-ses-cocycle-boundary`: the existing node computes a connecting morphism for a degreewise split short exact sequence of complexes; the new node proves finite-filtration induction for cohomology under a triangulated functor.
- `lem-weil-pbc-etale-lisse-filtration-devissage` vs `lem-pc-cone-short-exact-quasi-iso`: the existing node proves a cone-to-quotient quasi-isomorphism for one short exact sequence of complexes; the new node iterates filtration quotients and applies a Serre closure argument.
- `lem-weil-pbc-etale-lisse-filtration-devissage` vs `lem-sc-p1-injective-ses-homotopy-boundary-lift`: the existing node constructs a localized boundary lift under injectivity hypotheses; the new node concerns constructibility of all cohomology objects of a filtered input.
- `lem-weil-pbc-etale-lisse-filtration-devissage` vs `lem-sc-p1-split-ses-boundary-comparison`: the existing node compares explicit boundaries for a split complex sequence; the new node transfers a cohomology property through successive filtration triangles.
- `lem-weil-pbc-etale-lisse-filtration-devissage` vs `lem-pc-derived-functor-termwise-split-ses-triangle`: the existing node identifies the derived-image triangle for a termwise split sequence of K-injectives; the new node uses arbitrary finite filtrations and weak-Serre closure.
- `lem-weil-pbc-etale-lisse-filtration-devissage` vs `lem-weil-pbc-exact-functor-ses-triangle-image`: the existing node proves naturality of the connecting triangle under an exact functor; the new node applies a triangulated functor to a filtration and concludes constructibility.
- `lem-weil-pbc-etale-lisse-filtration-devissage` vs `lem-weil-pbc-complex-ses-triangle`: the existing node supplies the distinguished triangle for one short exact sequence of complexes; the new node is the finite induction over many quotient triangles.
- `lem-weil-pbc-etale-lisse-filtration-devissage` vs `lem-sf-derived-ses-triangle`: the existing node gives the degree-zero short-exact-sequence triangle; the new node handles an arbitrary finite filtration and cohomology in every degree.
- `lem-weil-pbc-etale-lisse-filtration-devissage` vs `lem-weil-proetale-dbc-triangulated`: the existing node gives a bounded constructible triangulated subcategory for pro-etale complexes; the new node is the etale finite-filtration lemma for a chosen derived functor and weak-Serre class, without boundedness.

- `lem-weil-pbc-etale-lisse-filtration-devissage` vs `lem-weil-pbc-etale-lisse-open-relative-line-constructibility`: the item proves constructibility for compactly supported images of lisse sheaves on an open relative affine line; the new node is the abstract finite-filtration induction for any triangulated functor and any weak-Serre class. It supplies only the filtration argument, not the geometry, cover, trace retraction or constant-coefficient theorem.

## What was wrong or incomplete

The returned delivery identified the former step 4 as a 2,226-character non-elementary step hiding several lemmas. I retained the item statement, Lean record, source route, and all other steps, and replaced that step with five steps (new steps 4--8), each below 830 characters. The first now cites the exactness and triangulated-derived-direct-image statements; the second isolates the geometry and constant-coefficient theorem; the third cites the new finite-filtration devissage node and the existing constructible Serre theorem; the fourth cites the existing finite disjoint-open biproduct and shriek composition statements; and the fifth gives the retract kernel argument explicitly. The former final induction step is now step 9 and says that the one-open case is steps 4--8.

I also repaired the stale `thm-nagata-compactification` citation quotes by copying its current statement verbatim into `citations.json`. The item still uses the Nagata theorem only for auxiliary compactifications, as in the source route. The new node was searched in the whole DAG and blueprint (`tools/blueprint_refs.py search filtration`, `search 0GKY`, and keyword searches); no existing node or blueprint node states it. Required LeanSearch, Loogle and Mathlib grep searches were run for the new node and recorded in its `mathlib_searches`; LeanSearch and grep returned only general filtration/triangulated APIs, while Loogle returned no exact match.

## Review by Q60

I reread the item against Stacks `more-etale.tex`, Tag 0GKY (`lemma-loc-constant-shriek-rel-dim-1`), and the preceding Tag 0GKX constant-coefficient lemma. The hypotheses remain a finite commutative coefficient ring, affine finite-type integer base, open in the relative affine line, finite locally constant sheaf, chosen compactification, and every cohomological degree. I checked the new node against the finite-filtration reduction in the final paragraph of Tag 0GKY and the weak-Serre/derived argument of Tag 06UQ (`derived.tex`, `lemma-cohomology-in-serre-subcategory`); it introduces all categories, the filtration, quotient objects, bounded-below derived functor, and edge cases `r=0` and zero quotients.

For steps 1--3 I reopened every cited node. Step 1 uses finite-type-over-Noetherian, affine Noetherianity, affine-line smoothness, smooth-dimension permanence, and the smooth definition exactly as their statements say. Step 2 is the elementary primary-idempotent decomposition, including the zero-ring case. Step 3 uses the finite-etale filtration, trace-degree retraction, finite direct-image exactness, finite properness, compactification, shriek composition/independence, and direct-image definitions; the finiteness and quasi-compact/separated hypotheses are checked in the text.

For repaired steps 4--8, I checked each cited statement word for word. Step 4 uses exact extension by zero, exact-functor derived triangulation, left exact direct image, enough injectives, and the derived direct-image triangulation theorem to establish that the chosen shriek is triangulated. Step 5 uses the finite-etale filtration statement, affine-morphism permanence, smooth-relative-dimension permanence, Nagata compactification, and the constant-coefficient relative-line theorem; the component morphisms are affine, separated, finite type, and smooth of relative dimension one under the stated hypotheses. Step 6 uses the new finite-filtration node and `thm-constructible-serre`; its quotient hypotheses are supplied by step 5. Step 7 uses the existing finite disjoint-open extension biproduct, compactification definition, exact extension by zero, shriek composition, and Serre closure to identify the finite direct sum of component images. Step 8 checks the retract by writing the image as `ker(1-e)` for the splitting idempotent and invokes kernel closure; it then handles the finite primary sum by repeated extensions. Step 9 is the original finite-principal-cover Mayer--Vietoris induction and uses only its existing triangle, Serre closure, long exact cohomology, and Nagata statements.

I tested the edge cases mentioned in the proof: empty principal opens, the zero sheaf, an empty filtration, a single component, and a one-open cover. The only new node is strictly smaller than the item and has no proof body, as required for an unsplit statement node. No statement or Lean field was changed.
