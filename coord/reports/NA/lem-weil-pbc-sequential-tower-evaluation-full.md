## New nodes

None. The split reuses existing DAG nodes; no Mathlib leaves or new statement nodes were needed.

## Attachments

None. I found no sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `/home/ubuntu/weil-newtargets-master/WeilConjectures` carrying this exact target statement.

## WANTED

None. The prerequisites are documented by Stacks Tags 079P, 070I, 05RU and 02MZ, all available in `literature/stacks-project/`.

## What was wrong in the imported split

The imported item had no proof steps although its statement is a genuine generic lifting assertion. The reconstruction ancestor's prose correctly warned that Tag 091I lifts objects only; I did not cite it as a morphism theorem. I kept the statement unchanged and wrote the missing strictification argument. The proof uses existing `lem-weil-pbc-small-module-diagrams-grothendieck`, `lem-pur-kinjective-degreewise-existence`, `lem-weil-tower-category-levelwise-abelian`, `lem-weil-tower-evaluation-kinjective`, `lem-weil-pbc-kinjective-hom-derived`, `def-sp-injective-resolutions`, and `def-weil-abstract-derived-category`.

## Review by NA

I read the target node and its ancestor proof in `dag/nodes/sec-proper-base-change/` and `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/lem-weil-pbc-reconstruction-uniform-tower.md`. I read Stacks `injectives.tex` at Tag 079P and `derived.tex` at Tag 070I, and `homology.tex` at Tag 02MZ; these provide Grothendieck K-injective resolutions, the homotopy/derived Hom bijection, and levelwise exactness of inverse systems. I also read the complete statements of every cited node. Step 1 uses the small-module-diagram Grothendieck statement, the K-injective-resolution-with-injective-terms statement, levelwise tower abelianity, and the derived-category localization statement exactly as quoted in `citations.json`; the hypotheses are a small site and the stated small positive-index tower. Step 2 uses the definition of injective objects and levelwise kernels/monomorphisms to extend a staircase map, yielding degreewise sections of each transition; this is an elementary extension argument and makes no unsupported claim that sections commute with differentials. Step 3 uses exactly the existing evaluation-K-injective and Hom-to-derived-Hom statements, so the adjacent defect is null-homotopic. Step 4 spells out the degreewise lift and the signs in the correction, checks that the correction is a chain map and that applying the transition recovers the defect, and performs the induction over positive integers. Step 5 uses only localization and the derived statement to assemble the strict tower map and records why no tower homotopy is needed. Step 6 uses levelwise cohomology and the definition of quasi-isomorphism to prove that any lift whose evaluations are isomorphisms is itself invertible. I checked zero, constant, one-stage and finite towers conceptually; the induction has base index 1 and no limit-stage step. I ran LeanFinder, Loogle, LeanSearch and Mathlib grep through `msearch.py`; LeanSearch was unavailable, while the available hits were inspected and had no matching simultaneous evaluation-fullness theorem. No statement or definition was changed, and no new node was created.

## Not duplicates

lem-weil-pbc-sequential-tower-evaluation-full vs lem-weil-tower-evaluation-kinjective: the existing node states only that evaluation preserves K-injectivity for one target complex; this item lifts a compatible family of morphisms at all evaluations to one strict tower morphism.
lem-weil-pbc-sequential-tower-evaluation-full vs lem-weil-pbc-kinjective-hom-derived: the existing node computes maps into one K-injective complex in one derived category; this item simultaneously strictifies maps between two inverse towers.
lem-weil-pbc-sequential-tower-evaluation-full vs lem-weil-tower-category-levelwise-abelian: the existing node gives abelian and exact levelwise structure; this item is the derived morphism-lifting conclusion that uses that structure.

## Second reading by NA

I checked the target statement clause by clause against the reconstruction ancestor and the definitions cited in its `stmt_deps`: the site, sheaf of rings, module category, strict inverse-tower category, derived evaluations, transition maps, compatibility equation, existence clause, and isomorphism clause all have the required hypotheses and objects. The empty, zero, constant, one-stage, and finite-tower cases are consistent; the induction starts at index 1 and has no limit stage.

I checked step 1 against `def-weil-abstract-derived-category`, `lem-weil-pbc-small-module-diagrams-grothendieck`, `lem-pur-kinjective-degreewise-existence`, and `lem-weil-tower-category-levelwise-abelian`; the localization representatives, Grothendieck hypothesis, resolution, and exact evaluations are exactly what those statements provide. Verdict: pass.

I checked step 2 against `def-sp-injective-resolutions` and `lem-weil-tower-category-levelwise-abelian`; the finite staircase inclusion is levelwise monic, injectivity gives the extension, and naturality gives the section equation. Verdict: pass; the text explicitly says these are graded sections and assumes no differential compatibility.

I checked step 3 against `lem-weil-tower-evaluation-kinjective` and `lem-weil-pbc-kinjective-hom-derived`; reindexing positive integers is harmless and bijectivity gives an actual homotopy class, hence a null-homotopic defect. Verdict: pass.

I checked step 4 against the Hom-to-derived-Hom bijection and the displayed cochain equations. The correction has the stated sign, is a chain map by $d^2=0$, remains homotopic to the original map, and its transition is the prescribed previous map. Verdict: pass.

I checked step 5 against `def-weil-abstract-derived-category`; adjacent commutation composes to all transitions, and localization gives the asserted derived morphism and evaluations. Verdict: pass; no tower homotopy or uniqueness is silently used.

I checked step 6 against `lem-weil-pbc-kinjective-hom-derived`, `lem-weil-tower-category-levelwise-abelian`, and `def-weil-abstract-derived-category`; levelwise cohomology and natural component inverses imply a quasi-isomorphism, which localization inverts. Verdict: pass.

There are no new statement nodes to audit and no duplicate or Mathlib leaf to remove. I checked every citation quote against the current cited node statement and found them verbatim and sufficient. I changed no node, citation, search record, or proof step; this second-reading section is the only change.
