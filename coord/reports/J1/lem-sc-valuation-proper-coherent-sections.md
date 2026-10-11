1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-valuation-proper-coherent-sections.json` — statement, split proof, and metadata; no Mathlib match.
- `dag/nodes/sec-abelian-varieties/lem-sc-valuation-proper-coherent-higher-direct-images.json` — new statement-only child; no Mathlib match.
- `citations.json` — verbatim dependency quotes for both item steps.

2. Attachments: none. No sorry-free declaration in `WeilConjectures/` states the item. The nearby `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_higherDirectImage` declaration has a locally Noetherian-base hypothesis and transitively rests on sorries, so it is not an attachment.

3. WANTED: none. The cited Stacks source is represented by the available project literature metadata; the stronger valuation-ring coherent-finiteness child remains an unsplit classical input.

4. What was wrong or incomplete in the imported item: the imported node had no proof and treated the degree-zero claim as a direct source input. The proof actually uses the stronger coherent higher-direct-image finiteness statement over a valuation ring, which is not the existing locally Noetherian `lem-pc-coherent-hi` result. I added that stronger statement as one child rather than duplicating the item. The invertible-module-to-finitely-presented reduction is elementary from the definition.

5. What I could not finish: the stronger valuation-ring coherent-finiteness theorem is not in Mathlib or the Lean source, so the new child is intentionally statement-only for a later worker.

## Not duplicates

lem-sc-valuation-proper-coherent-higher-direct-images vs lem-sc-valuation-proper-coherent-sections: the new node treats every finitely presented quasi-coherent module and every cohomological degree q, while the existing item treats only an invertible module and q=0.
lem-sc-valuation-proper-coherent-higher-direct-images vs lem-sc-valuation-zero-section-relative-cartier: the existing node concerns the zero scheme of a section and relative Cartier flatness, while the new node concerns finiteness of all cohomology modules.
lem-sc-valuation-proper-coherent-higher-direct-images vs lem-sc-picard-locus-closed-valuation-triviality: the existing node concludes triviality of an invertible sheaf from generic triviality, while the new node supplies the separate all-degree cohomological finiteness input.
lem-sc-valuation-proper-coherent-higher-direct-images vs lem-sc-valuation-closed-fibre-section-vanishing: the existing node descends vanishing of a section to a nonzero quotient A/(pi), while the new node asserts finite presentation of higher cohomology.
lem-sc-valuation-proper-coherent-higher-direct-images vs lem-sc-valuation-fp-torsionfree-free: the existing node proves finite freeness of a finitely presented torsion-free module over a valuation ring, while the new node proves finite presentation of cohomology before any torsion-free or freeness argument.

## Review by J1

I read the item source citation in `more-on-morphisms.tex` (Tag 0EX8) and the imported proof context in `lem-sc-picard-locus-closed-valuation-triviality.json`. Step 1 uses only the definition node `def-sc-invertible-module`; that node explicitly says an invertible module is quasi-coherent and locally free of rank one, which gives finite presentation on affine charts. Step 2 uses the new child, whose statement explicitly concludes finite presentation of `H^q(X,F)` for every q, so specializing q=0 gives exactly the item. The proper, flat, finite-presentation hypotheses and the valuation-ring hypothesis are unchanged in both statements. I checked existing valuation nodes and `lem-pc-coherent-hi`; the latter requires a locally Noetherian base and therefore cannot discharge this item. I also searched LeanFinder, Loogle, grep, and LeanSearch for the item and the new child; only generic finite-presentation morphism declarations appeared, with LeanSearch unavailable. The citation quotes are copied verbatim from the two cited node statements.

## Second reading by J1

- Item statement: checked against More on Morphisms, Lemma `lemma-triviality-generic-fibre-valuation-ring`, Tag 0EX8; verdict: hypotheses and degree-zero conclusion match.
- Item step 1: checked against `def-sc-invertible-module` and `def-amb-finite-locally-free-module`; verdict: rank-one local freeness supplies the child hypothesis.
- Item step 2: checked against the child statement; verdict: specializing `q=0` gives the exact conclusion.
- New node `lem-sc-valuation-proper-coherent-higher-direct-images`: checked against the coherent-cohomology paragraph in the Tag 0EX8 proof and small cases (rank zero, rank one, and a field base); verdict: valid stronger finite-locally-free formulation, with all notions cited.

Changes: replaced the child’s undefined “finitely presented quasi-coherent module” hypothesis with the existing finite-locally-free definition; cited that definition in the item step and citation log; added the module finite-presentation definition dependency for the child’s conclusion; documented this second reading.
