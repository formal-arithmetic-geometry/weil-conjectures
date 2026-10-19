1. Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-punctual-strict-completion-test.json` — split item, no Mathlib leaf.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-henselian-completion-open-rigidity.json` — new statement-only node, no Mathlib leaf.
- `citations.json` — verbatim statement quotes for every proof-step citation.

2. Attachments: none. No sorry-free declaration in `WeilConjectures/` states this item exactly; the source search for the item tag and its strict-completion terminology returned no declaration.

3. WANTED: Fujiwara 1995, Corollary 6.6.4, for `lem-per-henselian-completion-open-rigidity` (the cited ILO volume states the Noetherian case and gives the completion-comparison formulation in Exposé XX §4.4; the original Fujiwara paper is not present in `literature/`).

4. No statement error was found. ILO Exposé XVI Definition 3.2.1 and Proposition 3.2.4 state precisely the strict-henselian completion equivalence and do not impose excellence. The existing completion-comparison node was not reused for the new input because it assumes excellence, whereas this item explicitly forbids it. I created one genuinely smaller statement-only node for the general henselian-pair open-complement comparison instead of moving the item's conclusion into a new node. The node and item were checked for duplicate tags and keywords across the whole DAG; the closest existing completion comparison has an excellence hypothesis and a different supported-constant statement.

## Not duplicates

- `lem-per-henselian-completion-open-rigidity` vs `lem-per-completion-supported-constant-comparison`: the new node compares all torsion sheaves on the open complement of an arbitrary Noetherian henselian pair with its completion and has no excellence hypothesis; the existing node compares only constant twists and assumes an excellent henselian local ring.
- `lem-per-henselian-completion-open-rigidity` vs `lem-per-punctual-strict-completion-test`: the new node is the open-complement cohomology input; the item is the punctual Kummer-class equivalence for a regular local ring and its strict-henselized completion.

5. What I could not finish: no Lean code was written or compiled, as required for stage 1. The new rigidity node remains unsplit and is queued for a later worker.

## Review by Q40

I read the item against Illusie–Laszlo–Orgogozo, Exposé XVI Definition 3.2.1 and Proposition 3.2.4 (printed p.244), and read Exposé XX §4.4 (printed pp.373–374) for the completion comparison. I also read the source statements of every dependency cited in each step. The new node follows the CTC assertion in XX §4.4: a Noetherian henselian pair, its adic completion, the open complements, and the canonical pullback on torsion étale cohomology are all introduced explicitly. Its searches were run with LeanFinder, LeanSearch, Loogle, and Mathlib grep; the returned signatures concern adic completion algebra, local cohomology, and étale ring maps, so none is a Mathlib statement of this cohomological rigidity result.

Step 1 uses the strict-henselization triples statement for the residue field and maximal ideal, the three Stacks strict-henselization results for Noetherianity, regularity, and dimension, the existing completion Noetherian/local/dimension/regularity statements, module completion completeness, and complete-pair henselianity. I opened each statement and checked that its hypotheses apply to the Noetherian regular local ring and that the residue field is the selected separable closure. The assertion that the maximal ideal powers remain the completion powers is the module-completion statement specialized to the ring.

Step 2 uses the existing affine ind-étale closed-support base-change statement, the canonical pullback of finite Tate twists, the regular-immersion class calculus (including strict-local and flat-base-change compatibility), and the étale sheaf/Galois-set equivalence over a field. These statements give the actual Kummer class after strict henselization and show that pullback to the separable closure is exact and reflects isomorphisms. The common codimension is the dimension equality from Step 1.

Step 3 uses the strict-henselian closed-stalk section theorem, exactness of geometric stalks, the field-point Galois equivalence, enough injectives and bounded-below injective representatives, the supported-kernel adjunction, the right-derived-functor computation, and the definition of derived supported sections. I checked that the support kernel is identified term by term with the closed exceptional restriction and that the resulting global-sections calculation is normalized by the actual support inclusion. This step is non-elementary and is marked accordingly.

Step 4 applies the new open-complement rigidity node to the torsion Tate-twist sheaf, uses the twist pullback identification, and places the ambient and punctured cohomology comparisons in the two localization triangles. Exact global sections on strictly henselian schemes identify degree-zero ambient sections with the same residue-field stalk and kill positive ambient cohomology; the rigidity node supplies the punctured comparison in every nonnegative degree. I checked the five-term long exact sequence and the cited five lemma, including negative-degree vanishing.

Step 5 checks the completion map's faithful flatness and the common closed fibre, then uses the class calculus's stated flat-base-change compatibility to compare the specified Kummer maps themselves. The source and target supported cohomology maps are the maps induced by those classes, via Step 3, so the isomorphism from Step 4 transfers the isomorphism property in both directions. I checked the zero-dimensional edge case separately: both immersions are identities, the class is the identity, and the punctured spectra are empty. No excellence hypothesis or regularity of the completion morphism was introduced.
