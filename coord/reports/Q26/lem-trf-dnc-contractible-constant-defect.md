# Worker report

1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-dnc-contractible-constant-defect.json` — split statement node; its six proof steps follow Varshavsky's contraction argument.
- `dag/nodes/sec-trace-formula/lem-trf-constant-complex-a1-morphism-rigidity.json` — new unsplit statement node; Mathlib searches found no match.
- `citations.json` — verbatim statement excerpts for every proof-step citation.

2. Attachments: none.

3. WANTED: none; the cited Varshavsky PDF and all cited DAG statements are available in the project.

4. What was wrong or changed: the retained new rigidity node had an incorrect `created.item` value from an earlier worker; I corrected it to this delivered item. I retained the imported statement and expanded proof, which explicitly handles the nonreduced centre, the two inverse equations, reduction to the reduced origin, and the affine-line parameter-rigidity input. No statement dispute was found.

5. What could not be finished: the new rigidity lemma remains an unsplit non-Mathlib statement node, as required for a one-level stage-1 split.

## Review by Q26

I read the item against Varshavsky, *Lefschetz–Verdier trace formula*, the text around Example 3.1.2 and Lemmas 3.1.3–3.1.4 (the local copy is `varsh.txt`, and the cited PDF is in `literature/`). The item fixes the finite coefficient ring, affine line, thickened origin, Rees specialization and constant sheaf exactly as the source's constant-sheaf clause. Its proof realizes the source's contraction argument: Step 1 uses the functorial Rees-lift statement and the affine-space smoothness statement for the lifted projection; Step 2 uses the defect comparison's canonical map, the deformation-specialization definition, nearby-cycle finiteness/exchange, and constructible pullback to establish the first inverse equation and finiteness; Step 3 uses constructible pullback, the definition of universal homeomorphism, and the etale-topos invariance theorem to justify reduction to the reduced origin and reflection of isomorphisms; Step 4 uses the specialization exchanges and their composition/unit laws to form the affine-line family of endomorphisms; Step 5 uses the same exchange laws and the functorial Rees geometry to identify the endpoint maps with the canonical maps; Step 6 applies the new rigidity statement and the comparison node to obtain both inverse equations and hence the desired isomorphism.

I opened each cited node and checked that the quoted sentence in `citations.json` is verbatim and supplies the exact fact used by its step. The hypotheses were checked at the points where they are used: the Rees maps satisfy the ideal-containment condition; the projection is affine-line smooth; all complexes remain bounded constructible; the nilpotent reduction is a universal homeomorphism; and the coefficient torsion is prime to the characteristic. I tested the geometric edge cases in the argument (r=1) (reduced origin) and (r>1) (nilpotent thickening), and the endpoint parameters (a=0,1). The Mathlib searches recorded in `searches.jsonl` were run for the item and new rigidity node with LeanSearch, LeanFinder/Loogle and Mathlib grep; the returned declarations concern ordinary scheme or chain-complex operations and do not state this etale nearby-cycle result. The new node is therefore correctly marked `unsplit` with `mathlib_match: null`.
