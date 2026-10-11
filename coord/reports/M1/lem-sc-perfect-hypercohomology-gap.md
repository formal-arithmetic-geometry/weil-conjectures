1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-perfect-hypercohomology-gap.json`: statement node, split; Mathlib searches found no exact scheme-level declaration.

2. Attachments: none.

3. WANTED: none.

4. The item is not already present in `WeilConjectures/`; the keyword and blueprint-tag searches found no declaration carrying this result. I searched the DAG for the Stacks Tag 09M4, Tor-amplitude, and hypercohomology terms. The existing node `lem-sc-perfect-ext-bounded-qcoh-vanishing` uses this item and confirms the intended interval arithmetic. I did not create a child node because such a child would merely restate the item's conclusion.

## Review by M1

I read `literature/stacks-project/perfect.tex`, Tag 09M4, including the paragraph beginning “Say K^\\vee has tor amplitude in [a,b]”, and compared its hypotheses with the item: a scheme, a perfect complex with a finite Tor-amplitude interval, a complex with quasi-coherent cohomology, and an arbitrary integer degree. I also read the statements of `def-pc-perfect-complex` and `thm-sp-double-complex-spectral-sequences`. Step 1 uses the local bounded finite-projective model stated by the perfect-complex definition and the existing theorem's filtered double-complex spectral sequence. Step 2 uses exactly the existing theorem's finite convergence filtration and associated-graded identification; the Tor-amplitude interval supplies the displayed range of possible cohomology degrees. Step 3 is the elementary finite-filtration argument and locality of cohomology-sheaf vanishing. I checked the edge cases u=v and L=0. The recorded searches were run with `msearch.py`: LeanFinder returned only generic derived-category bounds, Loogle returned zero hits, and the Mathlib grep returned zero hits; the blueprint ancestor is `lem-sc-finite-duality`, with no same-as match.

5. What I could not finish: no Lean implementation was requested or permitted at this stage.

## Second reading by M1

- Statement: checked against Stacks Tag 09M4, including the Tor-amplitude interval and translated gap; tested zero L, u=v, and boundary degrees.
- Step 1: checked the affine perfect model against `def-pc-perfect-complex`; corrected the first-quadrant spectral-sequence citation to the bounded filtered-complex theorem `thm-sp-spectral-object-yields` and made the E1/E2 passage explicit.
- Step 2: checked interval arithmetic and finite-filtration convergence against `thm-sp-spectral-object-yields`.
- Step 3: checked the zero associated-graded filtration argument and locality; edge cases are covered.
- New nodes: none; existing spectral-sequence nodes were searched and no duplicate child was needed.
- Changes: corrected the theorem citation, expanded Step 1, and synchronized the citation records.
