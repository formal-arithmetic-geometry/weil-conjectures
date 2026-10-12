## What changed
Completed the gluing theorem by extracting the localized Mayer–Vietoris diagram, applying a named five-lemma bijectivity intermediate theorem, and packaging the middle comparison as an additive equivalence.

## Proved and sorry left
The target `cohomologyFractionPresentation_gluing` is proved. The intermediate theorem `localized_middle_comparison_bijective` remains `sorry` and records the five-lemma chase.

## No longer needed
The former private fraction extensionality work and no additional bridge lemmas are needed.

## Where the brief, the DAG or earlier work was wrong
The earlier attempt stopped at the parenthesized-open transport. This delivery isolates that transport and five-lemma step as a strictly smaller named intermediate theorem.

## New nodes
`lem-sc-invert-s-cohomology-gluing-aux` / `Sheaf.AlgebraicGeometry.CohomologySectionLocalizationGluingAux`.

## Second reading by P3

1. Compared the delivered gluing module with the repository version; the theorem signature and all existing declarations are unchanged. Verdict: pass.
2. Compiled both modules with `lcompile.py --all`; no errors or forbidden declarations were found. The only remaining `sorry` is the named auxiliary theorem `localized_middle_comparison_bijective`, with its split node.
3. Checked the split statement against the Mayer–Vietoris five-lemma step. It is a true, strictly smaller intermediate claim and its node and docstring identify the source and argument. Verdict: pass.
4. The proof follows the diagram extraction, middle bijectivity, and additive-equivalence packaging route; the unit route is retained. No shorter available declaration was found.
5. DAG proof/proof_deps agree with the Lean imports and calls; the auxiliary node records the split theorem and its dependency. Verdict: pass.

Changed only the proof body and added the auxiliary split module/node plus this review section; no statement or definition was changed.
