Files written: `dag/nodes/sec-picard-framework/lem-sc-ext-coherent-hom-injective-flasque.json`; no new nodes. Mathlib verdict: no match (LeanFinder, Loogle, grep; LeanSearch unavailable).

Attachments: none.

WANTED: none.

No statement or source error was found. The source is Cohomology Lemma 01EA in `cohomology.tex`; its proof uses extension by zero and injectivity to make restriction maps surjective. The existing module extension-by-zero node states the adjunction and stalk behavior needed here, and the existing stalk exactness node supplies the stalkwise monomorphism criterion. The split has four steps: identify Hom sections by the sheaf-Hom definition and extension-by-zero adjunction; prove the map between extensions by zero is a monomorphism stalkwise; apply the injective lifting definition to obtain surjectivity of restrictions; conclude flasqueness from its definition. I checked the hypotheses for nested opens and tested the edge cases `U'=U`, `U'=empty`, `F=0`, and a one-point scheme. The module extension node is declared as a generic tool because it supplies the ringed-space extension-by-zero interface used by the source route.

## Review by J1

I read Cohomology Lemma 01EA and the statements of every cited node. Step 1 uses exactly the global-sections clause of `def-pur-sheaf-hom` and the extension-by-zero adjunction. Step 2 uses the extension node's zero/identity stalk clauses and `lem-weil-pbc-module-stalk-exact` for stalkwise injectivity. Step 3 uses the injective-object definition and transports the resulting Hom surjection through the same adjunction identifications. Step 4 is the definition of a flasque abelian sheaf. The hypotheses are checked for arbitrary opens in the Zariski space; no coherence or Noetherian property is needed beyond the item's stated setting. I corrected the imported empty proof by writing these four source-aligned steps and replaced stale Mathlib search records with the actual search outputs from 2026-10-11.

What could not be finished: nothing.
