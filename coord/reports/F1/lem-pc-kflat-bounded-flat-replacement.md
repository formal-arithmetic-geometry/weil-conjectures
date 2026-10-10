1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-kflat-bounded-flat-replacement.json` — repaired cycle construction, kernel argument, dependencies, and blueprint split report.
- `dag/nodes/sec-picard-framework/lem-pc-sites-modules-quotient-j-shriek.json` — statement-only Stacks 03EW input; Mathlib no match.
- `dag/nodes/sec-picard-framework/lem-pc-sites-modules-j-shriek-flat.json` — statement-only Stacks 03EV input; Mathlib no match.
- `dag/nodes/sec-picard-framework/lem-pc-sites-modules-coproduct-flat.json` — statement-only Stacks 03EU input; Mathlib no sheaf-level match.
- `citations.json` — verbatim statement quotes for all step citations.

2. Attachments: none.

3. WANTED: `literature/stacks-project/sites-modules.tex`, Lemmas 03EU, 03EV, and 03EW, for the three new statement-only inputs (the repository contains their tag references but not the TeX source).

4. The returned version incorrectly formed $P^i=\\mathcal F^i\\times_{\\mathcal F^{i+1}}\\mathcal E^{i+1}$: its image need not be a cycle, so the displayed maps need not compose to zero. I repaired this to $P^i=\\mathcal F^i\\times_{\\mathcal F^{i+1}}Z(\\mathcal E^{i+1})$, and the kernel step now proves surjectivity onto $Z(\\mathcal K^{i+1})$ by lifting $(0,\\kappa)$. The old fixed-monoidal-category separator nodes were not valid citations for sheaves of modules over a sheaf of rings, so I added the ringed-site 03EW/03EV/03EU statements and cited them. The direct-sum flatness fact is now explicitly cited. The functoriality step no longer mentions unsupported free sheafification. The specialized `lem-kun-bounded-flat-replacement` remains only in `same_as`; it is not a dependency.

5. What I could not finish: the new Stacks inputs are intentionally unsplit statement-only nodes; no project Lean declaration proves this general ringed-site theorem.

## Not duplicates

`lem-pc-sites-modules-quotient-j-shriek` vs `lem-weil-pbc-sheaf-flat-separator`: the new statement is specifically about quotients of sheaves of modules by $j_{U!}\\mathcal O_U$ on a ringed site, while the existing node concerns a flat separator in a general sheaf category and does not state the quotient theorem.

`lem-pc-sites-modules-j-shriek-flat` vs `lem-weil-pbc-free-sheaf-flat`: the new statement is for $\\operatorname{Mod}(\\mathcal O)$ and extension-by-zero unit modules; the existing node is an A-valued sheaf generalization with a different flatness setup and does not state the ringed-site module theorem.

`lem-pc-sites-modules-coproduct-flat` vs `lem-weil-pbc-flat-coproduct`: the new statement concerns coproducts in sheaves of modules over a sheaf of rings; the existing node concerns an abstract Grothendieck monoidal category and is not the ringed-site statement required by the returned C4/C1 checks.

`lem-pc-sites-modules-j-shriek-flat` vs `lem-weil-pbc-sheaf-flat-separator`: the existing statement is a general flat-separator existence theorem for A-valued sheaves and does not assert flatness of a particular $j_{U!}\\mathcal O_U$ in Mod(O).

`lem-pc-sites-modules-j-shriek-flat` vs `lem-weil-pbc-free-yoneda-presheaf-module`: the existing statement is the Hom universal property of the presheaf free Yoneda module, with no flatness conclusion and no sheafification.

`lem-pc-sites-modules-quotient-j-shriek` vs `lem-weil-pbc-separating-family-epi-coproduct`: the existing categorical statement gives an epimorphism from a coproduct of all maps from a separating family, while the new statement identifies the concrete j-shriek generators for Mod(O) on a ringed site.

`lem-pc-sites-modules-quotient-j-shriek` vs `lem-weil-pbc-sheaf-free-separator`: the existing statement gives a separator and a Hom identification for A-valued sheaves; it does not state that every O-module sheaf is a quotient of j-shriek unit modules.

`lem-pc-sites-modules-quotient-j-shriek` vs `lem-weil-pbc-abelian-etale-sheaves-grothendieck`: the existing statement concerns Grothendieckness of abelian sheaves on a scheme's etale site and does not give the j-shriek quotient epimorphism.

`lem-pc-sites-modules-quotient-j-shriek` vs `lem-weil-pbc-constructible-generation`: the existing statement is restricted to finite coefficients on a quasi-compact quasi-separated scheme and uses constructible generators, not j-shriek O_U generators for an arbitrary ringed site.

`lem-pc-sites-modules-quotient-j-shriek` vs `lem-weil-pbc-module-sheaves-enough-injectives`: the existing statement asserts enough injectives for constant-ring etale module sheaves, not a quotient presentation by j-shriek unit modules.

`lem-pc-sites-modules-quotient-j-shriek` vs `lem-weil-pbc-module-sheaves-grothendieck-abelian`: the existing statement is the Grothendieck property and a generator for constant coefficients on a scheme etale site; the new statement is the general sheaf-of-rings quotient presentation required here.

## Second reading by F1

- Item statement: checked against Stacks Lemma 21.17.11 (Tag 06YS) and the bounded-above construction extracted from its proof; the bounded hypothesis, termwise epimorphism, quasi-isomorphism, and common-bound functoriality are coherent, including the zero complex and complexes concentrated in one degree.
- Step 1: checked against Tags 03EW, 03EV, and 03EU (Lemmas 18.28.8, 18.28.7, and 18.28.5) and the flatness/quasi-isomorphism definitions; the cycle pullback and epimorphism argument are valid. Repaired the generator choice by explicitly indexing summands by $(U,s)$ and describing its action on maps.
- Step 2: checked by the kernel calculation in the abelian category and the definition of quasi-isomorphism; the pair $(0,\\kappa)$ lies in the repaired pullback and gives surjectivity onto cycles, including the top degree.
- Step 3: checked against the same canonical generator construction and pullback universal property; the induced maps now explicitly commute with differentials and augmentations instead of asserting functoriality.
- New node `lem-pc-sites-modules-quotient-j-shriek`: checked against Tag 03EW clause (3); self-contained ringed-site hypotheses and quotient conclusion, no Mathlib match.
- New node `lem-pc-sites-modules-j-shriek-flat`: checked against Tag 03EV clause (2); self-contained and exact flatness conclusion, no Mathlib match.
- New node `lem-pc-sites-modules-coproduct-flat`: checked against Tag 03EU clause (2); self-contained direct-sum flatness conclusion, no Mathlib sheaf-level match.

Changes: corrected all three source places to the exact Stacks lemma labels; expanded Steps 1 and 3 to make the canonical generator indexing and functorial maps explicit. The three statement-only nodes remain necessary because no existing node states these ringed-site module facts.

## Review by F1

I reread the item against Stacks Tag 06YS and the construction route referenced by its source. The first step now uses the cycle pullback required by the return: $Z(\\mathcal E^{i+1})$ maps to $\\mathcal F^{i+1}$, so the induced differential lands in cycles and its composite with the next differential is zero. The three new source statements were checked against the cited sites-modules Lemmas 03EW (generator epimorphism), 03EV (flatness of $j_{U!}\\mathcal O_U$), and 03EU (coproducts of flat module sheaves); each statement introduces the site, ring sheaf, module category, and relevant object. Their Mathlib searches were run with LeanFinder, Loogle, and grep and recorded as no exact sheaf-level match.

For step 1, the cited nodes say exactly that the generator coproduct epimorphism exists, each generator is flat, coproducts of flat module sheaves are flat, and flatness is exactness of tensoring. For step 2, the cited quasi-isomorphism definition says that an isomorphism on every cohomology sheaf is the required conclusion; the new lift argument explicitly targets cycles. Step 3 uses only the functoriality of the already displayed coproduct, cycle pullback, and induced maps, and no longer invokes free sheafification. I checked the zero complex and a complex concentrated in degree $N$; the cycle pullback gives zero terms outside the bound and the expected single flat epimorphism in the concentrated case. The old invalid citations and the unsupported wording identified by the return were removed.

The ancestor blueprint is `def-weil-derived-tensor`; the item realizes its bounded-above flat replacement paragraph, and each new statement is linked to that paragraph through the repaired item. The existing specialized bounded-flat replacement was searched and retained only as `same_as`, since its hypotheses and module category differ.
