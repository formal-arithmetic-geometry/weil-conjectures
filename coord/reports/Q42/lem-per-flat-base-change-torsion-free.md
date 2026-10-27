## Worker report

Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-flat-base-change-torsion-free.json`: item, split into five steps using existing nodes; no direct Mathlib match.
- `citations.json`: ten verbatim statement quotations, one for each step/node citation.
- `report.md`: this report. `searches.jsonl` is the search command's unmodified log.

New nodes: 0. New Mathlib leaves: 0. The existing graph already supplies every ingredient.

Attachments: none. Searches in `lean/WeilConjectures/` by the exact blueprint tag and by torsion-free/base-change terminology found no declaration giving the item's entire statement. The source's torsion-free results concern specialized modules or different scalar rings.

WANTED: none.

The imported item was a correct statement-only Tag 0AXM node. I retained its mathematical statement, source, provenance, blueprint ancestry and inherited Q31 searches, added the existing tensor-product definition as a statement dependency, and supplied the missing proof. No statement dispute or source error was found. No Lean was written or compiled.

The proof uses the module localization V = (R minus zero)^(-1)N directly, rather than needing a separate tensor/localization comparison. Its R-flatness follows from localization flatness, field-module flatness and transitivity. This is the flatness formulation of the vector-space basis/direct-sum argument in the Stacks proof. The tensor target S tensor_R V is S-flat and hence S-torsion-free. This does not assert that N itself is flat over an arbitrary domain.

Nothing remains unfinished in this one-level split. The existing nodes used are Mathlib leaves, so no off-unit tool declaration or unit realization change is needed.

## Sources and searches

I read `literature/stacks-project/more-algebra.tex`, Tag 0AXM, label `lemma-flat-pullback-torsion`, statement and entire proof (lines 4824–4837), and checked the tag mapping. I also read the module localization fraction construction preceding Tag 07JZ (`definition-localization-module`), and Tags 00HT (`lemma-flat-localization`) and 00HI (`lemma-flat-base-change`) in `algebra.tex`. The existing transitivity leaf identifies `Module.Flat.trans`; I read its actual scalar-tower hypotheses and the source of `Module.Flat.baseChange` in `Mathlib/RingTheory/Flat/Stability.lean`. I read the flat tensor injection declaration and the flat-module regular-scalar/torsion result in Mathlib as well.

I read the chapter and unit records and their current blueprint texts under `literature/blueprint/latest/`, and the latest ancestor proof `lem-per-artin-gabber-affine-curve.proof.md`, especially Step 3. This is an existing historical regular-pair helper under that ancestry, not a replacement for the unit's perverse Fourier argument.

Before considering new nodes, I searched the whole DAG by torsion-free, fraction-field, localization, flatness and tensor terminology, and ran `tools/blueprint_refs.py ancestor` and blueprint searches for `torsion free`, `torsion-free`, `fraction field`, `module localization` and `flat extension`. No blueprint node states the item. The two flat-extension blueprint hits are a finite duality statement and a sheaf derived-scalar statement, not this arbitrary-domain module assertion. I reused all needed generic lemmas rather than creating duplicates.

For the item, I ran the required command with LeanFinder, Loogle, LeanSearch and grep, and a second LeanFinder phrasing. Exact query texts and returned summaries are appended in `mathlib_searches` and preserved by the command in `searches.jsonl`. I read the actual `IsSMulRegular.lTensor`, `.rTensor` and `.of_flat_of_isBaseChange` declarations: their regular scalars come from R. They do not supply arbitrary nonzero b in S. `Module.Flat.baseChange` has the stronger hypothesis that the original module is flat. The Bezout/Dedekind torsion-free-flat criteria add ring hypotheses, and the localization torsion-free result assumes a localization algebra. Thus none is an exact match or one-line specialization for this item. The earlier Q31 searches were retained, with their recorded results, and are consistent with these checks.

## Not duplicates

No new nodes were created, so there are no new/existing same-tag pairs. In particular, I reused `lem-trf-flat-tensor-preserves-injection`, `lem-trf-flat-module-torsionfree-domain`, `lem-pc-module-flat-transitive`, `lem-weil-pbc-flat-module-base-change`, `lem-weil-pbc-localization-flat` and `lem-weil-pbc-module-over-field-flat` instead of creating renamed special cases.

## Review by Q42

I reviewed the files against delivery-errors B through E with the cited node statements and Stacks source open. There are no new statement-only nodes to audit, no helper restating the item, and no proof hidden in a new statement. The item keeps all its hypotheses and conclusion. Every step is under 600 characters, so no step crosses the 2000-character long-step threshold.

Step 1 uses `def-weil-pbc-module-localization`, whose statement explicitly supplies the localized-ring module action and the criterion m/1 = 0 iff a denominator kills m. The proof uses that criterion, not an unstated theorem about a definition. R being a domain makes the nonzero elements multiplicatively closed, makes a/t nonzero exactly when a is nonzero, and gives the displayed inverse t/a. The given torsion-freeness of N then makes the localization map injective. These are written-out elementary consequences; no finiteness is used.

Step 2 uses exactly the statements of `lem-weil-pbc-localization-flat`, `lem-weil-pbc-module-over-field-flat` and `lem-pc-module-flat-transitive`. The first applies to the actual fraction localization K. The second allows arbitrary-dimensional vector spaces, so applies to V even when N is not finitely generated. The third takes the compatible restricted R-action and K-action constructed in Step 1, with flatness of K over R and V over K, and concludes only that V is R-flat.

Step 3 reads the flat ring map definition to get that S is R-flat, and applies `lem-trf-flat-tensor-preserves-injection` with its module M equal to S, its N and P equal to N and V, and its map equal to the injection already proved. The cited statement therefore really supplies the exact injection required. Its S-linearity is checked on pure tensors and extended by their generation, explicitly supplied by the tensor-product definition. No tensor-exactness theorem is inferred merely from a label.

Step 4 uses `lem-weil-pbc-flat-module-base-change` on the R-flat module V, not on N, and gets flatness over S with precisely the first-factor S-action. `lem-trf-flat-module-torsionfree-domain` then applies because S, not just R, is a domain. Its statement supplies injectivity for every nonzero scalar in S; it is not limited to the image of R. These hypotheses and the action convention are the key checks.

Step 5 uses only the tensor universal property and generation stated in `def-weil-pbc-module-tensor-product`. Both symmetry maps and their inverse composites are specified on pure tensors. The displayed S-linearity formula changes the item's second-factor action into the first-factor action used by Steps 3 and 4. The proof then writes out the equation b J tau(z) = J tau(bz) = 0 and both injectivity deductions. This proves the full conclusion without hiding a comparison lemma.

I tested N = 0, infinite free N, non-finitely-generated N (including a fraction field as a module), R = S, and a localization R to S. Zero-dimensional V causes no basis-choice exception because field-module flatness includes the zero module. I also checked a torsion-free but nonflat module over a general domain: the argument only requires its localization V to be flat, so it does not introduce an erroneous torsion-free-implies-flat assertion. The proof needs no injectivity or faithful-flatness assumption on R to S and never cancels an image of an R-scalar inside S. With S a field the same argument applies. Dropping the S-domain assumption would invalidate the regular-scalar step, and it is not dropped.

The only correction to the initially empty split was to expose this complete argument and the tensor-product dependency. All cited statements were read in full; `citations.json` records literal substrings without adjusting their wording. The source is Stacks throughout, with no SGA route. I sign this review as Q42.
