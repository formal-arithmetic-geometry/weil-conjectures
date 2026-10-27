# Stage-1 delivery: lem-per-normalized-blowup-tower-etale-descent

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-normalized-blowup-tower-etale-descent.json`: existing statement node, now split in ten steps; not a Mathlib leaf.
- `citations.json`: one verbatim statement excerpt for every step/node citation.
- `report.md`: this report.

New DAG nodes: 0. New Mathlib leaves: 0. No unit record changed: this is not the unit key statement. Sandbox-only `gabber.txt`, `cited-statements.txt`, and scripts are reading/writing aids, not library files.

## Attachments

None. Searches in live `lean/WeilConjectures/` for the exact blueprint tag, normalized blowup/tower spellings, and the notion found no project declaration stating this item. Existing general declarations cover individual ingredients only. No Lean file was written or compiled.

## WANTED

None. The ILO PDF and Stacks source files used are present.

## Corrections and source audit

The item had no proof. Its statement is retained verbatim; I added the definition dependencies already implicit in its prose, notably the componentwise normalization definition because `def-sc-normalization` alone concerns an integral scheme. No STATEMENT-DISPUTED correction was needed. I checked the latest blueprint ancestor proof, Step 3, the chapter and unit records, and the intervening absolute-Gabber parent split. This proves its general algebraic-geometric tool while retaining that route.

The ILO source citation in the imported node stopped at 2.2.4, but the effective descent proof is explicitly VIII 2.2.11, printed p.91; the step sources and proof origin now identify it. I read VIII 2.2.1--2.2.11, 3.4.8, and 5.5.3--5.5.5, printed pp.90--91,111,128--129. The proof is the source's descent of the ordered centers, supplemented by Stacks 02NS, 035P/035S, 07QU/07QV, 0B3I, and 0C4P for geometry and 023T for module descent. No prohibited SGA source is used.

## Not duplicates

No new nodes were created. Whole-DAG title/concept/tag searches and whole imported-blueprint searches (`normalized blowup`, `blowup tower`, `normalization smooth`, `07TD`, `quasi-excellent`, `descent`) found reusable inputs. In particular `lem-sfb-componentwise-normalization-smooth-pullback` already supplies the required absolute normalization comparison; creating another node for it would have been a duplicate. `lem-per-excellent-normalized-blowup-tower` assumes excellence and point centers and is not used for the quasi-excellent coherent-center argument. The existing relative-normalization smooth-base-change Mathlib leaf is not silently identified with absolute componentwise normalization.

## Mathlib searches

The inherited searches remain untouched, and the actual Q43 records from `searches.jsonl` were appended, with their literal query texts and log results. I ran LeanFinder in two phrasings (tower descent and absolute normalization comparison), LeanSearch, Loogle, and grep through the required msearch command. LeanFinder/LeanSearch returned relative-normalization declarations and algebra-level etale spreading, not this center-preserving tower theorem; Loogle and grep returned no blowup/tower match. I read the returned names and compared their object types with the item. All four services were available for these searches. This is not a new leaf, and no fabricated search was added.

## Review by Q43

I checked delivery-errors B--E against the node and the sources. Every cited node was opened and its statement read; `citations.json` copies the portions actually used (whole statements when multiple clauses or displayed formulas matter). The following records the mathematical hypothesis checks and corrections, rather than just mechanical gate results.

### Step 1: Geometry of the ordinary step

I read ILO VIII 2.2.1--2.2.5 and Stacks divisors.tex 02ND and 02NS. The finite-components statement and normal-component statement supply actual clopen integral components. The integral-blowup statement applies because nowhere dense centers give nonzero ideals on every component. I read both the Rees-presentation statement and Proj-functoriality statement: the former gives the graded surjection, the latter gives a closed immersion. The definition of the projective-bundle convention then supplies the claimed projectivity on the whole base; I did not substitute finite-projective-space projectivity.

Cited statements: `lem-weil-pbc-noetherian-finitely-many-components`, `lem-sfb-normal-locally-finite-components`, `lem-per-integral-blowup-projective-geometry`, `thm-nagata-blowup-flat-base-change`, `def-nagata-blowup-flat-base-change-map`, `lem-sfb-blowup-rees-symmetric-presentation`, `prop-nagata-relative-proj-functoriality`, `def-trf-projective-bundle-morphism`.

### Step 2: Finite normalization under quasi-excellence

I read Stacks 035S and its affine proof, and 07QU/07QV. The cited finite-type stability statement explicitly includes QUASI-excellent schemes; the older excellent-normalization preparation does not, so I did not cite it. The Nagata-ring definition gives the Japanese property for every prime quotient, and the Japanese definition includes the trivial finite fraction-field extension. The affine normalization statement supplies the finite product of exactly those integral closures. Thus this step is an explicit elementary affine finiteness argument, not an appeal to a normalization theorem with a missing excellence hypothesis.

Cited statements: `lem-trf-projective-bundle-proper`, `def-weil-proper-morphism`, `def-weil-finite-type-morphism`, `lem-per-quasi-excellent-finite-type-stability`, `lem-exc-quasi-excellent-nagata`, `def-weil-pbc-nagata-ring`, `def-weil-pbc-japanese-domain`, `lem-per-componentwise-normalization-affine-charts`, `def-weil-finite-integral-morphism`.

### Step 3: Induction for geometry and projectivity

I read Stacks 0B3I and 0C4P. The finite-projective-bundle node says projectivity for arbitrary finite scheme maps. The composition node explicitly needs a quasi-compact quasi-separated final target; Noetherianity and the cited local-Noetherian quasi-separated lemma give that for B and S. The relative-ample node explicitly includes finite type. The normality used here is in the statement of the componentwise-normalization generic-properties node, rather than inferred just from the definition. The base and induction step are written, including the identity tower.

Cited statements: `lem-trf-finite-projective-bundle`, `lem-trf-projective-bundle-proper`, `def-weil-proper-morphism`, `lem-per-quasi-excellent-finite-type-stability`, `lem-sfb-componentwise-normalization-generic-properties`, `lem-weil-pbc-locally-noetherian-quasi-separated`, `lem-per-projective-bundle-composition`, `lem-per-projective-bundle-relative-ample`.

### Step 4: Common open and integrality

I checked ILO VIII 2.2 and the componentwise-normalization generic-properties statement. Its generic-point BIJECTION and its one-point generic FIBRES are both needed to rule out additional preimages of a generic point. The complement node supplies an actual open isomorphism; smooth normalization pullback applies to the open immersion, and trivial-normalization applies to its normal source. Properness, including universally closedness, is obtained from projectivity using the proper-morphism definition. Finitely many images of centers form a closed nowhere dense subset. I explicitly checked the unit ideal, an invertible nonunit ideal whose blowup is an isomorphism, a disconnected normal base, and length zero.

Cited statements: `thm-nagata-global-blowup-complement`, `lem-per-integral-blowup-projective-geometry`, `lem-sfb-componentwise-normalization-generic-properties`, `lem-sfb-componentwise-normalization-smooth-pullback`, `lem-sfb-normalization-normal-locally-finite`, `lem-trf-projective-bundle-proper`, `def-weil-proper-morphism`, `def-pc-integral-scheme`.

### Step 5: Rigidity and the nonseparated cover

ILO VIII 2.2.3 says there are no base automorphisms. I expanded its application using the cited agree-on-dense-open statement, whose target must be separated. The cover U was NOT assumed separated: the argument restricts to affine base opens, where a projective source is separated. Normal components are integral; on them a function vanishing on a dense open is zero, so the open is schematically dense. Gluing over those base opens is exactly what the scheme-morphism-gluing node states. This supplies rigidity on U and on the overlap stages as well as on X.

Cited statements: `lem-trf-projective-bundle-proper`, `def-weil-proper-morphism`, `lem-sfb-normal-locally-finite-components`, `lem-chow-agree-on-dense-open`, `lem-weil-pbc-scheme-morphism-gluing`.

### Step 6: Etale comparisons and cover hypotheses

I read ILO VIII Lemma 2.2.9 and Stacks 07TD. The existing componentwise-normalization smooth-pullback node explicitly gives the etale case for locally Noetherian schemes, unlike the relative-normalization node, which is a different construction. I cited the blowup comparison DEFINITION together with its isomorphism theorem because the latter alone only says the constructed comparison is an isomorphism. Etale base-change finite limits gives the etale map on ordinary blowups. The definition of etale supplies flatness; the etale-smooth node and smooth-normal-ascent give normality of U and all overlap stages. Quasi-excellent finite-type stability gives their local Noetherianity. Uniqueness of normalization comparisons and coefficient pullback of Rees algebras prove composition coherence.

Cited statements: `def-weil-etale-morphism`, `def-nagata-blowup-flat-base-change-map`, `thm-nagata-blowup-flat-base-change`, `lem-weil-pbc-etale-base-change-finite-limits`, `lem-sfb-componentwise-normalization-smooth-pullback`, `lem-per-quasi-excellent-finite-type-stability`, `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`, `lem-sfb-smooth-normal-ascent`.

### Step 7: Arbitrary flat-family equality test

I checked ILO VIII 5.5.3 and Stacks 05CK, and read the flat-local-faithfully-flat statement. A jointly surjective family need not be fpqc, so I use stalks, not an fpqc descent theorem for this test. At each stalk one flat local map is faithfully flat. Universal injectivity applied to A/J detects ideal membership, and exact flat module pullback identifies the ideal being tested with its extension. The same argument detects the kernel of the descended inclusion. This does not assert normalization commutes with arbitrary flat base change.

Cited statements: `lem-weil-pbc-flat-local-hom-faithfully-flat`, `lem-weil-pbc-faithfully-flat-universally-injective`, `lem-weil-pbc-flat-module-pullback-exact-pushforward-injective`.

### Step 8: Effective descent of the ordered centers

I read ILO VIII 2.2.11 and Stacks descent.tex Proposition 023T in full, plus the statements of the Noetherian-submodule and coherent finite-type nodes. The singleton cover at stage i is the base change of u, so its fpqc condition is supplied by the covering-base-change node. The module-descent node is an equivalence on quasi-coherent MODULES and their MORPHISMS, so it descends both the center and its inclusion into the structure sheaf. The inclusion is injective by step 7. Coherence follows from a finite submodule of A and 01XZ, without requiring a finiteness-preservation clause not stated by the cited equivalence. A point above a generic point is generic because the fibre is zero-dimensional; this verifies nowhere denseness downstairs.

Cited statements: `def-weil-etale-morphism`, `lem-galois-fpqc-covering-base-change`, `lem-pc-fpqc-descent`, `lem-trf-noetherian-submodule-finitely-presented`, `pqf-lem-coherent-ft-locnoeth`, `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`.

### Step 9: Assembly and uniqueness of the prescribed datum

I checked VIII 2.2.11 and 5.5.5. The induction hypothesis includes identification of the datum through the current stage, not just an isomorphism of underlying schemes. The definitions of ordinary blowup and componentwise normalization supply the next concrete construction. Step 6 identifies its pullback with the next original stage; step 5 then identifies the given overlap map with this canonical one. Full faithfulness of module descent gives uniqueness of the next center and inclusion. No new node restates any clause of the item.

Cited statements: `lem-pc-fpqc-descent`, `def-nagata-global-blowup`, `def-weil-pbc-reduced-normalization`.

### Step 10: Synchronization and actions

I reread VIII 5.5.3--5.5.5, especially the distinction between contracted and synchronized towers. The proof retains all stages, even isomorphism steps from Cartier centers. At each stage the arbitrary flat-family test compares actual ideal subsheaves. The fpqc representable-descent statement gives compatible scheme morphisms and uniqueness, so both action maps and the equations defining an action descend; parameter products cover scheme-valued actions. This use is fully faithful morphism descent, not an unjustified assertion that arbitrary projective schemes descend.

Cited statements: `lem-weil-pbc-fpqc-representable-descent`, `lem-galois-fpqc-covering-base-change`.

The empty scheme is permitted throughout; the zero ring appears only as the empty product in the affine normalization formula. A unit center gives an identity normalized blowup on a normal stage. A nonunit invertible Cartier center also gives an identity morphism but remains a remembered center: it is never contracted away. On a nonempty integral component a nowhere dense zero set forces a nonzero ideal, exactly the blowup-integrality hypothesis. I checked no proof step exceeds 2000 characters. The fpqc and arbitrary flat-family arguments are kept distinct because only the former is used for effective descent.

General off-unit tools are declared in `split_report.tool_uses` for maintainer review; no approved top-level tool-use field was written. The split introduces no new mathematical claim lacking a node, and uses definitions only for their actual constructions and predicates.

## Unfinished work

None in this one-level stage-1 split. Supporting existing nodes retain their own stage status.

## Validation

The server `review_split` check passed before packaging. Required delivery dry run and final push results are recorded by the delivery tool.
