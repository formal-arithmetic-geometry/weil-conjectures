## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-pushforward-dimension-flatness.json: item, split with seven proof steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-base-flatness-maximal-localizations.json: statement, Mathlib leaf Module.flat_of_isLocalized_maximal (Mathlib/RingTheory/Flat/Localization.lean:66-73).
- citations.json: one verbatim statement quote per cited node per step.

Attachments: none. Project searches for the blueprint tag and finite pushforward/relative dimension flatness found no exact declaration. The module-sheaf, etale-sheaf and Weil-sheaf finite pushforward declarations found by the concept search are different objects or omit the relative-flatness/dimension clauses.

WANTED: none.

The original item was statement-only. Its imported ancestry reaches no blueprint.is node: blueprint_refs.py ancestor prints None. I retained the existing ancestry and filled the new leaf's from.place and via from it. I read the current latest blueprint sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability.proof.md, especially the proper/direct image and compactification paragraph. I did not alter its unit or chapter. The inherited unit record is an older differently placed sketch; no claim of a new blueprint equivalence is made.

No statement dispute was found. There is no finite-presentation, Noetherian, surjectivity, or base-flatness assumption in the proof. The confusingly named pqf-lem-finite-integral-lft is used only for its actual statement, namely that finite morphisms are integral, not for any unmentioned local-finite-type conclusion. The last step gives the needed local-finite-type argument from finite generators.

Nothing remains unfinished in this one-level split. The new algebraic lemma is a searched Mathlib leaf with no proof steps. Existing unsplit geometry nodes are reused as required, including the dimension-flatness chart criterion.

## Review by N5

I read Stacks flat.tex Tag 05UF (lemma-flat-dimension-n-representable), specifically the paragraph comparing F_T, G_1,T and pi_1,T,*G_1,T. It applies the finite-direct-image principle without proving it; the seven steps supply that algebraic argument. I also read coherent.tex Tag 02KG (lemma-affine-base-change), algebra.tex Tag 00HT (lemma-flat-localization), properties.tex Tag 01PB (lemma-finite-type-module), the localization fractions and Tag 00E3 (lemma-spec-localization), and spaces-flat.tex Tag 0CWS (lemma-pre-flat-dimension-n). For the new leaf I read the full Mathlib variable block and theorem at Flat/Localization.lean:53-73. Its scalars are R and an arbitrary R-algebra S, with no flatness of S required; specializing S=C gives exactly the new statement.

Step 1 uses the finite definition for affineness and finite B/A, the affine-base-change node for both quasi-coherence and the canonical isomorphism, and the finite-type-on-affines node for the finite generating sets. Each cited statement was opened. The b_i m_j spanning calculation is explicitly supplied, so there is no unsupported assertion that a finite pushforward preserves finite type.

Step 2 uses the finite-permanence node for arbitrary base change and affineness, the two module-pullback nodes for finite type and quasi-coherence, and the intrinsic stalk-tensor and affine-open-localization statements for N=(E_T)_w and M_q=(G_T)_z. The scalar action goes through O_T,t -> A_p, which is available even if the chosen affine V does not lie over an affine neighbourhood of t. I corrected the outline to use this stalk action rather than supposing a map O_T,t -> A or B exists. The tensor/fraction identification is written on generators.

Step 3 uses localization-base-change to identify C, the finite-algebra-local-radical statement to contract every maximal Q to p A_p, and localization-quotient-by-prime for q=Q cap B and Q=q C. The latter node is used only in the direction it actually states, from an existing prime Q in the localization to its contraction; no converse prime-correspondence theorem is silently taken from it. Finite generation of C/A_p is checked by its generators. Consequently each maximal Q really yields a point over w, even for a noninjective A -> B.

Step 4 is elementary fraction algebra from the module-localization definition cited in that step. It gives both maps and the reason the additional denominators b/s outside Q amount to denominators b outside q. This proves the needed R-linearity and the comparison N_Q=M_q explicitly; it does not identify the pushforward stalk with a product of point stalks, which would be false in this generality.

Step 5 uses localization-preserves-flatness in its actual form: localization in the C direction preserves flatness over the unrelated base ring R. The new Mathlib leaf gives only the converse test from all maximal Q. These are different directions, both cited. The empty fibre works because Step 3 forces the maximal-indexed hypotheses to be vacuous; the Mathlib theorem handles the zero algebra and zero module without a nonzero instance.

Step 6 uses finite-implies-integral, the algebraic-residue-extension leaf, and the cardinal transcendence-degree tower leaf. The latter explicitly includes algebraic iff degree zero, so it really gives the equality of the two degrees. I verified that the residues form a tower over kappa(t). Both implications of the threshold condition are supplied, and a point w outside the image is handled by Step 5, not by assuming finite maps are surjective.

Step 7 uses local-finite-type base change for W_T, the definition of local finite type together with the finite generating sets for Z_T, and the existing dimension-flatness-base-change-sheaf statement for equivalence between the intrinsic and all-chart/one-atlas tests. That statement is stronger than the chart clause used here, and its hypotheses are checked: a scheme base, locally finite type source morphisms, and finite-type quasi-coherent modules. Its P_n on the identity chart is the intrinsic threshold condition, and its one-surjective-atlas clause is explicitly present. This is an existing sibling tool, not a newly relabelled clause.

I checked B1-B10, C1-C8, D1-D5 and E1-E7 with the statements open. The only new node has a self-contained ring/module statement, inline meaning of maximal ideal, definition dependencies for localization and flatness, no proof sketch, exact Tag/label citation, and an actual Mathlib match with lines. Searches of the whole DAG by theorem name, by maximal flatness and by Tag 00HT, and blueprint_refs searches for flat maximal, maximal localizations, flat localizations, flatness maximal and flat module found no existing node giving this maximal-ideal test for an arbitrary algebra module over a separate base. The all-prime relative-flatness node needs more hypotheses (all primes tested over their respective base localizations), so it cannot simply be cited for the maximal-ideal hypothesis used in Step 5. Search hits are retained in searches.jsonl and search-results.jsonl; every recorded query was run through msearch.py. No compiler or build was invoked.

Small cases: h the identity reduces to the stalk identity; a closed immersion is included as a finite morphism; a disjoint union gives several primes rather than a single stalk; a non-surjective finite morphism and Z empty give the vacuous-fibre case; G=0 is flat everywhere; n=0 tests every point, while a threshold above all occurring degrees gives vacuous conditions. The new leaf with C=0 forces N=0 and is valid with no maximal ideals; with R=C a field it has the single localization N_(0)=N. No step exceeds 2000 characters, and the fraction comparison is a two-map routine argument, not a hidden general comparison lemma.

Generic off-unit tools are listed in split_report.tool_uses for the maintainer to review. They provide affine base change, localizations, affine stalks and module pullbacks, not replacements for the unit's direct-image route. Maintainer-owned tool_uses is untouched.

## New nodes

lem-sfb-base-flatness-maximal-localizations: Mathlib leaf, zero new unsplit nodes.

## Not duplicates

lem-sfb-base-flatness-maximal-localizations vs lem-sbc-canonical-stalk-spectrum-flat: the existing statement is Flatness of the canonical spectrum-of-stalk morphism; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-trf-flat-ring-map-principal-cover: the existing statement is Flatness of a ring map glues on target principal opens; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-trf-diagonal-taylor-faithful-flatness: the existing statement is Faithfully flat Taylor realization at the residue-field diagonal point; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-trf-flat-localized-field-descent: the existing statement is A field localization upstairs identifies the base localization with its residue field; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-pc-affine-pullback-chart-tensor-flat-stalks: the existing statement is Tensor flatness and relative stalk flatness on one pulled-back affine chart; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-pc-affine-associated-module-flat-over: the existing statement is Associated flat modules are flat over their affine base; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-sc-p1-localization-short-exact: the existing statement is Ordinary localization preserves short exact sequences of modules; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-pc-relative-flat-module-stalk: the existing statement is Relative affine flatness gives flat module stalks; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-pc-pullback-stalk-tensor-flat: the existing statement is Fibre-product stalk is flat over the tensor of stalks; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-pc-relative-flat-of-stalks: the existing statement is Relative flatness from stalks; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-pc-affine-flat-module-localization-preserves-flatness: the existing statement localizes an already-flat module (the forward direction); the new leaf descends flatness from maximal localizations (the reverse direction).

lem-sfb-base-flatness-maximal-localizations vs lem-pc-affine-chart-relative-flat-criterion: the existing statement is Relative flatness on one affine chart; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-pc-flat-model-opcycles-flat-zero: the existing statement is Flatness of degree-zero opcycles of a bounded-above free model; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-pc-affine-projective-sections-sheafification: the existing statement is Sheafification of a finite-projective affine section comparison; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-pc-affine-cover-module-tensor-flat-criterion: the existing statement is Affine-cover criterion for tensor module flatness after base change; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-pc-affine-flat-module-local-criterion: the existing statement gives only the forward implication to prime localizations over localized base rings; the new leaf gives a reverse implication from algebra-maximal localizations over the fixed base.

lem-sfb-base-flatness-maximal-localizations vs lem-pc-affine-flat-module-tensor-flat: the existing statement is Flat sections on affine subopens imply tensor flatness; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-pc-affine-sections-flat-over-base: the existing statement assumes all prime localizations are flat over their contracted base-prime local rings; the new leaf tests only maximal ideals of an arbitrary algebra, over one fixed unlocalized base R.

lem-sfb-base-flatness-maximal-localizations vs lem-sfb-finite-pushforward-dimension-flatness: the item is a scheme-level finite pushforward equivalence with base change, transcendence thresholds and chart tests; the new leaf is only a generic algebraic maximal-localization implication.

lem-sfb-base-flatness-maximal-localizations vs lem-sc-principal-cokernel-projective-descent: the existing statement is Injectivity and projective cokernel descend from a principal cover; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-weil-pbc-regular-local-maximal: the existing statement is Regularity of a ring map is local on the target; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-weil-pbc-localization-flat: the existing statement is A localization is a flat algebra; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-weil-pbc-localization-regular: the existing statement is A localization map is regular; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-weil-pbc-flat-local-ring-maps: the existing statement is A flat ring map induces flat local maps of local rings; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-weil-pbc-flat-map-local-criterion: the existing statement is Flatness of a ring map is local on the target; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-weil-pbc-regular-through-localization: the existing statement is A regular map factoring through a localization is regular from the localization; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-weil-pbc-weakly-regular-sequence-localization-prime: the existing statement is A sequence satisfying the nonzerodivisor conditions inside a prime becomes a regular sequence in the localization at that prime; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-weil-pbc-annihilator-localization-finite: the existing statement is Annihilator of a finite module commutes with localization at an element; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-weil-pbc-flat-over-localization: the existing statement changes the base from a ring to its own localization for a module already over that localization; the new leaf detects base flatness using maximal localizations of a separate algebra.

lem-sfb-base-flatness-maximal-localizations vs lem-weil-pbc-flat-localized-module-base-change: the existing statement is Base change preserves flatness at a module point; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-pod-rational-ordinary-cohomology-tensor: the existing statement is Canonical scalar comparison for rational ordinary cohomology; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.

lem-sfb-base-flatness-maximal-localizations vs lem-sc-affine-standard-cover-finite-free-local-fp-flat: the existing statement is A finite free module is finitely presented and flat; it does not state the reverse fixed-base flatness test for an arbitrary algebra module from all its maximal localizations.
