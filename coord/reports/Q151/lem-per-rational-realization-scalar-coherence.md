# Stage 1 delivery: lem-per-rational-realization-scalar-coherence

## Files written

- Item: unchanged statement and stmt_deps; three-step assembly of 1252 characters.
- lem-per-rational-scalar-balanced-localization: statement, unsplit, no Mathlib match. Retains original steps 1-4.
- lem-per-rational-scalar-completion-unit-square: statement, unsplit, no Mathlib match. Retains original steps 5-7.
- lem-per-rational-scalar-mixed-unit-cancellation: statement, unsplit, no Mathlib match. Retains original steps 8-9.
- citations.json: verbatim conclusion quotations for all five step/node citations. searches.jsonl and search-*.txt retain actual queries and complete results.

## Attachments

None. Searched WeilConjectures by the exact blueprint id and rationalRealizationScalar/realization-scalar terminology; no matching project declaration. The recorded Sheaf/Paper/RationalRealizationScalarCoherence.lean declarations have sorry (primary theorem line 119 and companion theorem lines), so are not attachments. No compiler or Lake was run.

## WANTED

None. Bhatt--Scholze and the Stacks source files are present.

## Repair order and scope

The released stage-1 repair note of 2026-10-22 explicitly overrides the prior passing split: at least two comparable statement-only nodes, assembly at most 3000 characters, keep statement and plan, retain every old argument. This delivery has three nodes, dividing steps 1-4 / 5-7 / 8-9. Creating nodes for these substantial argument blocks is explicitly required by the repair order; this is not an ordinary attempt to replace a proof by a restatement. Every old step is copied below without deletion, and its new owner is stated. The new nodes have statements only; their proof arguments below are handover material for the later workers, not proofs attached to unsplit nodes. No statement dispute was found. No other item, unit, Lean source, launcher file or shared repository file was written.

## Searches and overlap

Searched all DAG statements and titles for balanced/localization, completion-pullback-unit, mixed-coherence, scalar-realization terminology and the s/t and completed beta formulas. Searched blueprint_refs ancestor and searches 'scalar realization', 'balanced localization', 'completion pullback', 'mixed coherence', 'rational comparison', 'coefficient square', 'finite coefficient extension', 'completion unit'. No blueprint node states the new normalized conclusions. Read candidate statements: generic monoidal comparisons, finite-free completion transport and reflected coefficient squares are ingredients and remain statement dependencies of the new claims. Ordinary coherent formal completion concerns an unrelated ideal of a scheme, not coefficient completion. The trace-formula strict-system mixed-coherence node concerns finite whole quotient diagrams before realization, not raw rational realization and cancellation of completed pullback units. The normalized purity scalar-realization node concerns integral whole-system counits and has no rational comparison theta. Their arguments are not substituted for this unit's route.

Each new node received its own leanfinder, leansearch, loogle and grep query plus a second semantic phrasing. All services answered. The item itself received a fresh leanfinder/loogle/grep check in addition to its preserved earlier searches. The item Loogle query used an unknown identifier 'localization', recorded as such; the new nodes have valid Loogle queries. Read Mathlib SheafOfModules.pullbackComp and pullback_assoc (PullbackContinuous.lean:167,193), ModuleCat.extendScalarsComp (ChangeOfRings.lean:984), and AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (AsTensorProduct.lean:328). The first two are ordinary sheaf/module comparisons and the last is ordinary algebraic completion of finite modules, not the unbounded derived coefficient comparisons with quotient-normalized units. Other semantic hits were ordinary tilde localizations, etale algebras, or tensor coherence, not matches. Exact queries and returned names are in each node and searches.jsonl; no invented search records.

## Review by Q151

I read the current chapter/unit records and the current blueprint smooth-pullback proof. The fixed Fourier-perverse route is unchanged: these lemmas support the intervening rational continuous-coefficient comparison in its first paragraph. This is not its unit's key node, so no unit realized fields are changed.

For the item and balanced-localization node I read Bhatt--Scholze Lemma 6.8.2 on PDF pp.58-59, Proposition 6.8.14 on pp.61-62 and Remark 6.8.15, and Stacks sites-cohomology.tex labels lemma-pullback-K-flat (0G7E) and lemma-derived-pullback-composition (0D6D). The paper identifies the coefficient sheaves and rational category; the stronger explicit balancing, fraction and coherence arguments are agent expansions, not attributed verbatim to that paper. Finite-projection maps are available even for ramification e>1: t_E^n lies in t_L^n. Flat-term K-flat preservation lets the same representative compute both composites, and the rational denominator is a unit in L, not an assumed power of the chosen L uniformizer. The torsion-Hom fraction test is retained.

For the completion-unit-square node I read algebraization.tex labels lemma-derived-completion-koszul (0A0E) and lemma-pushforward-commutes-with-derived-completion (0A0G), and opened every old cited statement: finite-free-completed-scalar-comparison supplies rank [L:E]; finite-free-completion-transport requires the positive power t_E=u t_L^e and gives the exact kappa unit/tower equations; constant-completion-equivalence identifies quotient/Koszul units; ringed-koszul-completion-reflector gives reflectivity; reflected-adjunction-coefficient-squares states the inverse orientation kappa^{-1} Lambda(delta) and the required pasting, with delta=beta^{-1}; ringed-pushforward-completion supplies completeness and its normalized right-adjoint comparison. These hypotheses hold for the ringed coefficient square without assuming its ring map is an isomorphism. I retained their concrete application, not an unsupported claim of canonical isomorphism. The resulting hat-beta has the correct orientation and exact unit equation. Ordinary pullback units are invertible only on the constructible integral objects, as the pullback-comparison statement says; ambient completion units are not asserted invertible.

For mixed-unit-cancellation I read the same Bhatt--Scholze remark and all relevant node statements: rational-realization-pullback-comparison specifies alpha as ordinary balancing after JQ(gamma^{-1}); localization-inverse-image-coherence gives canonical units and geometric composition; monoidal comparisons specify the K-flat ordinary maps; reflected squares and completion transport supply pasting, as retained in the preceding new node. I checked types in the displayed mixed equation: both sides begin at J_LQ_L(C_{X'} hat-P_E K) and finish at H_L D_X J_EQ_EK. Precomposing uses the invertible J_LQ_L(C gamma_E), and the shared local formula uses i_{X'}(b'), rather than silently identifying inverse-image completed rings. Cancellation is legitimate and does not appeal to faithfulness of separate quotient evaluations.

Assembly step 1 cites balanced-localization's explicit s,t, raw naturality and tower conclusions. Step 2 cites completion-unit-square's kappa, hat-beta formula, unit equation and matching to the published scalar functor. Step 3 cites all three: the first two furnish the named theta and actual units required in the third's hypotheses, and the third gives the exact mixed equation and pasting conclusions. citations.json quotes those actual statement paragraphs. No assembly step calls an uncited non-elementary result. New nodes' statement dependencies include all introduced notions and the actual operations and normalization data; they have no proof/proof_deps.

Small cases checked: K=0 gives unique zero-object comparisons; E=L gives the literally identity raw scalar functor and multiplication unitors; g=id gives the canonical inverse-image identity; empty schemes give the zero sheaf category. For ramified extensions e>1 the unit-power relation is used, never an unramified or quotient-flatness assumption. For a four-field tower both flat models have the same product nml, with units inserted at repeated fields. The new node statements are substantial applications/cancellation claims, not elementary two-line nodes. No proof step exceeds 2000 characters; the long statements describe the separate work mandated by the human repair order. No new proof route, SGA source or pair-category descent was introduced.

## Not duplicates

lem-per-rational-scalar-balanced-localization vs lem-pe-kflat-scalar-tower-realization: The new claim compares completed l-adic coefficient localization, raw fractions and field towers with the specified realization maps; the existing claim concerns K-flat realization of the augmented derived scalar-extension tower. It does not state this combined s/t normalization on raw categories.

lem-per-rational-scalar-balanced-localization vs lem-sbc-pullback-comparison-comp: The new claim compares completed l-adic coefficient localization, raw fractions and field towers with the specified realization maps; the existing claim concerns Composition of coefficient pullback and single-complex comparisons. It does not state this combined s/t normalization on raw categories.

lem-per-rational-scalar-balanced-localization vs lem-sf-open-exchange-roos-restriction: The new claim compares completed l-adic coefficient localization, raw fractions and field towers with the specified realization maps; the existing claim concerns Restriction of the strict-limit completed open exchange and its units. It does not state this combined s/t normalization on raw categories.

lem-per-rational-scalar-balanced-localization vs lem-sf-scalar-pullback-composition: The new claim compares completed l-adic coefficient localization, raw fractions and field towers with the specified realization maps; the existing claim concerns Composition coherence of normalized scalar/pullback comparisons. It does not state this combined s/t normalization on raw categories.

lem-per-rational-scalar-balanced-localization vs lem-pur-factorized-pullback-square-pasting: The new claim compares completed l-adic coefficient localization, raw fractions and field towers with the specified realization maps; the existing claim concerns Pasting canonical pro-etale derived pullback comparisons for factored endomorphisms. It does not state this combined s/t normalization on raw categories.

lem-per-rational-scalar-balanced-localization vs lem-sf-semilinear-compositor-coherence: The new claim compares completed l-adic coefficient localization, raw fractions and field towers with the specified realization maps; the existing claim concerns Associative normalized compositors for arbitrary semilinear systems. It does not state this combined s/t normalization on raw categories.

lem-per-rational-scalar-balanced-localization vs def-sf-semilinear-proper-open-comparisons: The new claim compares completed l-adic coefficient localization, raw fractions and field towers with the specified realization maps; the existing claim concerns Canonical semilinear proper/open compositors and intrinsic clopen comparison. It does not state this combined s/t normalization on raw categories.

lem-per-rational-scalar-balanced-localization vs lem-tw-ordinary-immersion-chart-comparison: The new claim compares completed l-adic coefficient localization, raw fractions and field towers with the specified realization maps; the existing claim concerns Ordinary derived immersion and representable-chart comparison. It does not state this combined s/t normalization on raw categories.

lem-per-rational-scalar-balanced-localization vs def-zl-pbc-finite-raw-scalar-comparison: The new claim compares completed l-adic coefficient localization, raw fractions and field towers with the specified realization maps; the existing claim concerns Canonical comparison of normalized and embedding finite-field scalar extension. It does not state this combined s/t normalization on raw categories.

lem-per-rational-scalar-balanced-localization vs def-zl-finite-regular-coefficient-comparisons: The new claim compares completed l-adic coefficient localization, raw fractions and field towers with the specified realization maps; the existing claim concerns Finite regular coefficient comparisons and prescribed pullback compositor. It does not state this combined s/t normalization on raw categories.

lem-per-rational-scalar-balanced-localization vs lem-trf-derived-pullback-coherence: The new claim compares completed l-adic coefficient localization, raw fractions and field towers with the specified realization maps; the existing claim concerns Associativity of finite pro-etale derived pullback comparisons. It does not state this combined s/t normalization on raw categories.

lem-per-rational-scalar-balanced-localization vs def-trf-integral-comparison-realization-models: The new claim compares completed l-adic coefficient localization, raw fractions and field towers with the specified realization maps; the existing claim concerns Normalized realization interfaces for integral quotient systems. It does not state this combined s/t normalization on raw categories.

lem-per-rational-scalar-completion-unit-square vs lem-sbc-koszul-fibre-linear-descent: The new claim applies finite-free ramified coefficient completion to the actual geometric pullback square, identifies the published hat-beta and proves its exact quotient-unit equation and pasting; the existing claim concerns Linear descent of the explicit Koszul product-fibre construction. It supplies at most an ingredient, not this normalized coefficient/pullback application.

lem-per-rational-scalar-completion-unit-square vs lem-sbc-koszul-tensor-derived-tower: The new claim applies finite-free ramified coefficient completion to the actual geometric pullback square, identifies the published hat-beta and proves its exact quotient-unit equation and pasting; the existing claim concerns Ordinary Koszul tensor towers represent derived tensor towers. It supplies at most an ingredient, not this normalized coefficient/pullback application.

lem-per-rational-scalar-completion-unit-square vs lem-sf-completed-tensor-rational-naturality: The new claim applies finite-free ramified coefficient completion to the actual geometric pullback square, identifies the published hat-beta and proves its exact quotient-unit equation and pasting; the existing claim concerns Naturality and rationalization of a completed tensor comparison. It supplies at most an ingredient, not this normalized coefficient/pullback application.

lem-per-rational-scalar-completion-unit-square vs lem-sf-regular-roos-koszul-unit: The new claim applies finite-free ramified coefficient completion to the actual geometric pullback square, identifies the published hat-beta and proves its exact quotient-unit equation and pasting; the existing claim concerns Regular quotient Roos completeness detects the canonical Koszul unit. It supplies at most an ingredient, not this normalized coefficient/pullback application.

lem-per-rational-scalar-completion-unit-square vs def-sf-integral-koszul-intrinsic-unit: The new claim applies finite-free ramified coefficient completion to the actual geometric pullback square, identifies the published hat-beta and proves its exact quotient-unit equation and pasting; the existing claim concerns Integral one-uniformizer intrinsic Koszul unit. It supplies at most an ingredient, not this normalized coefficient/pullback application.

lem-per-rational-scalar-completion-unit-square vs def-sf-koszul-small-model-completed-tensor: The new claim applies finite-free ramified coefficient completion to the actual geometric pullback square, identifies the published hat-beta and proves its exact quotient-unit equation and pasting; the existing claim concerns Local derived completeness and completed tensor on the canonical small site model. It supplies at most an ingredient, not this normalized coefficient/pullback application.

lem-per-rational-scalar-completion-unit-square vs lem-sf-automorphism-completion-unit-comparison: The new claim applies finite-free ramified coefficient completion to the actual geometric pullback square, identifies the published hat-beta and proves its exact quotient-unit equation and pasting; the existing claim concerns Automorphism pullback commutes with completion with a unique unit normalization. It supplies at most an ingredient, not this normalized coefficient/pullback application.

lem-per-rational-scalar-completion-unit-square vs lem-sf-constructible-canonical-completeness: The new claim applies finite-free ramified coefficient completion to the actual geometric pullback square, identifies the published hat-beta and proves its exact quotient-unit equation and pasting; the existing claim concerns From an intrinsic presentation witness to canonical actual completeness. It supplies at most an ingredient, not this normalized coefficient/pullback application.

lem-per-rational-scalar-completion-unit-square vs lem-sf-open-quotient-koszul-completeness: The new claim applies finite-free ramified coefficient completion to the actual geometric pullback square, identifies the published hat-beta and proves its exact quotient-unit equation and pasting; the existing claim concerns DVR quotient augmentation, Koszul completion and open completeness. It supplies at most an ingredient, not this normalized coefficient/pullback application.

lem-per-rational-scalar-completion-unit-square vs lem-sf-derived-completed-tensor-bilinearity: The new claim applies finite-free ramified coefficient completion to the actual geometric pullback square, identifies the published hat-beta and proves its exact quotient-unit equation and pasting; the existing claim concerns Bilinearity of derived completed tensor and its rational Hom action. It supplies at most an ingredient, not this normalized coefficient/pullback application.

lem-per-rational-scalar-completion-unit-square vs lem-sfb-ringed-complete-triangulated: The new claim applies finite-free ramified coefficient completion to the actual geometric pullback square, identifies the published hat-beta and proves its exact quotient-unit equation and pasting; the existing claim concerns Exact Koszul completion and the triangulated complete locus. It supplies at most an ingredient, not this normalized coefficient/pullback application.

lem-per-rational-scalar-completion-unit-square vs lem-sfb-exact-completed-koszul-pullback: The new claim applies finite-free ramified coefficient completion to the actual geometric pullback square, identifies the published hat-beta and proves its exact quotient-unit equation and pasting; the existing claim concerns Exact product-preserving inverse image transports the actual Koszul unit. It supplies at most an ingredient, not this normalized coefficient/pullback application.

The first node vs prop-weil-pbc-scalar-extension: the latter defines T and its abstract scalar/pullback comparisons, but does not compare J with continuous-module scalar localization by s/t. The second vs lem-weil-pbc-finite-free-completion-transport: kappa alone does not identify the actual geometric pullback square and gamma. The third vs lem-per-rational-realization-pullback-comparison: alpha alone does not give the mixed field-extension square or the cancellation/pasting equations.

lem-per-rational-scalar-balanced-localization vs def-a1-proper-sections-germ-and-moving-point: The existing node defines Canonical proper compact rational germs and semilinear moving points; it makes no assertion of the normalized realization comparison proved here. This node additionally identifies the two actual localization routes s,t, proves naturality on raw fractions without torsion-free Hom groups, and gives finite-field tower/unit/pentagon equations for theta. It is not a special case of the existing statement.

lem-per-rational-scalar-balanced-localization vs def-per-derived-hom-pullback: The existing node defines Canonical pullback on shifted etale derived Hom; it makes no assertion of the normalized realization comparison proved here. This node additionally identifies the two actual localization routes s,t, proves naturality on raw fractions without torsion-free Hom groups, and gives finite-field tower/unit/pentagon equations for theta. It is not a special case of the existing statement.

lem-per-rational-scalar-balanced-localization vs lem-pod-constant-comparison-module-localization: The existing node states Canonical finite-coefficient derived composition is ordinary module composition localized. This node additionally identifies the two actual localization routes s,t, proves naturality on raw fractions without torsion-free Hom groups, and gives finite-field tower/unit/pentagon equations for theta. It is not a special case of the existing statement.

lem-per-rational-scalar-balanced-localization vs lem-pod-finite-system-pullback-coherence: The existing node states Coherent composition of finite-coefficient pullback on strict systems. This node additionally identifies the two actual localization routes s,t, proves naturality on raw fractions without torsion-free Hom groups, and gives finite-field tower/unit/pentagon equations for theta. It is not a special case of the existing statement.

lem-per-rational-scalar-balanced-localization vs lem-pod-integral-pullback-composition: The existing node states Composition isomorphism for integral derived pullbacks. This node additionally identifies the two actual localization routes s,t, proves naturality on raw fractions without torsion-free Hom groups, and gives finite-field tower/unit/pentagon equations for theta. It is not a special case of the existing statement.

lem-per-rational-scalar-balanced-localization vs def-pbc-successive-derived-scalar-normalization-data: The existing node defines Normalized presentation data for successive derived scalar extensions; it makes no assertion of the normalized realization comparison proved here. This node additionally identifies the two actual localization routes s,t, proves naturality on raw fractions without torsion-free Hom groups, and gives finite-field tower/unit/pentagon equations for theta. It is not a special case of the existing statement.

lem-per-rational-scalar-balanced-localization vs def-weil-pbc-actual-finite-coefficient-transport: The existing node defines Actual-ring finite coefficient transport and normalized local restriction; it makes no assertion of the normalized realization comparison proved here. This node additionally identifies the two actual localization routes s,t, proves naturality on raw fractions without torsion-free Hom groups, and gives finite-field tower/unit/pentagon equations for theta. It is not a special case of the existing statement.

lem-per-rational-scalar-balanced-localization vs def-weil-pbc-derived-direct-image-composition: The existing node defines Composition isomorphisms of derived direct images (conjugates of those of inverse images); it makes no assertion of the normalized realization comparison proved here. This node additionally identifies the two actual localization routes s,t, proves naturality on raw fractions without torsion-free Hom groups, and gives finite-field tower/unit/pentagon equations for theta. It is not a special case of the existing statement.

lem-per-rational-scalar-balanced-localization vs def-weil-pbc-derived-square-iso: The existing node defines Square isomorphism on bounded below derived categories; it makes no assertion of the normalized realization comparison proved here. This node additionally identifies the two actual localization routes s,t, proves naturality on raw fractions without torsion-free Hom groups, and gives finite-field tower/unit/pentagon equations for theta. It is not a special case of the existing statement.

lem-per-rational-scalar-balanced-localization vs def-weil-pbc-normalized-scalar-restriction: The existing node defines Normalized completed-coefficient scalar and restriction comparison; it makes no assertion of the normalized realization comparison proved here. This node additionally identifies the two actual localization routes s,t, proves naturality on raw fractions without torsion-free Hom groups, and gives finite-field tower/unit/pentagon equations for theta. It is not a special case of the existing statement.

lem-per-rational-scalar-balanced-localization vs def-weil-pbc-ring-restriction-pullback-comparison: The existing node defines Canonical restriction-of-scalars and identified-coefficient pullback comparisons; it makes no assertion of the normalized realization comparison proved here. This node additionally identifies the two actual localization routes s,t, proves naturality on raw fractions without torsion-free Hom groups, and gives finite-field tower/unit/pentagon equations for theta. It is not a special case of the existing statement.

lem-per-rational-scalar-completion-unit-square vs def-a1-principal-completed-koszul-towers: The existing node defines Actual completed-coefficient principal Koszul and quotient tensor towers; it makes no assertion of the normalized realization comparison proved here. This node concerns the ramified finite-field scalar/geometric pullback square with kappa, the published hat-beta and the exact gamma-unit equation; neither raw cochain factorization data nor one-field quotient-completion normalization states this square.

lem-per-rational-scalar-completion-unit-square vs def-a1-principal-intrinsic-completion: The existing node defines Principal intrinsic fiber and its specified chain unit; it makes no assertion of the normalized realization comparison proved here. This node concerns the ramified finite-field scalar/geometric pullback square with kappa, the published hat-beta and the exact gamma-unit equation; neither raw cochain factorization data nor one-field quotient-completion normalization states this square.

lem-per-rational-scalar-completion-unit-square vs def-derived-cochain-comparison-factors: The existing node defines Localization comparison for an additive functor on complexes; it makes no assertion of the normalized realization comparison proved here. This node concerns the ramified finite-field scalar/geometric pullback square with kappa, the published hat-beta and the exact gamma-unit equation; neither raw cochain factorization data nor one-field quotient-completion normalization states this square.

lem-per-rational-scalar-completion-unit-square vs def-derived-cochain-counit: The existing node defines Derived counit on complex localization; it makes no assertion of the normalized realization comparison proved here. This node concerns the ramified finite-field scalar/geometric pullback square with kappa, the published hat-beta and the exact gamma-unit equation; neither raw cochain factorization data nor one-field quotient-completion normalization states this square.

lem-per-rational-scalar-completion-unit-square vs def-derived-cochain-right-unit: The existing node defines Derived unit on complex localization; it makes no assertion of the normalized realization comparison proved here. This node concerns the ramified finite-field scalar/geometric pullback square with kappa, the published hat-beta and the exact gamma-unit equation; neither raw cochain factorization data nor one-field quotient-completion normalization states this square.

lem-per-rational-scalar-completion-unit-square vs def-derived-exact-equivalence-square-data: The existing node defines Data of compatible exact-equivalence derived squares; it makes no assertion of the normalized realization comparison proved here. This node concerns the ramified finite-field scalar/geometric pullback square with kappa, the published hat-beta and the exact gamma-unit equation; neither raw cochain factorization data nor one-field quotient-completion normalization states this square.

lem-per-rational-scalar-completion-unit-square vs def-weil-pbc-completed-constant-presentation-data: The existing node defines Common constant presentation of the two completion objects; it makes no assertion of the normalized realization comparison proved here. This node concerns the ramified finite-field scalar/geometric pullback square with kappa, the published hat-beta and the exact gamma-unit equation; neither raw cochain factorization data nor one-field quotient-completion normalization states this square.

lem-per-rational-scalar-completion-unit-square vs def-weil-pbc-completed-quotient-completion-unit: The existing node defines Bundled specified completed quotient-completion unit; it makes no assertion of the normalized realization comparison proved here. This node concerns the ramified finite-field scalar/geometric pullback square with kappa, the published hat-beta and the exact gamma-unit equation; neither raw cochain factorization data nor one-field quotient-completion normalization states this square.

lem-per-rational-scalar-completion-unit-square vs def-weil-pbc-completed-quotient-ordinary-unit: The existing node defines Ordinary completed quotient-limit unit; it makes no assertion of the normalized realization comparison proved here. This node concerns the ramified finite-field scalar/geometric pullback square with kappa, the published hat-beta and the exact gamma-unit equation; neither raw cochain factorization data nor one-field quotient-completion normalization states this square.

lem-per-rational-scalar-completion-unit-square vs def-weil-pbc-flat-scalar-koszul-models: The existing node defines Ordered coordinate and restriction models for scalar Koszul towers; it makes no assertion of the normalized realization comparison proved here. This node concerns the ramified finite-field scalar/geometric pullback square with kappa, the published hat-beta and the exact gamma-unit equation; neither raw cochain factorization data nor one-field quotient-completion normalization states this square.

lem-per-rational-scalar-completion-unit-square vs lem-constant-completion-unit-normalization: The existing node states Constant quotient completion unit on every complex. This node concerns the ramified finite-field scalar/geometric pullback square with kappa, the published hat-beta and the exact gamma-unit equation; neither raw cochain factorization data nor one-field quotient-completion normalization states this square.

lem-per-rational-scalar-completion-unit-square vs lem-derived-exact-equivalence-squares: The existing node states Compatible derived squares under exact equivalences. This node concerns the ramified finite-field scalar/geometric pullback square with kappa, the published hat-beta and the exact gamma-unit equation; neither raw cochain factorization data nor one-field quotient-completion normalization states this square.

## Retained arguments and handover to later workers

### Original step 1 — work assigned to lem-per-rational-scalar-balanced-localization

For $W=X,X'$, abbreviate $R_W=B_{E,W}$, $S_W=B_{L,W}$ and $C_W=S_W\otimes^L_{R_W}-$. The integral inclusion $i_W:R_W\to S_W$ has $n$-th projection $(\iota_n)_W\pi^E_n$, where $\iota_n:A/\varpi_E^n\to A_L/\varpi_L^n$ is induced by inclusion. For $g:X'\to X$, the two maps $g^{-1}R_X\to S_{X'}$ agree: after projection to $(A_L/\varpi_L^n)_{X'}$ both are the constant-sheaf coefficient map after the pulled-back $E$-quotient projection. Equality into the inverse limit proves the integral coefficient square. Under continuous-coefficient realization this says that precomposition with the geometric projection commutes with postcomposition by the field inclusion. Localization gives the same square for $E_W\to L_W$, preserving the coefficient units. In particular every nonzero constant of $E$ has inverse its constant reciprocal in $L_W$.

Original cited statements: def-weil-integral-scalar-extension, def-weil-pbc-completed-pullback, lem-weil-pbc-continuous-coefficient-realizations, lem-per-rational-module-realization-functor.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Lemma 6.8.2 and Remark 6.8.15; explicit finite-projection coefficient-square calculation.

### Original step 2 — work assigned to lem-per-rational-scalar-balanced-localization

Let $K\in\mathcal C_X$. The integral representative of $T_{L/E}QK$ is $C_XK$, by the scalar-extension statement. Set $U_X(K)=L_X\otimes^L_{R_X}K$. Derived pullback composition on the identity underlying topos supplies natural isomorphisms
$$s_K:L_X\otimes^L_{S_X}(S_X\otimes^L_{R_X}K)\xrightarrow{\sim}U_X(K),\quad t_K:L_X\otimes^L_{E_X}(E_X\otimes^L_{R_X}K)\xrightarrow{\sim}U_X(K).$$
They use the coefficient maps from Step 1. To compute them, take a flat-term K-flat representative $P$ of $K$; both $S_X\otimes_{R_X}P$ and $E_X\otimes_{R_X}P$ remain flat-term K-flat over their new rings. Thus $s_K$ and $t_K$ are induced by $(l\otimes b)\otimes p\mapsto lb\otimes p$, and their inverses insert $1$. Define $\theta_{L/E,X,QK}=t_K^{-1}s_K$. The derived composition and monoidal comparisons ensure independence of the representative and naturality for all integral derived morphisms, not merely chain maps.

Original cited statements: prop-weil-pbc-scalar-extension, lem-per-rational-module-realization-functor, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-sfb-ringed-derived-monoidal-comparisons.

Source: literature/stacks-project/sites-cohomology.tex, Tags 0G7E (lemma-pullback-K-flat) and 0D6D (lemma-derived-pullback-composition); Bhatt--Scholze Lemma 6.8.2.

### Original step 3 — work assigned to lem-per-rational-scalar-balanced-localization

Pass to raw rational morphisms using the stated formulas for $J$ and $T$. For $f/\varpi_E^n$, naturality of Step 2 for $f$ can be multiplied by the central scalar $\varpi_E^{-n}$ on both sides, since Step 1 makes that scalar invertible in $L_X$. This gives naturality for $f/\varpi_E^n$. Explicitly, if $f/\varpi_E^n=h/\varpi_E^m$, then some $r\geq0$ kills $\varpi_E^mf-\varpi_E^nh$ after multiplication by $\varpi_E^r$; applying the integral functors and multiplying by $\varpi_E^{-r-m-n}$ gives equality of their localized images. Each component remains invertible, with inverse $s_K^{-1}t_K$. This proves the required natural isomorphism on the raw categories.

Original cited statements: def-weil-pbc-rational-category, prop-weil-pbc-scalar-extension, lem-per-rational-module-realization-functor.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Proposition 6.8.14(2); explicit calculation on the raw scalar-localized Hom groups.

### Original step 4 — work assigned to lem-per-rational-scalar-balanced-localization

For $E\subset L\subset M$, express both successive-extension routes using $s,t$ and the specified raw scalar associators. The intermediate $s^{-1}s$ and $t^{-1}t$ cancel. On the common K-flat tensor model the remaining maps both send $m\otimes l\otimes p$ to $ml\otimes p$. These are precisely the derived monoidal composition comparisons, so the equality holds in the derived category and on raw fractions by Step 3. For a fourth field and a scalar $n$ from it, every pentagon route sends $n\otimes m\otimes l\otimes p$ to $nml\otimes p$; associativity of ring multiplication proves their equality. For repeated fields the raw functor is literally the identity and these maps reduce to the multiplication unitors. Their unit equations follow by $1l=l=l1$.

Original cited statements: prop-weil-pbc-scalar-extension, lem-sfb-ringed-derived-monoidal-comparisons.

Source: literature/stacks-project/sites-cohomology.tex, Tag 0D6D (lemma-derived-pullback-composition); normalized tensor associators and units, explicit field-tower calculation.

### Original step 5 — work assigned to lem-per-rational-scalar-completion-unit-square

Write $\Lambda_{E,W}$ and $\Lambda_{L,W}$ for local derived-completion reflectors, with units $\eta_E,\eta_L$. The ringed Koszul-completion theorem supplies these reflectors and their universal unit property. They are the specified quotient completions, with the same units, by the constant/completed coefficient comparison. The sheaf $S_W$ is finite free over $R_W$ of rank $[L:E]$. The inclusion preserves the absolute value, and the DVR factorization of $\varpi_E$ in $\mathcal O_L$ is $u\varpi_L^e$ for a unit $u$ and $e\geq1$: its absolute value is strictly less than $1$. These are the hypotheses of finite-free completion transport. Consequently there is a unit-normalized natural isomorphism
$$\kappa_W:C_W\Lambda_{E,W}\xrightarrow{\sim}\Lambda_{L,W}C_W,\qquad \kappa_{W,N}C_W(\eta_{E,N})=\eta_{L,C_WN}.$$
It respects identity coefficients and successive scalar associators. This applies to ambient complexes before any constructibility restriction, and allows arbitrary positive ramification index.

Original cited statements: def-weil-l-adic-coefficient-extension, def-weil-integral-scalar-extension, lem-weil-finite-free-completed-scalar-comparison, lem-weil-pbc-constant-completion-equivalence, lem-weil-pbc-finite-free-completion-transport, lem-weil-pbc-ringed-koszul-completion-reflector.

Source: literature/stacks-project/algebraization.tex, Tag 0A0E (lemma-derived-completion-koszul), with Bhatt--Scholze Lemma 6.8.2 and the unit-normalized finite-free completion comparison.

### Original step 6 — work assigned to lem-per-rational-scalar-completion-unit-square

Put $P_{F,g}=B_{F,X'}\otimes^L_{g^{-1}B_{F,X}}g^{-1}(-)$ for $F=E,L$. Step 1 and ringed derived composition give the ordinary balanced comparison $\beta_g:C_{X'}P_{E,g}\xrightarrow{\sim}P_{L,g}C_X$. On flat-term K-flat representatives both sides flatten to $S_{X'}\otimes_{g^{-1}R_X}g^{-1}P$; $s'\otimes r'\otimes p$ maps to $s'i_{X'}(r')\otimes p$. Apply the reflected-adjunction coefficient-square construction with $F_0=P_{E,g}$, $F_1=P_{L,g}$, $C_A=C_X$, $C_B=C_{X'}$ and its ordinary comparison $\delta=\beta_g^{-1}$. The ringed derived adjunctions are the canonical ones; their right adjoints preserve complete objects and have unit-normalized completion comparisons by the ringed-pushforward completion theorem. Step 5 supplies both $\kappa_T$. Thus all hypotheses of that construction hold. The resulting comparison is
$$\widehat\beta_g=\Lambda_{L,X'}(\beta_g)\kappa_{X',P_{E,g}K}:C_{X'}\widehat P_{E,g}K\xrightarrow{\sim}\widehat P_{L,g}C_XK.$$
It is the finite-quotient-normalized scalar/pullback comparison used in the scalar-extension statement, with its indicated orientation.

Original cited statements: lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-reflected-adjunction-coefficient-squares, lem-weil-pbc-ringed-pushforward-completion, def-weil-pbc-completed-pullback, prop-weil-pbc-scalar-extension.

Source: literature/stacks-project/algebraization.tex, Tag 0A0G (lemma-pushforward-commutes-with-derived-completion); unit-normalized reflected coefficient square, with sites-cohomology Tag 0D6D.

### Original step 7 — work assigned to lem-per-rational-scalar-completion-unit-square

The comparison in Step 6 respects the actual pullback completion units, rather than only the isomorphism classes of their sources and targets. Indeed the unit equation of Step 5 and naturality of $\eta_L$ give
$$\widehat\beta_{g,K}\,C_{X'}(\gamma_{E,g,K})=\Lambda_L(\beta_{g,K})\,\eta_{L,C_{X'}P_{E,g}K}=\gamma_{L,g,C_XK}\,\beta_{g,K}.$$
Here $\gamma_F$ is exactly ordinary pullback followed by its quotient-tower completion unit, by definition of completed pullback. The constant/completed coefficient comparison identifies that quotient unit with $\eta_F$. Thus the equation uses the finite quotient projections which fixed $\widehat P$; it does not choose an unrelated isomorphism. The pullback-realization statement makes both $\gamma$'s isomorphisms on the integral objects in question, and scalar extension carries these objects into the corresponding integral category.

Original cited statements: lem-weil-pbc-finite-free-completion-transport, def-weil-pbc-completed-pullback, lem-weil-pbc-constant-completion-equivalence, lem-per-rational-realization-pullback-comparison, prop-weil-pbc-scalar-extension.

Source: literature/stacks-project/algebraization.tex, Tag 0A0E (lemma-derived-completion-koszul); naturality of the completion unit and its finite-quotient normalization.

### Original step 8 — work assigned to lem-per-rational-scalar-mixed-unit-cancellation

Compare the two mixed routes starting at $J_{L,X'}Q(C_{X'}\widehat P_{E,g}K)$. Precompose both by the isomorphism $J_{L,X'}Q(C_{X'}\gamma_{E,g,K})$. Step 7 then replaces $\widehat\beta_g$ followed by this map with $\gamma_L\beta_g$. By the specified formula for $\alpha_F$, composing $\alpha_F$ with $J_FQ(\gamma_F)$ cancels $J_FQ(\gamma_F^{-1})$ and leaves ordinary balanced localization. The inverse-image localization comparison preserves the localization units and identifies $g^{-1}E_X$ with $(g^{-1}R_X)[1/\varpi_E]$. All remaining maps are therefore maps of the common model $L_{X'}\otimes^L_{g^{-1}R_X}g^{-1}K$. Before flattening, a local tensor $l'\otimes b'\otimes p$ with $b'\in R_{X'}$ goes on either route to $l'i_{X'}(b')\otimes p$. Step 1 supplies exactly the equality of coefficient actions needed for balancing. Equality on these local generators gives equality of the chain maps on the K-flat models, hence of the derived maps. Cancel the precomposed isomorphism. This proves the square for the specific $\alpha_g$ and the scalar/pullback comparison in the statement.

Original cited statements: lem-per-rational-realization-pullback-comparison, lem-weil-pbc-localization-inverse-image-coherence, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-pur-sheaf-tensor-product, prop-weil-pbc-scalar-extension.

Source: literature/bhatt-scholze-pro-etale-topology_arXiv-1309.1198.pdf, Remark 6.8.15; explicit mixed balanced-tensor square after cancellation of the specified completion units.

### Original step 9 — work assigned to lem-per-rational-scalar-mixed-unit-cancellation

These equations also respect the ambient pullback composition comparisons and every successive scalar associator. The ordinary comparisons are the monoidal K-flat comparisons already used in Steps 2, 4 and 6. For a second geometric map, both ordinary composite routes are the same scalar-insertion and multiplication map after the canonical inverse-image compositor. The localization inverse-image isomorphisms satisfy precisely this composition equation. Reflection preserves pasting and identities for the unit-normalized coefficient squares, so the equation of Step 7 persists under both geometric composition and coefficient towers; the $\kappa$'s have the corresponding tower equation by Step 5. Substitute $\alpha_F=({\rm ordinary\ balancing})J_FQ(\gamma_F^{-1})$ in any resulting diagram: each adjacent completion-unit pair cancels, and the remaining diagram is the ordinary one just described. For three coefficient scalars its value is their product acting on the pulled-back representative, independent of parentheses. Finally Step 3 carries each equation to fraction morphisms. This proves all asserted identity, pentagon and mixed coherences without changing the coefficient category.

Original cited statements: lem-sfb-ringed-derived-monoidal-comparisons, lem-weil-pbc-reflected-adjunction-coefficient-squares, lem-weil-pbc-finite-free-completion-transport, lem-weil-pbc-localization-inverse-image-coherence, lem-per-rational-realization-pullback-comparison, prop-weil-pbc-scalar-extension.

Source: literature/stacks-project/sites-cohomology.tex, Tag 0D6D (lemma-derived-pullback-composition); completion-unit-normalized pasting and localization composition.

## Unfinished work

No part of the mandated stage-1 re-split is omitted. The three new nodes deliberately remain unsplit for separate workers, as required. Their complete original arguments are retained above. The initial dry run requested additional same-tag duplicate comparisons (the server scans sorted paths); all listed statements were opened and distinguished above. The next dry run and direct delivery are the remaining validation operations.
