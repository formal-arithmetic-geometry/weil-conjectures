# Worker report

1. Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-derived-etale-zariski-equivalence.json` (item, split; statement unchanged); `dag/nodes/sec-six-functors-basics/lem-sfb-etale-zariski-module-geometric-stalk.json` (statement-only, unsplit; no Mathlib match). There are two new nodes and zero Mathlib leaves; the second is `dag/nodes/sec-six-functors-basics/lem-sfb-ringed-site-acyclic-basis-cohomology.json` (statement-only, unsplit; no Mathlib match). `citations.json` records verbatim statements for all step citations. Full fresh search outputs are retained under `search-results/` with the command log `searches.jsonl`.
2. Attachments: none. Searched the project WeilConjectures tree for the item id and derived Zariski/etale terminology. The ordinary module/cohomology comparisons do not state this unbounded derived comparison with its pullback clauses; no complete attachment was found.
3. WANTED: none. The relevant Stacks tex sources are present.
4. The imported item had no proof. The previous attempt reused `lem-sfb-scheme-derived-etale-qcoh-comparison`. The required resumed dry run revealed that this node has since landed with a proof citing this item, so its reuse is now circular. The repaired proof below removes that dependency and proves the 071Q argument directly from smaller inputs. Existing ringed-topos comparison nodes supply derivation and coherence. No correction of the item statement was necessary. The ancestry record has `blueprint.from.node = null`; `tools/blueprint_refs.py ancestor` confirms that value. I retain the imported ancestry and unit without inventing an ancestor. The latest blueprint is main-20261023-1620 (7284bb09daf97437d544c51882b325f9c52cd345). Its current direct-image proof is `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`; the historical supporting chain remains the one recorded in this item's ancestry. No unit realization change is needed for this supporting node.
5. Nothing remains unfinished in this stage-1 split. New-node proofs intentionally remain for subsequent stage-1 work; only the assigned item is split.

## Sources and search findings

Read `spaces-perfect.tex` Tags 08H8 (lemma-epsilon-flat), 071Q (lemma-derived-quasi-coherent-small-etale-site, including the unbounded affine-basis proof), and both diagrams and proof of 08GH (remark-match-total-direct-images). Read `descent.tex` 03FH(1),(2), `sites-cohomology.tex` 0D6D (K-flat pullback composition), and the 0BKZ unbounded basis calculation. For the new node read `etale-cohomology.tex` 04HX (lemma-describe-etale-local-ring) and `sites-modules.tex` 05V5 (lemma-pullback-stalk). The new node isolates their geometric stalk formula; it does not assert exactness, faithfulness, the derived equivalence or any of the item's comparison clauses.

Whole-DAG searches included 08H8/071Q/08GH/03FH, 04HX/05V5 and label searches, plus strict henselization, geometric stalk and tensor-pullback terminology. Whole-blueprint searches were made with blueprint_refs for 071Q, quasi-coherent, derived pullback, flat morphism of ringed, Zariski etale, stalk pullback, strict henselization, module stalk, 05V5 and 04HX. No blueprint node states the new combined module-stalk formula. Existing scheme-module stalk nodes concern maps of Zariski ringed spaces, not epsilon between the two topoi. Existing constant-coefficient etale tensor-stalk nodes do not identify the varying structure-ring stalk with a strict henselization.

Both the item and new node were searched through the required msearch command using LeanFinder (two phrasings), LeanSearch, Loogle and grep. The node records contain the exact executed queries and actual outputs. All services answered. Read Mathlib Topology/Sheaves/Stalks.lean at the stalkPullback definitions and AlgebraicGeometry/Sites/AffineEtale.lean at its dense-subsite equivalence. The former is inverse image of presheaves along continuous maps, the latter compares affine and full etale sites; neither provides the epsilon tensor-stalk formula nor the unbounded quasi-coherent derived equivalence. LeanFinder's Tilde stalk results concern affine Zariski localization, without the etale structure ring. Thus neither the item nor new node is a Mathlib leaf.

## Review by NZ

The paragraphs immediately below preserve the first attempt's reading and are superseded, for steps 1–5, by the numbered repaired-proof reading later in this report. In particular the scheme-derived comparison is no longer cited.

I checked B1–B10: the new statement introduces T, epsilon, the geometric point, local ring, residue separable closure, strict henselization and module M. It cites the definitions of those notions and contains no proof or proof dependencies. Both its isomorphisms are precisely 04HX and the specialization of 05V5 to epsilon, including the structural R action and naturality; there is no finiteness or quasi-coherence assumption. Its ancestry extends the item's existing chain, and its same_as search is empty. The source is recorded by verified tags and labels. No Lean file was written and no compiler was invoked.

For step 1 I opened the exact statement of the existing scheme-derived comparison: it really asserts exactness on modules, not just on QCoh. The new node provides the stalk tensor formula on all modules. The strict-henselization faithful-flatness node assumes only a local ring and a separable closure, exactly the data supplied here. The faithful-flatness definition reflects exactness, so applying it to 0 -> M_x -> 0 proves zero detection without importing an unnamed flat-descent theorem. The module-stalk node explicitly has exactness detection clause (5). Applying exactness to the image factorization then proves faithfulness on morphisms. Existence of geometric lifts uses the algebraic-closure node, whose statement includes existence for every field. No identification of epsilon inverse image with its direct image has been made.

For step 2 the existing scheme-derived node supplies both functor restrictions and the equivalence/quasi-inverse, on unbounded objects. The ringed-projection node explicitly supplies the canonical K-injective/K-flat derived adjunction for arbitrary small ringed topoi. Restriction to full stable object classes preserves the Hom bijections. The two existing Mathlib leaves explicitly make this particular counit invertible for an equivalence left adjoint, and this particular unit invertible for a fully faithful left adjoint. These give the actual adjunction maps, rather than arbitrary isomorphisms. This is why no fresh copy of 071Q was created.

For step 3 the ordinary square node states the equality of direct images on every etale module and includes the prescribed scalar action and adjunction comparisons, without quasi-coherence or separatedness in that clause. Thus it really gives the square used in 08GH. The general ringed-derived comparison node explicitly covers composition, tensor units and ring-compatible 2-isomorphisms for unbounded module derived categories. The K-flat tensor-pullback node explicitly asserts preservation of K-flat complexes with flat terms. The QCoh pullback-component node applies to arbitrary scheme morphisms on affine source charts landing in affine target charts; those cover the source. No flatness of h is used. I distinguished the underived square from the derived comparison so that deriving it does not assume a tensor representative remains resolving without a theorem.

For step 4 the cited scheme-derived comparison explicitly includes qcqs pushforward on unbounded quasi-coherent objects. It is exactly the clause used, and the hypothesis is qcqs rather than separated. Reusing this existing clause is not a new-node relabelling: the remainder of the item still proves the stronger pullback, faithful and normalized-adjunction assertions.

For step 5 I checked the actual scalar formulas: two contractions send c tensor b tensor m to c h-sharp(b) tensor m; both triple contractions give d k-sharp(c) (kh)-sharp(b) tensor m. Unit contraction cancels insertion of 1. The maps are balanced and restriction-compatible and localize on the representatives justified in step 3. The cited ringed-derived theorem states that these are the specified comparisons, including the tensor-unit normalization. Thus the computation checks the actual identity/composition/scalar maps and does not hide a claim behind 'transport'. This step is elementary after its two cited comparison theorems.

C1–C8: every non-elementary input is a named citation, every cited statement was read, proof_deps is the union of uses, and citations.json copies verbatim the statement each citation uses. Off-unit generic tools are declared with their roles in split_report.tool_uses. The prior reading found empty proof dependencies in the scheme-derived comparison. That observation was superseded by its same-day landing: it now cites this item. The resumed dry run detected this change; the repaired proof removes the resulting cycle, as explained below. D1–D5: one genuinely smaller local module-stalk input was added; the other comparison results were already present. No new node repeats an item clause. Every non-elementary step is shorter than 2000 characters.

E1–E7: no qcqs assumption is used before direct image, and no Noetherian, proper, separated, finite-type, constant-coefficient, bounded-below or termwise-quasi-coherent hypothesis enters. For a strictly henselian local ring the new formula reduces at the closed geometric point to M_x tensor_R R = M_x. For a field it is M tensor its separable closure, not M tensor the algebraic closure in general; this distinction prevents a false version over an imperfect field. Zero modules, the empty scheme (no geometric points and the unique zero module), identity h, two and three composable maps, and zero complexes satisfy the arguments. Faithfulness uses all module sheaves, while equivalence is restricted to QCoh cohomology; these are kept distinct. No statement dispute or source error was found.

## Not duplicates

lem-sfb-etale-zariski-module-geometric-stalk vs compatible-strict-henselization-core-data: existing statement concerns Compatible strict henselization core data without final residue square; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs compatible-strict-henselization-core-existence: existing statement concerns Strict henselization ring and residue existence; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs compatible-strict-henselization-residue-square: existing statement concerns Residue maps commute for compatible strict henselizations; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs compatible-strict-henselization-residues-core: existing statement concerns Core compatible strict henselization data; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs def-coef-space-base-change: the shared four-character tag is a Kerodon tag in this existing infinity-categorical statement, not Stacks 05V5 on module stalks.

lem-sfb-etale-zariski-module-geometric-stalk vs def-per-strict-localization-point-change: existing statement concerns Canonical change of geometric point on strict localizations; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs def-weil-pbc-etale-residue-triples: existing statement is The category of étale algebras with a prime and a residue-field embedding; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs def-weil-pbc-relative-separable-closure: existing statement is Separable algebraic closure of a field inside an extension; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs def-weil-pbc-strict-henselization-point-evaluation: existing statement concerns Canonical geometric-point evaluation of the neighbourhood ring colimit; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-coef-enriched-exponential-nerve-criterion: the shared four-character tag is a Kerodon tag in this existing infinity-categorical statement, not Stacks 05V5 on module stalks.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-coef-kan-fibration-slice-nerve-equivalence: the shared four-character tag is a Kerodon tag in this existing infinity-categorical statement, not Stacks 05V5 on module stalks.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-coef-space-universal-colimits: the shared four-character tag is a Kerodon tag in this existing infinity-categorical statement, not Stacks 05V5 on module stalks.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-coef-spaces-slice-cartesian-closure: the shared four-character tag is a Kerodon tag in this existing infinity-categorical statement, not Stacks 05V5 on module stalks.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-exc-affine-strict-local-ring-comparison: existing statement concerns Affine-chart comparison of geometric and algebraic strict local rings; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-kun-strict-local-algebraic-residue-models: existing statement concerns Strict-local models with a separably closed coefficient field and algebraic residue extensions; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-per-dimension-functions-strict-localization: existing statement concerns Dimension functions restrict to strict localizations and are tested there; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-per-etale-immediate-component-criterion: existing statement is Reduced local closure and strict-local component criterion; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-per-finite-henselian-algebra-local-model: existing statement is Finite algebras over a local henselization have finite-type strict local models; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-per-finite-quotient-strict-local-invariants: existing statement concerns Strict local invariant description of a finite group quotient; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-per-log-cotangent-characteristic-quotient: existing statement is Residue logarithmic cotangent quotient and finite characteristic cokernel; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-per-log-smooth-differential-generators: existing statement is Logarithmic differential generators with finite characteristic cokernel; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-per-normal-geometric-specialization-conjugacy: existing statement is Conjugacy of generic-to-closed geometric specializations; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-per-pseudo-open-strict-local-fibre: existing statement concerns The strict-local fibre of a pseudo-open immersion; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-per-regular-boundary-divisorial-chart: existing statement is Divisorial charts of a regular strict normal crossings pair; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-per-regular-strict-local-model: existing statement concerns Compatible strict localizations of a regular morphism; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-per-strict-localization-discrete-fibres: existing statement concerns Discrete nonempty generization fibres of strict localization; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-per-trait-affine-lefschetz: existing statement is Affine Lefschetz over a strictly localized finite-type trait model; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sbc-affine-strict-henselization-structural-flat: existing statement concerns Flatness of the canonical affine strict henselization structural ring map; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sbc-etale-triples-localized-strict-henselization: existing statement concerns Residue-triple colimits as strict henselizations of prime localizations; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sbc-geometric-strict-henselization-local-presentation: existing statement concerns Geometric strict henselization over a prime localization; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sbc-regular-divisor-strict-local-limit: existing statement concerns Pointed regular strict local ind-etale limit of a divisor; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sbc-strict-hensel-divisor-quotient-presentation: existing statement concerns Algebraic strict henselization presentation of a divisor quotient; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sbc-strict-hensel-regular-divisor-quotient-domain-part: existing statement concerns Domain property of strict henselization divisor quotient; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sbc-strict-hensel-regular-divisor-quotient-noetherian: existing statement concerns Noetherianity of canonical strict henselization; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sbc-strict-hensel-regular-divisor-quotient-regular: existing statement concerns Regular domain divisor quotient of canonical strict henselization; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sbc-strict-hensel-regular-divisor-quotient-regular-part: existing statement concerns Regularity of strict henselization divisor quotient; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sbc-strict-hensel-root-finite-etale-model: existing statement concerns Finite etale extension of the punctured group-order root pullback; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sbc-strict-henselization-module-fibre-factorization: existing statement concerns Module stalk comparison and geometric-fibre restriction factorization; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sc-field-higher-direct-image-stalk: existing statement is Higher direct image stalk over a field via algebraic closure; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sc-open-curve-boundary-higher-direct-image-vanishing: existing statement is Boundary higher direct images of the multiplicative group vanish; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sc-strict-henselization-dvr: existing statement concerns Strict henselization at a point with DVR local ring; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sfb-active-root-tower-normalization-splitting: existing statement is A punctured active-root tower splitting trivializes a finite normalization after strict localization; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sfb-affine-etale-derived-module-realization: existing statement concerns derived objects or an affine derived realization; the new statement identifies degree-zero geometric structure-ring and arbitrary module stalks before any derived equivalence.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sfb-connected-proper-fibres-proper: existing statement is Properness of flat separated families with connected proper fibres; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sfb-etale-detects-perfect: existing statement is Etale pullback detects Zariski perfectness; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sfb-log-cotangent-characteristic-quotient: existing statement is Characteristic quotient of the logarithmic cotangent fibre over a trivial log field; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sfb-proper-flat-space-derived-base-change: existing statement concerns derived objects or an affine derived realization; the new statement identifies degree-zero geometric structure-ring and arbitrary module stalks before any derived equivalence.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sfb-space-coherent-derived-internal-hom: existing statement concerns derived objects or an affine derived realization; the new statement identifies degree-zero geometric structure-ring and arbitrary module stalks before any derived equivalence.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sfb-space-proper-strict-local-test: existing statement concerns Detection of properness on strict localizations of the target; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sfb-space-stalk-ideal-pullback: existing node assumes a square of square-zero closed immersions of algebraic spaces and computes ideal stalks; the new node concerns arbitrary Zariski modules under epsilon, with no such square or ideals.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sfb-space-strict-local-flatness: existing statement concerns Etale local rings on charts and flat morphisms of algebraic spaces; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-sfb-trait-specialization-etale-chart-density: existing statement is Lifting smoothing traits to etale charts and detecting density; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-affine-coordinate-strict-local-model: existing statement concerns Affine coordinate sections and their strict-local polynomial models; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-closed-immersion-strict-localization-cartesian: existing statement concerns Strict localization of a closed subscheme is the base change of the ambient strict localization; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-finite-base-strict-localization: existing statement concerns Finite base change of strict localizations along a finite morphism; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-finite-monoid-stalk-data-spreading: existing statement is Finite monoid data and equations spread from an etale stalk; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-formal-chart-geometric-regularity: existing statement is Formal toric models give log regular geometric stalks; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-gabber-strict-local-torsion-bound: existing statement concerns Gabber strict-local torsion cohomological bound; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-ind-etale-strict-local-invariance: existing statement concerns Strict localizations are invariant under ind-etale morphisms; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-log-chart-strict-local-tor: existing statement concerns Monomial quotient Tor vanishing for an arbitrary chart at a geometric point; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-nearby-closed-image: existing statement is Nearby-cycle comparison for a morphism through its closed image; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-normal-generic-arrow-transitivity: existing statement is Transitivity on generic geometric specialization arrows over a normal base; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-normality-from-completed-monoid-chart: existing statement is Normality descends from saturated completed strict-local monoid models; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-oriented-affine-neighbourhood-limit: existing statement is Affine neighbourhood pro-scheme of an oriented geometric point; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-projective-strict-local-intersection-acyclic: existing statement concerns Artin acyclicity for intersections of projective strict localizations; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-proper-geometric-specialization-lift: existing statement is Proper surjections lift prescribed geometric specializations; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-smooth-strict-local-base-model: existing statement concerns Strict-local base change model of a smooth morphism; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-smooth-strict-local-closed-fibre-model: existing statement concerns Smooth strict-local closed fibre as a strict henselization; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-snc-divisorial-log-chart: existing statement is Divisorial charts of a smooth strict normal crossings pair; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-strict-henselization-quasi-finite-ring: existing statement concerns Strict henselization under a quasi-finite local map; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-strict-local-closed-chart-map: existing statement concerns Canonical strict-local map in closed affine quotient charts; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-strict-local-comparison-ind-etale: existing statement concerns The canonical strict-local ring comparison is ind-etale on an ind-etale chart; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-tor-strict-henselian-detection: existing statement concerns Tor vanishing detected by geometric strict henselian local rings; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-trf-toric-chart-strict-local-preparation: existing statement concerns Face-localized toric chart strata and unit-compatible completed sharp charts; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-clopen-etale-neighbourhood-cofinality: existing statement is Clopen refinements are cofinal among pointed etale neighbourhoods; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-compatible-strict-henselization-residue-image: existing statement concerns Containment of compatible strict-henselization residue images; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-compatible-strict-henselization-residue-lift: existing statement concerns Lift specified residue embeddings between fixed strict henselization models; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-compatible-strict-henselization-residue-polynomial: existing statement concerns Separable polynomial for a compatible strict-henselization residue element; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-compatible-strict-henselization-residue-separability: existing statement concerns Separability of compatible strict-henselization residue elements; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-etale-algebra-residue-field-separable: existing statement is Residue field extensions of an etale algebra are finite separable; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-etale-chart-essentially-surjective: existing statement is Essential surjectivity of a compatible affine chart functor; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-etale-chart-full: existing statement is Fullness of a compatible affine chart functor; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-etale-chart-functor-construction: existing statement is Construction of the affine chart functor with ring and point formulas; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-etale-chart-residue-triples-equivalence: existing statement is Affine chart pointed neighbourhoods are equivalent to residue-field triples; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-etale-local-ring-triples: existing statement is The etale local ring at a geometric point as a colimit over etale algebras with a point; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-geometric-specialization-strict-local-lift: existing statement concerns Lifting geometric specializations to strict local schemes; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-ind-etale-affine-strict-local-base-change: existing statement concerns Strict-localization base change for an ind-etale affine map; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-p1-compatible-strict-henselization-residues: existing statement concerns Compatible strict henselizations with integral geometric residue maps; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-pointed-etale-neighbourhood-affine-shrink: existing statement is Shrinking a pointed etale neighbourhood to an affine open around the point; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-small-strict-henselization-ind-etale: existing statement concerns Ind-etale affine charts for the small representative strict henselization; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-affine-chart-ind-etale: existing statement concerns Strict henselization is ind-etale over an affine chart; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-chart-maximal-ideal: existing statement concerns Maximal ideal and structural map in an affine strict-henselization chart; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-closed-fiber: existing statement concerns The singleton distinguished fibre of a strict henselization; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-closed-fiber-backward: existing statement concerns The closed point lies over the distinguished point; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-closed-fiber-forward: existing statement concerns No non-closed point in the distinguished fibre; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-functoriality: existing statement concerns Strict henselizations at a geometric point and their functoriality; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-local-structure: existing statement concerns Local structure of the chosen strict-henselization colimit; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-point-evaluation-comparison: existing statement concerns Affine-chart colimit comparison preserves pointed evaluation; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-point-evaluation-image: existing statement concerns Pointed evaluation lands in the relative separable closure; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-point-evaluation-pointed: existing statement concerns Pointed evaluation coprojection equation; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-point-evaluation-properties: existing statement concerns Surjectivity of canonical pointed evaluation; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-pointed-map: existing statement concerns Surjective pointed map from the neighbourhood colimit to the relative separable closure; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-pointed-map-core: existing statement concerns Residue map with surjective kernel; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-pointed-map-factorization: existing statement concerns Pointed factorization for the residue map; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-residue-separable-model: existing statement concerns Separable residue extension of a strict-henselization model; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-small-closed-fiber-comparison: existing statement concerns Canonical strict-henselization comparison preserves the structural map and closed fibre; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-henselization-triples: existing statement concerns The colimit over etale algebras with a point and a residue embedding is strictly henselian; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-local-base-affine: existing statement concerns Affineness of a geometric strict-local base; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-weil-pbc-strict-local-base-ind-etale: existing statement concerns Canonical ind-etale coordinate ring of a geometric strict-local base; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-wf-geometric-triples-colimit-comparison: existing statement is Recognition of local ind-etale algebras by geometric neighbourhood colimits; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lem-wf-strict-henselization-finite-lifts: existing statement concerns Strict henselization as finite local lifts over the henselization; it does not state the geometric stalk of epsilon pullback of every Zariski module, naturally as an R^sh-module.

lem-sfb-etale-zariski-module-geometric-stalk vs lemma-weil-pbc-affine-neighbourhood-cofinal: existing statement is Affine pointed neighbourhoods are cofinal; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs lemma-weil-pbc-p1-exchange-geometric-stalk: existing statement is Exchange on a geometric stalk; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs new-lem-sbc-etale-triples-prime-localization-component-extension-aux-model: existing statement is Affine model data for component extension; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs new-lem-sbc-etale-triples-prime-localization-component-extension-unique-aux-compatible: existing statement is Existence of a compatible descended affine model; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs split-etale-chart-functor: existing statement is Affine chart residue triples indexing categories admit an equivalence; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs split-etale-chart-ring-iso: existing statement is Affine chart equivalence carries global sections to triple rings; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs thm-exc-curve-open-constructible-general: existing statement is Open direct-image constructibility on arbitrary curves; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

lem-sfb-etale-zariski-module-geometric-stalk vs thm-exc-curve-open-dimension-general: existing statement is Open direct-image dimension on arbitrary curves; its hypotheses/conclusion do not give the Zariski-to-etale epsilon tensor-stalk formula for an arbitrary module.

The ordinary scheme QCoh equivalence `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence`, ordinary functor square `lem-trf-zariski-etale-functor-comparison-square`, and affine derived realization `lem-sfb-affine-etale-derived-module-realization` were also checked: the first two are reused where needed, and the last is not a substitute for arbitrary module stalks on any scheme. The new statement is neither elementary from these nor a clause of the item: it supplies the strict-henselization tensor identification used to prove faithfulness.


lem-sfb-ringed-site-acyclic-basis-cohomology vs lem-sfb-affine-etale-derived-module-realization: the existing statement identifies the derived category of modules over one affine coordinate ring with etale quasi-coherent derived objects and proves tensor compatibility; it does not state acyclic-basis hypercohomology for arbitrary ringed sites.

lem-sfb-ringed-site-acyclic-basis-cohomology vs lem-sfb-proper-flat-space-derived-base-change: the existing statement is derived base change and perfectness for proper flat algebraic spaces; it neither states nor generalizes ringed-site cohomology from cohomology-sheaf acyclicity.

lem-sfb-ringed-site-acyclic-basis-cohomology vs lem-sfb-scheme-derived-etale-qcoh-comparison: the existing statement is a specific scheme Zariski/etale equivalence and qcqs pushforward comparison, and its current proof depends on this item; the new node is the independent general 0BKZ ringed-site acyclic-basis theorem.

lem-sfb-ringed-site-acyclic-basis-cohomology vs lem-sfb-space-affine-global-trace-adjunction: the existing statement concerns global sections of an affine algebraic space and its duality/trace adjunction; the new node concerns arbitrary ringed sites, arbitrary unbounded module complexes, and an acyclic covering basis.

## Repaired proof: review by NZ

The required first dry run after resumption exited with a two-node cycle: the item cited the scheme-derived comparison, but that existing node had now landed with a proof citing the item. I read its complete current statement, proof and maintainer review. I changed only the sandbox item, added the missing smaller 0BKZ input, and preserved the existing stalk node, citations, searches and historical report. The item statement remains byte-for-byte unchanged. The repaired proof uses no 071Q-equivalence node and no direct-image-comparison node that depends on the item.

I reread spaces-perfect.tex 08H8 in full, 071Q in full, both diagrams and the proof of 08GH, and sites-cohomology.tex 0BKZ (lemma-cohomology-over-U-trivial), including its bounded-below truncations, derived-limit short exact sequence, eventual constancy and canonical edge maps. This last statement is the new general ringed-site lemma. Its source makes no constant-ring or boundedness assumption. The existing lem-kun-0bkz uses D(X_Et), whose definition is the abelian/constant-coefficient category, so applying it directly to a complex of structure modules would require a separate unbounded scalar-forgetting theorem. The new node states the actual ringed-site source instead. I searched the whole DAG by 0BKZ, the label, acyclic/basis terminology, and the blueprint by the same tag and terminology. The affine Zariski basis lemmas require term and differential-cokernel acyclicity; those are extra hypotheses unavailable for a general representative here. They do not subsume the new statement. The new node has no proof, no proof dependencies, an explicit covering-basis hypothesis, module-derived vanishing hypotheses, the canonical natural comparison, ancestry and all recorded search kinds. Its searches reuse the retained basis search outputs and logs: generic H, cohomologyPresheaf and K-injective/localization hits do not provide this result.

1. Exactness: the new stalk statement identifies all module stalks, without QCoh. The strict-henselization statement gives faithful flatness for exactly the local ring and separable residue closure in that statement. The faithful-flat definition supplies tensor exactness. The Zariski module-stalk statement supplies exactness of the input stalk sequence. The two geometric-stalk statements supply exactness and conservativity only for abelian sheaves; I therefore explicitly use the existing exact faithful module-forgetting statement, rather than silently treating their coefficients as structure modules. Vanishing of the homology sheaf is then a few-line kernel/image argument. I checked every cited statement and quoted it in citations.json.
2. Zero detection and faithfulness: the stalk formula and faithful-flatness reflection give M_x=0. Existence of geometric lifts is supplied by the algebraic-closure definition's existence clause. The Zariski stalk statement detects exactness of 0 -> M -> 0. Exactness from step 1 preserves images, so vanishing of the pulled-back difference of two maps forces their equality. No separate descent theorem is hidden here.
3. Derived adjunction and the left restriction: the ringed-projection node really supplies the unbounded canonical derived adjunction on small ringed sites. The ordinary QCoh equivalence really identifies epsilon tensor pullback and restriction and their ordinary units and counits. Exact pullback commutes with kernels, cokernels and hence cohomology; it preserves the QCoh class on cohomology, with no assertion on the terms of a representative.
4. Basis calculation: affine opens of each etale source scheme give a covering basis by the affine-opens statement. The definition of space QCoh says restriction to any etale scheme object is a quasi-coherent associated module. The ordinary QCoh equivalence and etale slice equivalence identify it with the input of the affine-etale vanishing node. That node gives abelian vanishing; the ringed-site module/abelian evaluation-slice comparison gives precisely the module-derived version, with enough injectives ensured by the K-injective-existence statement (Grothendieck category). The new 0BKZ node then gives the unbounded basis calculation. I checked all these hypotheses; the proof never infers convergence of an unbounded spectral sequence just from the bounded-below one.
5. Derived restriction: on a K-injective I, restriction is termwise epsilon_*I, representing R epsilon_*E. The three-line adjunction proof that it remains K-injective uses the definition of K-injective and exactness from step 1; adjunction carries every homotopy term, so no injectivity assertion is assumed. The exact module-presheaf-sheafification node states both sectionwise homology and exact sheafification. Applying it to the presheaf W -> I(W), and using step 4 on the affine-open basis, gives H^q(R epsilon_*E)=epsilon_*H^q(E). The ordinary equivalence makes the latter QCoh. The affine basis means no affine-intersection separatedness hypothesis is needed.
6. The counit map: I checked that the edge identifications in step 4 are the truncation/cycle comparisons used in 071Q, so the cohomology of the derived counit is the ordinary counit, evaluated by restriction and scalar multiplication. The ordinary equivalence states that this actual counit is invertible. The triangle identity then makes epsilon^* of the derived unit invertible. Exactness and zero detection from steps 1–2 reflect zero cohomology, so reflect quasi-isomorphisms and make the unit itself invertible. The canonical derived adjunction is therefore the equivalence adjunction. This replaces the old application of an already-existing derived equivalence and is not a new node restating the item.
7. Pullback comparison: this retains the earlier explicit ring-compatible square and derivation by the generic ringed-derived monoidal/composition theorem. I reread the ordinary square's statement: its all-module clause has no qcqs or separated hypothesis. The K-flat tensor-pullback statement says pullbacks preserve K-flat flat-term representatives. The affine-local derived-pullback QCoh component says exactly that cohomology is QCoh on every affine source chart mapping into an affine target chart. These charts cover the source. Thus the comparison is on the required full subcategories for arbitrary h.
8. Direct-image preservation: the Zariski QCoh theorem has exactly a qcqs morphism hypothesis, not qcqs schemes. The etale QCoh/right-adjoint node does assume qcqs source and target spaces, so I apply it only after restricting to affine W in the target. The qcqs permanence statement implies h^{-1}W is qcqs. The etale chart-calculus statement supplies restriction to that open and locality of QCoh cohomology. These three statements therefore cover arbitrary target T; no false inference from qcqs h to globally qcqs T was made.
9. Direct-image map: the generic ringed-derived theorem gives the comparison Psi between R epsilon_* R h_et,* and R h_* R epsilon_* and identifies composite adjunctions. I wrote the full unit-Psi^{-1}-counit composite. Every arrow is invertible by steps 6 and 8 and that theorem, and its normalization follows from its adjunction-compatibility clause. This supplies the actual 08GH comparison, rather than unspecified isomorphisms of functors.
10. Scalar normalization: the retained elementary tensor calculation now references step 7. Both parenthesizations contract a triple tensor to the same product by the ring-map and associativity identities; unit contraction cancels insertion of 1. These formulas preserve balancing and restrictions. The existing generic comparison theorem states that it uses these ordinary comparisons and their tensor unit. Hence the local computation checks identity, composition, structure module and scalar insertion as required.

For the new 0BKZ node I tested a terminal ringed site (evaluation is exact, so the conclusion is ordinary complex cohomology), zero K, an empty site, a sheaf placed in a nonzero degree, and unbounded sums of shifts on an affine scheme. Its covering-basis assumption is essential and is retained. For the stalk node I reread 04HX and 05V5 in full and retained the imperfect-field distinction: the residue extension is the separable closure, not an arbitrary algebraic closure. For the item I tested empty T, zero modules and complexes, identity h, non-qc T and non-separated qcqs h; the direct-image proof deliberately restricts to affine target charts. Every repaired non-elementary step has fewer than 2000 characters. No source error or statement dispute was found. The long prior duplicate-pair list is retained, and the added new-node pairs follow below. No SGA source, Lean writing, compiler, Lake or build is used.

## Not duplicates

lem-sfb-ringed-site-acyclic-basis-cohomology vs lem-kun-0bkz: the existing statement assumes the constant-coefficient/abelian D(X_Et); the new node is the arbitrary-ringed-site module statement, with its actual varying structure ring and canonical edge maps.

lem-sfb-ringed-site-acyclic-basis-cohomology vs lem-kun-0f1g: the existing statement concerns Detection of objects supported at closed points; it does not assert the arbitrary-ringed-site acyclic-basis evaluation theorem under only cohomology-sheaf acyclicity.

lem-sfb-ringed-site-acyclic-basis-cohomology vs lem-kun-site-rgamma-derived-limit: the existing statement concerns Derived sections on a ringed site preserve derived limits; it does not assert the arbitrary-ringed-site acyclic-basis evaluation theorem under only cohomology-sheaf acyclicity.

lem-sfb-ringed-site-acyclic-basis-cohomology vs lem-kun-site-truncation-derived-limit: the existing statement concerns Reconstruction from lower truncations on a ringed site; it does not assert the arbitrary-ringed-site acyclic-basis evaluation theorem under only cohomology-sheaf acyclicity.

lem-sfb-ringed-site-acyclic-basis-cohomology vs lem-sc-affine-basis-sections-derived-unit: the existing statement is on a Zariski affine scheme basis and assumes acyclicity of the terms and differential cokernels in addition to homology; the new node assumes only cohomology-sheaf acyclicity on an arbitrary ringed-site covering basis.

lem-sfb-ringed-site-acyclic-basis-cohomology vs lem-sc-affine-basis-acyclic-sections-preserves-homology: the existing statement concerns underived evaluation and additionally assumes differential-cokernel acyclicity on a Zariski basis; it does not compute unbounded ringed-site derived evaluation from cohomology-sheaf vanishing alone.

The final local citation audit noticed an additional live edit to lem-sfb-qcqs-space-pushforward-right-adjoint: its statement now explicitly names the universe and module-functor conventions. Its qcqs hypotheses and preservation conclusion are unchanged. I reread it and narrowed the step-8 quote to the unchanged preservation clause. The complete cited closure was checked again and does not reach the item.
