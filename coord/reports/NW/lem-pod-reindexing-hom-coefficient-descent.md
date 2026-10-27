# Stage-1 repair: lem-pod-reindexing-hom-coefficient-descent

1. Files written: `dag/nodes/sec-poincare-duality/lem-pod-reindexing-hom-coefficient-descent.json` (split; repaired proof, statement clarification retained), `dag/nodes/sec-poincare-duality/lem-pod-specified-hom-scalar-evaluation.json` (statement, unsplit; no Mathlib match), `report.md`, and `citations.json`. **1 new node, 0 Mathlib leaves**. Sandbox-only helper files and the authentic search log are retained.
2. Attachments: none. The exact blueprint tag and concept searches under `lean/WeilConjectures/` give no declaration stating the item or the new pin. The existing bounded-finite-cohomology `tensorBijective_fieldExtendScalars` is a field-module Hom-group statement, not a completed pro-etale internal-Hom operation normalization. Generic chain scalar-Hom maps do not identify the specified completed comparison.
3. WANTED: none. Sources are present. The proof is explicitly agent-written; Stacks is used for its actual adjunction, not as a claim that Stacks states the completed normalization.
4. The imported item left $c^0$ undefined. The accepted notation repair from returned head `561c2d7ca22` is retained, with its two sibling statement dependencies. The current read-clone item is still unsplit. Its non-proof metadata and extraction provenance are preserved; the delivery tool reconstructs the commit against current server main. The initial inherited dry run exited successfully at `ba8bf2f443c`; this only verified the mechanical gates, and did not discharge the substantive return.
5. Nothing remains unfinished in this one-level split. The new normalization lemma is deliberately statement-only and joins the queue; it is not represented as proved or attached.

## Statement clarification — STATEMENT-DISPUTED

The inherited statement used “the integral $c^0$” without defining it. The retained correction names the ambient map $FH_R(M,N)\cong H_R(FM,FN)$ from `lem-pod-reindexing-hom-resolution-model` and its constructible-Hom restriction from `lem-pod-reindexing-completed-evaluation-reflection`, adding both to `stmt_deps`. The return explicitly accepted this clarification. The repair makes no further statement change and adds no hypotheses to the item.

## Repair of the return

The returned proof used the construction inside the proof of `lem-pur-integral-operations-scalar-extension` as though its statement pinned the comparisons. It does not: tower-compatible unit rescalings can satisfy that statement. Steps 7–9 now identify the actual tensor, pullback and Hom comparisons from statements which explicitly fix their maps. The final common-stage conjugation uses those pinned maps.

The minor Step 2 fault is repaired by inserting both normalized basis maps $a_H$ and $a_N$ (the coordinates lemma calls the latter $a_Q$). The displayed equation is now exactly $\beta U(\gamma)a_H\iota_i=H(M,a_N\iota_i)$.

Returned Step 4 incorrectly used equality after $U$ to deduce equality before $U$. It now compares the two $S_X$-linear transposes in $D(S_X)$ itself and invokes the tensor-Hom adjunction bijection there. The local formula is used only to prove equality of the actual representative maps on their total-complex summands, with fixed localized augmentations; it is not detection of derived morphisms by sections or by restriction of scalars.

Returned Step 5 omitted the tensor-tower assumption. The repaired step first invokes `lem-sfb-scalar-hom-tensor-coherence` for the simultaneous normalized scalar/tensor models of the tensor-data lemma, then applies the conditional scalar-Hom tower theorem. Its identity substitution is included.

The completed tensor pin is the existing `lem-pur-normalized-scalar-comparison-realization`. The pullback pins are the existing `lem-weil-specified-pullback-comparison-alpha` and `lem-weil-isomorphism-comparison-scalar-extension`. Before using the latter, Step 8 proves that the completion/reindexing sibling's pullback identification is precisely `def-weil-inverse-image-pullback-comparison(b)`'s kappa: both have the same map $(0,(F(z\bmod\varpi^n)\otimes1)_n)$ on the same K-flat quotient tower and the same inverse resolution augmentation. Both Roos coordinates are fixed. It then writes the supplied alpha/kappa/beta square explicitly.

The existing `lem-zl-specified-hom-scalar-evaluation` requires separated finite-type schemes over an algebraic closure of a finite field, so it cannot be applied to the item's arbitrary schemes. The new node is the precise missing Hom pin on arbitrary schemes, on the item's constructible-Hom domain. It specifies the existing chain-Hom construction and states its equality with gamma after the canonical chi maps. It contains no reindexing, rationalization or common-field descent conclusion, and is not a renamed clause asserting that the entire item holds.

## Sources and route

I read `dag/chapters/sec-poincare-duality.json`, `dag/units/sk-def-weil.json`, and the current `main-20261015` proof of `prop-pod-dual-tate-data-compatibility`, especially Step 5. The unit supplies strict Weil/contragredient operations; the item's task is the generic coefficient transport underlying that step, not a new duality or purity theorem. The original ancestor and precise `blueprint.from.place` already identify this clause and are preserved. The common-stage/rational source definitions were read in `literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sf-operations/def-weil-rationalization-karoubi.md` and `def-weil-algebraically-closed-coefficients.md`.

I also read Stacks Tag **08J9**, `sites-cohomology.tex`, label `lemma-internal-hom` (line 8896), including the K-flat/K-injective argument for the derived tensor-Hom adjunction, and Tag **0GMX**, `sites-modules.tex`, label `remark-pullback-internal-hom` (line 3787), including the sectionwise pullback-Hom formula. These are the adjunction and underived comparison sources; neither is misrepresented as a verbatim finite-free completed coefficient theorem. The additional finite-free, completion, and descent arguments are recorded as an agent elaboration. No SGA source is used.

Whole-blueprint searches were run for `finite free`, `reindexing`, and `Hom coefficient`, in addition to searching the DAG and Lean. The blueprint scalar-six-tensor-hom/coefficient-comparisons nodes cover broader operation packages or restricted constructible/Tor domains, not this entire reindexing and localized-arrow statement. The finer ringed finite-free Hom, coordinate, and completion interfaces already exist, so no duplicate nodes are introduced. `blueprint.same_as` is `[]`. The ancestor command identifies `prop-pod-dual-tate-data-compatibility` as expected. This item is not a unit's key statement, so no unit record is changed.

## Mathlib searches

The inherited five search records are retained. I ran five additional searches through the required `batch2/msearch.py` command: LeanSearch, Loogle, grep, and two different LeanFinder phrasings. All returned successfully and are logged exactly in `searches.jsonl`; the appended records use the same tool and query strings. I read the actual results. They concern free sheaves, ordinary ModuleCat extension/restriction, Ext maps and light-condensed internal Hom. None states the normalized unbounded derived ringed-site comparison, much less its completed/rational/common-stage equations. The grep gave only trivial-square-zero ring-map and ring-flatness references. The ModuleCat change-of-rings source was inspected; it is ordinary modules. These are useful building blocks, not a one-line specialization proving this item. No query that did not run is recorded.


For this repair I reread current statements of every cited node, the main-20261015 Step 5, and Stacks 08J9 (`sites-cohomology.tex`, `lemma-internal-hom`, lines 8896–8936) and 0GMX (`sites-modules.tex`, `remark-pullback-internal-hom`, lines 3787–3824). The new node's source is main-20261015 Step 5's coefficient construction, expanded as an agent normalization bridge; 08J9 provides only its underlying adjunction. Its statement is not quoted from the proof of the old scalar lemma: the new node exposes exactly the extra theorem now needed as a dependency. No SGA source is used.

For the new node I ran five further logged searches: LeanFinder with the specified completed-comparison phrasing, Loogle `SheafOfModules, CategoryTheory.MonoidalClosed`, grep for internal-Hom/completion/scalar/evaluation, LeanSearch for conjugation by completion maps, and a second LeanFinder phrasing using the chain formula. All five returned successfully. I read all hits: Gamma-Spec adjunctions and light-condensed points do not concern completed coefficient operations; generic `ihom.ev` is an evaluation definition; ordinary ModuleCat scalar adjunctions lack derived sheaf completion; `AdicCompletion.ofTensorProduct` and its naturality concern ordinary modules. The actual `AdicCompletion/AsTensorProduct.lean` source, including lines 14–80, confirms this. No match is a one-line specialization of the new pin. Every new search record has the exact tool/query text and actual hit summary from the log.

## Review by NW

I checked every return fault against the current source statements, not just against the old prose. Steps 1 and 3 retain the accepted ambient finite-free proof: `lem-weil-finite-free-completed-scalar-comparison` supplies finite freeness and the canonical chi, `lem-sf-ringed-finite-free-hom-base-change` states its evaluation transpose and invertibility for arbitrary unbounded inputs, and the representative/tensor-data statements give the actual evaluation and scalar tensor formulas. No perfectness is transferred from the coefficient module to M.

Step 2 uses `lem-sfb-dc-hom-scalar-adjunction` only for its evaluation-normalized beta, and the coordinates statement for precisely its normalized a_H/a_N equation. Step 4 uses the resolution/evaluation siblings for c and its evaluation equation, the scalar-tensor-K-flat statement for b, and finite-free-Hom/representative statements for gamma and its transpose. Expanding these definitions produces identical S-linear representative pairings. The adjunction is bijective on derived Hom sets. Conservativity of U is irrelevant to this equality proof.

Step 5 uses tensor-data to choose the normalized tensor maps, tensor-coherence to discharge exactly the conditional tower hypothesis, and scalar-Hom-tower for its displayed equation and identity value. It applies on the same small pro-etale sites, with the actual balanced associators. Finite freeness gives invertibility separately, including ramified towers.

Step 6 retains the completion-exchange hypothesis checks accepted by the return: the DVR factorization has positive exponent, principal-Koszul strict replacement gives injectivity and the exact quotients for E and L, and the countable-product statement applies to R-modules, S-modules and constant-Z modules (abelian sheaves). Its cited exchange states epsilon T(eta)=eta T, and ambient-operation-models states the unit-preserving identification with completed tensor. These alone no longer claim to pin theta.

Step 7 additionally uses normalized-scalar-realization, with f=id_W, whose statement pins the actual tensor comparison as realization of the entire-system balanced scalar tensor map. The quotient association respects the augmentation, including zero shifted coordinate. When comparing with completion exchange the arithmetic-subsequence quasi-isomorphisms are inserted and inverted; equal powers of the two uniformizers are never equated. The written tensor-unit equation is thus for the specified theta, not an arbitrary completion isomorphism.

Step 8 compares the two definitions on the same representative, proving equality of the cone maps before localization. The completion-unit-tensor sibling states the quotient-unit identification and the specified pullback tensor comparison; the kappa definition gives its full coordinate formula. The alpha-pin statement gives the actual chosen scalar arrow, and the isomorphism-comparison-scalar statement gives precisely alpha C(kappa)=kappa beta and beta's chi/b formula. All of its completeness and constructibility hypotheses hold on the stated domain.

Step 9 uses the new node only for its displayed theta-Hom/chi/gamma equality on M,N with constructible Hom, separately on X and Y. This is where the old finite-type restriction is removed; it is not silently ignored. Reindexing preserves the domain by completed-evaluation-reflection, and scalar base change preserves it because gamma and chi identify the output with scalar extension of the original constructible Hom (the operation scalar lemma states constructible preservation). The same reflection statement supplies the two actual Hom bijections with complete target; hence precomposition with the unit proves the completed evaluation and transpose squares. In pullback coordinates c is explicitly H(kappa_M inverse,kappa_N)c^0 kappa_H inverse. Substitution of the pinned alpha, theta-Hom and tensor-unit equations gives the comparisons that the common-stage operation definition actually uses.

Steps 10–12 retain the raw localization argument: rationalization has the same objects and Hom tensor E, both variables respect balancing, and naturality/evaluation terms have coefficient lambda_i nu_j. Transposition is linear. The signed-shift, inverse and scheme-composition equations come from the completed-reflection statement. The scalar comparisons now come from Steps 7–9; the operation-scalar statement is used here only for its explicitly asserted identity and tower laws. Step 12 uses the prescribed scalar-extension morphism formula from rationalization, so torsion killed on rationalization causes no problem.

Steps 13–14 use exactly the arrow-colimit and equality-after-enlargement criterion in algebraically-closed-coefficients, the operation definition's conjugation formulas, and the stated tower equations. Every finite diagram can be put over a compositum; its equality is proved there before passing to the colimit. Thus neither equality detection by scalar extension nor faithfulness of the transition functors is assumed.

For the new node I checked its statement against the actual chain-Hom construction and 08J9's representative adjunction. The coefficient algebra is finite free for arbitrary schemes; flat-term K-flat and K-injective representatives live in the ambient categories. The output and both inputs are complete by the explicitly assumed constructible-complete domain, so each chi is invertible. It imposes no separatedness, no finite-type condition and no finite-field base. Its data are the existing theta construction, and its conclusion is the missing equality with gamma, not a definition by fiat or an assertion about arbitrary choices of theta.

I tested identity g and E=L (all comparisons reduce under multiplication/completeness unitors), zero complexes, the empty scheme, rank-one extension, negative Hom shifts, torsion arrows annihilated by localization, and ramified extensions with e>1. The new pin is meaningful in all these cases. Arbitrary pairs are never declared closed under constructible Hom. Every proof step is below 2000 characters; the largest is the explicit S-linear transpose calculation, rather than a hidden comparison lemma. The item and new node have the correct ancestor/via/same_as fields. Proof dependencies equal the union of uses, all statement quotes in citations.json are verbatim, and graph traversal found no dependency path back to the item. Generic off-unit tools are declared with their specific roles. No Lean files or compiler/build tools are used.

## Not duplicates

The new node pins the specified completed coefficient-Hom comparison through chi on arbitrary schemes. Existing ambient scalar-Hom, adjunction and tower nodes are reused; they do not identify this chosen completed arrow. Existing tensor/pullback pins are reused and no replacement nodes are introduced. The following records every existing node sharing Stacks 08J9 (often merely as background); names below describe each existing statement's distinct subject.

lem-pod-specified-hom-scalar-evaluation vs lem-per-adic-closed-constructible: the existing statement concerns “Closed tensor structure and internal-Hom finiteness for adic constructible complexes”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-per-dual-lisse-tensor: the existing statement concerns “Dual of a lisse tensor”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-per-ind-etale-derived-hom-continuity: the existing statement concerns “Derived sections and Hom along affine etale limits”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-per-localization-dual-boundary-pairing: the existing statement concerns “The dual localization boundary transposes to evaluation followed by the support boundary”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-per-potential-finite-bidual-comparison: the existing statement concerns “Finite direct image and evaluation biduality for potential complexes”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-per-proper-potential-bidual-comparison: the existing statement concerns “Proper direct image and relative potential evaluation biduality”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-per-relative-bidual-triangles: the existing statement concerns “Relative evaluation biduality respects distinguished triangles”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-per-trait-dualizing-scalar-restriction: the existing statement concerns “Scalar endomorphisms of the relative dualizing complex over a complete trait”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pod-reindexing-evaluation-shift-composition: the existing statement concerns “Evaluation normalization and signed coherence of the reindexed Hom complex”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pod-reindexing-system-hom-reduction-square: the existing statement concerns “Reindexing internal Hom on actual derived coefficient systems and its reduction square”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-augmented-cech-tensor-pullback: the existing statement concerns “Augmented Cech tensor actions commute with derived inverse image”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-integral-constructible-hom-sums: the existing statement concerns “Derived Hom groups from a constructible integral complex commute with countable bounded-below sums”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-kflat-rhom-currying: the existing statement concerns “Evaluation-normalized natural currying on K-flat representatives”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-ringed-complete-element-multiplication: the existing statement concerns “Multiples of complete local sections are complete”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-ringed-derived-complete-elements-ideal: the existing statement concerns “Vanishing localizations form an ideal”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-ringed-equivalence-module-hom: the existing statement concerns “Module and closed Hom transport under a ringed equivalence”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-ringed-internal-hom-exact-restriction: the existing statement concerns “Derived internal Hom calculus on small ringed sites”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-ringed-localization-complex-models: the existing statement concerns “The unchanged localization complex models and K-flat coefficient certificate”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-ringed-localization-natural-currying: the existing statement concerns “Natural evaluation-normalized currying for bounded localization complexes”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-ringed-localization-rhom-calculus: the existing statement concerns “Derived internal Hom and localization of a bounded localization complex”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-ringed-model-currying: the existing statement concerns “Currying with a specified K-flat coefficient sheaf”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-ringed-model-restriction: the existing statement concerns “Canonical coefficient and tensor-complex transports along a further slice”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-coef-ringed-tensor-hom-model: the existing statement concerns “Canonical closed tensor-Hom representative model on a ringed site”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-sf-finite-coefficient-site-chain-tensor: the existing statement concerns “Canonical finite coefficient site comparison on total tensor complexes”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-sf-finite-coefficient-site-hom-arrow: the existing statement concerns “Canonical finite coefficient site internal-Hom arrow”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-sf-finite-coefficient-site-scalar-arrow: the existing statement concerns “Canonical finite coefficient site scalar comparison”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-sf-site-hom-restriction-comparison: the existing statement concerns “Canonical site Hom restriction maps and comparison square”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-trf-dualizing-complex: the existing statement concerns “Dualizing complex and Verdier dual”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-bidual-evaluation-shift-one: the existing statement concerns “Degree-one signed shift compatibility of coefficient evaluation”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-derived-system-evaluation-calculus: the existing statement concerns “Coherent derived reduction, limit adjunction and fiberwise evaluation”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-enriched-sequence-projection-formula: the existing statement concerns “Uncurried finite projections of the enriched sequence adjunction”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-etale-hom-transpose-exact: the existing statement concerns “Reversed exactness of the specified étale Hom transpose”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-finite-adjunction-transition: the existing statement concerns “Finite-level adjunction transition compatibility”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-finite-hom-domain-calculus: the existing statement concerns “Finite coefficient tensor domains and ambient evaluation transpose”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-finite-point-reconstructed-evaluation-square: the existing statement concerns “Signed evaluation square for reconstructed finite-point Hom”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-hom-tower-scalar-model: the existing statement concerns “Hom-tower representative and scalar-adjunction comparison”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-integral-finite-extension: the existing statement concerns “Integral duality and a finite extension of coefficient fields”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-pairing-system-dinaturality: the existing statement concerns “Dinaturality of the system projection-evaluation word”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-ringed-pullback-hom-evaluation-comparison: the existing statement concerns “Evaluation-defined Hom comparison for ringed pullback”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-scalar-hom-zero-compatibility: the existing statement concerns “Degree-zero normalization of scalar internal Hom”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-signed-derived-internal-hom-exact: the existing statement concerns “Normalized exactness of contravariant internal derived Hom”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-signed-single-dual-restriction: the existing statement concerns “Normalized slice comparison for a single coefficient dual”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-system-adjunction-transpose-coherence: the existing statement concerns “Resolution-normalized tensor transposes and mates of system adjunctions”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-system-enriched-projection-adjunction: the existing statement concerns “Enriched system adjunction from the actual counit and projection”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-system-internal-hom-representability: the existing statement concerns “Sequence-site internal Hom and punctual representation of mapping systems”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-system-projection-evaluation: the existing statement concerns “Projection-evaluation word on ringed coefficient systems”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-coef-tower-natural-currying: the existing statement concerns “Natural tower currying isomorphism”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pod-completed-hom-scalar-transpose: the existing statement is restricted to perfect point models over the algebraic closure of a finite field; the new node allows arbitrary schemes and all stated constructible-Hom pairs.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-admissible-hom-substitution: the existing statement concerns “Signed and coefficient-natural substitution in actual derived internal Hom”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-coefficient-dual-model-transport: the existing statement concerns “Restriction and finite-field transport of coefficient dual models”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-derived-hom-substitution-coherence: the existing statement concerns “Derived internal-Hom substitution with coefficient and signed-shift comparisons”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-etale-generic-evaluation-coherence: the existing statement concerns “Evaluation coherence of generic stratum-Hom exchange”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-etale-generic-exchange-algclosed: the existing statement concerns “Geometric-generic closed-support and internal-Hom exchange over arbitrary algebraically closed fields”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-etale-generic-hom-triangle: the existing statement concerns “Internal-Hom comparison respects the finite stratification triangles”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-etale-generic-stratum-mate: the existing statement concerns “Canonical tensor-Hom adjunction formula for an immersion”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-etale-twisted-bidual-transport: the existing statement concerns “Transport of evaluation biduality across an invertible dualizing twist”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-even-line-hom-shift: the existing statement concerns “Signed first-variable shift compatibility of the internal-Hom line comparison”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-finite-free-comparison-isomorphism-naturality: the existing statement concerns “Scheme-isomorphism naturality of finite-free counit and evaluation coefficient maps”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-general-hom-comparison-cocycles: the existing statement concerns “General hom comparison cocycles”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-lisse-flat-hom-site-comparison: the existing statement concerns “Local finite-flat lisse calculation for the evaluation Hom comparison”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-rational-slice-completed-evaluation: the existing statement concerns “Restriction compatibility for completed rational evaluation”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-rational-thick-evaluation: the existing statement concerns “Triangulated closure of the rational evaluation class”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-ringed-derived-closed-symmetric-monoidal: the existing statement concerns “The derived category of a ringed site is closed symmetric monoidal”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-ringed-derived-tensor-hom-adjunction: the existing statement concerns “Evaluation-normalized adjunction for the fixed native derived tensor”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-ringed-finite-free-hom-base-change: the existing statement is the ordinary ambient evaluation-transpose isomorphism gamma, with no identification of the specified completed theta via chi.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-ringed-finite-free-hom-coordinates: the existing statement concerns “Finite-free basis inclusions and normalized scalar-Hom transpose”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-ringed-finite-free-hom-transpose: the existing statement concerns “Finite-free evaluation transpose is invertible”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-ringed-finite-free-tensor-complex: the existing statement concerns “Actual scalar tensor comparison on complexes and K-flat preservation”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-ringed-finite-free-tensor-data: the existing statement concerns “Strong scalar tensor comparison for supplied normalized derived models”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-ringed-forget-tensor-transposition: the existing statement concerns “Normalized derived tensor and transposition under ringed forgetting”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-ringed-rhom-derived-complete: the existing statement concerns “Derived internal Hom into a complete object on a ringed site”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-site-hom-comparison-thick: the existing statement concerns “Exactness and thick isomorphism locus of the specified site Hom comparison”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-stratum-hom-comparison-mate: the existing statement concerns “The stratum Hom composite is the normalized evaluation comparison”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-weil-bidual-evaluation-realization: the existing statement concerns “Realization of the native Weil evaluation transpose”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-boundary-alpha-normalization: the existing statement concerns “The evaluation-normalized transpose gives the costalk duality comparison”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-boundary-evaluation-currying: the existing statement concerns “Ringed-site exceptional evaluation and opposite currying”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-closed-costalk-duality: the existing statement concerns “Exceptional restriction of a Verdier dual”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-duality-pairing: the existing statement concerns “The duality pairing and the double-dual morphism”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-ringed-slice-evaluation-coherence: the existing statement concerns “The normalized slice comparisons preserve the evaluation counit”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-ringed-slice-evaluation-transpose: the existing statement concerns “Slice restriction preserves evaluation for an arbitrary dualizing object”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-pbc-ringed-slice-representative-evaluation: the existing statement concerns “Normalized slice evaluation on K-flat and K-injective representatives”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-weil-stratum-ambient-hom: the existing statement concerns “Internal Hom from extension along a stratum”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs prop-coef-integral-dualizing: the existing statement concerns “The integral dualizing object and its adjunction”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs sk-thm-sf-kunneth-verdier: the existing statement concerns “Künneth–Verdier isomorphism”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs thm-coef-integral-verdier: the existing statement concerns “Integral Verdier biduality”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs thm-trf-internal-hom-pullback: the existing statement concerns “Internal Hom versus pullback for a site-perfect first variable”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-sfb-finite-model-topology-comparison-maps: the existing statement concerns “Canonical finite-model coefficient-topology Hom maps”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-sfb-flat-hom-evaluation-roof-data: the existing statement concerns “Canonical flat scalar Hom comparison and evaluation-roof data”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-sfb-internal-section-derived-tensor-comparison: the existing statement concerns “Normalized internal-to-sectionwise derived tensor comparison”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-sfb-internal-slice-derived-hom-comparison: the existing statement concerns “Local internal module-object derived Hom and restriction comparison”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-sfb-ringed-slice-comparison-model: the existing statement concerns “Normalized ringed slice comparison data”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-sfb-scalar-hom-canonical-iso: the existing statement concerns “Canonical internal-Hom comparison from a normalized scalar tensor map”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-sfb-scalar-hom-comparison-data: the existing statement concerns “Actual scalar-adjunction and normalized tensor-Hom comparison data”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs det-lem-int-integral-heart-dualizable: the existing statement concerns “Local duals of integral constructible sheaves”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-closed-scalar-hom-comparison: the existing statement concerns “Five Hom bijections and evaluation for a tensor-preserving left adjoint”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-component-slice-hom-comparison-test: the existing statement concerns “Slice restriction and the normalized local derived-Hom comparison”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-dc-hom-scalar-adjunction: the existing statement concerns “Derived internal Hom under restriction of coefficient scalars”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-derived-internal-hom-sections-model: the existing statement concerns “Derived internal Hom into a K-injective and its derived global sections”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-finite-local-model-rhom-continuity: the existing statement concerns “Finite constant local models have bounded-target internal-Hom continuity”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-finite-model-topology-derived-hom: the existing statement concerns “Derived global Hom topology comparison for finite-field constructible models”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-free-parameter-evaluation-coherence: the existing statement concerns “Free-parameter evaluation, whole-family substitution and coefficient mates”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-hom-flat-evaluation-roof: the existing statement concerns “Flat scalar comparison is the evaluation-normalized resolution roof”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-hom-flat-scalar-evaluation-model: the existing statement supplies ordinary flat scalar evaluation and derived coherence, not identification with the particular completed operation comparison through quotient units.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-hom-kflat-chain-transpose: the existing statement concerns “Derived transposition on a tensor model with one K-flat factor”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-hom-strict-numerator-transpose: the existing statement concerns “Transpose of the strict normalized Hom numerator for arbitrary coefficient modules”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-internal-hom-localization-comparison: the existing statement concerns “Internal Hom and scalar localization under sequential continuity”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-internal-section-hom-continuity-comparison: the existing statement concerns “Continuity and evaluation scalar comparison under internal-to-section module equivalence”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-module-object-ringed-site-derived-comparison: the existing statement concerns “Module-object and ringed-site derived internal Hom agree”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-point-pullback-derived-hom: the existing statement concerns “Condensed-point pullback preserves unbounded derived internal Hom”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-qlbar-internal-hom-coefficient-comparison: the existing statement concerns “Algebraic-closure internal Hom comparison from finite-field continuity”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-ringed-hom-composition-model: the existing statement concerns “Hom-complex composition and its agreement with the derived adjunction”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-ringed-ordinary-evaluation-localization: the existing statement concerns “Unsigned ordinary evaluation and its localization through the two augmentation comparisons”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-sfb-ringed-signed-bidual-localization: the existing statement concerns “Signed ordinary bidual chain map and its localization through the two augmentation comparisons”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-pur-coefficient-base-change-hom: the existing statement concerns “Evaluation-defined internal Hom comparison under coefficient base change”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-pur-derived-constant-pullback-comparison: the existing statement concerns “Canonical derived constant-sheaf pullback comparison”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-pur-external-rhom-pairing-interface: the existing statement concerns “External global Hom evaluation interface”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-asd-internal-adjunction-evaluation: the existing statement concerns “Evaluation formula for the canonical internal compact-support adjunction”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pur-co-smooth-etale-locality: the existing statement concerns “Source-etale locality, without derived descent”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pur-external-evaluation-transpose-natural: the existing statement concerns “Naturality and open restriction of the external evaluation transpose”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pur-external-rhom-adjunction-naturality: the existing statement concerns “Naturality of the composite global tensor-Hom adjunction”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pur-external-rhom-cone-pairing: the existing statement concerns “External global derived Hom evaluation respects coefficient cones”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pur-external-rhom-derived-braiding: the existing statement concerns “Localization tensor comparison preserves Koszul braiding”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pur-external-rhom-evaluation-naturality: the existing statement concerns “Four-variance naturality of the external evaluation transpose”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pur-external-rhom-signed-cones: the existing statement concerns “Transport normalized external evaluations to both native coefficient cones”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pur-global-hom-evaluation-flat-lift: the existing statement concerns “Flat K-flat lifts of resolved global Hom evaluations”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pur-global-hom-evaluation-model: the existing statement concerns “A-linear evaluation-normalized global derived Hom model”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pur-integral-operations-scalar-extension: the existing statement asserts existence, naturality and tower laws, but does not fix its Hom map by the chi/gamma formula; this missing normalization is precisely the new conclusion.

lem-pod-specified-hom-scalar-evaluation vs lem-pur-lifted-external-evaluation-chain-model: the existing statement concerns “Lifted external evaluation chain models with common shifted targets”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-pur-scalar-hom-comparison-tower: the existing statement proves tower laws for ordinary evaluation-defined maps under tensor-coherence hypotheses, not the specified completed Hom pin.

lem-pod-specified-hom-scalar-evaluation vs prop-asd-internal-adjunction: the existing statement concerns “Internal ambient adjunction”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-trf-trace-class-source: the existing statement concerns “Trace-class source”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-trf-correspondence-class: the existing statement concerns “The class of a correspondence”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-trf-derived-bimodule-tensor-hom: the existing statement concerns “Derived tensor-Hom adjunction with a bimodule and retained scalars”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-trf-exceptional-internal-hom-composition: the existing statement concerns “Composition coherence of exceptional internal-Hom exchange”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-trf-exceptional-internal-hom-exchange: the existing statement concerns “Exceptional internal Hom versus exceptional pullback”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-trf-kv-evaluation-formula: the existing statement concerns “Evaluation of the canonical Künneth–Verdier map”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-trf-tensor-double-hom-exact-comparisons: the existing statement concerns “Exact tensor and two-target double-Hom functors with specified signed comparisons”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs def-zl-ringed-derived-closed-symmetric-monoidal-data: the existing statement concerns “Representative coherence data for derived tensor on a ringed site”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-zl-lisse-cohomology-derived-dual: the existing statement concerns “Cohomology of the coefficient dual of a lisse-cohomology complex”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-zl-proetale-coefficient-slice-closed-comparison: the existing statement concerns “Closed slice comparison with transported pro-etale coefficients”; it does not identify the specified completed coefficient-Hom theta through the three canonical chi maps on arbitrary schemes.

lem-pod-specified-hom-scalar-evaluation vs lem-zl-specified-hom-scalar-evaluation: the existing pin requires a separated finite-type scheme over the algebraic closure of a finite field; the new pin allows any scheme with ell invertible, and only claims the constructible-Hom-domain identification needed here.

lem-pod-specified-hom-scalar-evaluation vs lem-pod-point-scalar-hom-evaluation: the existing statement concerns point sections of perfect finite-projective coefficient models and their module dual, not arbitrary schemes and constructible-Hom pairs.

lem-pod-specified-hom-scalar-evaluation vs lem-sf-hom-comparison-finite-free: the existing statement is a finite-coefficient etale/pro-etale site comparison with bounded finite-free first input, not a completed coefficient-change normalization.

lem-pod-specified-hom-scalar-evaluation vs lem-pur-normalized-scalar-comparison-realization: the existing statement pins completed tensor and pullback scalar maps on whole systems, not internal Hom; it is cited for tensor instead.

## Validation

The inherited dry run passed before repair. The repaired dry run exited OK at 7605a20b4a2. The final audit then added an explicit citation for preservation of the constructible-Hom domain under scalar extension and clarified rationalization of kappa; the final dry run is repeated after these edits. No local preflight, check_dag or review_split is run.
