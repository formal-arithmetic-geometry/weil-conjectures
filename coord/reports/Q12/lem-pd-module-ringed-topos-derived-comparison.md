# Q12 stage-1 repair: lem-pd-module-ringed-topos-derived-comparison

## Files written

- dag/nodes/sec-poincare-duality/lem-pd-module-ringed-topos-derived-comparison.json: statement; accepted Steps 1–4 preserved, Step 5 now applies the new derived-open-adjunction child and assembles the open projection. Statement and stmt_deps are identical to current live. The assembly is 2085 characters in five steps; no step exceeds 2000 characters.
- dag/nodes/sec-poincare-duality/lem-pd-section-derived-open-adjunction-normalization.json: one new statement-only node, status unsplit, no proof, no proof dependencies, no Mathlib match. It exposes the remaining original Step 9: scalar-action normalization, ordinary Hom comparison, exactness, and compatibility of the independently specified derived open adjunctions.
- citations.json: verbatim statement quotations for all eight parent step/node citations, including the new Step 5.
- searches.jsonl: six genuine Mathlib searches for the new child. Every query was run through the required msearch.py command, and its actual result was read.
- report.md: this repaired report. prior-report.md archives the returned report unchanged; returned-parent.json archives that parent unchanged. original-proof-notes.md retains all nine original arguments and source places unchanged. The two Python scripts in the sandbox only perform this item's JSON/report edits.

The live N6 children lem-pd-section-derived-pushpull-normalization, lem-pd-section-ordinary-oplax-normalization and lem-pd-section-derived-tensor-normalization are not delivered or edited. They are now split by their own workers. This repair adds one new node and zero Mathlib leaves, completing the missing extraction alongside those three already-landed children.

## Attachments

None. The project-source searches under lean/WeilConjectures by the item tag and by internal-module/section/open-adjunction concepts found no declaration stating this comparison exactly. Scheme.exists_scheme_iso_derived_open_adjunction concerns Zariski structural-ring modules on isomorphic schemes and preservation of unit invertibility for restriction/right-adjoint adjunctions; it does not compare internal condensed-module extension by zero with section modules. The live Sheaf/Paper/ModuleRingedToposDerivedComparison.lean contains sorry at derived_homEquiv, delta_comparison and composition_comparison. Its open_homEquiv proves a relevant local equality, but is in the Sheaf library and is only one part of the newly extracted ordinary/derived normalization. It is useful evidence for the route, not an attachment of the whole item. No Lean was written and no compiler or Lake command was run.

## WANTED

None. All source texts used here are already available locally.

## What was wrong and what changed

The return G1/A6/D correctly identified missing structural work. The previous submission made ordinary oplax normalization a direct citation but left original Step 9 inline in Step 5; passing the preflight did not make that a completed re-split. This repair moves that argument out into the new statement-only lem-pd-section-derived-open-adjunction-normalization. Its conclusion specifies the canonical ordinary extension comparison on scalar actions, equality of the given ordinary Hom bijections, exactness on both sides, and the derived comparison equation for every morphism q. The equation fixes the particular derived adjunctions, units and counits; it does not merely assert that isomorphic functors admit some adjunction.

The new child has its own objects and hypotheses: arbitrary schemes U,X, an open immersion, a commutative condensed coefficient, small site representatives, both module categories, the fixed E_T, alpha_j, ordinary operations, localization conventions and explicit domains for q. It does not take the parent theorem as a premise. It uses the live pushpull child only to specify D(E_T) and the already-normalized pullback comparison b. It proves no tensor or proper-projection comparison and does not restate the full parent. Parent Step 5 now applies it; the remaining open-projection argument is just composition of the already-identified e, eta, epsilon and mu. The parent statement, its hypotheses, and its stmt_deps are unchanged.

There is no statement dispute or source error. The repair does not regeneralize any landed N6 child. No SGA source is cited. The source route and the fixed chapter/unit records are unchanged.

## Preservation and allocation of the original argument

I compared the sandbox with the current repository: before this repair only proof, proof_deps and split_report differed; in particular the parent statement and statement dependencies already agreed. I read the returned entry in coord/returns/Q12.md and the current re-split note. The initial required dry run completed successfully at d82fac4a912 without pushing; the substantive repair below is additional work prompted by the content return, not an unchanged re-push.

Original Step 1, the relative balancing universal property and constraints, and the flat/K-flat/total-complex part of original Step 2 are supplied by the existing lem-pe-internal-section-tensor-comparison; ordinary operation comparisons also use lem-sfb-internal-module-operations-transport. Original Steps 3–5, termwise derived equivalence, K-injective preservation, resolution transformations, independent derived pull-push adjunction and geometric compositors, are allocated to the live pushpull-normalization child. Original Step 6, the actual ordinary oplax mate and its two inverse balanced-generator formulas, is allocated to the live ordinary-oplax child. Original Step 2's derived tensor descent and original Step 7's actual delta/mu comparison are allocated to the live derived-tensor child. Original Step 8 remains the elementary proper-mate assembly in parent Step 4.

Original Step 9's action on each extension-by-zero summand, ordinary Hom bijection, exactness and canonical derived adjunction are now the new child's independent statement. Its last sentence, the open projection, remains the explicit three-factor composite in parent Step 5. Thus no argument was deleted to obtain a shorter proof. The full original nine steps remain verbatim in original-proof-notes.md for the next worker.

## Sources and proof handoff for the new unsplit child

I read sites-modules.tex Tag 03DI, lemma-extension-by-zero, including the summand construction and both directions of its Hom bijection. Its presheaf on V is the sum over arrows V to U of the module evaluated on that arrow; a scalar from R_X(V) acts through the restricted ring and alpha_j. This is the same linear action as the internal projection-formula linearization of def-sfb-module-linear-open-lower-shriek, followed by the alpha_j scalar restriction of def-sfb-module-open-lower-shriek. Hence the section comparison fixes each local summand and the scalar action. For an ordinary map q out of extension by zero, the two transposes both restrict q to the summand over V to U. Conversely they both send a summand section m to its given restricted image in the target, and then use sheafification. Their composites are identities on every summand; the sheafification universal property extends this equality. Evaluating these identical Hom bijections at identities identifies the ordinary units and counits. This is also exactly the ordinary comparison already stated by lem-sfb-internal-module-operations-transport; it should be cited rather than recreated by the child's future worker.

I read Tag 03DJ, lemma-extension-by-zero-exact: direct sums preserve injections before sheafification, sheafification is exact, and the adjoint is right exact. Restriction is exact by lem-pur-site-restriction-module-adjunction-exact, for an arbitrary commutative ring sheaf, not merely a constant coefficient. I read the alpha_j statement and only Part (1) of lem-weil-proetale-weakly-etale-localization: U_proet is the localized site X_proet/U. Its constant-ring clauses are not applied to a condensed ring.

For the unbounded derived passage, lem-weil-pbc-termwise-adjunction-homotopy states the componentwise unit/counit and Hom formulas, including the triangle identities on complexes and the homotopy quotient. lem-weil-pbc-exact-functor-derived-factorization says exact termwise functors preserve quasi-isomorphisms and their localization comparison is canonical without resolutions. Part (2) of lem-weil-pbc-localization-universal-property says natural transformations descend uniquely and that this descent preserves identities and composition. Thus the ordinary comparison squares and triangle identities localize. When the right adjoint is written Lj^* rather than the degreewise exact restriction, use the canonical exact left-derived comparison, exactly as specified in def-weil-exact-derived-adjunction and in the live pushpull child. This gives the displayed h_sec(D(E_X)(q) composed with c_K inverse) = b_M composed with D(E_U)(h_int(q)) on all derived morphisms by the localized unit/counit Hom formula. This paragraph is a handoff of the old argument; the delivered new node remains statement-only with proof [] and proof_deps [].

## Search and blueprint accounting

Before creating the child I searched the whole DAG by 03DI/03DJ, derived-open-adjunction-normalization, and internal/section/open/adjunction concepts. The exact new id is absent from live; N6's superseded extraction is not a node to reuse. I read all close candidate statements: ordinary internal-module transport gives no derived open adjunction; pushpull normalization concerns Lj^* left adjoint to Rj_*, not extension left adjoint to restriction; the ringed-site restriction/exactness lemma has no internal/section comparison. The closest overlapping definitions fix existing operations and give no comparison theorem. Additional same-tag statements are distinguished below.

Whole-blueprint searches with blueprint_refs.py for section-derived-open, internal/section/open, open/adjunction, section equivalence and derived open found no imported node stating the new normalization. The derived-open matches are finite-coefficient exchange/projection definitions, not this comparison of arbitrary condensed-module presentations. The ancestor command returns null: as for the existing children, blueprint.from.node is null, via lists the parent and nt-target-poincare-isiso, and from.place specifies original Step 9 and seeded target Step 2. same_as is []. I read dag/units/sk-thm-sf-verdier-exchange.json and dag/chapters/sec-poincare-duality.json; the new generic comparison stays below the existing route.

Six Mathlib searches are recorded exactly from searches.jsonl: LeanFinder in two phrasings; Loogle for SheafOfModules, CategoryTheory.Adjunction; LeanSearch for the equivalence and open derived adjunction; grep for extension-by-zero names in Algebra/Category/ModuleCat/Sheaf; and grep for derived-adjunction names in CategoryTheory. All services answered. I read the hits and the relevant source: SheafOfModules.overMapPushforwardAdj and overPushforwardOverAdj concern ordinary slice direct-image adjunctions; pushforwardPushforwardAdj and pullbackPushforwardAdjunction concern ordinary ringed-module functors. Scheme.Modules.restrictAdjunction concerns Zariski restriction left adjoint to direct image. Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean constructs absolute derived adjunctions from specified derived functors, with no internal-module section equivalence or open scalar-action comparison. None is an exact match or a one-line specialization of the new statement. The new node is therefore unsplit, not a Mathlib leaf. Existing parent/child searches were not fabricated or rerun; their records are retained.

## Review by Q12

I read B–E of coord/delivery-errors.md against the two delivered JSON files and the source statements. The new child is a self-contained statement, not an inline proof or a new copy of a landed helper. Its symbols, ring maps, module categories, universes and canonical adjunction choices are introduced explicitly. Its proof is empty and it has no proof dependencies; all its notions refer to existing definitions. The parent has no changed assertion or added hypothesis. The retained accepted Steps 1–4 are identical to the returned delivery. The structural correction is the extraction the maintainer requested, not compression of Step 5.

Step 1 uses sk-def-sfb-sheaf-tensor(1–2) for strong monoidal sheafification and the closed sheafified abelian tensor on our small site, which discharge the precise hypotheses of lem-pe-internal-section-tensor-comparison. That theorem states the normalized exact symmetric monoidal E, total tensor identification and flat/K-flat preservation and reflection. lem-sfb-internal-module-operations-transport states additivity and the ordinary operation and adjunction identifications. I checked these statements in full; none is just a definition cited for a theorem. The parent uses a commutative coefficient and the prescribed universe convention, as required. I read the underlying tensor source, sites-modules.tex Tag 03EL and the fixed sheaf-tensor blueprint source, retaining the previously accepted route.

Step 2 cites the live pushpull-normalization statement, which explicitly includes termwise D(E), preservation/reflection of K-injectives, resolutions, both operation comparisons, compatibility with their resolution transformations, the independently derived canonical adjunction, its unit/counit, and geometric pullback compositors. I read it in full and checked that the fixed coefficient map is the adjunct of alpha_f. The parent's finite-type k-schemes specialize its arbitrary schemes. The source is sites-cohomology.tex 07A6 and 0FPI; no transported choice replaces the independent ringed adjunction.

Step 3 cites ordinary-oplax normalization for both actual balanced-generator maps, not only an abstract isomorphism; it then cites derived-tensor normalization with exactly that ordinary normalization and Step 2's derived operations. That statement identifies the K-flat tensor/unit, actual delta and inverse mu as natural transformations. I read both whole statements. On a one-point site and for any commutative ring map R' to S, the composites reduce to s tensor (m tensor n) and (s tensor m) tensor (t tensor n), respectively, using R' balancing and S balancing. Zero rings and zero modules obey the same equations. This is the existing 03EL/07A4 route; landed children were not edited.

Step 4 uses the actual definition of alpha in lem-weil-pbc-ringed-projection-mate-exact. Its statement says alpha is adjunct to (epsilon tensor 1) followed by the oplax comparison (called mu there). The parent's mu_f is the inverse lax arrow; Step 4 consistently uses delta_f in the oplax direction. Steps 2–3 identify the Hom bijection and this composite, so equality of adjuncts is elementary. I read sites-cohomology.tex Tag 0B56, equation-projection-formula-map; this argument asserts no general invertibility of the proper projection map.

Step 5 now cites only the new derived-open-adjunction child for the extension, canonical derived Hom comparison, unit and counit. Its displayed equation says precisely what Step 5 takes from it; citations.json quotes the full statement verbatim. The new child's hypotheses hold for an open of our scheme with the same pulled-back condensed ring and site universe. The right adjoint b is the same comparison as in Step 2. The only remaining reasoning is the equality of a composite of three already-identified maps: e(eta tensor 1), e(mu), epsilon. The tensor and actual mu are from Step 3; the extension and units/counits are from the new node. No uncited comparison or change of coefficient category remains inline. Source 03DI/03DJ is read as detailed above. The extracted argument is not declared elementary; it is an independent worker item.

For the new statement I tested U empty: extension is zero, Hom from the zero extension is the singleton group, and the normalization equation is the unique equality. For U=X the normalized extension and restriction are identities under their canonical identifications and the equation is the section-equivalence Hom comparison. Zero coefficient rings and zero objects cause no failure. No quasi-compactness, no flat coefficient map, no boundedness of complexes, and no constant-sheaf hypothesis was inserted. For the equation, c_K inverse has source e_sec(D(E_U)K), D(E_X)(q) has target D(E_X)M, so its h_sec image has the same target Lj_sec^*D(E_X)M as b_M composed with D(E_U)(h_int(q)). This checks the potentially delicate orientation.

Every non-elementary fact in the parent is a cited statement, and every cited statement was opened and checked. Generic tools retained from other units are the existing tensor comparison, ordinary module-operation transport and ringed projection-mate lemma; they do not replace the unit's geometric route. The new child uses the existing generic exact/localization and ordinary open statements only as its future proof inputs, not as an extra proof hidden in its statement. No cycle to the parent was introduced. Each parent step is under 2000 characters and the total is below 3000. The original long open argument is now available for separate work rather than shortened away.

## Not duplicates

The new node is the explicit missing extraction authorized by the return. It is distinguished below from the parent, its live children, the closest generic ordinary comparison, and every unmerged existing node sharing source Tag 03DI or 03DJ. Same source tags alone do not state the internal/section derived normalization.
lem-pd-section-derived-open-adjunction-normalization vs def-a1-finite-adic-open-section-data: the existing statement is about Finite adic open extension and fibre data; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs def-coef-semilinear-derived-calculus: it defines a calculus interface for strict semilinear coefficient towers; it neither asserts the internal/section equivalence nor proves its derived open-adjunction normalization.

lem-pd-section-derived-open-adjunction-normalization vs def-pd-proetale-section-module-functors: this definition fixes ordinary section-module functors and tensor normalizations, not the new derived Hom comparison.

lem-pd-section-derived-open-adjunction-normalization vs def-pd-section-derived-realization: this definition specifies the existing localized operations and independently derived adjunction; it explicitly leaves their internal/section compatibility to the comparison theorem.

lem-pd-section-derived-open-adjunction-normalization vs def-pd-section-derived-tensor-data: this definition introduces conjugate derived tensor and localization data, not a theorem identifying independently specified open adjunctions.

lem-pd-section-derived-open-adjunction-normalization vs def-pd-section-module-operations-data: this definition fixes ordinary operations and mate-normalized comparisons, not their compatibility with the independently derived open adjunction.

lem-pd-section-derived-open-adjunction-normalization vs def-pur-ringed-open-extension-on-complexes: the existing statement is about Termwise sheafified ringed slice extension on cochain complexes; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs def-sf-open-normalization-data: it defines Cartesian-square ringed-site tensor/operation data; it does not state the internal/section derived Hom-bijection comparison.

lem-pd-section-derived-open-adjunction-normalization vs def-sf-semilinear-proper-open-comparisons: it defines comparison maps for semilinear module systems and their clopen/projector operations, not a presentation change from internal modules to section modules.

lem-pd-section-derived-open-adjunction-normalization vs def-sfb-adic-residue-lift-comparisons: the existing statement is about The coefficient comparisons and actual finite-reduction Hom tower; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs def-sp-open-coefficient-unit-iso: the existing statement is about Open coefficient isomorphism normalized by the open unit; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs def-sp-semilinear-constant-ring-operations: the existing statement is about Constant-ring semilinear system operations and normalized evaluation mates; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs def-sp-varying-ring-operations: the existing statement is about Canonical geometric operations on varying-ring systems; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs def-sp-varying-ring-proper-open-arrows: the existing statement is about Intrinsic varying-ring clopen proper/open arrows; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs def-weil-extension-by-zero-presheaf: the existing statement is about The extension-by-zero presheaf of a module on a localized ringed site; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs def-weil-pbc-extension-by-zero: the existing statement is about Extension by zero for open immersions; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs def-weil-pbc-local-coefficient-localization: the existing statement is about Coefficient localization and local section multiplication on a ringed site; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs def-weil-pbc-ringed-derived-restriction: the existing statement is about RingedDerivedRestriction; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-cbc-completed-open-strict-mate-identification: the existing statement is about Completed open exchange agrees with the actual constant-coefficient strict mate; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-cbc-completed-ring-strict-finite-exchange: the existing statement is about Strict finite open exchange over completed coefficient rings; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-cbc-extension-zero-stratified-perfect: the existing statement is about Extension by zero preserves stratified perfect local models; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-cbc-finite-open-exchange-scalars: the existing statement is about Finite open exchange commutes with coefficient restriction and tower transitions; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-cbc-localized-extension-zero-linear-derived: it establishes A-linearity and triangulatedness for derived section-module extension, not the comparison with internal modules or the adjunction Hom equation.

lem-pd-section-derived-open-adjunction-normalization vs lem-cbc-open-extension-zero-etale-adjunction-agreement: the existing statement is about Open-immersion and etale extension by zero have the same adjunction; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-cbc-open-localized-counit-comparison: the existing statement is about Open localized finite pullback is the pulled-back extension counit; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-cbc-ringed-open-scalar-limit-coherence: the existing statement is about Ringed open extension, scalar restriction and normalized strict limits; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-pc-inverse-image-open-free-sheaf: the existing statement is about Inverse image of a represented open free abelian sheaf; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-pc-open-embedding-sheaf-pullback-injectives: the existing statement is about Open embedding sheaf pullback preserves injectives; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-pc-open-extension-derived-unit-isiso: it gives invertibility of a derived open-extension unit for structural-ring sheaves; it does not identify internal condensed-module Hom bijections with section-module ones.

lem-pd-section-derived-open-adjunction-normalization vs lem-pc-open-free-restriction-hom: the existing statement is about Restriction of morphisms from the image-open free sheaf; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-pc-open-inverse-image-injectives: it preserves injective abelian Zariski sheaves under an open inverse image, not the extension/restriction derived Hom comparison.

lem-pd-section-derived-open-adjunction-normalization vs lem-pc-open-restriction-data: the existing statement is about Degree-zero restriction data in the cartesian open-subscheme square; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-pc-open-restriction-ext-bijective: it proves bijectivity of represented Zariski Ext restriction maps, not internal condensed-module/section-module adjunction normalization.

lem-pd-section-derived-open-adjunction-normalization vs lem-pc-scheme-module-free-yoneda-iso: it identifies the sheafified structural-ring free Yoneda object with extension of the localized unit; it does not compare any internal/section derived adjunction.

lem-pd-section-derived-open-adjunction-normalization vs lem-pd-module-ringed-topos-derived-comparison: the parent also proves exact symmetric monoidal and K-flat tensor transport, derived direct image, compositors, actual delta/mu, and proper/open projection comparisons; the child isolates only the original Step 9 open-adjunction normalization and supplies no tensor or proper clause.

lem-pd-section-derived-open-adjunction-normalization vs lem-pd-section-derived-pushpull-normalization: that lemma compares pullback left adjoint to direct image; the new lemma compares extension by zero left adjoint to open restriction, with its distinct Hom bijection.

lem-pd-section-derived-open-adjunction-normalization vs lem-pd-section-derived-tensor-normalization: that lemma identifies K-flat derived tensor, delta and mu, not the derived extension-by-zero/restriction adjunction.

lem-pd-section-derived-open-adjunction-normalization vs lem-pd-section-ordinary-oplax-normalization: that lemma computes the ordinary tensor mate on balanced generators; the new lemma concerns extension/restriction Hom bijections and their exact derived localization.

lem-pd-section-derived-open-adjunction-normalization vs lem-pur-sequence-site-open-extension: the existing statement is about Geometric and levelwise open extension on ringed sequence sites; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-pur-site-restriction-module-adjunction-exact: it gives exactness and an adjunction within section-ring module sheaves; it neither mentions internal module objects nor compares their derived Hom bijections.

lem-pd-section-derived-open-adjunction-normalization vs lem-sc-module-extension-by-zero-unit-epi: it asserts that an ordinary ringed-space open unit is epic, not an equality of canonical internal/section derived adjunctions.

lem-pd-section-derived-open-adjunction-normalization vs lem-sc-module-extension-by-zero-unit-isiso: it asserts invertibility of the ordinary ringed-space open unit, not a comparison with condensed internal-module derived adjunctions.

lem-pd-section-derived-open-adjunction-normalization vs lem-sc-module-extension-by-zero-unit-mono: it asserts that an ordinary ringed-space open unit is monic, not an equality of canonical internal/section derived adjunctions.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-open-extension-scalar-restriction-coherence: it compares finite constant-ring scalar restriction with open extension and coefficient composition; the new statement compares internal and section presentations over arbitrary commutative condensed coefficients.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-open-operation-models: it produces an Operations record for a Cartesian open square of ringed-site models, not a comparison of internal module objects with section modules.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-semilinear-clopen-unit-projector: the existing statement is about Clopen system projection is the specified direct-image unit; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-site-finite-projective-lift: the existing statement is about exists local lift overMap from finiteFree; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-site-finite-projective-section: the existing statement is about exists local section overMap of finiteFree retract; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-site-perfect-derived-restriction-iso: the existing statement is about overFunctor derivedRestrictionIso; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-site-perfect-lower-model: the existing statement is about exists strictPerfect lower model; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-site-perfect-opcycles-retract: the existing statement is about exists local retract opcycles of perfect tor; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-site-perfect-opcycles-retract-transport: the existing statement is about transport slice retract; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-site-perfect-overmap-additive: the existing statement is about sitePerfectOverMap additive; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-site-perfect-overmap-comp: the existing statement is about sitePerfectOverMapComp; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-site-perfect-overmap-exact: the existing statement is about overMap exact ofUniverses; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-site-perfect-package-map: the existing statement is about StrictPerfectCoefficientPackageOnSite.map; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-site-perfect-restriction-additive: the existing statement is about sitePerfectOverFunctor additive; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-site-perfect-restriction-exact: the existing statement is about overFunctor exact ofUniverses; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sf-site-perfect-upper-model: the existing statement is about exists strictPerfect upper model; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sfb-exact-open-closed-unbounded-calculus: it localizes given exact open/closed adjunctions and support triangles, assuming their ordinary data; it does not compare internal condensed modules with section modules or normalize that equivalence.

lem-pd-section-derived-open-adjunction-normalization vs lem-sfb-internal-module-operations-transport: it identifies the ordinary internal and sectionwise module operations and adjunctions only; the new statement fixes the resulting unbounded derived open Hom equation with the canonical Lj^* comparison.

lem-pd-section-derived-open-adjunction-normalization vs lem-sfb-locally-closed-extension-coherence: the existing statement is about Restriction and composition for locally closed extension by zero; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sfb-locally-closed-module-extension-coherence: the existing statement is about Normalized locally closed extension on module sheaves; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sfb-open-filtration-successor: the existing statement is about Natural quotient for two nested open module pieces; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sfb-proetale-identified-open-closed: the existing statement is about Exact open and closed extensions with identified inverse-image coefficients; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sfb-proetale-identified-supported-reconstruction: the existing statement is about Normalized supported reconstruction for actual tensor pullbacks; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sfb-proetale-locally-closed-extension: the existing statement is about Pointwise exact locally closed extension; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sp-slice-restriction-strict-derived-limit: the existing statement is about Slice restriction commutes with total derived inverse limit of strict towers; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sp-subterminal-module-local-calculus: the existing statement is about Intersection and local detection calculus for subterminal module slices; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sp-varying-ring-cartesian-comparison-lift-relabelling: the existing statement is about The cartesian open comparison on varying-ring systems relabels lifts; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-sp-varying-ring-open-unit-coherence: the existing statement is about Exact localization and identity unit law for varying-ring open extension; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-trf-topos-complement-module-stalks: it gives constant-ring complementary-subtopos support/stalk formulas, not the normalized equivalence of two module presentations with arbitrary condensed coefficients.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-affine-free-finite-stalk-generation: the existing statement is about Finite affine free maps generating one module stalk; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-element-presheaf-extension: the existing statement is about Direct-sum computation and left exactness of presheaf element extension; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-etale-graph-section-extension-map-linear: the existing statement is about The presheaf map from the etale sum presheaf to direct image is linear over the constant sheaf of rings; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-extension-by-zero-adjunction: the existing statement is about Extension by zero is left adjoint to restriction (étale site); it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-extension-by-zero-exact: the existing statement is about Extension by zero is exact (étale site); it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-free-etale-module-shriek-comparison: the existing statement is about Free representable module sheaves are etale extensions by zero; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-free-sheaf-derived-sections: the existing statement is about Free sheaf shifted Hom computes derived module global sections; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-free-sheaf-flat: the existing statement is about The sheafified free presheaf on a representable with flat coefficients is flat (j_{X!} of a constant flat sheaf is flat); it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-free-yoneda-presheaf-module: the existing statement is about Morphisms out of the free presheaf of modules on a representable are sections; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-integral-model-open-closed-pieces: the existing statement is about Integral open and closed pieces remain constructible and rationalize to the localization sequence; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-proetale-ringed-open-closed: the existing statement is about Ringed pro-etale open-closed localization; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-ringed-slice-extension-preserves-exact: the existing statement is about Ringed-slice extension preserves exactness; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-sheaf-free-separator: the existing statement is about The coproduct of the sheafified free presheaves on representables with coefficients in a separator is a separator of the sheaf category; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-site-extension-by-zero-exact: the existing statement is about Extension by zero on a localized site is exact; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-site-extension-by-zero-presheaf-adjoint: the existing statement is about The sheafified direct-sum presheaf is left adjoint to restriction to a localized site; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-site-restriction-exact: the existing statement is about Restriction to a localized site is exact; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-site-restriction-injectives: the existing statement is about Extension by zero and restriction on a localized site; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-zariski-etale-pushed-resolution: the existing statement is about Local vanishing gives the pushed injective-resolution augmentation as a quasi-isomorphism; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-zariski-etale-pushed-resolution-finite-limits: the existing statement is about Finite-limit preservation for the pushed resolution; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-zariski-etale-pushed-resolution-quasi-iso: the existing statement is about Quasi-isomorphism of the pushed resolution augmentation; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-zariski-extension-by-zero-adjunction: the existing statement is about Extension by zero of abelian Zariski sheaves is a left adjoint of restriction to an open; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs lem-weil-pbc-zariski-extension-by-zero-exact: the existing statement is about Extension by zero of abelian Zariski sheaves is exact; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs new-lem-amb-closed-support-hom-sequence: the existing statement is about Underived closed-support Hom sequence on injective sheaves; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs new-lem-sc-nested-slice-extension-stalks: the existing statement is about Nested slice extension stalk maps; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs new-localized-restriction-extension-exists-universes: the existing statement is about Exact extension adjoint for localized restriction with independent coefficient universe; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs new-open-embedding-sheaf-pullback-adjunction: the existing statement is about Extension by zero adjunction for open embeddings; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs new-open-embedding-sheaf-pullback-preserves-monomorphisms: the existing statement is about Open embedding sheaf pullback preserves monomorphisms; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs new-over-pullback-adjunction-mono: the existing statement is about Extension by zero adjunction preserving monomorphisms; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

lem-pd-section-derived-open-adjunction-normalization vs new-over-pullback-preserves-injectives: the existing statement is about Restriction to a slice Grothendieck site preserves injective abelian sheaves; it does not identify the specified internal condensed-module/section-module derived open Hom bijections, scalar actions and both units/counits.

## Unfinished work

No stage-1 repair remains intentionally unfinished. The new statement is deliberately unsplit for another worker, as instructed. Required validation and direct delivery follow this report; successful delivery is reported only after the push command prints DELIVERED.
