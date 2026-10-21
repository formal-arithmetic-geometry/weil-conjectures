# Stage-1 repair: sk-prop-sfb-cartesian-coefficients

## Files written

- dag/nodes/sec-proetale-coefficients/sk-prop-sfb-cartesian-coefficients.json: statement unchanged; eight short assembly steps replace the six coarse steps. All imported, source, citation/search, Lean, review and blueprint metadata are retained except for the updated split report and dependency list required by this repair.
- dag/nodes/sec-proetale-coefficients/lem-sfb-products-zero-additive.json: statement; Mathlib leaf, CategoryTheory.Functor.additive_of_preserves_binary_products, Mathlib/CategoryTheory/Preadditive/AdditiveFunctor.lean:234–239.
- dag/nodes/sec-proetale-coefficients/lem-sfb-finite-exactness-nat-iso.json: statement; Mathlib leaf, CategoryTheory.Limits.preservesFiniteLimits_of_natIso and CategoryTheory.Limits.preservesFiniteColimits_of_natIso, Mathlib/CategoryTheory/Limits/Preserves/Finite.lean:92–94 and 248–250, respectively.
- dag/units/sk-prop-sfb-cartesian-coefficients.json: only realized and realized_by filled, assigning each of its three original proof paragraphs to the item; chapter, statement and unit route untouched.
- citations.json: every step/node pair has a verbatim quotation of that node's statement. Complete statements are quoted to retain all hypotheses.
- searches.jsonl: real search-command output records; all new-node Mathlib searches are selected from that log with identical tool/query text.

## Attachments

No attachment for the whole item. The upstream isIso_condensedPullbackHom covers the untwisted ring comparison; the declarations for eta identities/composition also do not state the full twist, finite-free and exact-lift conjunction. The current Sheaf.Paper.CartesianCoefficients file has named sorry theorems (including the final theorem); no finished whole-item proof was found. I read its actual lift and comparison constructions, and the upstream module pullback and scalar-change declarations, without compiling.

## WANTED

None. All sources used are present. No SGA source is used.

## Return repaired

The sandbox initially contained only dispatcher markers, with no retained node, report or search log. I reconstructed the delivered six-step split from the current read-only repository: it agrees with the return description, including the three long final steps and the already-landed Lean statement. The parent statement is byte-for-byte unchanged after JSON parsing, including the existing coefficient and Tate-twist domains. Nothing was rebased with a git command; delivery.py performs the authorized worktree construction against current server state.

The former fourth step rebuilt abelian sheaves as modules over the constant integer sheaf just to invoke a Grothendieck-abelian theorem. The existing statement lem-weil-pbc-site-sheaves-enough-injectives already supplies abelianness for every small site. Citing it directly removes that unnecessary comparison construction. The tensor and module-category hypotheses remain supplied by existing exact statements, rather than moved to a redundant bundle node.

The former fifth step is now a direct specialization of the existing extension-along-isomorphism theorem. The new step explicitly cites sk-def-sfb-transport for the equality of underlying mapMod functors; restriction's equality comes from def-sfb-modobj-restriction. Commutativity of the source ring follows from its ring isomorphism to Lambda_X. This is a short assembly of already-split nodes, not a new copy of a parent clause.

The former sixth step hid two generic categorical arguments. They are now two independent Mathlib leaves: the product/zero criterion for additivity, and invariance of finite-limit/colimit preservation under a natural isomorphism. The remaining terminal-object/zero-arrow check is elementary and written out, followed by a separate exact-lifting application and a separate transfer along the comparison. Both new nodes are strictly smaller than any clause of the parent: they mention no scheme, coefficient ring, Tate twist or extension of local fields.

Mathlib leaves intentionally have no new proof steps, as required by brief-stage1 §3 and delivery-errors B1/B8. Their proof in words is recorded here for the finer-split review. For products-zero-additive, binary products in a preadditive category are biproducts. Preservation of products and zero arrows identifies their injections and projections. Express addition by diagonal, direct sum of two maps, and codiagonal; its image is addition. This is exactly the proof route in the Mathlib source at lines 227–239 and Stacks 0DLP, lemma-additive-functor. For finite-exactness-nat-iso, a natural isomorphism gives an isomorphism between the two image cones of each finite diagram; composing cone maps with its components identifies their universal mapping properties. The same argument with cocones gives the colimit clause. Mathlib provides each clause separately at the recorded lines. Stacks 0034, definition-exact, is cited only for the meaning of preservation/exactness, not as a claim that it proves this invariance theorem.

## Unfinished work

None in this stage-1 repair. No Lean source was written and no compiler, Lake or build command was run. These new inputs are Mathlib leaves, so they do not introduce an unsplit proof obligation.

## Review by Q30

I read the current main-20261015 chapter, unit, parent section and all three proof paragraphs. I also read the parent in the DAG and every statement used by its old and new proof. The route is unchanged: coefficient comparison, twist comparison, integral basis and its two induced sheaf isomorphisms, then the exact inverse-image lift. The source's implicit final exactness sentence is precisely where the finer categorical split is needed; no target or definition meaning was changed.

For step 1 I checked that sk-def-sfb-coefficient-morphisms states an isomorphism of ring objects, not merely of underlying abelian sheaves, and lem-sfb-alpha-iso supplies invertibility for any condensed ring and any scheme morphism. The fixed finite-subextension interpretation of Qbar is retained, as are discrete finite A. This step needs no invertibility of ell on the schemes.

For step 2 I read det-prop-sfb-cartesian-coefficients-twists and the domain in sk-def-sp-tate-twist: ell must be invertible on both schemes, and finite A is ell-power torsion. The cited statement supplies all integer twists, alpha compatibility and module structures. It is used only on that domain. In characteristic ell the twist statement is not invoked; this avoids the mu_ell=0 edge case without changing the untwisted clauses.

For step 3 I read both the integral-basis node and finite-free detail node. The former gives an actual basis of O_F over O_E of length [F:E], while the latter assumes exactly that chosen basis and gives both the integral and field coefficient-sheaf isomorphisms. I checked E=F (rank one), the zero/empty scheme, and finite ramified extensions: no unramified or normality hypothesis is silently imposed.

For step 4 I checked the universe/small-skeleton convention in def-weil-pbc-proetale-site before applying the small-site theorem lem-weil-pbc-site-sheaves-enough-injectives. Its abelian-category clause is exactly what is taken; its stronger injective conclusion is unused. The symmetric closed tensor is supplied by sk-def-sfb-sheaf-tensor, and det-def-sfb-sheaf-tensor-closed expressly states additivity and preservation of all colimits in each variable. Therefore tensoring with either coefficient ring preserves finite colimits. sk-def-sfb-pulled-back-coefficients supplies the commutative ring objects, so the hypotheses of lem-sfb-modobj-abelian all hold. Abelianness also supplies equalizers/coequalizers for the next scalar-change theorem.

For step 5 I opened def-sfb-modobj-extension-along-iso together with its stated setting def-sfb-modobj-restriction-equivalence. Step 4 supplies a braided closed category, equalizers/coequalizers and tensor-colimit preservation; step 1 gives invertible alpha, and the source coefficient ring is commutative through alpha. The theorem's direction is Ext_alpha to Res_(alpha inverse). Its whiskering with mapMod is precisely the canonical comparison required. sk-def-sfb-transport states that mapMod commutes with forgetful functors; def-sfb-modobj-restriction states that restriction leaves every underlying object and arrow unchanged. Thus U_X G = f^{-1} U_Y is justified on objects AND maps, and the displayed action is precomposition with alpha inverse, not alpha.

For step 6 I read clauses 3 and 4 of det-pe-topos-functoriality-inverse-image, which give finite-limit preservation on sets and computation of the abelian inverse image on those sets. Terminal sheaves are the zero abelian sheaves; binary products carry the induced componentwise group laws. A zero arrow factors through the zero object, so inverse image preserves it. The new Mathlib theorem requires precisely binary products in the source, product preservation and zero-morphism preservation; all three have now been checked. In particular no assertion that set-valued colimits automatically compute abelian colimits is used.

For step 7 I read the full statement of det-prop-sfb-module-pullback-exact-lifted. Both ambient categories are abelian, tensor is additive in each variable and right exact on the two rings, F=f^{-1} is additive by step 6 and exact by clause 4 of det-pe-topos-functoriality-inverse-image, and U_X G = F U_Y is step 5. Those are every hypothesis of the cited lifting statement; it gives both finite-limit and finite-colimit preservation, not only short-sequence preservation.

For step 8 I checked both declarations underlying the new natural-isomorphism leaf. Apply them with F=G (the lift), G=f^* and the inverse of the comparison from step 5. This orientation supplies preservation to f^*. No additivity hypothesis or separate existence of all finite (co)limits is hidden in either Mathlib declaration. The specified natural isomorphism remains the one constructed by scalar extension along alpha, rather than an arbitrary replacement of the coefficient action.

I searched the entire DAG and blueprint for each prospective new statement before writing it, including exact theorem names and Stacks tags. I inspected the real Loogle, LeanFinder, LeanSearch and grep results; both leaves match exactly, so no absence conclusion is made. The first failed camel-case Loogle name is retained only in searches.jsonl; the successful snake-case query is what the node records. The grep script's single-file display parses its line number as a file field; I read AdditiveFunctor.lean directly and recorded its actual file and line 234. I did not alter the search output or the launcher scripts.

I tested the product criterion on the identity and zero functors; the non-zero constant functor is excluded by zero-arrow preservation, so the hypothesis is necessary. The natural-isomorphism leaf was tested on an identity comparison, the zero functor, and absent finite (co)limits: the conclusion is preservation of existing universal cones/cocones and imposes no false existence claim. Both have the exact universes and object kinds of their Mathlib statements. The item statement is unchanged; no STATEMENT-DISPUTED correction is required.

The longest parent step is under 500 characters and no new proof contains a long step. I checked B1–B10 (self-contained statements, definitions, TeX, source places, exact Mathlib matches, blueprint provenance), C1–C8 (every non-elementary input is stated by a cited node, dependency direction, no cycle, explicit generic tool uses), D1–D5 (no new node copies a parent clause and no proof is hidden in a definition), and E1–E7 (all hypotheses, correct actions and functor orientation, no unsupported transport). Generic off-unit uses are listed in split_report.tool_uses for review; I did not add to the maintainer-owned tool_uses list.

The revised parent proof has 2545 characters, versus 5449 in the baseline, with step lengths 197, 198, 244, 440, 478, 348, 338, 302. Both new nodes are Mathlib leaves (proof length zero).

## Not duplicates

lem-sfb-products-zero-additive vs lem-sfb-preserving-colimits-additive: the existing theorem assumes abelian categories and finite-colimit preservation; the new theorem assumes only preadditivity, binary products and zero-arrow preservation and uses limits, not colimits. Neither it nor its direct Mathlib declaration is already a statement of the former node.

lem-sfb-products-zero-additive vs def-sp-left-exact-additive: the latter defines terminology for functors between abelian categories and derived functors; it does not state the binary-product/zero criterion between arbitrary preadditive categories.

lem-sfb-products-zero-additive vs lem-sfb-extend-scalars-preserves-homology: the existing statement concerns homology preservation by extension of condensed coefficients under a flatness hypothesis; the new statement is the product/zero criterion for an arbitrary preadditive functor.

lem-sfb-finite-exactness-nat-iso vs def-sc-picard-external-right-cech-models: the existing statement is “Fixed scalar Cech functors and right external coefficient Cech models”; it has its own definitional data and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sc-perfect-open-stalk-chain-map-equality: the existing statement is “Local equality of restricted strictly perfect complex maps”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sc-perfect-open-stalk-homotopy-spread: the existing statement is “Spreading a single perfect open stalk homotopy”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sc-perfect-open-stalk-retract-map-equality: the existing statement is “Local stalk equality for a finite retract sheaf”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sc-perfect-open-stalk-reverse-components-lift: the existing statement is “Lifting reverse-degree stalk components without equations”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sc-picard-external-cup-right-cech-diagram: the existing statement is “Short exact Cech comparison diagram for external cup in the right coefficient”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sc-picard-external-right-cech-comparison: the existing statement is “Cup comparison of the fixed right external Cech sequences”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sc-picard-external-right-cech-exact: the existing statement is “Short exactness of the fixed right external Cech sequences”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-wf-exact-finite-gsets-forgetful: the existing statement is “Exact finite-valued functors on finite continuous group sets are forgetful”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs def-galois-category: the existing statement is “Galois category”; it has its own definitional data and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs def-galois-exact-functor: the existing node defines preservation and exactness; the new statement proves transfer of both preservation properties across a specified natural isomorphism.

lem-sfb-finite-exactness-nat-iso vs def-weil-pbc-strict-henselization-structural-map: the existing statement is “Structural map of the strict henselization”; it has its own definitional data and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs def-pc-standard-single-flat-counit-presentation-on-open: the existing statement is “Presentation property on a source open”; it has its own definitional data and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs def-pc-standard-single-flat-counit-presentation: the existing statement is “Bounded flat sheaf-complex presentation of single base change before stalks”; it has its own definitional data and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-pc-affine-finite-type-pullback-zero-test: the existing statement is “Finite affine sections test vanishing after arbitrary pullback”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-pc-coproduct-truncation-couple: the existing statement is “Natural coproduct truncation exact-couple comparison”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-pc-ring-pseudo-coherent-localization-glue: the existing statement is “A bounded-above finite-free model of a module complex glues from a finite standard-open cover”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-pc-tensor-hom-restriction-scalar: the existing statement is “Tensor-Hom transposition of local scalar multiples”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-pc-truncated-higher-image-quasi-coherent: the existing statement is “Quasi-coherence of each truncated higher image”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sc-derived-algebra-qcoh-of-underlying: the existing statement is “Bounded-below quasi-coherent algebra-derived objects detected on underlying cohomology”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sc-derived-locally-bounded-below-global: the existing statement is “A locally bounded-below derived object on a Noetherian scheme has a uniform lower bound”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sc-derived-tensor-precomposition-open: the existing statement is “Quasi-coherent tensor precomposition invertible on an inverse-image open”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sc-determinant-wedge-quotient-factor: the existing statement is “Factorization of the pre-quotient wedge map”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sc-pseudo-coherent-rhom-qcoherent: the existing statement is “Derived internal Hom from a pseudo-coherent module preserves bounded-below quasi-coherence”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs sk-def-sfb-change-of-scalars: the existing statement is “Restriction, extension and coextension of scalars”; it has its own definitional data and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs def-weil-pbc-sites-and-cohomology: the existing statement is “Sites, morphisms of sites and cohomology on an object of a site”; it has its own definitional data and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sp-exact-functor-half-plane: the existing statement is “Limiting and large-page comparisons for an exact functor”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-affine-intersection-quotients-stalk: the existing statement is “Localization of affine quotient systems with a prescribed kernel filtration”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-bounded-above-projective-model: the existing statement is “Upper bounded derived module objects admit projective models”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-coherent-of-formal-quotients-torsion-kernel: the existing statement is “Coherence from a single formal quotient and an annihilated map kernel”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-condensed-qbar-derived-scalar-basis-sections: the existing statement is “Coherent ordinary scalar-extension copowers and exactness”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-condensed-qbar-derived-scalar-basis-unit-of-sections: the existing statement is “Ordinary exact scalar-unit copowers descend to the derived category”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-condensed-qbar-derived-scalar-basis-unit: the existing statement is “Coherent coefficient sections giving the derived scalar-extension unit decomposition”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-condensed-qbar-function-coefficients: the existing statement is “Naturality and basis properties of explicit bounded coefficient scalars and geometric fibers”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-devissage-second-adic-system-comparison: the existing statement is “Canonical interchange of two ideal-power quotients”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-finite-discrete-coefficient-terminal: the existing statement is “The coefficient comparison at the pulled terminal object”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-finite-etale-locally-free-models: the existing statement is “Finite etale pushforwards and unit quotients are locally finite free”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-formal-comparison-algebraization-quotient-lift: the existing statement is “Algebraization of a formal pullback isomorphism with canonical quotient compatibility”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-formal-completion-affine-sections: the existing statement is “Affine sections identify a quasi-coherent module completion with its adic completion”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-formal-completion-pullback-normalized: the existing statement is “Completion pullback normalized on quotient projections”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-formal-graph-discrepancy-zero: the existing statement is “Vanishing of the completed formal graph discrepancy”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-formal-graph-first-quotient-epi: the existing statement is “The finite formal comparison graph surjects onto the first ideal quotient”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-formal-second-ideal-quotient-adic: the existing statement is “Second-ideal quotients of coherent formal modules are adic”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-formal-second-ideal-quotient-supported: the existing statement is “Second-ideal quotient systems are annihilated by the thickening ideal”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-ideal-power-local-maps-eventually-agree: the existing statement is “Eventual agreement of local ideal-power maps”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-integral-scalar-contractive: the existing statement is “Contractive scalar units in continuous integral coefficients”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-limit-residue-field: the existing statement is “A point of a limit is the limit of its images”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-module-inverse-image-action-adjunction: the existing statement is “Underlying inverse image for modules from a normalized ring presentation”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-popescu-auxiliary-quotient-smooth: the existing statement is “Smooth localizations of the explicit Popescu auxiliary quotient”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-popescu-height-zero-auxiliary-witnesses: the existing statement is “Singular-element witnesses in the height-zero auxiliary algebra”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-popescu-lift-chart-flat: the existing statement is “Flat local map on a prepared Popescu chart”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-popescu-lift-partial-chart-dimension: the existing statement is “Dimension of the special fibre of a partial Popescu chart”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-popescu-unit-residue-extension: the existing statement is “Admissible unit enlargement with a residue-field extension certificate”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-popescu-unscaled-unit-basis: the existing statement is “Unscaled residue differential basis and a residue inverse after adjoining one unit”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-proetale-point-components-maps: the existing statement is “Maps from a weakly contractible affine to finite constant objects”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-sections-over-quasi-compact-open: the existing statement is “Sections over the complement of V(I) and maps from powers of I (quasi-compact scheme)”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-simple-transcendental-differential-decomposition: the existing statement is “Canonical differential decomposition for a simple transcendental extension”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-site-morphism-composition: the existing statement is “Composition of morphisms of sites (Stacks 03CB)”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-strict-henselization-affine-chart-ind-etale: the existing statement is “Strict henselization is ind-etale over an affine chart”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-weil-pbc-strict-henselization-point-evaluation-image: the existing statement is “Pointed evaluation lands in the relative separable closure”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs new-chow-pushforward-support-closed: the existing statement is “Closed support of proper pushforward lies in image”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs new-stage3-coherent-formal-quotients-affine-sections: the existing statement is “Affine section finiteness from a formal quotient and torsion kernel”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs prop-weil-pbc-inverse-image-exact: the existing statement is “Exactness of inverse image”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs stage3-proetale-comparison-square-proetale-path-normalization: the existing statement is “Exact derived normalization of the ProEtale comparison path”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sfb-comap-preserves-k-injectives: the existing statement is “Flat restriction of scalars preserves K-injectives”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sbc-pointed-etale-ring-colimit-base-map-naturality: the existing statement is “Naturality of the pointed etale neighbourhood base-ring maps”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-exc-finite-galois-prime-residue-lifting: the existing statement is “Prime conjugacy and residue-automorphism lifting in finite Galois normalization”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-exc-finite-tame-character-tower: the existing statement is “Wild inertia surjectivity and scaled tame characters in finite towers”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-pur-kinjective-set-iso-classes-bounded-size: the existing statement is “Set of bounded-size object isomorphism classes”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-pur-kinjective-set-of-subobjects: the existing statement is “Subobjects form a set in an abelian category with a generator”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-sc-smooth-strict-local-field-model-core: the existing statement is “Regularity, dimension, residue and function field of the smooth strict localization”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs new-lem-sc-smooth-strict-local-field-model-coeff-data: the existing statement is “Construct the coefficient field and its residue isomorphism”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

lem-sfb-finite-exactness-nat-iso vs lem-trf-comparison-truncated-direct-images: the existing statement is “Truncated higher-direct-image comparison”; it has its own objects and hypotheses and does not assert invariance of finite-limit and finite-colimit preservation for arbitrary naturally isomorphic functors.

## Validation

The first dry run identified exactly two metadata errors: both new Mathlib matches recorded the verified lines as a list but lacked the required integer `mathlib_match.line`. Added line 234 and line 92 respectively, retaining the full per-clause line details in `how`. The server diagnostic contained only these two blocking findings; unrelated unit-route advisories are recorded by the checker without refusal.
