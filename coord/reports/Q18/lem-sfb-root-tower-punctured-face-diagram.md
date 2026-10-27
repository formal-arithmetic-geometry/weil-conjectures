# Stage-1 report: lem-sfb-root-tower-punctured-face-diagram

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-root-tower-punctured-face-diagram.json: statement, split; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-residual-root-tower-local-charts.json: statement, unsplit; no Mathlib match. This is a geometric presentation lemma, with no derived-functor or unit assertion.
- citations.json: literal statement quotes for all 33 step/node citations.
- searches.jsonl: the search command's unmodified query/result log; every recorded new-node query was actually run.
- report.md: this report.

## Attachments

None. Searches of lean/WeilConjectures by the blueprint tag, punctured tower, rootTower and Kummer gave no declaration stating this item. The related root-tower input declarations under lean/Sheaf are sorried, not completed attachments. No Lean was changed or compiled.

## Sources wanted

WANTED: a human-written proof of the all-continuous E/Omega punctured Kummer face diagram, for lem-sfb-root-tower-punctured-face-diagram. The recorded blueprint direct-images paragraph (3) gives the open/proper route, not this extracted theorem. Existing puncture-invariance and coordinate-face statements are the exact geometric interfaces used here. The parent proof is honestly marked agent-written.

No new literature is needed to state the new geometric lemma: I read Stacks etale.tex Tag 0BIA (lemma-strict-normal-crossings), algebra.tex Tag 00NQ (lemma-regular-ring-CM), and Tags 00UB/00UC (definition-standard-etale/lemma-standard-etale). The first identifies the vanishing branch equations as distinct parameters, the second describes their regular quotients, and the third gives etaleness of roots of units. These are supporting places, not a claim that Stacks literally states the assembled infinite-tower presentation.

## What changed and what was wrong

The item had no proof. Its exact statement and stmt_deps are retained; there is no statement dispute or weakening. The chart needs care: B_J can be disconnected, a remaining label can be a unit or can have disconnected zero locus, and the unbounded functors cannot simply be replaced by degreewise base change. The new geometric input handles the first issue; open-slice comparisons on K-injectives handle the second. Applying the original chart hypothesis directly to the whole residual face would be unjustified.

The current main-20261015 unit and its paragraph (3) were read alongside the chapter and recorded unit JSON. The unit JSON still refers to the older chapter sec-six-functors and older snapshot. I retain the item's current sec-six-functors-basics chapter and its inherited unit, and follow paragraph (3) of its recorded current source. This is not the unit's key node and I do not change its realization record. blueprint_refs.py ancestor returns None; the inherited null ancestry and via chain are retained, with a precise from.place. Whole-blueprint searches for punctured tower, coordinate face, root face, root stratum and residual root found no equivalent statement (the apparent root/face hits concern Tate twists, weights, purity and projective space).

## Review by Q18

I read delivery-errors B–E whole (both copies), the item's current source paragraph, and every statement cited by the seven proof steps. I checked the public statements themselves, rather than borrowing assertions from their proofs. I did not use any SGA source.

Step 1 uses internal-module-operations-transport to pass to ring-sheaf modules without changing adjunctions; ring-sheaves-grothendieck supplies the category property, grothendieck-enough-injectives supplies injectives, and left-exact-injective-resolution-degree-zero supplies resolutions with exactly zero negative terms. kinjective-computes states that these bounded-below injective complexes are K-injective. module-derived-pushpull computes the total functor on them; module-lower-star explicitly states additivity and left exactness. Thus applying either structural direct image leaves negative terms zero. This proves the two boundedness assertions for the actual unbounded functors, without claiming a cohomological upper bound or a complete coefficient field.

Step 2 applies puncture-invariance only on the original full tower with the supplied lisse module: the outer subset and the whole index set are allowed, including the empty outer subset. profinite-base-change identifies the P terms and their opens. The intermediate unit is the open restriction of the full-puncture unit. I explicitly added module-direct-image-open-pasting and kinjective-direct-image-open-word-model to justify deriving the open-slice comparison, plus alpha-iso for its coefficient hypothesis. clean-open-unit-parametrized-exchange identifies the actual unit under that comparison. derived-composition-adjunction-normalization says exactly that the derived composite unit is the actual composite unit. Hence lambda is the required inverse, not a chosen unrelated isomorphism.

Step 3 pulls the lisse module to a zero-root face. The definition of lisse gives finite-free local trivializations; exact module pullback and the coefficient identification preserve these. The new residual chart statement supplies the missing regular finite-type chart for the reduced face, absorbs the roots of inactive units into an affine pro-etale base, and identifies the outer open with a subset of active parameters. These are precisely the hypotheses of puncture-invariance, now applied on each residual chart. Open-pasting plus the K-injective word model identify local restrictions of the global unit with those local units. The final assertion is elementary sheaf gluing on the open cover: all cohomology sheaves of its cone restrict to zero. I do not invoke conservativity of points for condensed coefficients.

Step 4 uses coordinate-face verbatim: its beta is the pullback-of-counit adjunct, it is invertible, and its statement explicitly includes open restriction. I apply it over U and restrict to V. ringed-open-closed gives exact closed direct images; I checked its quasi-compact-complement assumption, since the complement of U_J (and V_J) is the finite union of the principal opens D(t_j). Composition-normalization identifies the middle composite after ad_J = g_J a_J. The formula for tau is an explicitly typed composite from the punctured closed term to g_* H_J. Inverting beta_U then gives mu.

Step 5 is the normalization check. Naturality of the closed unit first removes kappa. The two remaining composites factor restriction to the same scheme T_{J,V}[P] in opposite orders. coordinate-face explicitly identifies its closed adjunct with Rq_* of the actual closed unit; mate-pasting and derived-composition normalization identify the two composites, because both transpose to the identity on the restricted module. Cancelling omega and beta gives mu Ra_*(u) nu_all = v and then mu Ra_*(u) = v lambda. This checks equality of specified arrows, not merely invertibility of source and target objects.

Step 6 uses the coordinate-face statement's successive-restriction clause. The extra open units are natural with respect to the closed-unit maps. Pasting their mates makes both paths the restriction to T_{J',V}[P]; cancellation gives the nested-face equation. There is no new theorem concealed in this elementary composition argument: the non-elementary mate-pasting input is explicitly cited. Together with the augmented-unit equation this covers every arrow of the finite face diagram.

Step 7 uses the stated module-map, parameter-map, pro-etale-change and action naturalities of puncture-invariance, coordinate-face and clean-open-unit-parametrized-exchange. I checked that their statements explicitly say equality on whole Q-parametrized terms. profinite-base-change identifies T[P][Q] with T[P x Q]. Composition and inversion of the same commuting squares prove the requested family equality without a pointwise test. The residual chart choices enter only the proof of invertibility of omega, never its definition, so they create no functoriality choice.

For the new node I read the local parameter/regular intersection argument of Stacks 0BIA and the quotient result 00NQ, as well as the standard-etale criterion 00UB/00UC. Its proposed proof for a future worker is as follows. Work at a point of B_J; its vanishing original equations are distinct parameters. Quotient by J and keep their remaining images. Shrink to an affine neighbourhood on which all other labels are units and every active zero locus has the single integral component through that point; distinct active intersections cannot coincide because their local codimensions differ. These active equations give an SNC boundary on the residual regular neighbourhood. Over the corresponding pro-etale base R_W, adjoin only the inactive roots. Each finite stage and each transition is finite etale: n and every root of a unit are invertible, so n x^(n-1) is invertible. The filtered limit is affine pro-etale. Adjoining the remaining active roots over this base gives exactly the original algebra: use the common divisibility multiple to compare the double colimit and the diagonal colimit, with coefficients and root generators fixed. Localization removes only the active factors because the inactive factors are already units. All maps are fixed on generators, so base change commutes. Profinite parameters are another base change. This is a new geometric presentation, not a clause of the parent's derived conclusion; it is not split here.

Small cases checked: r=1 and J all indices leave no root variables; J empty recovers the full tower; disconnected B_J is covered componentwise, not assumed connected. The affine-plane axes give the expected residual one-variable root tower. An outer parameter that is a unit contributes only to D_W, while an outer parameter with empty face makes the relevant term zero. For a rank-zero module all functors give zero objects. I_o empty makes b and b_J identities; a singleton inner set has just one face. Empty P, an empty chart, an empty residual intersection and the zero coefficient/base ring introduce no nonexistent point or required nonempty cover. No partition exists for r=0 with I_i nonempty. The profinite-family argument includes Q empty and Q a singleton. No step uses completeness of Omega, a boundary trivialization or an internal-Hom comparison.

C1/C4 audit: all non-elementary inputs above have cited nodes and literal statements in citations.json. B1: the new node has no proof, proof_deps or proof sketch in its statement. B2/B3: it introduces all rings, indices, maps and hypotheses and cites the notions it uses. B4: single TeX escaping was checked after parsing JSON. B5: supporting source labels/tags were read. B6/B8: no false Mathlib leaf is declared. B7: all new-node searches are exactly command-log entries, with their actual hits and no claimed outage. B9/B10: blueprint/Lean searches were performed before writing the new node. D1/D2: the derived assertions are assembled from existing geometric inputs, not copied into new nodes. D3–D5: the residual geometric subclaim is made explicit, and the unit/mate computations remain in the parent. E1–E6: regularity, separated finite type, affine pro-etale chart, lisse coefficients, exact closed images and quasi-compact complements were checked at each application. E7: no mathematical source error was found. No step exceeds 2000 characters; the longest is the residual-chart assembly, which cites the separate geometric lemma instead of hiding it.

## Not duplicates

lem-sfb-residual-root-tower-local-charts vs lem-per-embedded-surface-curve-resolution: the existing statement concerns embedded snc resolution on a regular surface; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-per-ind-etale-regular-coordinate-locus: the existing statement concerns openness and ind-etale invariance of a labelled regular-coordinate locus; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-per-marked-finite-diagram-approximation: the existing statement concerns regularity and boundary intersections persist under sufficiently fine marked approximation; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-per-ordinary-henselian-pointed-neighbourhood-limit: the existing statement concerns ordinary henselization as a limit of residue-preserving affine etale neighbourhoods; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-per-regular-pair-alteration-pullback: the existing statement concerns regular base change preserves regular alteration pairs; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-per-snc-boundary-parameter-criterion: it is the same local SNC criterion, with no residual tower or infinite unit-root algebra.

lem-sfb-residual-root-tower-local-charts vs lem-per-snc-root-algebra-structure: the existing statement concerns structure of the simultaneous parameter-root algebra over a strict local ring; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-per-tame-kummer-group-algebra-completion: the existing statement concerns tame finite-index group algebra base change; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-fd-artin-schreier-finite-lisse: the existing statement concerns artin–schreier character sheaves over arbitrary finite rings are flat lisse lines; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-weil-pbc-etale-locally-standard: the existing statement concerns etale algebras are zariski-locally standard etale (stacks 00ue); it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-weil-pbc-etale-ring-map-prescribed-residue-field: the existing statement concerns an etale ring map realizes a prescribed finite separable residue field extension at a prime; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-weil-pbc-etale-section-lifting-henselian-pair: the existing statement concerns lifting of sections of etale algebras implies henselian pair; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-weil-pbc-etale-section-lifting-idempotents: the existing statement concerns idempotent lifting from etale section lifting; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-weil-pbc-etale-section-lifting-radical-and-henselian: the existing statement concerns radical and root-lifting consequences of etale section lifting; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-weil-pbc-standard-etale-monic-derivative: the existing statement concerns the standard etale algebra of a monic polynomial localized at its derivative; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-weil-pbc-standard-etale-pair-maps: the existing statement concerns maps out of a standard etale algebra are roots f(b)=0 with h(b) a unit; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-weil-pbc-strict-henselization-triples: the existing statement concerns the colimit over etale algebras with a point and a residue embedding is strictly henselian; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-coef-infinity-equivalence-section-restriction: the existing statement concerns equivalences preserve strict section spaces of right fibrations; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-coef-infinity-full-essential-image: the existing statement concerns a fully faithful infinity-functor is equivalent to its full essential image; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-coef-infinity-isofibration-pullback-equivalence: the existing statement concerns pullback along an equivalence over an isofibration is an equivalence; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-coef-infinity-op-mapping-reversal: the existing statement concerns opposite quasicategories reverse mapping spaces and composition; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-coef-joyal-walking-isomorphism-fibration-test: the existing statement concerns walking-isomorphism lifting test for joyal fibrations; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-coef-kan-homotopy-pullback-invariance: the existing statement concerns weak-equivalence invariance of path-model homotopy pullbacks; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-coef-kan-nerve-pullback-recognition: the existing statement concerns path pullbacks recognize cartesian squares in the coherent nerve of kan complexes; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-coef-kan-weak-equivalence-space-edge: the existing statement concerns weak equivalences of kan complexes give coherent-nerve equivalence edges; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-coef-quillen-b-discrete-fibration-base-change: the existing statement concerns quillen b base change along a discrete fibration; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-coef-simplicial-relative-homotopy-invariance: the existing statement concerns invariance of relative simplicial homotopy classes under target equivalence; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-closed-component-stalk-calculus: the existing statement concerns closed components, reduced unions and intersections at ordinary stalks; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-equivariant-nodal-smooth-pair-resolution: the existing statement concerns equivariant resolution of one split marked nodal curve over a smooth pair; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-nested-open-regular-alteration: the existing statement concerns regular alteration adapted to nested opens and a prescribed finite cover; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-parameter-root-punctured-cover-tower: it treats the punctured full-root cover, not an unpunctured zero-root face with inactive roots absorbed.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-pointed-cover-compatible-unit-roots: the existing statement concerns compatible unit roots and roots of unity on a pointed universal cover; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-proper-generic-radicial-etale-factorization: the existing statement concerns generic radicial-etale factorization of a proper generically finite map; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-quasi-split-tower-smooth-resolution: the existing statement concerns smooth resolution of a quasi-split marked nodal tower and its cartier sub-boundary; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-snc-boundary-parameter-criterion: it is the equivalence defining SNC locally, with no residual tower or infinite unit-root algebra.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-snc-branch-equation-nonzerodivisor: the existing statement concerns branch equations of an snc boundary on a regular affine chart are nonzerodivisors; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-snc-finite-root-face-regular: it proves regularity of finite-level faces only, not the residual local active-root presentation.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-snc-finite-root-regular-ring: the existing statement concerns regularity of finite simultaneous roots along strict normal crossings; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-snc-finite-tame-root-model: the existing statement concerns finite tame pro-etale sheaves have finite root-level etale models; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-snc-labelled-affine-stratum-charts: it provides charts around a deepest stratum after removing other components; it does not identify the full residual tower along arbitrary J or absorb inactive unit roots.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-snc-labelled-root-algebra-geometry: it handles finite root algebras on the original chart, not the zero-root residual face and the infinite inactive-root pro-etale base.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-snc-root-local-presentation: it gives local quotients and finite-stage localization at a prime, but no open residual cover, inactive full-root base or isomorphism of infinite active towers.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-snc-root-stage-system: it gives finite regular stages and a full-tower open pair before quotienting coordinates, not the residual-face active/inactive presentation.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-snc-tame-root-etale-extension: the existing statement concerns a finite tame cover has an etale model after a simultaneous finite root base change; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-transverse-prime-ideal-parameters: it is a local-ring parameter/quotient theorem; it has no open-chart, pro-etale or full-root presentation assertion.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-unit-binomial-derivative-presentation: it gives a finite polynomial derivative certificate, not the residual infinite-tower geometry.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-unit-binomial-finite-etale: it treats one finite root of a unit, not a residual SNC chart or the infinite active/inactive presentation.

lem-sfb-residual-root-tower-local-charts vs lem-cbc-kan-fibration-fiber-criterion: the existing statement concerns contractible fibers and trivial kan fibrations; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-cbc-kan-realization-mapping-classes: the existing statement concerns realization compares homotopy classes into a kan complex; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-cbc-kan-whitehead-inverse: the existing statement concerns a realization weak equivalence between kan complexes has a simplicial homotopy inverse; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-cbc-simplicial-homotopy-equivalence-weak: the existing statement concerns simplicial homotopy equivalences are realization weak equivalences; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-cbc-standard-simplex-mapping-contractible: the existing statement concerns standard-simplex coherent mapping sets are contractible; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-weil-pbc-localized-separable-polynomial-model: the existing statement concerns descending a separable minimal polynomial and its bezout identity; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-trf-nodal-pair-projective-resolution: the existing statement concerns resolution of a nodal curve over a smooth normal-crossings pair; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-trf-snc-divisorial-log-chart: the existing statement concerns divisorial charts of a smooth strict normal crossings pair; it does not assert the residual open-chart cover and the infinite inactive/active root-algebra identification.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-unit-root-coordinate-tower-comparison: assumes coherent roots of units are already supplied and rescales equations; it does not construct the pro-etale inactive-root base on a residual face.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-root-tower-coordinate-face: asserts normalized derived closed base change, not a geometric residual-chart presentation.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-root-tower-profinite-base-change: asserts scalar-extension and profinite-product formulas, not the SNC residual geometry or inactive-root etaleness.

lem-sfb-residual-root-tower-local-charts vs lem-sfb-active-root-tower-normalization-splitting: descends a supplied punctured cover splitting and normalization, rather than presenting zero-root faces as active towers.

lem-sfb-residual-root-tower-local-charts vs lem-trf-etale-coordinate-intersection-geometry: gives regularity and etale base change of coordinate intersections, without infinite root presentations or an inactive-unit base.

## Unfinished work and validation

The new geometric node is intentionally statement-only for the next stage-1 item. All seven parent proof steps are complete relative to their cited statements; no requested parent clause is left as a new obligation. Server review_split was run once before the report and passed; its route notices led me to declare three additional generic tools explicitly. The full dry run and push are the next actions. No repository, launcher or Lean source file was written.
