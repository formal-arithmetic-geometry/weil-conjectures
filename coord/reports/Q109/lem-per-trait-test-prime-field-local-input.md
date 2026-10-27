1. Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-trait-test-prime-field-local-input.json: assigned statement unchanged; new three-step proof through strict completion, smooth parameter models, finite-type coordinate Kummer purity, and supported continuity.
- dag/nodes/sec-deligne-laumon-a1/lem-per-prime-local-smooth-parameter-models.json: new statement-only algebraic approximation input; Mathlib verdict no match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-prime-smooth-coordinate-kummer-purity.json: new statement-only ordinary derived Kummer-purity input for finite-type smooth coordinate pairs over either prime field; Mathlib verdict no match.
- citations.json: ten exact statement quotations, one for each node cited in each step.
- searches.jsonl and search-results/: retained original item searches and ten actually executed searches for the new nodes, with their results. No search was invented or silently rerun.
- repair-history/report-64300314e12.md: retained report of the returned delivery, superseded by this repair report.

Two new nodes, zero Mathlib leaves. No unit or chapter changed.

2. Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and punctual/prime-field purity notions found no finished declaration proving this item. The KummerClass.lean normalization interface assumes its rank-one purity assertion; it does not prove the assigned local purity theorem. Neither new node has an exact project declaration.

3. WANTED

None. The consulted ILO, Stacks, Milne, and current blueprint sources are available locally. The proof is marked agent-written because the simultaneous algebraic approximation and the ordinary prime-field coordinate interface are formulated here; ILO Proposition 3.2.5 alone is not a proof of this split.

4. Findings and corrections

This repairs every part of the C4/C5 route and D2 return of 64300314e12. The previous proof merely specialized lem-per-prime-field-punctual-purity. That theorem belongs to the withdrawn Q45 graph and remains listed in coord/route-pivot-dropped.txt. The Q84 re-admission record coord/changes/20261024-Q84-gabber-purity-inputs.md does not re-admit it. The previous report's assertion that reusing its statement avoided the excluded route was wrong: a statement citation re-attached that graph. The parent Q08 return and accepted ce9cc357 replacement are consistent with the present local item being a fresh obligation, not a request to reuse the withdrawn theorem. This repair removes that citation entirely, including its scheme-level relabelling argument.

The proof now uses the admitted local strict-completion and supported-continuity interfaces. The two new inputs do different substantive work: one constructs simultaneous smooth finite-type coordinate models, and one proves their canonical derived Kummer maps invertible. Neither is the assigned arbitrary regular-local purity conclusion or one of its clauses. In particular the finite-type smooth-coordinate hypothesis is much stronger than the item's arbitrary regular local k0-algebra hypothesis; passing between them needs the algebraic model theorem, the supported-arrow continuity theorem, detection over the separably closed residue field, and strict-completion descent. No new node simply restates the item.

No STATEMENT-DISPUTED: the assigned statement agrees with ILO XVI Definitions 3.2.1--3.2.2 and Proposition 3.2.5. The item still assumes no excellence or finite type. Both new nodes have their own complete hypotheses, ordinary derived conclusions where relevant, statement dependencies, actual searches, and filled blueprint.from.place and same_as fields. Their nearest blueprint ancestor is lem-per-artin-gabber-affine-curve, proof Step 3, through the item and the recorded parent chain. Whole-DAG and blueprint searches for prime field, regular pair, smooth coordinate, smooth pair, Kummer Gysin, and the source tags found no admitted node giving either new statement.

5. Unfinished work

The two new inputs remain unsplit, as required for a one-level stage-1 delivery. This report supplies the mathematical checks and intended source route, not an assertion that their Lean proofs exist. There is no unfinished assembly step in the assigned item.

## Not duplicates

The following includes every existing node containing one of the four algebraic source tags, even when a tag occurs only in an existing proof or search result. The other close coordinate-purity candidates are also compared. Shared source tags do not mean the whole statements coincide.

lem-per-prime-local-smooth-parameter-models vs def-weil-pbc-filtered-colimit-smooth-algebras: the existing node concerns "Filtered colimit of smooth algebras ('PT holds')"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs def-weil-pbc-g-ring: the existing node concerns "G-ring"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs def-weil-pbc-popescu-resolution: the existing node concerns "The ideal h_A and resolutions of R -> A -> Lambda ⊃ q (Popescu's local problem)"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-coef-enriched-marked-realization: the existing node concerns "Degreewise relative categories realize enriched localization"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-complete-base-algebraic-dualizing-existence: the existing node concerns "Dualizing complexes over essentially finite type complete-local bases"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-complete-local-excellence: the existing node concerns "Complete Noetherian local rings are excellent"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-complete-mixed-regular-pair-approximation: the existing node assumes mixed characteristic and approximates over a complete Cohen trait; the new node assumes a prime-field algebra and gives smooth stages over its polynomial parameter ring.

lem-per-prime-local-smooth-parameter-models vs lem-per-completed-base-regularity: the existing node concerns "Regularity is unchanged on completing the base of a continuous adic map"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-excellent-normal-surface-local-data: the existing node concerns "Local data at the singular points of an excellent normal surface"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-g-ring-local-closed-fibre-criterion: the existing node is a criterion for regularity of a local map with regular source completion; it gives no smooth parameter models or quotient colimits.

lem-per-prime-local-smooth-parameter-models vs lem-per-gabber-partial-algebraization: the existing node concerns "Partial algebraization of a complete normal strictly local scheme"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-inseparable-surface-differential-data: the existing node concerns "Finite differential coordinates for a prime-degree inseparable surface cover"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-normal-surface-cover-completed-degree: the existing node concerns "Normalization covers of regular surfaces and their completed local degrees"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-normalized-tower-regular-pullback: the existing node concerns "Normalization of centered towers and regular pullback"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-pointwise-log-regular-completion: the existing node concerns "Completed sharp chart at a single log regular point"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-prime-field-complete-coordinate-model: the existing node is excluded; its conclusion is a coefficient-field power-series presentation, whereas the new node supplies smooth finite-type prime-field parameter models with a simultaneous residue-quotient colimit. It is neither cited nor re-admitted.

lem-per-prime-local-smooth-parameter-models vs lem-per-prime-field-punctual-purity: the existing node is excluded and concerns cohomological purity. The new algebraic node has no cohomological assertion and constructs simultaneous smooth parameter models. No edge to the excluded theorem or its proof is added.

lem-per-prime-local-smooth-parameter-models vs lem-per-regular-etale-direct-image-base-change: the existing node concerns "Regular base change for etale derived direct image"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-regular-morphism-formal-completion: the existing node concerns "Regular morphisms remain regular after formal completion"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-rig-regular-formal-resolution: the existing node concerns "Strong regular-functorial resolution of rig-regular formal varieties"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-simultaneous-cohen-rigidification-lift: the existing node concerns "Simultaneous Cohen ambient lift of two tame rigidifications"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-per-small-divisor-formal-completion: the existing node concerns "Small-divisor completion gives a rig-regular locally principal formal variety"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-sfb-affine-properness-formal-arc-test: the existing node concerns "Testing properness of affine finite-type morphisms by formal arcs"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-sfb-regular-local-separable-residue-adic-smooth: the existing node proves adic formal smoothness of the field map; the new node gives smooth algebras over the polynomial parameter map and both colimit identifications.

lem-per-prime-local-smooth-parameter-models vs lem-trf-artin-approximation-etale-local-map: the existing node concerns "Artin approximation by an etale local algebra"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-bennett-normal-flat-numerical-criterion: the existing node concerns "Bennett numerical criterion for normal flatness along a regular prime"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-compatible-coefficient-source-presentation: the existing node concerns "Compatible coefficient fields and a source Cohen presentation"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-complete-local-ci-presentation-independence: the existing node concerns "Independence of a regular-sequence kernel from the regular-local presentation"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-completed-chart-coefficient-surjection: the existing node concerns "Coefficient construction and surjectivity for a completed monomial chart"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-completion-local-complete-intersection: the existing node concerns "Complete-intersection neighbourhoods detected by the completed local ring"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-equicharacteristic-complete-local-presentation: the existing node gives a power-series surjection for a possibly singular ring, not smooth prime-field stages or simultaneous regular quotient limits.

lem-per-prime-local-smooth-parameter-models vs lem-trf-generic-center-formal-normal-slice: the existing node concerns "Generic smooth centers and completed normal coordinates"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-generic-monotone-diagram: the existing node concerns "Generic monotone diagram and regular vertex generators"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-log-regular-completed-chart: the existing node concerns "Completed local charts of an fs log regular scheme"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-normalized-curve-branch-coordinates: the existing node concerns "Power-series coordinates on the actual normalized curve branches"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-ordinary-point-delta-branches: the existing node concerns "Ordinary curve points characterized by delta and branch number"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-parameter-chart-completion-substitution: the existing node concerns "Completed parameter charts preserve a chosen coefficient section"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-projective-order-completed-normal-form: the existing node concerns "Completed normal form and weighted order at a projective point"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-rational-nodal-completion-algebra: the existing node concerns "Coefficient-compatible presentation of a rational split-node completion"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-regular-complete-coefficient-coordinates: the existing node requires a specified coefficient-field section and identifies a power-series ring; it gives no smooth polynomial-base approximation or quotient diagram.

lem-per-prime-local-smooth-parameter-models vs lem-trf-relative-cohen-flat-presentation: the existing node gives compatible complete presentations for a flat local Q-algebra map; it supplies no smooth finite-type prime-field model system.

lem-per-prime-local-smooth-parameter-models vs lem-trf-relative-nodal-point-pinching: the existing node concerns "Finite smooth-point pinching on curves proper over a reference scheme"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-relative-power-series-fibre-diagram: the existing node concerns "Relative power-series evaluation and its closed-fibre diagram"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-surjective-kernel-nonzerodivisor-dimension-drop: the existing node concerns "A surjection killing a nonzerodivisor drops Krull dimension"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-taylor-normal-cone-splitting: the existing node concerns "Associated graded comparison for the local Taylor map"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-test-sequence-order-recovery: the existing node concerns "Recovery of point and boundary orders from test sequences on cosupport"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-trf-varying-base-smooth-span-model: the existing node descends a pointed etale span over a completed finite-type Z-scheme; it does not apply to arbitrary complete prime-field regular local rings or supply this parameter quotient system.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-coefficient-residue-section: the existing node concerns "A section of the characteristic-zero residue map"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-coefficient-subring-principal-source: the existing node concerns "Coefficient properties of the image of a complete local PID"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-cohen-coefficient-ring-exists: the existing node concerns "Cohen structure theorem: a complete local ring has a coefficient ring"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-cohen-power-series-presentation: the existing node concerns "Cohen power series presentation of a complete local ring"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-cohen-ring-lift-complete-local: the existing node concerns "Lifting a prescribed Cohen-ring residue isomorphism"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-cohen-structure-power-series-surjection: the existing node concerns "Cohen structure theorem: a complete local ring is a quotient of a power series ring over a field or a Cohen ring"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-complete-local-domain-finite-over-regular: the existing node concerns "A Noetherian complete local domain is finite over a regular complete power series subring"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-complete-local-flat-presentation: the existing node concerns "A local map of complete Noetherian local rings has a flat Cohen presentation"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-complete-local-map-cohen-presentation: the existing node concerns "Compatible Cohen power-series presentations of a complete local map"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-complete-local-map-regular-presentation: the existing node concerns "Compatible regular presentations of a map of complete local rings"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit: the existing node factors a finitely presented algebra map through an already-given diagram; it does not construct the smooth approximation or establish regularity of its pairs.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-first-order-power-series-comparison: the existing node concerns "First-order power series comparison for a complete local algebra over a field"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-g-ring-completion-regular: the existing theorem concerns only regularity of a completion map; the new node constructs a smooth parameter approximation and its simultaneous residue quotient over a prime field.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-henselian-pair-approximation: the existing node approximates finite polynomial solutions in a henselian G-ring; the new node constructs smooth models of a complete regular local ring and its closed point.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-local-first-order-coordinates: the existing node concerns "Square-zero coordinates on a local ring with a residue section"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-minimal-prime-over-proper-ideal: the existing node concerns "A proper ideal has a minimal prime over it"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-noetherian-ideal-set-maximal: the existing node concerns "In a Noetherian ring every nonempty set of ideals has a maximal element"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-popescu-final-solve: the existing node concerns "If the singular ideal generates the unit ideal of Lambda, A -> Lambda factors through a smooth algebra"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-popescu-reduce-to-field: the existing node concerns "Popescu's theorem reduces to a field as base"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-popescu-resolve-char-p: the existing node concerns "Popescu's local problem is resolvable in characteristic p for geometrically regular Lambda"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-popescu-resolve-separable: the existing node concerns "Popescu's local problem is resolvable at a regular prime with separable residue field"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-popescu-smoothing: the existing theorem assumes a regular map and gives a small filtered diagram; the new node must establish regularity of the polynomial parameter map, choose a directed-poset presentation, and retain regular residue quotients and their limiting immersion.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-power-series-first-order-coordinates: the existing node concerns "Constant and linear coordinates on the first-order power-series quotient"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-power-series-quadratic-ideal: the existing node concerns "Vanishing constant and linear coefficients imply membership in the quadratic variables ideal"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-power-series-universal-property-complete: the existing node concerns "Universal property of a power series ring mapping into a complete ring"; it does not assert a simultaneous smooth polynomial-parameter model system for an arbitrary complete prime-field regular local ring with the stated regular quotient and colimit compatibility.

lem-per-prime-local-smooth-parameter-models vs lem-weil-pbc-smooth-polynomial-factorization: the existing node factors one finite polynomial solution through a smooth algebra after assuming regularity; it does not establish the parameter-map regularity or construct the simultaneous quotient system.

lem-per-prime-smooth-coordinate-kummer-purity vs cor-pur-affine-space-zero-section-purity: the existing node uses the fixed finite datum over the blueprint ground field and its pro-etale realization; the new node concerns ordinary etale F_ell sheaves on smooth pullbacks of the origin over Q or F_p. The fixed-ground-field assertion cannot be specialized to Q.

lem-per-prime-smooth-coordinate-kummer-purity vs lem-pur-finite-type-coordinate-support-orientation: the existing node is a zero-section statement over the fixed blueprint field; the new node is the ordinary derived Kummer map for smooth coordinate pairs over either prime field, including Q.

lem-per-prime-smooth-coordinate-kummer-purity vs lem-per-smooth-divisor-kummer-purity: the existing node is excluded, assumes an algebraically closed ground field, and gives codimension-one cohomology maps. The new node concerns the derived canonical map for smooth coordinate pairs over prime fields in arbitrary codimension; it does not cite the excluded node.

lem-per-prime-smooth-coordinate-kummer-purity vs lem-per-noetherian-prime-power-smooth-duality: the existing node is excluded and asserts all-Noetherian smooth exceptional duality. The new node is restricted to finite-type smooth coordinate pairs over prime fields and specifies ordinary closed-support Kummer purity; no exceptional smooth-duality statement is used.

## Review by Q109

I reread delivery-errors.md B--E against the repaired files. For the assigned item I read ILO Expose XVI, printed pp.244--245 (PDF pp.250--251): local Kummer purity is Definition 3.2.1, punctual purity is Definition 3.2.2, strict-completion invariance is Proposition 3.2.4, and prime-field purity is Proposition 3.2.5. Proposition 3.2.5 states the result and cites Fujiwara; it does not itself supply the new algebraic and geometric argument. Accordingly the assembly is agent-written, and the two new non-elementary inputs are stated explicitly. No SGA source is used.

For lem-per-prime-local-smooth-parameter-models I read Stacks algebra.tex Tag 032A (Cohen structure) and Tag 0C0S (regular complete rings containing a field), more-algebra.tex Tag 0AH2 (regularity of G-ring completion), and smoothing.tex Tag 07GC (Popescu). The construction is as follows. Choose a residue-field section F into B and regular parameters t by Cohen; the chosen parameter map identifies B with F[[t]]. The map k0[T] to F[T] is regular because k0 is perfect, so every field extension F/k0 is geometrically regular. The T-adic completion map F[T] to F[[T]] is regular: the polynomial ring over a field is excellent, hence a G-ring, and Tag 0AH2 applies. Their composite k0[T] to B is therefore regular between Noetherian rings. Popescu yields a small filtered diagram of smooth k0[T]-algebras, which can be indexed cofinally by a small directed poset. Base change to T=0 gives smooth k0-algebras D_a, and quotient commutes with this colimit. The maps D_a to F make every quotient nonzero. Flatness over the polynomial ring preserves the successive parameter injections; smoothness over a regular field or polynomial ring gives regular Noetherian stages. Thus the regular equations, their fixed order, and both limiting rings are retained. This is a genuine algebraic approximation lemma, not just Cohen's coordinate isomorphism or Popescu with its regularity hypothesis left unchecked. Its future one-level proof can cite existing generic Cohen/completion/Popescu nodes; no withdrawn cohomological node is needed.

For lem-per-prime-smooth-coordinate-kummer-purity I read Milne, Lectures on Etale Cohomology, section 16, Theorem 16.7 and Lemma 16.8, printed pp.111--112. These treat smooth pairs over an arbitrary field and their etale local coordinate charts, reducing the calculation to the rank-one curve case and products. I also read literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/cor-pur-affine-space-zero-section-purity.proof.md in full. Its ordinary affine-space adjunction, normalized projective-line trace sending the positive coordinate class to 1, and ordered products specify the Kummer normalization of the derived zero-section map. The new finite-type prime-field interface combines this coordinate argument with smooth local charts; it does not claim Milne alone states this exact normalized derived interface. It deliberately does not apply thm-pur-finite-coefficient-smooth-purity or the existing fixed-field zero-section statements over Q. The admissible proof route is the lecture-note coordinate/diagonal construction and the normalized affine-line calculation, with ordinary etale witnesses; no withdrawn all-Noetherian smooth-duality theorem and no forbidden trace source is imported.

For Step 1 I opened def-weil-regular-scheme and the codimension-zero clause of lem-per-regular-immersion-class-calculus. A dimension-zero regular local ring has maximal ideal generated by zero elements, hence is its residue field, and the identity class is 1. I opened lem-per-trait-test-strict-completion-input: it explicitly supplies Noetherian regularity, dimension, complete strict henselianity, the separably closed residue field, invertibility of ell, and the implication from the canonical completed map to the original one, without excellence. The unital prime-field map into the nonzero ring B is injective, so no new equicharacteristic assumption is being added.

For Step 2 I read both new statements against the model construction above. Their common polynomial base is k0[T_1,...,T_d], every stage is regular affine Noetherian with nonzero smooth residue quotient, and the coordinate equations and their order are fixed under transitions. The first node gives both colimit identifications, not just approximation of finitely many elements. The second node gives the actual canonical Kummer morphism and its derived supported sections, not an unspecified abstract isomorphism or only degreewise ranks. Invertibility of ell at every stage follows already from the prime field: over Q it is automatic, while over F_p the item forces ell != p. Consequently the second node applies with c=d and exactly A=F_ell.

For Step 3 I opened lem-per-trait-test-supported-kummer-continuity and checked each of its hypotheses against Step 2: the indexing set is small, nonempty and directed; all schemes and limits are regular affine Noetherian; transitions are affine; the preserved global sequence has length d; and ell is invertible. That statement explicitly identifies the limiting canonical Kummer arrow, including its sign, through a derived commutative square whose vertical maps are isomorphisms. It requires no flatness of the transition maps. I opened def-per-closed-support-plus-adjunction and lem-amb-closed-support-hom: the former fixes the ordinary bounded-below adjoint and the latter identifies derived Hom out of the closed constant sheaf with the support cone. Together these identify this supported arrow with derived sections of the exact map being tested. I opened lem-exc-etale-sheaves-gsets-point: over the separably closed F its Galois group is trivial, so the sheaf equivalence induces the exact conservative equivalence on A-modules. Therefore sections detect all cohomology isomorphisms. I opened lem-weil-pbc-unbounded-derived-iso-cohomology, which gives precisely the isomorphism criterion used; D+ is a strictly full subcategory of the unbounded category by def-weil-pbc-derived-categories, already among the item's statement dependencies. Finally Step 1 descends the resulting canonical isomorphism. The two off-unit generic tools are declared in split_report.tool_uses; neither replaces the unit's purity route.

I checked small cases: d=0 and c=0 use empty products and identity immersions; positive characteristic excludes ell=p; arbitrary characteristic-zero residue extensions are allowed; the residue field may be imperfect in positive characteristic despite k0 being perfect. Cohen coefficients need only fix the prime field, which any unital field section does. No finite generation of F/k0 is assumed. The approximation theorem makes stages nonzero through their maps to B and F; quotient stages cannot disappear. Smooth affine morphisms here are quasi-compact and quasi-separated, hence finite presentation, so the finite-type coordinate calculation applies. The original R need not be excellent: only the polynomial ring over the coefficient field is used as a G-ring.

The source-tag duplicate comparisons above distinguish the new simultaneous model lemma from each existing coordinate, formal-smoothness, factorization, and mixed-characteristic assertion. The finite-type coordinate lemma is distinct from the existing fixed-ground-field statements and from excluded broader assertions. New nodes are statement-only, not split a second level. Elementary identities and the exact-conservative-equivalence consequence stay in the assembly steps rather than becoming artificial nodes. Every proof step is below 2000 characters and the whole assembly is below 3000; there is no hidden long lemma in an assembly step.

I read all ten new Mathlib-search outputs, retaining their exact tool/query text and raw hits. LeanFinder was tried with two phrasings for each new node; Loogle, grep, and LeanSearch were also run. Hits concern smooth charts, power-series division, formal smoothness, residue fields, and polynomial loci; none gives the simultaneous parameter approximation or the derived etale Kummer purity assertion. The original item's unchanged search question reuses its retained logged results. There are zero new Mathlib leaves.

Every entry of citations.json is checked against the exact statement of the node used in that numbered step. I traversed statement and proof dependencies of the repaired item and both new nodes against the current route-pivot exclusion list: no excluded node is reachable and no path cycles back to the item. The previous report's dependency audit checked only circularity and missed exclusion; this repair checks both. The excluded Q45 purity theorem, its complete-coordinate node, regular-supported-base-change node, and all-Noetherian smooth-duality node are not cited or used as proof inputs. The retained old report is history only and is explicitly superseded here.
