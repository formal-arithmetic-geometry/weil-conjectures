Files written:
- dag/nodes/sec-trace-formula/lem-trf-krull-principal-primary-decomposition.json — repaired statement split; no statement change; Mathlib searches found no exact item match.
- dag/nodes/sec-trace-formula/lem-trf-height-one-localization-dimension.json — statement-only Mathlib leaf, exact `IsLocalization.AtPrime.ringKrullDim_eq_height`.
- dag/nodes/sec-trace-formula/lem-trf-dvr-power-radical.json — statement-only unsplit support node; Mathlib has component declarations but no single exact bundled statement.
- dag/nodes/sec-trace-formula/lem-trf-localization-maximal-contraction.json — statement-only Mathlib leaf, exact `Localization.AtPrime.under_maximalIdeal`.
- citations.json — verbatim citations for every non-elementary fact used by step 2.

Attachments: none.

WANTED: literature/swanson-huneke-integral-closure.pdf, Definition 4.10.1 and Proposition 4.10.3, printed p. 89. The local PDF is absent; the imported statement and route were checked against the cited result description and the online reference named in the node.

## Not duplicates

- lem-trf-height-one-localization-dimension vs lem-sc-dvr-dimension-one: the new node computes the dimension of R_P from ht(P) before any DVR conclusion; the existing node only states that an already-given DVR has dimension one.
- lem-trf-height-one-localization-dimension vs lem-sc-normal-dim1-dvr: the new node is a localization-dimension theorem; the existing node is the one-dimensional normal-local-to-DVR criterion.
- lem-trf-height-one-localization-dimension vs lem-sc-dvr-field-extension-order: the new node concerns Krull dimension; the existing node concerns order of finite field extensions of DVRs.
- lem-trf-height-one-localization-dimension vs lem-sc-smooth-connected-curve-local-rings: the new node is a ring localization theorem; the existing node packages local rings on a smooth connected curve.
- lem-trf-height-one-localization-dimension vs lem-sc-dvr-saturation-line-smith-normal-form: the new node computes localization dimension; the existing node is a saturation/Smith normal form statement.
- lem-trf-height-one-localization-dimension vs def-weil-pbc-cohen-ring: the new node is a dimension theorem; the existing node is the definition of a Cohen ring.
- lem-trf-height-one-localization-dimension vs lem-weil-pbc-cohen-completion-dvr: the new node is general prime-localization dimension; the existing node concerns a specific Cohen completion being a DVR.
- lem-trf-height-one-localization-dimension vs lem-weil-pbc-completion-of-dvr-is-dvr: the new node is a height theorem; the existing node concerns completion preserving the DVR property.
- lem-trf-height-one-localization-dimension vs lem-weil-pbc-dvr-completion-regular: the new node is a localization-dimension equality; the existing node concerns regularity of a completed DVR.
- lem-trf-height-one-localization-dimension vs lem-weil-pbc-dvr-unit-times-uniformizer-power: the new node computes dimension from height; the existing node factors elements in a DVR.
- lem-trf-height-one-localization-dimension vs lem-weil-pbc-pid-noetherian-normal: the new node is a localization dimension theorem; the existing node relates PID, Noetherian, and normal properties.
- lem-trf-dvr-power-radical vs def-sc-discrete-valuation-ring: the new node proves the radical of a positive uniformizer power; the existing node defines DVRs and uniformizers.
- lem-trf-dvr-power-radical vs lem-sc-dvr-dimension-one: the new node is an ideal-radical calculation; the existing node computes DVR dimension.
- lem-trf-dvr-power-radical vs lem-sc-dvr-field-extension-order: the new node is an ideal-radical calculation; the existing node concerns residue-field extension degrees.
- lem-trf-dvr-power-radical vs lem-sc-smooth-connected-curve-local-rings: the new node is a ring-theoretic radical calculation; the existing node packages curve local rings.
- lem-trf-dvr-power-radical vs lem-sc-dvr-saturation-line-smith-normal-form: the new node concerns radicals; the existing node concerns saturation and Smith normal form.
- lem-trf-dvr-power-radical vs def-weil-pbc-cohen-ring: the new node is a radical theorem; the existing node is a definition.
- lem-trf-dvr-power-radical vs lem-weil-pbc-cohen-completion-dvr: the new node is a general radical theorem; the existing node concerns a particular completion.
- lem-trf-dvr-power-radical vs lem-weil-pbc-completion-of-dvr-is-dvr: the new node computes a radical; the existing node proves completion remains a DVR.
- lem-trf-dvr-power-radical vs lem-weil-pbc-dvr-completion-regular: the new node computes a radical; the existing node proves regularity.
- lem-trf-dvr-power-radical vs lem-weil-pbc-dvr-unit-times-uniformizer-power: the existing node supplies the unit-times-power factorization, while the new node supplies the missing radical equality.
- lem-trf-dvr-power-radical vs lem-weil-pbc-pid-noetherian-normal: the new node computes a radical; the existing node relates ring properties.
- lem-trf-localization-maximal-contraction vs lem-sc-free-prime-membership: the new node is the contraction of the whole maximal ideal; the existing node is a coordinatewise membership criterion for finite free modules.
- lem-trf-localization-maximal-contraction vs lem-weil-pbc-filtered-colimit-localization-at-prime-data: the new node concerns one ordinary localization; the existing node constructs filtered-colimit localization data.
- lem-trf-localization-maximal-contraction vs lem-weil-pbc-filtered-colimit-localization-at-prime: the new node is a maximal-ideal contraction equality; the existing node is a filtered-colimit localization comparison.
- lem-trf-localization-maximal-contraction vs lem-weil-pbc-localization-of-localization: the new node identifies a contraction; the existing node compares iterated localizations.
- lem-trf-localization-maximal-contraction vs lem-weil-pbc-localize-localization-at-prime: the new node identifies the maximal ideal contraction; the existing node gives isomorphisms between localizations at corresponding primes.
- lem-trf-localization-maximal-contraction vs def-weil-ring-localization-away: the new node is a theorem about the maximal ideal of R_P; the existing node defines localization away from an element.
- lem-trf-localization-maximal-contraction vs lem-weil-pbc-quotient-local-structure: the new node contracts a maximal ideal along localization; the existing node describes the maximal ideal after quotienting a local ring.

The returned delivery had `created.item` set to `lem-trf-normalization-principal-minimal-primes`; it is corrected to this item. The prior step 2 also used the one-dimensional localization, DVR power/radical, and contraction facts without nodes. I read the existing statements of `lem-sc-normal-dim1-dvr`, `def-sc-discrete-valuation-ring`, and `def-weil-pbc-localization-at-prime`, then added the three support nodes and cited their exact statements in `citations.json`. I reran Mathlib searches for each new node using LeanFinder, Loogle, grep, and LeanSearch; the recorded results and verdicts are in the node files and the search log.

## Review by NN

I reread the item, its unit record `dag/units/sk-i-curve-zero.json`, the chapter record, and the inherited blueprint ancestor. The statement remains the Swanson–Huneke Definition 4.10.1/Proposition 4.10.3 formulation, including the empty-list convention, the finite list of height-one primes containing b, the contractions (J_i), and the radical conclusion. Step 1 is the finite-character clause of the Krull definition. In repaired step 2, the new height-one-localization node supplies that (D_{P_i}) has dimension one; the Krull hypothesis supplies Noetherianity and normality and localization supplies locality, so the existing `lem-sc-normal-dim1-dvr` applies. The new DVR node supplies the unit-times-uniformizer power, positive exponent for a nonunit, and radical-of-power statement. The new localization-contraction node supplies that the maximal ideal contracts to (P_i). The remaining equivalence (x\in\sqrt{J_i}\iff x/1\in\sqrt{bD_{P_i}}) follows directly from the definitions of contraction and radical, and I wrote it explicitly. Steps 3 and 4 use only the Krull intersection clause, localization units away from primes containing b, and the stated empty-intersection convention; their edge cases are unchanged.

I checked the support-node statements against their sources and Mathlib search output. `IsLocalization.AtPrime.ringKrullDim_eq_height` is at `Mathlib/RingTheory/Ideal/Height.lean:418`; `Localization.AtPrime.under_maximalIdeal` is at `Mathlib/RingTheory/Localization/AtPrime/Basic.lean:207` (with the deprecated `comap_maximalIdeal` alias); and the DVR component declarations are in `Mathlib/RingTheory/DiscreteValuationRing/Basic.lean:98,338` together with `Ideal.radical_pow`. Small cases checked are a field (empty support), a DVR with b a positive uniformizer power (one component), and a UFD with several prime factors. No Lean, compiler, Lake, or build tool was run.
