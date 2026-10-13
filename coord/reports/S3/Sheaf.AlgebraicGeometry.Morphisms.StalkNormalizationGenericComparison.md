## What changed

Proved `AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_generic_comparison`
with its original signature and docstring unchanged. Added proof imports of
`GaloisCoverBaseChange`, `NormalizationStalkBaseChange`, and `StalkGenericOpenPullback`.
A private, proved helper transports relative normalization across an isomorphism over the base.

Added two fully proved modules. `StalkGenericOpenPullback` identifies the open pullback
using a DVR uniformizer, the fraction-field localization, and minimality of the boundary point.
`NormalizationStalkBaseChange` proves the canonical normalization comparison is invertible
for any qcqs source morphism under stalk base change. Its private affine proof adapts Andrew
Yang's Mathlib smooth-base-change proof using the existing integral-closure localization theorem.
The public proof establishes the required localizations through affine cartesian squares.
The DAG now records the actual three-step assembly and both new proved lemmas.

All three modules compile without warnings. The proof works for empty total spaces and uses
no arbitrary witness chosen from an unproved existence theorem. The torsor comes from the
existing, fully proved base-change construction; both new theorems are fully proved.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.GaloisCover.stalk_normalization_generic_comparison`
(node `lem-sbc-stalk-normalization-generic-comparison`).

Added 0 holes. Both new public theorems are proved:
`AlgebraicGeometry.Scheme.Hom.isIso_normalizationPullback_stalk`
(node `lem-sbc-normalization-stalk-base-change`) and
`AlgebraicGeometry.Scheme.stalk_generic_open_isPullback`
(node `lem-sbc-stalk-generic-open-pullback`). All private helpers are proved.
No `sorry` remains in any delivered module. This is a proof, not a decomposition.

## No longer needed

None: the original node had no proof dependencies or proof-only imports to remove.
The original public imports still supply notions appearing in the unchanged signature.
No previously required node or module is pruned. No ramification, finiteness of the
normalization, normality of the total space, or normal-extension uniqueness lemma is needed.
The retained normality and generic-open hypotheses are unused in the proof; a declaration-local
unused-variable linter option accommodates the unchanged signature.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The node's single informal step had no Lean proof dependencies;
its localization and punctured-spectrum parts are now separate, fully proved statements.
Mathlib supplies tensor-product integral-closure localization and qcqs flat base change
of sections, so neither requires a new holed theorem. The blueprint unit route is preserved:
this is precisely the local trait comparison in the maximal-open reduction.
LeanSearch returned an Internal Server Error; successful LeanFinder, Loogle and source searches
are recorded in the search log and the new nodes.

## New nodes

`lem-sbc-normalization-stalk-base-change`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-normalization-stalk-base-change.json`, records the
proved general comparison in `Sheaf.AlgebraicGeometry.Morphisms.NormalizationStalkBaseChange`.
It uses the existing Mathlib leaves for flat base change of sections and localization of
integral closure, and introduces no extra geometric assumptions.

`lem-sbc-stalk-generic-open-pullback`, in
`dag/nodes/sec-smooth-base-change/lem-sbc-stalk-generic-open-pullback.json`, records the
proved open cartesian square in `Sheaf.AlgebraicGeometry.Morphisms.StalkGenericOpenPullback`.
Its data are a specified commuting map, and its proof proves the universal property.
No change record or forced adaptation is needed: all existing interfaces are unchanged.

## Second reading by S3

1. **Interface: pass.** Read all three delivered modules and diffed the item against
   the repository. Compared the entire original theorem signature byte for byte:
   it is identical, including the finite/open quasi-compact instances and the equation
   over the local total space. The existing docstring is unchanged. The only additions
   there are three non-public proof imports, a private proved normalization transport
   lemma, a declaration-local linter option, and the proof. No existing definition,
   hypothesis, conclusion, visibility, or target changed; no change record is needed.

2. **Proof and axioms: pass.** Compiled the three modules in import order with
   `lcompile.py --all`; no errors or warnings (9.1, 2.7, 5.3 seconds).
   Scratch copies with `#print axioms` verified both public supporting theorems,
   the original theorem, and both private helpers: precisely `propext`,
   `Classical.choice`, `Quot.sound`, with no `sorryAx`. Scanned every delivered
   source for forbidden declarations/options and sorries: none. Read the actual
   construction in `GaloisCover.exists_baseChange`: its total space is the pullback,
   its action is lifted on projections, and its torsor law is proved; W is not
   an arbitrary witness from a holed existence theorem. Normalization transport
   uses its universal property in both directions, with both inverse identities proved.

3. **Supporting statements: pass.** There are no split-off holes. The two new,
   fully proved statements are strictly separate geometric parts of the original
   argument. For `stalk_generic_open_isPullback`, checked that the uniformizer
   localization gives the fraction field, that primes containing the uniformizer
   are exactly the closed point, and that minimality plus injectivity of fromSpecStalk
   identifies the inverse image of U. For normalization base change, checked the
   restricted affine cartesian square, the stalk localization and scalar towers,
   both qcqs flat section comparisons, and the identification with the canonical
   comparison, rather than merely some isomorphism. The qcqs assumptions apply
   to f, not c. Tested the arguments on an empty C/P or empty generic fibre,
   c equal to the identity on a trait, and a nonreduced source P: none needs
   nonemptiness, normality of P, or a domain assumption on its section rings.
   The nonfield DVR hypothesis supplies a uniformizer; the field case is excluded
   explicitly, not silently. Each supporting theorem has its proof docstring and node.
   Independent LeanFinder searches used "relative integral closure under localization
   on a scheme" and "open complement of the closed point in the spectrum of a DVR
   is the spectrum of its fraction field"; Loogle used
   `PrimeSpectrum, IsDiscreteValuationRing` (no hits). Read the candidate algebra
   localization results and searched lean/Sheaf, lean/WeilConjectures, and Mathlib:
   no existing exact scheme-level statement or shorter completed route was found.

4. **Route and pruning: pass.** Read Mathlib Normalization's smooth-base-change
   instance and its localization tensor-product lemma, and the upstream flat stalk
   instance. Smooth base change does not apply to an arbitrary stalk localization;
   the affine adaptation is needed. The imports are used for signatures or for the
   proof; all three added imports in the item and the upstream Flat import are
   non-public. The original proof_deps was empty, so `No longer needed` is complete.
   Read `dag/units/sk-prop-input-spreading.json`: the proof implements the local
   trait comparison in the maximal-open step, without replacing its tame or
   depth-two extension steps. The unit's pre-existing empty realized arrays are
   unchanged; this delivery neither removes nor bypasses a realized unit node.

5. **DAG and sources: pass.** The existing node changes only proof, proof_deps,
   and proof_origin. Its three recorded steps match gamma/open pullback, torsor
   base change/pasting, and normalization comparison/transport in Lean.
   The normalization node's two dependencies match the actual flat-sections and
   integral-closure localization results; the open-pullback node uses elementary
   DVR and open-immersion facts. Both new nodes have creation, source, searches,
   blueprint ancestry, chapter/unit, and Lean records matching their declarations.
   Read the sources online because this clone has no literature texts:
   [0307](https://stacks.math.columbia.edu/tag/0307),
   [035I](https://stacks.math.columbia.edu/tag/035I),
   [02KH](https://stacks.math.columbia.edu/tag/02KH), and
   [0EYJ](https://stacks.math.columbia.edu/tag/0EYJ).
   They support the localization, normalization universal property, flat sections,
   and maximal-open/trait reductions respectively.

Second reading changed only this review report and the independent sandbox search
log. No Lean or DAG repair was needed. One original hole closed, zero holes added,
zero split-off holes, and no nodes or modules pruned.
