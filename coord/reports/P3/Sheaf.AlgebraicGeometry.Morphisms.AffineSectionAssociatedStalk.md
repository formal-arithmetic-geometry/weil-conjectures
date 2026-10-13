## What changed

Proved `AlgebraicGeometry.Scheme.exists_associated_stalk_germ_ne_of_isAffineOpen`
without changing its signature, docstring, existing imports, or visibility.
It uses the proved associated-prime zero criterion, Mathlib association transfer
under localization, and the new proved affine germ localization theorem.
All three added imports in the item are proof imports.

Added `Sheaf.AlgebraicGeometry.Morphisms.AffineModuleGermLocalization`, proving
`AlgebraicGeometry.Scheme.isLocalizedModule_affine_germ`. Its linear map is the
actual germ; it satisfies the three localization axioms using the existing proved
upstream basic-open extension and torsion lemmas. This proof adapts the private
`quasicoherent_affine_stalk_germ_localization` argument in
`Sheaf.AlgebraicGeometry.FiniteTypeModuleSupportClosed`.
The upstream Tilde import is a plain proof import. Public imports supply the
scheme-module, quasi-coherence, module-stalk, and localization types of the signature.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.exists_associated_stalk_germ_ne_of_isAffineOpen`
(node `lem-sbc-affine-section-associated-stalk`).

Also proved the newly added helper
`AlgebraicGeometry.Scheme.isLocalizedModule_affine_germ`
(node `lem-sbc-affine-module-germ-localization`). The first worker left this as
one split-off hole; the second reading closed it. Final delivery: one original
hole closed, zero holes added, no textual sorry in either module, no remaining
split-off obligations. Both declarations' `#print axioms` list exactly
`propext`, `Classical.choice`, and `Quot.sound`. Both modules compile without warnings.

## No longer needed

No existing import removed and no module claimed pruned from the target closure.
`lem-weil-pbc-associated-prime-localize-at-prime` is no longer a proof dependency
of the item: Mathlib's general localized-module association theorem applies to
the actual stalk, via the recorded Mathlib match of
`lem-weil-pbc-associated-prime-localization-depth-zero`.

`lem-weil-pbc-affine-tilde-gamma-adjunction` and
`lem-weil-pbc-spec-tilde-stalk-localization` are no longer direct dependencies
of the item. The helper's actual proof uses
`lem-weil-pbc-affine-module-basic-open-localization`,
`lem-weil-pbc-affine-open-spec-points`, and
`lem-weil-pbc-affine-open-stalk-localization` instead of a new counit/stalk transport.
The first two old nodes remain upstream of the basic-open tools as appropriate;
no claim is made that any other target route ceases to need them.
`lem-weil-pbc-module-injects-localizations-associated-primes` and
`lem-weil-pbc-affine-open-stalk-localization` remain direct item dependencies.

## Where the brief, the DAG or earlier work was wrong

The first worker missed an existing private proof of the ambient affine module
stalk localization statement in FiniteTypeModuleSupportClosed. It cannot be
imported as a public theorem, but its short denominator argument closes the new
helper using public, proved upstream extension and torsion lemmas. The related
IntrinsicFlatModuleStalkTensorPresentation module also contains this argument;
its public tensor-equivalence assertion alone does not specify germ compatibility.
No new unproved dictionary step is necessary.

The item does not need its finite-generation assumption, which remains unchanged.
The zero module has no unequal sections. Empty affine opens likewise have no
unequal sections, and the helper has no point on an empty open (including the
zero-ring affine case). The helper is valid on non-Noetherian affine opens:
the proof uses only quasi-coherence and the basic-open denominator properties.

Independent LeanFinder, Loogle, and grep searches used alternative localization
queries. Mathlib gives ring-germ and tilde-stalk tools, but no ambient affine
module germ theorem. Local source search found the private proof and upstream
denominator lemmas. The Stacks sources were checked at
[Tag 01IA](https://stacks.math.columbia.edu/tag/01IA) and
[Tag 01HV](https://stacks.math.columbia.edu/tag/01HV), especially basic-open and
stalk identifications. The unit's existing route is preserved.

## New nodes

`lem-sbc-affine-module-germ-localization`: a proved localization property of the
actual affine section-to-stalk germ map for any quasi-coherent module. Its node
now records the basic-open denominator proof and its three dependencies. It
contains no associated-prime detection assertion and is strictly the dictionary
part of the original argument. Its map is constructed directly, without choosing
data from any unproved existence theorem. No change record is required: existing
statements, definitions, and visibility are unchanged, with no consumer adaptation.

## Second reading by P3

1. Compared the item with the repository by `diff`: the sole existing declaration's
   signature and docstring are byte for byte unchanged. Only its proof and three
   plain proof imports changed. The other Lean module and its node are new;
   there is no existing definition change or consumer adaptation.
2. Compiled both files in import order through lcompile.py without warnings.
   Scratch copies with `#print axioms` show only propext, Classical.choice,
   Quot.sound for each theorem, with no sorryAx. Checked both files for forbidden
   declarations and textual sorry: none remain. The helper constructs its germ
   map directly; there is no hollow definition or arbitrary witness selection.
3. Checked the helper's scalar action, denominator complement, and all localization
   axioms. Tested zero modules and empty affine/zero-ring opens as above; no
   Noetherian or finite-generation premise is needed. Independent Mathlib and
   local source searches found an existing private proof, which was adapted to
   close the helper. No new unproved statement remains.
4. Read the algebraic proof from the top: the associated-prime zero criterion,
   inverse affine chart, association transfer, and equality-denominator criterion
   combine correctly. Checked all added imports against their uses; public
   imports of the new helper supply its signature. The old proof dependencies
   absent from the new route are all listed above. Read
   dag/units/sk-prop-input-spreading.json, including its realized field: this
   affine detection subargument replaces no unit step and changes no unit route.
5. Compared both nodes with their Lean declarations and proofs. The item's
   proof and dependencies match the algebraic reduction. Rewrote the helper's
   proof, proof_deps, and proof_origin to match its now-complete denominator
   proof; its lean.statement matches the signature verbatim. The new node has
   source, searches, creation, blueprint, chapter, unit, and lean records.

Second-reading changes: closed the affine germ-localization hole using existing
proved upstream tools; replaced its proof-only public Tilde import with a plain
upstream proof import and explicit signature imports; updated its docstring,
node proof plan/dependencies/origin, and this report. Kept the original item proof.
