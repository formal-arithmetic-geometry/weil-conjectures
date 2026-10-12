## What changed

Proved `AlgebraicGeometry.exists_supported_koszul_relative_detector` with its original
signature, universes and visibility. The proof follows the three-step supported Koszul
route: form S = T ∩ (X \ U), use the affine detector on V, extend it by zero, transfer
orthogonality, and detect zero on the cover U,V.

Added the proved theorem `AlgebraicGeometry.supported_open_extension` in the new module
`Sheaf.AlgebraicGeometry.SupportedOpenExtension`. This is the general construction for an
arbitrary supported perfect B on an affine open, including its shifted Hom formula. It
contains no detection assertion and is proved completely from existing library interfaces.
Its object is the actual exact extension-by-zero composite applied termwise and localized;
no object is chosen from an unproved mere-existence theorem.

The main module has three proved private helpers: transport of the localization universe
through the over equivalence, the homology-stalk comparison for open restriction, and
vanishing of original cohomology stalks where a derived restriction is zero. The construction
also proves compactness of the affine support complement explicitly. Added proof imports
for open localizations, restriction of quasi-coherent cohomology, localization size,
abelian stalk functors and zero abelian groups. Updated the main node's proof and dependencies,
and added a node for the new proved extension theorem. No existing public interface changed.

Sources checked: Stacks Tags [0A9A](https://stacks.math.columbia.edu/tag/0A9A),
[08DP](https://stacks.math.columbia.edu/tag/08DP) and
[08DF](https://stacks.math.columbia.edu/tag/08DF). The local literature checkout does not
contain perfect.tex, so these primary webpages were read directly. All delivered Lean files
compile together in import order with lcompile.py, without warnings.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_supported_koszul_relative_detector`
(node `lem-pc-supported-koszul-relative-detector`).

Also proved the new theorem `AlgebraicGeometry.supported_open_extension`
(node `lem-pc-supported-open-extension`). The item and the new module contain no `sorry`.
Holes closed: 1. Holes added: 0. No residual statements were split off.
The proof uses existing stated dependencies; this does not claim their entire transitive
closure is already free of `sorry`.

Edge cases were checked against the argument: if U is total then S is empty; if U is empty,
the cover forces V to be total and the argument becomes affine detection; if T is empty,
all support conditions are zero conditions; if V is empty, the cover forces U to be total.
Neither proof selects a point, assumes a nonempty open, or excludes the zero object.

## No longer needed

Removed these direct imports from the item:

- `Sheaf.AlgebraicGeometry.SupportedOpenPushforward`
  (`lem-pc-supported-open-pushforward`).
- `Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`
  (`lem-sc-derived-open-restriction-adjunction-exact`).
- `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`
  (`lem-pc-derived-direct-image-preserves-qcoh`).

Their uses are now inside the proved SupportedOpenExtension module, where they are imported
and recorded in its node. They remain transitive dependencies and are not globally pruned.
No original planned lemma or module becomes unnecessary in the targets' import closure.
Removed the unused Mathlib.Topology.Sheaves.Abelian and Mathlib.Algebra.Category.Grp.Zero
imports from the new module after the support argument was simplified to the existing
extension/restriction isomorphism and outside-stalk theorem.

## Where the brief, the DAG or earlier work was wrong

No false statement or changed target was needed. The original proof plan did not give
interfaces for transporting the ambient Hom universe to the actual open subscheme or for
identifying homology stalks across the localized-site/scheme restriction presentations;
these are now proved explicitly. The supported-open-pushforward interface requires both
derived adjunctions and an adjunct equation for its canonical comparison. The new theorem
constructs these and proves the equation, instead of treating the comparison as automatic.
The existing exact-derived-adjunction helper in
WeilConjectures.CategoryTheory.DerivedCategory.Adjunction carries monoidal/flat-resolution
hypotheses; the exact-left-adjoint specialization in RightDerivedFunctor.Adjunction, followed
by rightDerivedFunctorIsoMapDerivedCategory, avoids those unrelated hypotheses.

The final sentence of the inherited docstring, "No right adjoint is used here", is too broad
if read literally about the construction: a canonical derived direct-image adjunction is
used to compare extension by zero with Rj_*. The detector statement and its zero-detection
argument require no additional right-adjoint witness or unit-isomorphism hypothesis.
The original docstring and signature were preserved.

The existing node's blueprint.from points to another created node, so blueprint_refs.py
ancestor reports None for it. The new node records the actual ancestor lem-sc-finite-duality
and the intervening chain from SupportedKoszulUnitSummand; no existing ancestry field was
edited.

The restriction-of-quasi-coherence node belongs to sk-thm-picard-f-representable. It is used
as an already proved generic exact-restriction tool, not as a replacement for the unit's
route; the supported-generator construction itself is unchanged.

## New nodes

`lem-pc-supported-open-extension`, in
`dag/nodes/sec-picard-framework/lem-pc-supported-open-extension.json`, records the proved
extension construction, canonical comparison, support calculation and shifted Hom formula.
Its module is lean/Sheaf/AlgebraicGeometry/SupportedOpenExtension.lean. LeanFinder and Loogle
found the underived restriction adjunction and generic adjunction ingredients, and source
search found the already stated supported pushforward interfaces. No existing theorem states
the complete constructed extension and Hom interface. LeanSearch returned Internal Server
Error, recorded as unavailable. No change record is needed: no existing statement,
definition, public import or visibility changed, and no other module was adapted.

## Second reading by J2

1. Compared the delivered detector module with the repository version. The target theorem signature and all existing declaration statements are byte-for-byte unchanged; only proof text and proof-only/public imports needed by the new construction changed. Verdict: pass.

2. Compiled `SupportedOpenExtension.lean` and `SupportedKoszulRelativeDetector.lean` independently with `lcompile.py`; both compile without errors or warnings. Searched the delivered Lean and DAG files for forbidden commands and residual `sorry`; none occur. Verdict: pass.

3. Read the new extension statement and checked its edge cases (empty support/open and total open). It constructs extension by zero and states only the required perfectness, support, and Hom equivalence; it does not restate the detector. The detector statement remains unchanged and is proved with the stated hypotheses. Verdict: pass.

4. Checked the proof from the target downward. The route uses the affine supported detector, the supported extension construction, restriction-zero, and open-cover isomorphism; removed direct imports are now transitive through the extension module. No shorter existing declaration was found for the derived extension/Hom construction. Verdict: pass.

5. Checked the detector and extension DAG nodes against the Lean proofs, including proof dependencies, sources, and unit route. The unit route through affine supported detection and supported extension is retained. Verdict: pass.

Changes made during second reading: added this review section to satisfy the stage-3 report contract; no Lean code or DAG statements were changed.
