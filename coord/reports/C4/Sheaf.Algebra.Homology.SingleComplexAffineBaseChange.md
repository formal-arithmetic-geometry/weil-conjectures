## What changed

Closed the proof body of `AlgebraicGeometry.singleComplexAffineBaseChange` without
changing its signature, visibility, or existing docstring. Added the proof-only
import `Sheaf.Algebra.Homology.AffineBaseChangeCohomologyModel` and the Mathlib proof
import for local bijectivity. The derived cohomology isomorphism criterion is
already available through the statement imports.

The new public theorem `AlgebraicGeometry.exists_affineBaseChangeCohomologyModel`
states the degreewise module realization and actual commuting localization squares
of node steps 1–3, with no stalk-invertibility hypothesis. The main proof chooses
existing K-flat coordinates, transports bijectivity across additive equivalences,
applies `bijective_of_localized_maximal`, transports the resulting isomorphism
through restriction of scalars and tilde, cancels the cohomology comparison
isomorphism, and applies `DerivedCategory.isIso_iff`. This is a real implementation
of the localization-to-derived-isomorphism step.

Updated the original node's proof, proof_deps, and proof_origin to this reduction.
Added the new module and its node. No existing definition, statement, instance,
visibility, public import, or target signature changed. No forced adaptations.

Validation: both modules compile with lcompile.py. The linear-map arguments use
Mathlib's maximal-localization theorem; there is no finite-generation, boundedness,
flatness, or Tor-independence assumption. The new lemma was checked mathematically
on zero objects, identity squares, empty Spec (zero A'), arbitrary unbounded
quasi-coherent objects, nonflat maps, and zero phi: it asserts identifications of
maps without assuming those maps invertible. Additive equivalences suffice to
transfer bijectivity across different stalk scalar rings. No data is defined or
chosen from the new existence hole: witnesses are eliminated locally inside a
proof of a proposition.

## Proved and sorry left

Closed: `AlgebraicGeometry.singleComplexAffineBaseChange`
(node `lem-pc-rf-single-complex-affine-base-change`), the item's only original hole.
The item's module now has no sorry.

Added and left: `AlgebraicGeometry.exists_affineBaseChangeCohomologyModel`
(node `lem-pc-affine-base-change-cohomology-model`), exactly one public named
whole-proof sorry, with source and complete proof in its docstring and DAG node.

Accounting: one upper hole closed, one lower hole added; this is a decomposition,
not a fully sorry-free theorem or positive net-hole progress. The imported
prerequisites may still contain their existing holes; none was edited or duplicated.

## No longer needed

Removed these direct proof imports from the repository item:

- `Sheaf.Algebra.Homology.AffineDerivedBaseChangeComparison`
- `Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde`
- `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`
- `Sheaf.AlgebraicGeometry.DerivedCategory`
- `Sheaf.AlgebraicGeometry.DerivedDirectImagePreservesQCoh`

The first, second, third and fifth remain needed by the new cohomology-model item
and are imported there as proof dependencies. DerivedCategory remains a statement
dependency through existing public imports. Thus **no module or underlying
mathematical support node is globally pruned** by this delivery.

The original node's direct dependencies
`lem-pc-affine-derived-base-change-comparison-map`,
`lem-pc-affine-derived-pullback-tensor-tilde`,
`lem-pc-affine-qcoh-derived-equivalence`,
`lem-pc-derived-direct-image-preserves-qcoh`,
`lem-weil-pbc-localization-module-exact`, and
`lem-weil-pbc-spec-tilde-stalk-localization` now belong below the new model node.
`def-pc-derived-category` remains in the statement closure.
`lem-weil-pbc-linear-map-bijective-at-maximal-localizations` and
`def-weil-abstract-derived-category` remain direct proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt was byte-for-byte the unproved original module and
had no report or completed reduction. Its NOANSWER was not a usable delivery.

The four-step DAG plan is mathematically sound, but its existing Lean declarations
do not supply the canonical degreewise comparison between the scheme adjunction
base-change map and the ring tensor comparison, nor its natural square for the
actual `SingleComplexBaseChange.Coordinates` stalk maps. The new node makes precisely
these identifications an explicit next item. It does not repackage the upper
invertibility assertion: it takes one degree, assumes no stalk condition, and
asserts commuting identifications of maps. The localization criterion and the
passage from cohomology to derived invertibility are proved in the original module.

The local literature files named in the node are not present on this machine;
read the obtained Stacks source at https://stacks.math.columbia.edu/tag/0DJ8 instead.
The proof follows its affine cohomology and localization paragraph. The unit
record `sk-thm-picard-semicon` is unchanged and its route is retained.

LeanSearch was attempted but returned Internal Server Error; this is recorded as
unavailable without a no-match verdict. LeanFinder and source grep searches found
no existing theorem of the required canonical geometric comparison square.

## New nodes

`lem-pc-affine-base-change-cohomology-model`, in
`dag/nodes/sec-picard-framework/lem-pc-affine-base-change-cohomology-model.json`,
is stated by `AlgebraicGeometry.exists_affineBaseChangeCohomologyModel` in
`lean/Sheaf/Algebra/Homology/AffineBaseChangeCohomologyModel.lean`.
It groups steps 1–3 of the original affine argument, leaving its algebraic
localization and derived-category conclusion to the proved main theorem. Its
hypotheses and two commuting squares are self-contained; its source is Tag 0DJ8.
No change record is needed: no existing interface changed.

## Second reading by C4

1. **Interface preservation: PASS.** Compared the delivered existing module with
   the repository using diff and extracted its theorem signature. The signature
   is byte-for-byte identical, including every hypothesis and the conclusion;
   its visibility and docstring are unchanged. No existing definition or instance
   is edited. Only the original proof and proof-only imports change. The new
   theorem is in its own module. No forced adaptation or change record is needed.
2. **Proof and axioms: PASS as a decomposition.** Compiled both modules locally
   in import order with lcompile.py. The original module has zero textual holes;
   the new module has exactly the one reported, public, whole-theorem sorry.
   Scratch-copy #print axioms checks of both declarations returned only propext,
   Classical.choice, Quot.sound, and sorryAx. No prohibited declaration mechanism,
   data definition, or hidden proof hole is introduced. The existential witnesses
   of the model theorem are eliminated only inside the proof of a proposition.
3. **Split statement: PASS.** Read the actual Coordinates, stalkComparison,
   schemeDerivedBaseChangeMap, and affine module-comparison declarations. Checked
   Tag 0DJ8 directly at https://stacks.math.columbia.edu/tag/0DJ8: its tensor-algebra
   action and displayed cohomology localization formula give precisely U,V,a and
   the localization square; exact tilde and the normalized derived adjunction
   identify the geometric cohomology square. The represents equation for c makes
   the second square valid for the supplied coordinates. Zero complexes and zero
   phi give zero maps; identity squares give the ordinary localized map; A'=0
   gives zero modules and no prime conditions. Arbitrary unbounded complexes and
   nonflat ring maps require derived tensors, which the statement retains. No
   finite-generation or Tor-independence assumption is smuggled in. This is a
   degreewise identification result without the upper theorem's stalk hypothesis
   or invertibility conclusion, hence a strict part of the argument.
   Independent LeanFinder search for localization of derived-tensor cohomology
   on affine schemes found sheaf-cohomology and abelian-category declarations;
   Loogle query '"stalk", "homology"' found no hits. Source rg searches and the
   Mathlib grep service found no duplicate of these two squares. Also read the
   nearby affine-sections mate and coordinate-invariance statements: neither
   supplies both squares. Closing the new geometric/model compatibility theorem
   is substantial further formalization, not a short omitted library application.
4. **Route and pruning: PASS after one import repair.** The main proof implements
   the maximal-localization criterion and derived cohomology criterion directly
   from Mathlib; the model node retains old steps 1–3. It does not simply apply a
   renamed invertibility assertion. Every old proof dependency removed from the
   original node is accounted for in No longer needed, and remains below the
   model or in the statement closure. No support module is globally pruned.
   Read dag/units/sk-thm-picard-semicon.json: its realized fields are unchanged
   (currently empty), and the delivery preserves its affine base-change route.
   Removed the redundant proof import
   Mathlib.Algebra.Homology.DerivedCategory.HomologySequence: the complete proof
   still compiles without it. Retained Mathlib.RingTheory.LocalProperties.Exactness:
   a scratch compile without it reports unknown bijective_of_localized_maximal.
   The new module's public imports are used by its signature; its plain Sheaf
   imports retain the planned lower proof dependencies.
5. **Nodes: PASS.** The existing node differs only in proof, proof_deps, and
   proof_origin. For both nodes, proof_deps equals the union of the proof steps'
   uses. The original reduction names exactly the model, coordinates,
   maximal-localization criterion, and derived-category criterion it uses.
   The new node has source, complete proof plan, search records, provenance,
   blueprint ancestry, chapter/unit, and a Lean record matching its declaration.

Second-reading changes: removed the redundant HomologySequence proof import and
updated this report. No mathematical statement, proof body, definition, or node
was changed. Hole accounting remains one upper hole closed and one strictly
lower hole added (net zero; decomposition).
