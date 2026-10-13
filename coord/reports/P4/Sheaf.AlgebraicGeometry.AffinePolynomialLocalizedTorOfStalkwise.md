## What changed

Proved `AlgebraicGeometry.affinePolynomial_localized_finiteTorDimension_of_stalkwise_of_kernel_le`
with its signature unchanged. Added proof-only imports of the two comparison modules and
Mathlib flatness of localization. The scheme, Noetherian, polynomial and Tor public imports are retained. Second reading
replaced the unused projective-dimension public import with ModuleCat.Localization,
the interface required by the statement.

Added `Sheaf.AlgebraicGeometry.AffinePolynomialSupportedLocalizationStalk`, with the complete
proof of `AlgebraicGeometry.affinePolynomial_supportedLocalization_stalk`. A supported prime
maps to a prime of the affine coordinate ring, hence a point. The affine germ is a module
localization at the original prime because the two prime complements have the same image.
The universal property yields the required module isomorphism; naturality of germs verifies
the actual stalk-map scalar action.

Added `Sheaf.RingTheory.TorVanishingRestrictionFlatBase`, with the complete proof of
`ModuleCat.isZero_tor_restrictScalars_of_flat`. Extend a projective resolution of the test
module along the flat map, use tensor associativity and exact restriction of scalars, then
use the existing Tor symmetry theorem. This avoids constructing a bounded flat resolution
of the stalk and works for an arbitrary flat base algebra, not only a localization.

Updated the item's node and added nodes for both proved auxiliaries. The unit record
`sk-thm-picard-duality` has no realized node at this level; its statement and route are
unchanged. No definition, target statement, existing signature, or visibility was changed.

## Proved and sorry left

Closed the item's only hole:
`AlgebraicGeometry.affinePolynomial_localized_finiteTorDimension_of_stalkwise_of_kernel_le`
(node `lem-pc-affine-polynomial-localized-tor-of-stalkwise`).

Both new auxiliary declarations are fully proved:
`AlgebraicGeometry.affinePolynomial_supportedLocalization_stalk`
(node `lem-pc-affine-polynomial-supported-localization-stalk`) and
`ModuleCat.isZero_tor_restrictScalars_of_flat`
(node `lem-pc-tor-vanishing-restriction-flat-base`).

No `sorry` remains in any delivered module. Holes closed: 1; holes added: 0; split off: 0.
The proof uses the library's existing `CategoryTheory.nonempty_tor'_flip_iso` and inherits
its dependency status; its proof and dependencies were not modified.

Edge cases: the geometric comparison has no prime when the quotient ring is zero, and the
proof uses no positive-variable assumption, so n = 0 works. The flat transfer is valid in
Tor degree zero, for the zero test module, and for the zero base algebra. The final bound
is chosen only at the point corresponding to p; no uniform bound on all primes is asserted.

## No longer needed

Removed `Mathlib.RingTheory.LocalProperties.ProjectiveDimension` from the item: no
projective-dimension or local-projectivity result is used. Its needed localization
interface is supplied directly by `Mathlib.Algebra.Category.ModuleCat.Localization`.
No Sheaf module was pruned. The old module had no proof-dependency imports.
`pqf-def-locnoeth` is no longer a proof dependency of the item: the proof does not use
Noetherianity or finite type. It remains a statement dependency, and the existing binders
and public imports are retained. The bounded-flat-resolution construction in the original
proof sketch is unnecessary: extending the test module's projective resolution and using
Tor symmetry proves the same transfer directly. No named existing node or module for that
construction was imported or needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement or its three-step plan was found. Its proof_deps
listed definitions only, rather than the actual comparison statements required to execute
the plan. The updated node records the two complete comparisons and localization flatness.
The existing TorVanishingLocalizedBase theorem transfers vanishing in the reverse direction
from the one needed here, so it cannot alone supply the last step.

The cited Stacks source is not present in this clone. Read Tag 069C,
`lemma-check-perfect-stalks`, online at https://stacks.math.columbia.edu/tag/069C, especially
the supported polynomial localization in (3) implies (1). The new nodes mark the detailed
Mathlib comparisons as agent expansions of that argument. LeanSearch returned Internal
Server Error; this is recorded as unavailable, with no mathematical verdict inferred.
LeanFinder, Loogle, Mathlib source searches, and searches of both library roots were used.

## New nodes

`lem-pc-affine-polynomial-supported-localization-stalk` records the supported affine
localization/stalk isomorphism as a module over the affine base. It has no perfectness, Tor,
Noetherian or finite type hypotheses, and is completely proved in its own module. The
point is used within a theorem proof; no definition chooses data from mere existence.

`lem-pc-tor-vanishing-restriction-flat-base` records a fixed-degree Tor transfer along an
arbitrary flat ring map and is completely proved in its own module. Tor symmetry is an
existing generic tool, recorded in `tool_uses`. Neither auxiliary restates the original
Tor-bound theorem. The import pruning made during second reading is recorded in
`coord/changes/AffinePolynomialLocalizedTorOfStalkwise-imports.md`; no signature or
definition changes or forced adaptations are needed.

## Second reading by P4

1. Compared the existing module and node against the repository with diff. The existing
   theorem signature is byte-for-byte unchanged, as are its visibility and all definitions.
   The existing node changes only proof, proof_deps and proof_origin. The two other modules
   and their nodes are new. Verdict: no accidental statement or definition change.
2. Compiled all three files with lcompile.py. Scanned the delivered source for forbidden
   declarations and sorry: none. Scratch #print axioms checks of all three public theorems
   show only propext, Classical.choice and Quot.sound, including the imported Tor symmetry
   dependency. No object is defined by selecting an arbitrary unproved existence witness.
   Verdict: kernel-checked proofs with no remaining or added holes.
3. Read both auxiliaries in full. The affine point is constructed from p.map g; surjectivity
   and the kernel condition give the exact denominator comparison. Tensor associativity,
   flat extension of a projective resolution and exact restriction give the flat transfer.
   Tested the mathematics at n = 0, empty affine V, zero quotient, degree zero, zero test
   module, identity map and zero flat base algebra: the claims remain correct. Both have
   full proof docstrings and matching nodes; neither restates the target. Independent
   LeanFinder search for flat extension and Tor and Loogle search for surjective localization,
   plus searches of both library roots, found ingredients only. In particular,
   ProjectiveRestrictionTorBound concerns projective modules and an existing base Tor bound;
   AffineSectionsTorBoundStalk and TorVanishingLocalizedBase go in the reverse direction.
   Verdict: true, useful intermediates; no split-off holes.
4. Read from the target down through both comparisons and the existing Tor symmetry.
   The direct projective-resolution route is appropriate and avoids a new flat-resolution
   theory. Replaced the unused ProjectiveDimension import with the statement's direct
   ModuleCat.Localization import; retained public imports that provide statement constants
   or required instances, and plain imports for proof-only comparisons and flatness.
   The old proof dependency pqf-def-locnoeth is named under No longer needed. Read the
   sk-thm-picard-duality unit: its realized statement and step arrays are empty; this item
   realizes neither, and no unit route is bypassed. Verdict: pruned and route preserved.
5. Checked each Lean declaration against its node's verbatim signature, and checked that
   proof_deps is the union of proof-step uses. The target records the actual stalk comparison,
   localization flatness and flat restriction; the new nodes include source, origin, searches,
   creation, blueprint, unit, chapter and Lean records. Re-read Stacks Tag 069C (3) implies
   (1) online. Verdict: DAG agrees with the code and its source expansion.

Changes in second reading: corrected the target proof docstring to describe extension of
N's projective resolution and Tor symmetry, replaced the unused projective-dimension import
with the direct localization import, and updated the import/pruning report. No proof body,
signature, definition or node needed repair.

Import-pruning change record: `coord/changes/AffinePolynomialLocalizedTorOfStalkwise-imports.md`.
The sole importer already publicly imports the removed module itself, so no adaptation
or change to its statement or proof is required.
