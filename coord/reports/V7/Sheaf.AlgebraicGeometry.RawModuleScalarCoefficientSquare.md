## What changed

Complete the current retirement assignment for
Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare by withdrawing its
unused compatibility wrapper through deleted.txt. The canonical replacement
proofs already live in WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientSquare.
No source-library declaration, public signature, factor construction or target
statement changes. The change record is
coord/changes/V7-retire-raw-module-scalar-coefficient-square.md.

The current source already implements the verified route: the generic private
shift_square transports rawModuleScalar_coefficient_unshifted using
rawModuleScalar_derivedPullbackIso_commShift, and the existing structural helper
constructs kernel-checked endpoint congruences. The public wrapper applies the
result. moduleCoefficientFactor already shares higherDirectImageRawOverCoefficient
in the canonical factor module. There is no reason to duplicate these constructions.

The live library and quarantine have zero importers of the retired wrapper.
All six historical consumers were checked individually. The four already
withdrawn consumers need no adaptation; the two surviving formulas obtain their
factors through canonical factor/native-factor imports. The seven current DAG
parent references retain the canonical theorem nodes and attachments. Neither
coefficient-square node realizes a unit statement or step. No node edit is needed.

Validation: the published canonical two square theorems, the unshifted theorem,
the CommShift theorem and all three factors were checked with #print axioms.
Each reports exactly propext, Classical.choice and Quot.sound. The first audit also attempted the historical
derivedPullbackIso alias, which the published build does not yet expose; a
canonical-only audit omits that unrelated alias. A fresh rebuild
of the unchanged upstream square hit the 60-second limit; a separate profiling request
is pending and is excluded from the delivery. The published canonical declarations are present and contain no
proof holes. This retirement does not rebuild or modify their upstream module.

## Proved and sorry left

The assigned Sheaf module initially has zero declarations and zero sorry holes.
This is a retirement repair, not a new proof: zero holes closed, zero added,
zero split off, and zero remaining in the delivered module set.

The retained canonical declarations
AlgebraicGeometry.Etale.rawModuleScalar_coefficient_square_of_unshifted and
AlgebraicGeometry.Etale.rawModuleScalar_coefficient_square already have complete
proofs. Their nodes are lem-sbc-raw-scalar-coefficient-square-shift-transport and
lem-sbc-raw-scalar-coefficient-square. No deferred theorem is introduced.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.RawModuleScalarCoefficientSquare.
Its two public imports are removed with the unused wrapper:
WeilConjectures.AlgebraicGeometry.RawModuleScalarCoefficientSquare and
Sheaf.AlgebraicGeometry.RawModuleScalarDerivedPullbackIso.
Both imported modules remain available at their existing locations; neither is
withdrawn or claimed unnecessary for the library. The canonical square,
unshifted and CommShift nodes remain needed and attached to their existing
upstream declarations. No mathematical node or unit route is pruned.

## Where the brief, the DAG or earlier work was wrong

The supplied proof-route note predates the current source. Its named ROUTE
sandbox is absent on this machine, while its coefficient-square proof and shared
module-factor construction are already present in the adopted source tree.
The current queue and coord/retire-items.tsv identify this assignment as a
retirement with six historical consumers. All six have since migrated or been
withdrawn. The item itself is now only a declaration-free reexport.

Copying the old proof or reporting a newly closed sorry would be inaccurate.
The concrete repair is to remove the remaining unused compatibility wrapper,
preserving the complete canonical replacement and every current DAG parent.
The two theorem nodes already have the correct upstream ownership; the factor
node already records moduleCoefficientFactor and abelianCoefficientFactor at
the canonical upstream factor module, while scalarCoefficientFactor correctly
remains attached to the upstream coefficient-square module. The source-library
boundary forbids moving that existing definition out of the adopted source tree.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
