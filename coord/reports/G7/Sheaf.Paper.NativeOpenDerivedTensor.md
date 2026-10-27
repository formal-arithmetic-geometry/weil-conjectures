## What changed

`native_open_derived_tensor` now has a complete Lean assembly proof from three
strict intermediate parts of its existing source argument: native sheaf/K-flat
data, localization with all representative squares, and unit/forgetting
normalization. No hypothesis, conclusion, universe or target signature changes.

The three existing data declarations `NativeOpenTensorData`,
`NativeOpenDerivedTensorData`, and `NativeOpenPresentationCompatibility` move
verbatim to `Sheaf.Paper.NativeOpenTensorComparisonData`. The original entry
module publicly reexports it. This avoids a cycle between the existence theorem
and the modules stating its genuine intermediate steps. All old public imports
are retained through this reexport. The existing balanced `nativeOpenPullComp`
is untouched. No adopted `WeilConjectures` declaration changes.

The theorem node's proof and dependencies follow the new assembly. The data
node's Lean attachment follows the verbatim relocation; its declaration list
now lists its three actual native declarations, with the generic records and
concrete operations remaining under their previously established owners.

Change record: `coord/changes/G7-native-open-tensor-comparison-data.md`.

Validation through the mandated `lcompile.py`: the unchanged original module
compiled in 10.0 seconds. The extracted data module and the three intermediate
modules compiled in 52.7, 54.5, 42.8 and 46.9 seconds, respectively. An initial
main-module typeclass elaboration error was repaired by explicitly supplying
the IsIso instance for the forgotten unit before reflecting it. The repaired
main theorem compiled in 5.3 seconds. The unchanged direct importer initially took
63 seconds. Its profiling run compiled successfully in 15.8 seconds, with only
5.07 seconds of declaration elaboration. No slow definition was exposed and no
consumer adaptation was necessary. The temporary consumer copy (identical except
for development profiler options) was removed from the sandbox after checking it.
No profiler options occur in the delivery.

## Proved and sorry left

This is a decomposition, not a net mathematical proof: one original hole is
closed in its module and three strictly smaller holes are added. Net hole change
is +2. The item's module itself has zero holes. No hole occurs in a definition.

Closed original hole: `AlgebraicGeometry.ProEtaleWeilSheaf.native_open_derived_tensor`
(node `lem-sf-native-open-derived-tensor`), by constructing its derived-data record
from the independently supplied comparisons and normalization proofs, proving
invertibility of the lifted unit by reflection through the native forgetful
functor, and using
the eighteen unchanged presentation equalities.

The three added holes, each in its own new module with a complete source proof
in its docstring, are:

- `AlgebraicGeometry.ProEtaleWeilSheaf.native_open_sheaf_tensor_existence`
  (`lem-sf-native-open-sheaf-tensor-existence`): source steps 1--4, only the
  sheaf adjunction, sheaf tensor maps and preservation of categorical K-flatness;
  the lifted unit is proved invertible in the main module, not left as a new hole.
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_open_tensor_localization`
  (`lem-sf-native-open-tensor-localization`): source steps 3--6, totalization and
  descent, conditional on the sheaf data, with no unit or forgetting conclusion.
- `AlgebraicGeometry.ProEtaleWeilSheaf.native_open_tensor_normalization`
  (`lem-sf-native-open-tensor-normalization`): source steps 7--8, equations for
  supplied, representative-normalized comparisons; no existence construction
  of sheaf, chain or derived comparisons is shifted into this statement.

None is the original conclusion with its hypotheses repackaged: the first has
no derived comparison, the second has no derived adjunction/forgetting
normalization, and the third only identifies maps already supplied. The final
Lean proof actually assembles `NativeOpenDerivedTensorData` and the existential
witnesses; it does not apply a renamed copy of its conclusion.

## No longer needed

No module or mathematical node is withdrawn or globally pruned. The old
17 proof dependencies remain needed in the intermediate arguments or by the
already constructed balanced compositor. They are replaced as direct dependencies
of the item by the three intermediate theorem nodes and the existing data and
operation definition nodes. The old parent-level tool approvals are removed,
except those for fixed-pair reflection and the ordinary open unit, which the
main proof uses directly. The new nodes request the original generic tool uses
for their actual steps in `split_report`.

The old explicit public imports `WeilConjectures.WeilSheaf.LowerShriek`,
`WeilConjectures.WeilSheaf.UpperStarComp`,
`Sheaf.Paper.DerivedWeilTensorOperations`, `Sheaf.Paper.NativeWeilClosedForgetful`,
`Sheaf.Paper.NativeOpenTensorPresentation`, `Sheaf.Paper.NativeOpenTensorOperations`,
and `Sheaf.CategoryTheory.ExactDerivedAdjunction`, and the private
`WeilConjectures.SixFunctors.ProEtale.Adic.Constructible` import move with the data
into the data module. The original module publicly imports that module, so these
public declarations remain available. The three new theorem modules import only
the data required by their statements; the item imports them for its proof.

## Where the brief, the DAG or earlier work was wrong

The rework row records quarantine through `SfP1ProjectionTraceFalseTail`; both
the item and its archive are currently present and identical. The original
module compiles through the prescribed private dependency overlay. No archive
was deleted, no dependency was withdrawn on the basis of quarantine, and no
source declaration was removed. There is no current return entry for this
module in `coord/returns/G7.md`.

The stated ringed-site dependencies do not immediately give records about the
specific native Weil functors and their chosen tensor models. Their remaining
Frobenius lifting and representative-normalization argument is now stated as
source-backed intermediate theorems, rather than silently treated as a direct
application of the ordinary theorem. No mathematical correction to the target
or unit route is claimed.

Edge cases checked in the statements: the empty open and identity open,
zero inputs, arbitrary unbounded complexes, and absence of a separate
quasi-compactness hypothesis on j. Preservation is two-sided categorical
K-flatness, not merely flat terms. The sheaf data are quantified rather than
selected as an arbitrary witness inside a definition. Equalities pin the actual
native functors, insertions and chosen models. Forgetting uses the actual fixed
tensor comparison and exact-functor factors and asserts both the restriction
square and unit-normalized open comparison.

The imported unit record has no realized steps for this auxiliary node; the
current blueprint's Step 1 second Hom bijection and its open projection factor
are retained. The blueprint search returned two broad projection-formula nodes,
neither the native intermediate statements. Mathlib searches returned only
ordinary scheme restriction lemmas, which do not perform the equivariant
construction or its representative normalization.

## New nodes

`lem-sf-native-open-sheaf-tensor-existence` states the sheaf/K-flat part of the
existing proof, with the original generator, exactness and fixed-pair tools.
It does not assert either derived comparison or its ordinary forgetting.

`lem-sf-native-open-tensor-localization` states the complex/localization part
for supplied sheaf data, and retains all summand and representative equations.
It neither reconstructs the sheaf adjunction nor proves the normalization of
the derived inverse or the ordinary forgetting square.

`lem-sf-native-open-tensor-normalization` isolates those last equations for
supplied, representative-normalized maps. It relies on the exact-derived
adjunction and ordinary unit normalization, with no new geometric assumptions.

The existing definition node `def-sf-native-open-tensor-presentation-data` owns
the new data module by relocation. It introduces no new notion or postponed
data. Change record: `coord/changes/G7-native-open-tensor-comparison-data.md`.

## Second reading by G7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
