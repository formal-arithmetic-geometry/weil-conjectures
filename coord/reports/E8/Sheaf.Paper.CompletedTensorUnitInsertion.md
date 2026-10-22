## What changed

Prove `CategoryTheory.ConstantCompletion.completedTensorUnitInsertion` from the actual
completion adjunction and native tensor-Hom adjunction. The main proof constructs the
tensor insertion isomorphisms by testing Hom into complete objects, obtains pullback
insertion from the ordinary derived adjunction, constructs the normalized completed
comparison and its unit, and proves comparison uniqueness by cancellation. The completed functor coherence is proved
by monoidal localization: retain the strong reflectors, identify the normalized
tensor and unit comparisons by cancellation, and descend the braiding equation
along the complete-object unit isomorphisms.

Separate the independent categorical coherence statements and the ordinary native
pullback tensor comparison into their own modules. Move the eleven existing interface
definitions verbatim to `CompletedTensorUnitInsertionData`, publicly reexported by the
item, to avoid import cycles. Only their docstring blueprint annotations change.
Change record: `coord/changes/E8-completed-tensor-shared-interface.md`.

The unclaimed `RingedDerivedClosedSymmetricMonoidal` module retains the native
identifications of its existing coherence construction in a proved private helper.
Its original public theorem keeps its signature and follows by forgetting those
identifications. The new pullback theorem reuses this existing construction through
a private proof import. All original imports, definitions and attributes of the
coherence module remain verbatim. Change record:
`coord/changes/E8-native-model-witness-api.md`.

## Proved and sorry left

The original hole is
`CategoryTheory.ConstantCompletion.completedTensorUnitInsertion` (node
`lem-pur-completed-tensor-unit-insertion`). Its proof body is complete.

All three new supporting results also have complete proof bodies:

- `CategoryTheory.ConstantCompletion.constantNativePullbackMonoidal` (node
  `lem-pur-constant-native-pullback-monoidal`).
- `CategoryTheory.ConstantCompletion.reflectiveCompletedMonoidal` (node
  `lem-pur-reflective-completed-monoidal`).
- `CategoryTheory.ConstantCompletion.reflectiveCompletedPullbackCoherence` (node
  `lem-pur-reflective-completed-pullback-coherence`).

There are no `sorry` tokens in any of the six delivery modules. The eleven
relocated definitions contain no holes. No source-library hole is added.
The packet fills one original hole and adds no proof holes; closure-ledger figures
remain the delivery tool's separate measurement against its pinned baselines.

All six delivery modules compile together on the project server with
`lcompile.py --all` (exit 0), without warnings. The assembled main theorem compiled
in 22.1 seconds, the native pullback comparison in 56.1 seconds, the completed
monoidal model in 7.9 seconds, and completed pullback coherence in 5.7 seconds.
The retained source construction separately compiled in 23.0 seconds; the assembled
check reused its artifact. The native proof applies a proved categorical lemma to
replace both representatives, replace the three counit components, and cancel the
target tensor and canonical total-comparison isomorphisms.

## No longer needed

The direct proof imports removed from the original item are
`Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence` and
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`. The old DAG
step 4 also named `lem-weil-pbc-pullback-tensor-canonical-shift-unit`, whose tensor
interface is not the native tensor used by this item's fixed statement. The proof
uses the existing native model and `RingedDerivedComparisons.tensorLift_exists`
instead. These removals are from this proof's immediate dependencies; transitive
uses in existing declarations remain needed, and no upstream declaration is removed.

The original closed symmetric monoidal construction now retains its native witness
identifications in a proved private helper. The native pullback proof reuses this
helper, so its direct proof imports of
`Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction` and
`Sheaf.Algebra.Homology.RingedTensorComplexConstraints` are removed. Both remain
needed by the original coherence construction; the main completion proof also uses
the tensor-Hom adjunction. The original public closed-coherence statement and its
public interface import stay unchanged. No existing Lean module is withdrawn.
No blueprint unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The old step 4 did not directly match the fixed native tensor interface. The existing
canonical derived tensor lift does match it after retaining the native tensor model
and descending the actual complex-level left-derived counit to the homotopy category.
The original statement, its statement dependencies, and all definition bodies remain
unchanged. The relocated interfaces are recorded as a proof dependency.

`tools/downstream.py` with all eleven relocated declaration names reports zero
modules downstream of the item, and each name occurs only in the item itself.
Edge checks use the identity reflector and identity inverse image, where insertion
maps and normalized comparisons reduce to the ordinary constraints; no ideal,
quotient perfectness, or boundedness hypothesis is introduced. The generic statements
require explicit local Hom bijections and insertion isomorphisms, so an arbitrary
endofunctor cannot satisfy their hypotheses just by naming it a completion.

## New nodes

`def-pur-completed-tensor-unit-insertion-data` attaches the eleven unchanged explicit
interface definitions in `Sheaf.Paper.CompletedTensorUnitInsertionData`.

`lem-pur-constant-native-pullback-monoidal` isolates ordinary native pullback tensor
coherence, independently of any ideal or completion, with the actual cochain
normalization.

`lem-pur-reflective-completed-monoidal` isolates the symmetric monoidal structure
and exact constraint formulas on a tensor-compatible full reflective subcategory.

`lem-pur-reflective-completed-pullback-coherence` isolates the inheritance of
symmetric oplax monoidal coherence by an already constructed normalized completed
comparison, after both completed constraint models are supplied. It does not assert
any tensor insertion, pullback insertion, existence, or uniqueness result.

Change record: `coord/changes/E8-completed-tensor-shared-interface.md`.
The native witness reuse is recorded in
`coord/changes/E8-native-model-witness-api.md`.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
