## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.unboundedBaseChangeExtension` in
`Sheaf.Paper.UnboundedBaseChangeExtension`, keeping its signature and both public definitions
unchanged. The proof uses the existing proper-image and inverse-image preservation clauses,
the exact-functor comparison API, compatible shifts on the actual derived adjunctions, and
the generic triangulated isomorphism-locus instance. Private, fully proved helpers establish
shift compatibility, preservation of sums by the two composites, and the localizing
determination argument. The DAG proof now describes this implementation.

The preflight requested a record of the extra universe names and file-local instance
registration: `coord/changes/K3-unbounded-base-change-proof-commands.md`. It audits all
39 downstream modules and confirms that their visible interface is unchanged. No
consumer is adapted.

The earlier coefficient split was only an abandoned sandbox draft. Its report was stale;
none of its proposed statement modules or nodes is included in this delivery.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.unboundedBaseChangeExtension`
(node `det-proper-base-change-unbounded-extension`). Added zero holes and zero new modules.
There are no `sorry` declarations left in the item module. Imported, already stated
preservation results remain the project's existing downstream proof obligations.

The complete module compiled with `lcompile.py` in 15.2 seconds before import pruning.
The pruned module also compiled cleanly in 20.9 seconds. The final delivered module also passed the delivery compiler and axiom/declaration
probe on resumption. The first resumed preflight required the command-change record
above; the subsequent dry run checks the complete delivery.

## No longer needed

Removed five proof imports: `Sheaf.Paper.CartesianCoefficients`,
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`,
`Mathlib.CategoryTheory.Adjunction.CompositionIso`,
`Mathlib.CategoryTheory.Triangulated.Subcategory`, and
`Sheaf.Paper.CondensedModuleDerivedPushpull`. The exact pullback and derived adjunction
interfaces are already exported by the upstream ambient exchange imports; the subcategory
interface is already exported by the localizing closure import.

The separate restricted-functor construction of
`lem-weil-pbc-triangulated-functor-restriction` is unnecessary: the proof works in the ambient
categories and intersects the exchange's isomorphism locus with the source localizing closure.
The high-level declaration planned by `sk-lem-sf-determination` is not invoked; its
localizing determination argument is proved directly by the private `extend_iso` helper.
`Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus` is not imported: its theorem assumes
sum preservation on the entire source, while this proof needs only preservation of sums of
localizing objects. The generic upstream isomorphism-locus theorem is used instead.
The unit's proper-image, pullback, and determination route is retained mathematically.
No claim is made that these nodes or modules become unreachable from all other parents.

## Where the brief, the DAG or earlier work was wrong

The prior sandbox report described five coefficient split-offs that are not present in the
current sandbox. They are unnecessary: one generic preservation-to-extension proof handles
every coefficient. The original DAG's target restriction and coproduct constructions can be
avoided by intersecting with the ambient isomorphism locus. The proof uses only existing
ambient colimits, so it does not assume that arbitrary sums beyond the fixed small universe
exist. The six coefficient cases, including finite-subextension-valued algebraic closure
coefficients, and the canonical base-change map are unchanged.

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
