## What changed

Restored the assigned quarantined module
`Sheaf.AlgebraicGeometry.PerfectGeneratorPullback` as a public re-export of
`WeilConjectures.AlgebraicGeometry.PerfectGeneratorPullback`, with a proved exact-signature
compatibility theorem `AlgebraicGeometry.perfect_generator_pullback_compat`.
The stronger adopted theorem remains available under its original name.
`nonempty_derivedOpenLocalization` supplies its extra source-open localization family;
projection gives exactly the archived conclusion. No extra hypothesis is imposed.

The node `lem-pc-perfect-generator-pullback` keeps its Sheaf module/file and mathematical
statement. Its Lean attachment now names the compatibility theorem. The proof metadata
retains the adopted proof's adjunction, affine equivalence, shift and conservativity
inputs and adds the existing perfectness and open-localization inputs.
Change record: `coord/changes/Z5-perfect-generator-pullback-compat.md`.

Repair of return C-8879e (delivery head 8879eb555c8): retain the reviewed restoration
and its complete compatibility proof, and rebuild the delivery on current `sheaf-dag`
through `deliver3.py`. The previous landing failed while reading the unrelated,
quarantined `StrictLocalBaseChangeGlobalHomology` module; that module is not an import
of this restoration and is not changed or withdrawn here. On 2026-10-22 the restored
module and exact-signature/axiom probe were compiled again on the project server.
Both import-cycle checks were repeated successfully against the current repository.

The main module compiles without errors or warnings. The compatibility signature was
compared textually with the archive: only its name differs. A separate server-compiled
probe checks the complete archived assertion and prints both the adopted theorem's
axioms and the compatibility theorem's axioms. The only code caller and DAG parent,
`WeilConjectures.AlgebraicGeometry.AffinePullbackPerfectDetectsIso`, already calls the
adopted theorem and requires no adaptation. An additional server-compiled probe imports
the restored module together with that
consumer and checks all three declarations; no duplicate declaration occurs. Both
imports pass import-cycle checks. The axiom probe reports exactly
`propext`, `Classical.choice`, and `Quot.sound` for both generator theorems.
Empty schemes, zero objects and identity morphisms impose no extra conditions; the
open-localization theorem holds for all schemes and all opens.

## Proved and sorry left

This is a repair with zero original holes: proved 0 of 0 sorries; added 0 holes;
0 statements split off. The archived theorem was already proved.
`AlgebraicGeometry.perfect_generator_pullback_compat` has a complete proof.
No sorry remains in the restored module. The public adopted theorem is proved too.
No definition chooses arbitrary data from an unproved existence statement: the
localization family is obtained inside a theorem proof from a proved size theorem.

## No longer needed

Removed the archived public import `Sheaf.AlgebraicGeometry.DerivedPullback`, which is
withdrawn. Its canonical replacement is publicly available through the adopted generator
module. The separate public imports of `WeilConjectures.AlgebraicGeometry.PerfectComplex`
and `Mathlib.AlgebraicGeometry.Morphisms.Affine` are supplied by that same public module.

Removed the archived private imports
`WeilConjectures.AlgebraicGeometry.AffineDerivedPushforwardConservative`,
`Sheaf.AlgebraicGeometry.DerivedPullbackTensorQCoh`,
`WeilConjectures.AlgebraicGeometry.FiniteAffineDerivedEquivalence`, and
`WeilConjectures.AlgebraicGeometry.DerivedAdjoint` from this module. Their canonical
declarations remain required by the complete adopted source theorem and therefore
remain in the DAG dependencies. No mathematical node or source module is pruned.
No module is withdrawn; the quarantine archive and parent/unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

The assignment is quarantined zero-hole restoration, rather than an open proof.
Its archived import points at a retired derived-pullback module. Its original theorem
name is now owned by an adopted theorem that additionally asserts perfectness and asks
for localization families on opens of both schemes. Blindly copying the archive does
not restore the interface; re-export plus a compatibility theorem resolves both the
name collision and the changed interface. No upstream declaration is changed or removed.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
