## What changed

Proved `AlgebraicGeometry.affineQCohDerivedEquivalence_core_triangulated` in
`Sheaf.AlgebraicGeometry.AffineQCohDerivedTildeTriangulated`, preserving its signature.
The proof passes through the homotopy category: descend the assumed isomorphism through
fully faithful precomposition by the homotopy quotient, then use Mathlib shift descent
and triangulatedness descent along `DerivedCategory.Qh`. The composite on homotopy
categories is triangulated because termwise additive tilde preserves cone triangles.
Updated the existing node's proof to record the actual argument. No imports were added.

The shared sheaf category requires an explicit type annotation for tilde and its additive
instance proved with `tilde.map_add (R := .of A)`. The local transparency option allows
Lean to identify the shared sheaf and Scheme.Modules morphisms. Explicit application of
`Functor.IsTriangulated.instComp` avoids a composite-instance inference failure.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.affineQCohDerivedEquivalence_core_triangulated`
(node `new-affine-qcoh-derived-tilde-triangulated`).
No sorry remains in the item. No holes were added or split off.
Local compilation passes without warnings. The dry run checks the declaration's axioms;
the current delivery tool uses local compilation, followed by the maintainer's global build.

## No longer needed

No imports, nodes, or modules were removed. All three existing public imports are used
by the unchanged statement and proof. No additional affine exactness or derived-functor
construction module is needed: the factorization hypothesis allows direct descent.
The existing dependency `def-pc-derived-category` stays; no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original plan did not identify the Mathlib descent interfaces. Its exactness
argument is unnecessary under the given factorization hypothesis. Additivity suffices
on the homotopy category; the existing functor G and its specified factorization supply
the required localization. This does not change the statement, including either derived
category universe or the ring assumptions. It also works for the zero ring.

The referenced unit has no realized statement or steps assigned to this node; the proof
retains its intended compatibility step. The blueprint source files are absent from
this checkout; the unit record and the existing node/docstring were read.

## Second reading by N1

1. Compared the delivered module and node against the repository versions. The existing
   theorem signature is byte for byte unchanged; no definition or declaration was added.
   All public imports occur in the statement (including `IsTriangulated`). Verdict: pass.
2. Local compilation passes without warnings. The file contains no remaining sorry or
   forbidden declaration. A scratch-copy axiom probe reports `propext`, `Classical.choice`,
   `Quot.sound`, with no `sorryAx`; the module closes its own sole hole. Read the
   Mathlib shift-localization and
   triangulated-descent lemmas: the lifting isomorphism determines the transferred shift,
   and no arbitrary witness is used as data. Verdict: pass.
3. No new statements or split-off holes exist. The proof uses existing Mathlib results,
   rather than restating the item under another name. The ring assumptions are untouched;
   additivity and the supplied factorization work also for the zero ring. Verdict: pass.
4. Searched the library for the same declaration and Mathlib for homotopy triangulation,
   localization shift transfer, and triangulated descent. The chosen route uses those
   generic results directly. All three public imports are required by the signature;
   the old `proof_deps` contains only `def-pc-derived-category`, which remains used.
   The unit's `realized` fields are empty, so no assigned statement or step is bypassed.
   Verdict: pass; nothing can be pruned here.
5. Read the node alongside the proof. Its three steps match additivity, fully faithful
   quotient precomposition, and localization descent. The proof dependencies and origin
   remain consistent with this compatibility argument. Verdict: pass.

Second reading changed only this report, adding the required review and recording the
actual axiom probe. No Lean repair was needed; one hole closed, zero holes added.
