## What changed

Repair of the returned head `c1773f63b5e`: the reviewer passed the mathematics, but
landing rejected the reviewer's change-record override basename. The packet includes
`coord/changes/P7-native-hom-source-shift-data.md`; the landing tool accepts a reviewer
override for it only as `P7-native-hom-source-shift-data.change.md`. The change record
now states both paths explicitly so a subsequent review can use the correct mapping.
No corrected reviewer file was retained in the current return records. The accepted
Lean files and DAG edits are retained verbatim from the returned head.

The current server queue still assigns the original proof obligation, with no rework
row or build-error file for the item. Comparison against current main shows that the
item's original Lean file and node have not changed since the returned delivery's
base; both new modules remain absent on main. The delivery tool rebases the packet on
current `sheaf-dag` and runs its compile and preflight checks before pushing.
The repair's `lcompile.py --all` returned exit code zero for all three modules,
reusing valid cached server results. The hole count is still zero in the item, zero
in the data module, and one in the successor module.

Reduced the single hole in `Sheaf.CategoryTheory.NativeHomSignedShiftLaws` to the raw
source-Hom successor recurrence, with its second shift parameter fixed to one. This is
an induction reduction, not the original two-parameter statement under another name.
The original theorem's signature is unchanged.

The item now proves naturality of the prescribed maps, their zero law by expanding the
adjoint mate, the exact quadratic-sign recurrence for every integer, and a general
integer-induction argument recovering arbitrary addition from successor addition.
The backward induction cancels the degree-one isomorphism and uses faithfulness of the
shift functor; it assumes no new inverse law or pre-existing Hom CommShift structure.

The four explicit definitions move verbatim to `NativeHomSourceShiftData`, publicly
reexported by the item, so `NativeHomSourceShiftSuccessor` can state the remaining
one-parameter obligation without an import cycle. No data is chosen from an unproved
theorem. No existing module other than the assigned item changes.

Validation: `lcompile.py --all` compiled the data module, the successor statement,
and the item without warnings; the item took 7.4 seconds. Both direct consumers
compiled unchanged against these files: `NativeHomLocalizedConeBoundary` in 3.2
seconds and `NativeDerivedHomSignedExact` in 6.3 seconds. Their unchanged validation
copies were removed from the sandbox. A source comparison also confirms that the
original theorem signature and all four relocated definition signatures/bodies are
identical. All delivered Lean lines are at most 100 characters.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.siteHom_signed_source_shift_laws`
(node `lem-sf-native-hom-signed-shift-laws`) by decomposition.

Added exactly one hole:
`AlgebraicGeometry.ProEtale.siteHom_opposite_source_shift_successor`
(node `lem-sf-native-hom-source-shift-successor`), in the new module
`Sheaf.CategoryTheory.NativeHomSourceShiftSuccessor`. Its assertion is only the raw
addition case `(m, 1)`, without a zero clause, a quadratic normalization, or a second
arbitrary integer parameter. Its source and complete mate-calculation proof plan are
in its docstring and node. The data module has zero holes; the item has zero holes.
Net hole change: zero (one closed, one added); this is one decomposition and zero
fully closed original holes in the transitive proof closure.

Proved private helpers include `sourceShift_zero`, source and signed naturality,
`quadratic_sign_successor`, `signedSource_zero`, `signedSource_successor`,
`isoAdd_cancel_first`, and `coherent_of_successor`. In particular the zero conjunct
and the full all-integer coherence assembly are proved, including negative indices.

## No longer needed

No existing node or module is withdrawn or pruned. The original five public Mathlib
imports are relocated verbatim into the new data module; their public API remains
available through its public import. The new successor import is private and used
only by the proof. The private Ring tactic import proves the numerator identity.

The original plan's arbitrary two-parameter raw mate computation and the general
identity q(m+n)=q(m)+q(n)+mn are not needed: only the degree-one raw recurrence and
q(m+1)=q(m)+m+1 remain. No previously declared proof dependency is dropped; the old
node had an empty dependency list.

## Where the brief, the DAG or earlier work was wrong

The old node treated the entire two-parameter mate calculation as elementary and
left all of the zero law, sign algebra, and coherence assembly inside one hole.
These are separate arguments. The new proof checks zero, sign algebra and integer
induction in Lean and isolates only the raw degree-one tensor interchange.
The unit route is unchanged. The source states derived Hom exactness with details
omitted, so the explicit mate expansion is identified as agent-written throughout.

Edge cases considered: zero shift has quadratic sign 1 and the opposite zero unitor;
the scalar recurrence holds for all integers, including m=-1 and m=-2, by exact
integer division; backwards induction uses invertible maps and a faithful shift,
so it does not impose positivity or exclude zero objects or characteristic two.
No consumer interface, target, mathematical definition, or hypothesis is changed.

## New nodes

`def-sf-native-hom-source-shift-data` records the four existing explicit map definitions
in their new shared module; it adds no mathematical assertion or hole.

`lem-sf-native-hom-source-shift-successor` states only the raw degree-one mate recurrence.
The parent proves the remaining sign conversion and every other integer case.

Change record: `coord/changes/P7-native-hom-source-shift-data.md`.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 1 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.CategoryTheory.NativeHomSignedShiftLaws": "6e8d11aeb01fda44fd9ff033cef1976e09e4d428", "Sheaf.CategoryTheory.NativeHomSourceShiftData": "e1db05faeff8a3ed0c00f5912eb3b724d7cd1832", "Sheaf.CategoryTheory.NativeHomSourceShiftSuccessor": "47c38407210548f4ad599942e1d3a9b911ebe71c"}, "results": {"Sheaf.CategoryTheory.NativeDerivedHomSignedExact": {"hash": "b9982a76d0884b2e6e9a1d8271d551afb48f585b", "status": "INFRA"}, "Sheaf.CategoryTheory.NativeHomLocalizedConeBoundary": {"hash": "b8a7d73d2a449e7470afeb9981ab2a5142e66c4d", "status": "OK"}}, "seconds": 70, "time": "2026-10-28T08:26:14+0800", "transitive": 0, "version": 1}
```

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
