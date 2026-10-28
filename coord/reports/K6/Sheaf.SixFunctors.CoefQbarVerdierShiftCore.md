## What changed

Repaired `Sheaf.SixFunctors.CoefQbarVerdierShiftCore`: its old hypothesis permitted
arbitrary finite exact shifts, whereas descent requires compatibility with the
normalized scalar-extension comparisons. The corrected `descended_shift_core`
assumes naturality of concrete `shiftComponent` maps and has a complete categorical
assembly proof. The proof transports finite shifts, cancels opposite inclusion
comparisons, detects zero/addition laws on the covering finite inclusions, and
identifies the finite comparison's shift structure using `CommShift.ofIso`.

Added `Sheaf.SixFunctors.CoefQbarVerdierShiftComponents`. Both definitions are real
constructions from the given functors and shifts. The finite-restriction structure
is irreducible, with a proved compatibility lemma that avoids unfolding its data. Its one unfinished theorem isolates the
finite exact shift choice and explicit arrow-naturality equation. It does not
assert a global coherent shift or the finite comparison conclusion.

Adapted the only caller, `Sheaf.SixFunctors.CoefQbarVerdierShift`, to choose the
normalized finite family. Its public statement is unchanged. Updated both DAG
proof plans and the core's statement-change record.

Change record: `coord/changes/K6-coef-qbar-shift-naturality.md`.

Validation: `lcompile.py --all` compiled Components (16.9 s), the generic assembly
(its previous compile was 2.3 s), Core (14.5 s), the adapted Shift caller (13.3 s),
and an unchanged copy of the direct consumer CoefQbarVerdierExactness (18.4 s).
The unchanged consumer copy was removed after verification. All debugging options
and temporary proof holes are removed. Node signatures, blueprint docstrings and
proof-dependency unions agree with the source; the caller's signature is unchanged.

## Proved and sorry left

The item originally had one textual hole. The original unrestricted statement is not
claimed proved: its hypothesis was defective. The corrected conditional
`WeilConjectures.CoefQbarVerdier.descended_shift_core` is completely proved, including
all zero and addition coherence and all finite comparison squares. Its categorical helpers in the new
`Sheaf.SixFunctors.ShiftDescentAssembly` are proved (compiled in 2.4 seconds). The caller's proof is complete with its original
signature.

One hole is added and remains:
`WeilConjectures.CoefQbarVerdier.finite_shift_naturality`, node
`lem-coef-qbar-verdier-shift-naturality-K6`. It requires the actual finite internal-Hom
shift normalization and the quotient-arrow naturality calculation described in its
docstring. This is a statement repair plus a decomposition, not a proof of the old
unrestricted statement. The delivered modules have exactly one remaining hole;
net hole reduction is zero. No data is chosen from the unproved theorem in a
definition.

## No longer needed

Removed the core's redundant direct public import of
`Mathlib.CategoryTheory.Triangulated.Opposite.Functor`; the new component module
publicly imports it because its statements need the opposite shift conventions.
The original functor module remains publicly available through that same module.

The core's categorical assembly no longer needs finite triangulatedness as a
hypothesis, nor `lem-coef-rational-operations` as a direct proof dependency.
Finite exactness and rational internal-Hom normalization are needed by the new
finite naturality theorem. They are not globally pruned. The old arbitrary
`RationalVerdier.Datum.exact.choose` route in the caller is removed because it
does not normalize finite shifts under scalar extension. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: exactness of independently prescribed finite shifts does not
imply their compatibility with the normalized beta comparisons. For X = Spec(D.k), with the identity
structure map over the fixed algebraic closure, all finite rational triangles are split. Twisting the degree-n comparison
by a^n preserves exactness and shift coherence. Different nonzero choices a=1
and a=2 at nested fields violate the scalar-extension shift square on the unit.
The change record gives the full obstruction. The old core's proof text selected
canonical shifts, but its Lean signature quantified over arbitrary exact ones.

The parent statement and the unit route are retained. Canonical finite shift
normalization is now an explicit obligation, rather than being inferred from an
existential exactness field. The assembly is an actual Lean proof, rather than
another copy of the global descent assertion.

## New nodes

`lem-coef-qbar-verdier-shift-naturality-K6`, in the same chapter and unit as the
item, records the finite exact shift choice and naturality of explicit components.
Its source is the existing node's evaluation-transpose and representative proof
plan, expanded in its docstring. Zero/addition and finite-comparison compatibility
are excluded from its conclusion and proved in the core.

`lem-commshift-object-cover-assembly-K6` records the proved generic assembly
construction in `Sheaf.SixFunctors.ShiftDescentAssembly`. It uses no coefficient
data and isolates the zero/addition cancellation argument. It adds no holes.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarVerdierShift": "09d0af7c0a3367d67eb51c4247442bf1a95d0785", "Sheaf.SixFunctors.CoefQbarVerdierShiftComponents": "481d8e3d8dc78f522058d3688f0aa7796864d4a9", "Sheaf.SixFunctors.CoefQbarVerdierShiftCore": "8a001f54db9b0dcc2effb642aa154a4b41e31c5c", "Sheaf.SixFunctors.ShiftDescentAssembly": "1132078ccd0a71de29bd762342f3bd36d7ad9ab4"}, "results": {}, "time": "2026-10-28T12:37:52+0800", "transitive": 0, "version": 1}
```

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
