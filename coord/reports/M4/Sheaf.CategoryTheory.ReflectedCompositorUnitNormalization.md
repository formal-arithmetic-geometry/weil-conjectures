## What changed

Proved `CategoryTheory.ReflectedCompositor.unit_normalization` in
`Sheaf.CategoryTheory.ReflectedCompositorUnitNormalization`, following all five steps of
`lem-sbc-reflected-compositor-unit-normalization`.

Two proved private helpers compute the included reflected unit and reflected Hom bijection.
The main proof identifies the successive-unit composite transpose with the reflected transpose,
uses the ambient and reflected conjugacy unit equations, and applies injectivity of the ambient
composite Hom bijection. Natural transformation extensionality gives the natural equation;
the same transpose calculation gives the inverse-transpose formula.

Existing statements, definitions and imports are unchanged. Both planned dependencies are Mathlib
leaves already available through the existing imports: `Adjunction.comp` and
`unit_conjugateEquiv_symm`. The DAG route and dependencies are unchanged, so no node copy is needed.

Validation: the complete file compiled without warnings through `lcompile.py` (6.3 seconds).
A further compile with `#print axioms CategoryTheory.ReflectedCompositor.unit_normalization`
reported exactly `propext`, `Classical.choice`, and `Quot.sound` (3.9 seconds).
The temporary print command was removed before delivery.

## Proved and sorry left

Closed: `CategoryTheory.ReflectedCompositor.unit_normalization`
(node `lem-sbc-reflected-compositor-unit-normalization`), 1 of 1 original holes.
Added: zero holes. Remaining: zero holes. Split off: zero statements.
The private helpers `map_unit` and `map_homEquiv` are fully proved.

## No longer needed

None. All three original public imports remain necessary for the existing definitions.
Both declared proof dependencies are used through their recorded Mathlib matches.
No nodes or modules are pruned, and no new proof imports were necessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing statements and the planned two-transpose
argument work unchanged. The source-reflector assumption `_r₀` is unused in the proof,
as its existing name suggests; its binder is preserved verbatim.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
