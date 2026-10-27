## What changed

Added two proved objectwise specializations in the item module:
`CategoryTheory.brownHypotheses_finiteField_object_compactness` proves the finite-field
case for all six admissible coefficients. It obtains essential smallness from the
existing Noetherian smallness proof, chooses a small skeleton, applies the existing
finite-field compactness theorem, and transports compactness to the caller's object.
`CategoryTheory.brownHypotheses_integral_object_compactness_of_ext_bounded` proves the
integral case over an arbitrary positive-characteristic field with the uniform
constructible Ext bound explicitly supplied. It rewrites the final clause of
`integralConstructibleCompactness` along the proved equality of the two localizing
closures. Both conclusions use the caller's coproduct structure.

Added statement imports of `FiniteFieldFiber` and `LocalizingAdmissibleCoefficients`;
added private proof imports of the existing finite-field compactness, Noetherian
smallness, integral compactness, localizing-closure equality, and ObjectProperty
smallness modules. Existing statements, definitions, and public imports are preserved.
No other existing module is changed. These are partial results, not a proof of the
unrestricted disputed theorem.

## Proved and sorry left

Original holes closed: 0 of 1. Holes added or split off: 0.

Proved, with no local holes:
- `CategoryTheory.brownHypotheses_finiteField_object_compactness`.
- `CategoryTheory.brownHypotheses_integral_object_compactness_of_ext_bounded`.

The one remaining hole is
`CategoryTheory.brownHypotheses_arbitraryField_compactness_obligation`, node
`new-sfb-brown-arbitrary-field-compactness-obligation`. Its signature and existing
`STATEMENT-DISPUTED` warning are preserved. Neither new proof uses that declaration
or imports `BrownHypotheses`, which would create an import cycle. Existing dependency
holes remain dependency items as intended by stage 3. The new specializations are not
counted as closing, or decomposing, the original hole.

Validation: the corrected item module and its unchanged direct importer,
`Sheaf.SixFunctorsBasics.BrownHypotheses`, both passed single-file compilation through
`lcompile.py` (exit 0). The temporary importer copy was removed after this check.
Delivery preflight records the final probe and mechanical checks. An earlier compile
found a missing local CompactSpace instance in the integral proof; the corrected
proof derives compactness and local Noetherianity from finite type over the field.

## No longer needed

No existing import, node, or module is withdrawn. The original disputed theorem is
still used by `BrownHypotheses.brownHypotheses_arbitraryField_compactness_witness`,
so zero importers cannot justify withdrawal here. The integral Ext criterion in
`BrownHypotheses` is not imported: it depends on this item through its parent module,
and it is only a conditional criterion. The integral specialization uses its lower
inputs directly instead. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the assigned statement quantifies over every scheme and every
commutative condensed coefficient ring. It does not even retain the parent statement's
finite-type, characteristic, or coefficient-admissibility assumptions. Its sole DAG
step is not a proof plan for that claim: it explicitly says the assertion is false.
The finite-field input requires the specified geometric finite-field datum and the
six admissible coefficients. The integral criterion is an equivalence with a uniform
Ext bound, not an unconditional source of that bound. The two new Lean proofs make
exactly these valid uses of the existing inputs.

The parent's documented obstruction takes characteristic 3, coefficient F_2, and
k = algebraicClosure(F_3)(t_1,t_2,...). Nonzero Kummer cup symbols in arbitrarily high
degrees obstruct compactness of the rank-one constant object. This field-cohomology
calculation is not formalized by this packet; no Lean counterexample is claimed.
In the mathematical argument, take the successive valuations in t_n,...,t_1.
The iterated residue of the n-fold Kummer symbol is 1 in F_2, so that symbol is
nonzero. The remaining independent variables may be retained in every residue
field. Thus the constant rank-one sheaf has nonzero self-Ext in every positive
degree. Its shifted single-term complexes are degreewise disjoint, so exact
countable products identify their coproduct with their product in the derived
category and in the full localizing closure. The product property assembles a map
with all these nonzero components. Compactness would give finite support for that
map, a contradiction. This is a reason to correct the source claim, not a missing
categorical glue lemma.
Even imposing the parent's finite-type hypotheses does not supply a uniform Ext
bound on such a field. A further split into an unconditional Ext bound or
surjectivity assertion would simply introduce another false statement. No such
statement is added. The original source obligation needs mathematical correction;
these two proved conditional/specialized results do not silently change its meaning.

## New nodes

`p3-brown-finite-field-object-compactness` records the finite-field objectwise
specialization, including the Noetherian smallness and skeleton argument.
`p3-brown-integral-object-compactness-with-ext-bound` records the integral
objectwise specialization with the Ext bound as a real hypothesis. Both are proved
in the item module and add zero holes.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
