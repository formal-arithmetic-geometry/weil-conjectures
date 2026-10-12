## What changed

Replaced the earlier attempt with a constructive reduction of
`AlgebraicGeometry.Scheme.exists_reduction_units_finite_filtration`, preserving its
signature and original docstring. The filtration terms are now the explicit kernels
`Scheme.reductionUnitsPowerKernel X j` of restriction modulo `X.nilradical ^ (j + 1)`.
No definition obtains data by choosing witnesses of an unproved existence theorem.

Proved positive-power nilpotence of the nilradical by a finite affine subcover and
Mathlib's ring nilpotence theorem, including the empty cover. Proved that the final
kernel vanishes when its defining ideal is zero. Proved the whole transport to the
reduction: pullback of kernels, the counit comparison identifying the initial
kernel, preservation of the zero term and of short exact complexes, and transport
of all three endpoint isomorphisms.

The remaining geometric step is a single new theorem about consecutive, fixed
kernel sheaves on X, without Noetherianity or a global nilpotence exponent. It
states only the quasi-coherent short exact quotient, not existence of a finite
filtration or any claim about the inverse image on the reduced site. Its new module
is `Sheaf.AlgebraicGeometry.Curve.ReductionUnitsPowerQuotient`. The two other new
modules are `ReductionUnitsPowerKernel` and `ReductionNilradicalNilpotence` in the
same namespace. The main module imports the quotient and nilpotence modules for
its proof. Each has its own DAG node, and the original node's proof and dependency
list follow the implemented route.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.exists_reduction_units_finite_filtration`
(node `lem-sc-reduction-units-finite-filtration`): its complete Lean proof uses the
new single-step quotient theorem. There is no sorry in the item's module.

Also proved, with no sorry dependency,
`AlgebraicGeometry.Scheme.exists_nilradical_pow_succ_eq_bot`
(node `lem-sc-reduction-nilradical-nilpotent`) and the private helper
`isZero_reduction_units_kernel_of_eq_bot`. The definition
`AlgebraicGeometry.Scheme.reductionUnitsPowerKernel` is a real kernel construction.

Added exactly one hole:
`AlgebraicGeometry.Scheme.exists_reduction_units_power_quotient`
(node `lem-sc-reduction-units-power-quotient`). Its proof is exactly `by sorry` and
its docstring supplies the complete local algebra and descent argument.

This is a decomposition: one original hole closed and one strictly smaller hole
added, net zero holes. The nilpotence and categorical transport parts are proved;
the full filtration theorem still depends on the quotient hole. All four modules
compile through lcompile.py; the delivery dry run verifies their axiom probes.

## No longer needed

Removed the proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Etale` from the main module.
Its original proof dependency `etale-proposition-etale-reduced` is not used: our
kernel filtration is defined by restriction to the actual subschemes of ideal
powers, so no identification of an etale object's own reduction is necessary.
This theorem may remain reachable elsewhere, so no global pruning count is claimed.

The definition node `def-sc-etale-qcoherent-module` remains needed in the new
quotient node and in the main signature; it is not pruned. The reduction universal
homeomorphism and topos invariance dependencies remain in the implemented proof.

Deleted the earlier sandbox's unused `ReductionUnitsNilpotence.lean`, the proposed
`reduction_units_filtration_construction` and
`reduction_units_initial_identification` declarations, and their two node files.
Neither is imported or needed by this delivery. No unit statement or realized unit
step is bypassed; the unit record's realized lists are empty for this subargument.

## Where the brief, the DAG or earlier work was wrong

The earlier `reduction_units_initial_identification` was false: the zero sheaf
with a zero-length filtration satisfies all its hypotheses, which would force
the reduction-units kernel of every Noetherian scheme to vanish. On the dual
numbers over a field it does not vanish (units 1+a epsilon give nonzero kernel).
The old construction lemma allowed just that irrelevant zero filtration. Those
statements and incomplete node records were removed, not used as assumptions.

The earlier report's claim that all existing imports were required was also
incorrect. The old auxiliary uniform bound on powers of individual nilpotent
sections did not by itself provide the ideal-power vanishing needed here; the new
proof establishes ideal-sheaf nilpotence directly.

No source declaration or target signature was changed. Searches found the
Mathlib ring nilpotence theorem, which the new scheme proof uses, but no existing
scheme-level quotient theorem. LeanSearch returned Internal Server Error; those
searches are recorded as unavailable, not as absence of matching declarations.
The cited blueprint file is not present in this checkout; its subargument is
available in the original theorem's docstring and node. The new proof sketches
are agent-written, as recorded in proof_origin, following that cited subargument.

## New nodes

`def-sc-reduction-units-power-kernel`: the explicit kernel sheaf modulo a power of
the nilradical, in `ReductionUnitsPowerKernel.lean`; no sorry, no chosen filtration.

`lem-sc-reduction-nilradical-nilpotent`: the proved positive-power uniform
nilpotence theorem, in `ReductionNilradicalNilpotence.lean`.

`lem-sc-reduction-units-power-quotient`: the only new sorry, the single-step
quasi-coherent quotient theorem, in `ReductionUnitsPowerQuotient.lean`. Its zero
ideal, empty scheme and j=0 cases are included in its stated proof. The field
over dual numbers has a nonzero first kernel and zero next kernel, consistent
with its additive quotient, and creates no initial-identification contradiction.

There are no change records: all existing public signatures and definitions are
unchanged, and new module imports in the main module are private proof imports.

## Second reading by J1

1. I compared the delivered main module with the repository version. The theorem signature and all existing declarations are byte for byte unchanged; only proof imports, the private helper, and proof bodies changed. Verdict: pass.

2. I compiled all four delivered modules with `lcompile.py --all`. They compile without errors. The only remaining `sorry` is the named theorem `exists_reduction_units_power_quotient`; there are no axioms, unsafe declarations, hollow definitions, or unnamed holes. Verdict: pass, with one documented split theorem.

3. I checked the new statements against their definitions and edge cases. The power-kernel definition is constructive; the nilradical nilpotence theorem includes empty schemes; the quotient theorem is strictly smaller than the filtration target and has the stated proof source and DAG node. Repository and Mathlib searches found no duplicate declaration. Verdict: pass.

4. The proof follows the explicit kernel filtration, nilpotence, quotient, and topological-invariance route. The unused etale morphism import was removed and recorded above; the old false zero-filtration auxiliary statements were removed. Verdict: pass.

5. The Lean proof, DAG proof steps, dependencies, and unit metadata agree. No unit statement or realized step is bypassed. Verdict: pass.

I changed no statements or definitions. I only repaired the report and verified the delivered modules and DAG records.

Scratch-copy `#print axioms` checks passed: the explicit power-kernel definition
and nilpotence theorem use only `propext`, `Classical.choice`, and `Quot.sound`.
The filtration theorem and the quotient theorem additionally use `sorryAx`, as
expected from the one reported quotient hole. My fresh Loogle search
`"Units", "IsNilpotent"` found only a ring Krull-dimension result; a fresh `rg`
search of both library roots found no matching quotient-of-kernel-sheaves theorem.
