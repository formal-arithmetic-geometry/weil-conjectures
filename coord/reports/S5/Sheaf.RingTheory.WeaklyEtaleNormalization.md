## What changed

Replaced the hole in `weaklyEtale_normalization_tensor` by a proof using the generic
algebra `Frac(C) ⊗[C] D`. Flatness makes the images of nonzero elements regular;
absolute flatness makes every regular element of the generic algebra a unit. This
identifies that algebra with the total ring of fractions. Applied the proved
weakly-etale integral-closedness theorem to the tensor normalization, then used
uniqueness of integral closures to construct the canonical comparison. Checked the
specified fraction-clearing equation in the tensor normalization before applying the
equivalence; this avoids expanding the nested fraction and tensor maps during elaboration.

For the minimal-prime factor, used the existing total-fraction decomposition,
passed through the residue fields to `Frac(D/P)`, identified the integral closure
over the diagonal ring `D` with the product of the component normalizations, and
selected the requested coordinate. The complement is an actual product ring,
including the empty product. All helpers are private proved theorems; no definition
or statement signature changes, no axioms and no new public declarations.

Validation after the returned delivery: reapplied the private helpers and complete proof
to the latest shared module, preserving its theorem signature and public imports verbatim.
The dependency `ReducedNoetherianTotalRingFractions` is now imported from its current
`WeilConjectures.RingTheory` location; the retired `Sheaf` twin is not imported.
The initial repaired file compiled through `lcompile.py` with exit code 0 and no warnings
in 24.8 seconds. Later checks exposed slow typeclass inference. Profiling identified
repeated reconstruction of tensor-ring algebra structures; caching the existing
structures locally and obtaining reducedness explicitly from the absolute-flatness
equivalence avoids that search. The revised proof compiles with no warnings in
20.5 seconds (20.3 seconds when compiled under its actual module name). A separate
`#print axioms weaklyEtale_normalization_tensor` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`; the diagnostic full axiom probe also passes.
No limits are raised, and all these structures are the original
inferred structures, with no definition or public-interface changes.

Change record: `coord/changes/S5-weakly-etale-normalization-local-instance.md`.
The local instance command is scoped to this file and exports no attribute.
The public signature and public imports match the current source verbatim;
the direct consumer requires no adaptation.
The unchanged direct consumer `Sheaf.RingTheory.WeaklyEtaleLocalComponentDimension`
compiles against this proof from the diagnostic sandbox overlay in 16.0 seconds,
with exit code 0 and no warnings.

## Proved and sorry left

Closes `weaklyEtale_normalization_tensor`
(`lem-exc-weakly-etale-normalization-tensor`), the sole original hole.
No textual `sorry` remains and no hole is added. No result is split off.
The complete proof compiles. Closed 1 original hole; added 0 holes; split off 0 results.

## No longer needed

The finite-etale-subalgebra argument and
`lem-sc-finite-etale-algebra-criterion` are unnecessary: the already-proved
absolutely-flat element equation gives the inverse of a regular element directly.
The finite-product integral-closure theorem `integralClosure_finite_pi` is not
imported: it treats a product of base rings, whereas this proof needs the diagonal
base ring `D`.

Removed proof imports:

- `Sheaf.RingTheory.WeaklyEtaleField`: the proof uses the proved absolute-flatness
  API in `WeilConjectures.RingTheory.ProEtale.WeakDimension` directly. Its node
  `lem-weil-pbc-weak-etale-field` and its obsolete `tool_uses` approval are removed
  from this node's proof dependencies.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: no finite-etale criterion
  is used; `lem-sc-finite-etale-algebra-criterion` is removed from proof dependencies.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`: the ring localization API suffices;
  `def-weil-pbc-module-localization` is removed from proof dependencies.

Also removed redundant proof imports `Mathlib.RingTheory.RingHom.Flat` and
`Mathlib.RingTheory.Etale.Weakly`: the flatness and weak-etale APIs used here are
already public imports of `WeilConjectures.RingTheory.ProEtale.WeakDimension`.
Removed `Sheaf.RingTheory.IndEtaleUniverseTransport`: no universe-transport
construction is used; the statement's `Algebra.WeaklyEtale` comes from the
preserved public import `Sheaf.RingTheory.IndPrincipalZariski`.

All public imports and statement dependencies are preserved. No claim is made that
these nodes disappear from the entire targets' closure; other parents may need them.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found in the statement or the original ten-step plan.
The plan can be shortened at Step 3 using the existing proved source API.
At Step 9 transitivity of integrality through the quotient maps supplies the
lifted annihilating polynomials without an explicit coefficient-lifting routine.
No unit or chapter route changes.

The retained attempt had temporary profiling options and an expensive denominator check
through two tensor products. Removed the profiling options and proved the denominator
equation in the tensor normalization itself, then transported it along the equivalence.
No limits were raised and no definitions or signatures changed.

The landing return identified a concurrent change to the item after base `061d3b229`.
This repair starts from the current shared file and uses the upstream total-fraction
module installed by that change, rather than restoring the retired import from
returned delivery `b7bb5a09c8`. No source-library file is edited.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
