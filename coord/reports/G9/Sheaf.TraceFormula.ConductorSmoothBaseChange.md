## What changed

Filled `AlgebraicGeometry.conductor_smooth_base_change` in
`Sheaf.TraceFormula.ConductorSmoothBaseChange`. The two public definitions, every
public signature, and all public imports are unchanged. All added helpers are private
and completely proved; no other Lean module is modified.

The argument obtains finite normalization and its dense normal open from
`reduced_algebraic_normalization_field_change`. Finite pushforward and kernel/cokernel
coherence give the two coherence assertions. The scheme-theoretic-support theorem
identifies the existing `ofIdeals` definition with its affine annihilator family.
On affine opens, exactness of the quasi-coherent cokernel identifies its vanishing
with normalization being an isomorphism. This proves the support and normality
claims without needing the stronger extracted stalk quotient theorem.

For smooth base change, specialize `normalizedBlowup_calculus` to the unit ideal.
Its smooth clause supplies the absolute normalization cartesian square. The existing
canonical affine structure-sheaf base-change isomorphism respects the unit maps:
the private proof checks this through the adjunction and the equality of the ring
maps around the square. Preservation of cokernels supplies the cokernel comparison.
Affine pullback sections, finite generation, and finite flat annihilator base change
then give the ideal equality on an affine covering. Identity and composition use the
existing ideal-sheaf functoriality API.

Added only private proof imports for these calculations, including the ULift field
instance, the coherence/finite-type equivalence, affine cokernel exactness, canonical
structure base change, pullback sections, finite affine sections, and ideal-sheaf restriction. The normalization imports already expose
schematic dominance and ideal-sheaf functoriality. Removed an unused private support helper.
Updated the item's DAG proof, proof dependencies, and proof origin to match this route.
For the returned delivery at head `750f346f440`, removed the unnecessary
`set_option warn.sorry false` command. The source ledger had treated the `sorry`
component of the option name on line 42 as an unattributed hole. No proof term
changes were required by this repair.
The static preflight classifies the extra proof-elaboration commands as a visible
change. `coord/changes/conductor-smooth-base-change.md` documents these commands;
no statement or definition changes. All new imports pass the
project import-cycle check. A text comparison confirms that both public definition
bodies, the theorem signature, and all public imports are unchanged.

The field instance is supplied explicitly for `ULift ℚ`. The affine covering argument
also covers the empty scheme and empty pullback; for a normal scheme the ideal is the
unit ideal. No nonemptiness, integrality of S, or extra hypothesis on h is introduced.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.conductor_smooth_base_change`
(node `lem-trf-conductor-smooth-base-change`).

The item contains zero remaining `sorry` proofs. Added zero holes and split off zero
statements. All private helpers are proved. The imported existing statements
`normalizedBlowup_calculus` and
`Module.annihilator_tensorProduct_flat_base_change` remain dependencies; this delivery
does not claim to close their existing holes.

## No longer needed

Removed the private import `Sheaf.RingTheory.AnnihilatorLocalizationAway`:
`lem-weil-pbc-annihilator-localization-finite` is unnecessary as a direct proof
dependency, since ideal-sheaf extensionality glues the equalities and the existing
support theorem already supplies the compatible affine annihilator family.

Also removed duplicate private imports already supplied by public imports:
`Mathlib.AlgebraicGeometry.Properties`,
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
`Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree`,
`Mathlib.AlgebraicGeometry.IdealSheaf.Basic`, and
`Sheaf.AlgebraicGeometry.ReducedNormalization`.
The private `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` import is also redundant
because the unchanged public ideal-sheaf module already imports it.
Removed `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`, already publicly
imported by `Sheaf.AlgebraicGeometry.ReducedNormalization`. Also omitted redundant
new imports of schematic dominance and ideal-sheaf functoriality; the retained
normalization imports already expose those APIs.

The latest DAG plan's `lem-trf-finite-normalization-quotient-local-criterion` and
`lem-trf-smooth-normalization-quotient-comparison` are not needed by this proof.
Their required portions are proved directly in the private affine cokernel and
cartesian cokernel-comparison arguments from existing library declarations. No
module or node is withdrawn: these nodes may have other parents. No unit-level
statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The first delivery preflight required a change record for the altered command
list; the record is included. The landing return for `750f346f440` additionally
reported `<unattributed:42:1892>`. Inspection located that exact token in the
file-level warning option, outside every declaration. Removing the unnecessary
command repairs the packet: the source ledger now finds 14 declarations, zero
hole rows, zero scanner warnings, and no missing-gate failures. The repaired
module compiled successfully through `lcompile.py` in 9.8 seconds, with exit code
0 and no compiler diagnostics. Both public
definition bodies, the public theorem signature and all public imports remain
verbatim. No consumer adaptations are needed.

The latest shared node cites two recently extracted quotient nodes with no Lean
attachments. They cannot simply be imported. The available normalization,
quasi-coherent cokernel, canonical structure base-change and pullback APIs suffice
for the portions needed here, so no new statement is necessary.

No false statement or definition defect was found. In particular `ofIdeals` is not
assumed to reproduce an arbitrary family: the proof first constructs the compatible
support ideal and uses `ofIdeals_ideal` on that actual ideal family.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
