## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.exists_open_geometricallyIrreducible_finiteCover_linearSystem`
with the Lean assembly of irreducible Bertini. Its signature and all existing public imports
are byte-for-byte unchanged. No source-library file, existing definition, or other module
was changed.

The proof constructs the tensor-pulled-back linear system, proves its scalar identity, applies
`exists_open_geometricallyIrreducible_linearSystemMember`, identifies the basis-coordinate
member and its zero scheme through the self-field base change, and transports through
`IdealSheafData.comapIso`. Only Bertini on T is needed: the finite etale map has nonempty clopen
image in connected X, hence is surjective; geometric irreducibility then descends from T_v to
H_v by the already proved source `GeometricallyIrreducible.of_surjective`. Finite etale base
change, smooth composition, and geometric irreducibility give the remaining conclusions.

Added and proved `BertiniFiniteCoverBaseCodimension`. Generation away from S puts the generic
point of any base component above a closed point of S. The finite-type-domain dimension
formula and flat locally-quasi-finite preservation of coheight show that its codimension is
exactly d. This statement works over any field, for any etale map, and does not need vanishing
on S, connectedness or finiteness of T, or d >= 2. The caller supplies d >= 2.

Added `BertiniFiniteCoverTransverseComponent` for the genuinely separate independent-cotangent
and height-two-component argument in paragraph 3 of the source. It concludes only Bertini's
codimension-two witness; it asserts nothing about any general member or parameter open.
Its statement does not assume sections vanish on S, nor that S is nonempty. The full local
and globalization argument remains in its docstring and node.

## Proved and sorry left

Closed the one assigned syntactic hole:
`AlgebraicGeometry.exists_open_geometricallyIrreducible_finiteCover_linearSystem`
(node `lem-zl-bertini-finite-cover-irreducible-system`). Its proof is complete from the named
inputs.

Proved the new theorem `AlgebraicGeometry.bertini_finiteCover_base_codimension`
(node `lem-zl-bertini-finite-cover-base-codimension`), with zero holes. All private comparison,
nonvanishing, and dimension helpers are fully proved.

Added one hole, the whole proof of
`AlgebraicGeometry.bertini_finiteCover_transverse_component`
(node `lem-zl-bertini-finite-cover-transverse-component`). No other sorry remains in the
packet. This is a decomposition, not an unconditional proof or a net hole reduction:
one upper hole closed, one strictly smaller geometric input added, net zero.

Validation: all three modules compile without errors or warnings. The delivery reached
server preflight, which accepted the Lean and node checks but required a change record for
the added namespace/attribute commands. That record is included and the check is rerunning.

## No longer needed

The assigned module no longer imports these proof dependencies directly:

- `Mathlib.Algebra.MvPolynomial.Basic`
- `Mathlib.AlgebraicGeometry.Artinian`
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Mathlib.AlgebraicGeometry.Noetherian`
- `Mathlib.AlgebraicGeometry.Properties`
- `Mathlib.CategoryTheory.MorphismProperty.Comma`
- `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`
- `Mathlib.RingTheory.LocalRing.Module`
- `Mathlib.RingTheory.Localization.AtPrime.Basic`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`
- `Mathlib.Topology.Connected.Basic`
- `Mathlib.Topology.Sets.Closeds`
- `Sheaf.AlgebraicGeometry.ClosedPointField`
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`
- `Sheaf.AlgebraicGeometry.GeometricIrreducibilityFiniteSeparableTest`
- `Sheaf.AlgebraicGeometry.IsRegularScheme`
- `Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`
- `Sheaf.AlgebraicGeometry.RationalUnramifiedCotangentCriterion`
- `WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre`
- `WeilConjectures.AlgebraicGeometry.Picard.ZeroScheme`
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`
- `WeilConjectures.RingTheory.Etale.LocalDimension`
- `WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRingLocalization`
- `WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence`

The finite-separable test node `lem-zl-geometric-irreducibility-finite-separable-test`
(`Sheaf.AlgebraicGeometry.GeometricIrreducibilityFiniteSeparableTest`) is unnecessary for
this route: connectedness over the separably closed field and smoothness give geometric
irreducibility by already proved source APIs.

The node `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`
(`Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`) is unnecessary here. Etale
smoothness is inferred directly, and the base proof never passes through Artinian fibres.
Its obsolete top-level tool-use entry was removed from the item node.

The node `lem-weil-pbc-finite-type-dim-zero-artinian` is not needed: the base proof uses the
generic point and preserved coheight instead of proving that the upstairs base support is a
finite set of closed points. The separate transverse argument needs only that a finite
morphism has finite fibres, and etale fibres are discrete. Fibres over closed points are
closed, so their individual points are closed as well.

The parameter-space nodes `lem-weil-pbc-polynomial-ring-domain` and
`lem-zl-spectrum-irreducible-nilradical-prime` are no longer needed by this proof: surjective
descent makes the second Bertini open and the intersection argument unnecessary. The
statement's polynomial coefficient space remains unchanged.

The removed chart, cotangent, regular-sequence, closed-point, and localization imports
are still mathematical dependencies of the new transverse-component node; they are
not claimed globally pruned. The finite-type-domain dimension theorem remains a dependency
of the proved base-codimension node. The unit's own statement and route are retained.
No declaration is removed from `WeilConjectures/`.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or definition repair. The existing fifteen-step plan was stronger
than necessary in three places: it tested geometric irreducibility by field extensions,
proved finiteness of the base support upstairs, and applied Bertini twice. The proved
source geometric-connectedness, coheight, and surjective-image APIs avoid these detours.
The hard source argument choosing two independent section coefficients and globalizing
their height-two prime is a separate needed result, not an already stated consequence of
the cotangent or regular-sequence declarations alone.

Edge cases reviewed: d = 2 gives a zero-dimensional transverse component; positive
characteristic is unchanged; a kernel of psi causes no issue because the parameter domain
and basis stay V; no reducedness of the scheme-theoretic base locus is used. The new base
lemma also permits empty S, empty T, and d = 0 or 1, with its exact-codimension conclusion.
The transverse lemma remains true for empty S; r < 3 is incompatible with the assumed
immersion of the nonempty open of dimension at least two. No target signature changed.

## New nodes

`lem-zl-bertini-finite-cover-base-codimension`: the proved exact-codimension statement for
base components under etale pullback. Its node records the generic-point proof and its
actual source APIs. Module: `Sheaf.AlgebraicGeometry.BertiniFiniteCoverBaseCodimension`.

`lem-zl-bertini-finite-cover-transverse-component`: paragraph 3's section-selection,
regular-parameter, height-two, and global-component argument, isolated as condition (3)
of Stacks Tag 0G4F. Module:
`Sheaf.AlgebraicGeometry.BertiniFiniteCoverTransverseComponent`.

Both nodes have self-contained statements, source places, complete proof plans, actual
three-kind searches, and exact Lean attachments. Blueprint searches for codimension two,
base locus, and 0G4F found no existing blueprint statement with either conclusion; the
existing irreducible-member and independent-functions nodes assume the witness instead.
Change record: `coord/changes/M5-bertini-finite-cover-proof-scope.md`. Preflight requires
it for the added scope commands; it records that signatures and public imports are unchanged.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
