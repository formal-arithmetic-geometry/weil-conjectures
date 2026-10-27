## What changed

Proof work in `Sheaf.Paper.IntegralResidueProperFormulas` follows the finite-coefficient
route of the unit. The finite proper theorem is specialized to the first quotient;
the normalized exchange and projection rectangles supply reduction compatibility.
Private lemmas prove both cancellation arguments for arbitrary coefficient rings
before specializing to the first residue coefficients. Equalities of the actual
canonical maps identify the comparison interfaces with the statement interfaces.
Private coefficient data bundles the rings and their actual reduction map so equality
of the topology presentations transports all canonical maps together.

The private `finiteProperBaseChange_of_coefficientIso` helper in
`Sheaf.Paper.FiniteProperBaseChange` states its projection clause through the existing
`moduleObjectProjectionMap` API. It remains private. Its proof and the public finite
theorem's proof unfold that small wrapper. Public signatures, attributes and imports
are unchanged. The change record is
`coord/changes/G3-finite-private-projection-api.md`.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidueProperFormulas`
(blueprint `lem-sfb-integral-residue-proper-formulas`): 1 of 1 holes closed.
Remaining item holes: 0. Holes added: none. Split-off holes: 0. The new
`AlgebraicGeometry.ProEtale.CondensedRing.finiteCoefficientProperFormulas` adapter
is fully proved. All three submitted Lean files have zero `sorry` tokens.

All three modules compiled together through `lcompile.py --all`. Profiling settings
were removed. A compiled signature audit found no private constants in either
public theorem's type. The item's statement text and public imports match the
current source exactly. The delivery command performs the final compile and packet checks.

The finite helper was already proved. Its private API change closes no additional
hole. Its public consumers `Sheaf.Paper.FiniteProperLocalizing`,
`Sheaf.Paper.ProperOpenBoundaryZero`, and
`Sheaf.SixFunctors.ProperDirectImageCoefficientRestriction` compiled unchanged
against the modified helper module. Their temporary sandbox copies have been removed from the packet.

## No longer needed

No existing module is withdrawn. The proof uses equality of the recorded coefficient
data rather than a separate general coefficient-equivalence transport theorem.
All original public imports are retained. The finite theorem still needs its own
coefficient-encoding and coefficient-isomorphism machinery transitively; no global
pruning of those dependencies is claimed. The item no longer needs direct proof
imports of `FiniteProperExchange` or `RingedSiteModulesGrothendieckOfUniverses`:
the comparison-tools module uses them. The extra section-realization conclusions of
the quotient-exchange comparison are unused here, but their declarations and all
upstream dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

The topology-identification and discreteness lemmas are already proved privately in
`DerivedNakayamaResolution`; proof-only `import all` permits their reuse. The existing
finite coefficient-isomorphism helper can likewise be reused without changing its
visibility. Its private projection interface is normalized as explained above;
no public interface changes. The existing node's declaration
list still named three helper instances absent from the current item source; its
attachment list is reconciled to the unchanged public theorem.

The private transport procedure constructs heterogeneous congruence proofs, using
Lean's generated congruence lemmas, proof irrelevance and function extensionality.
It respects binder scope when caching equalities. Structure projections and the
ordinary arithmetic quotient indices are normalized before comparison. Every
resulting term is checked by the kernel; no transparency-respect or kernel-checking
option is disabled by this delivery. Explicit map equalities avoid repeated conversion through the
large derived-functor constructions. The finite theorem applications first transport
their arrow propositions explicitly, avoiding an expensive implicit comparison of
the concrete coefficient instances. The scalar wrapper `D` is explicitly unfolded
only when transporting the final assertion to the common coefficient-data form.

## New nodes

`lem-sfb-finite-coefficient-proper-formulas` records the fully proved unbundled
adapter in `Sheaf.Paper.FiniteCoefficientProperFormulaTools`. It bundles the schemes
and inputs for the existing finite theorem and identifies its canonical exchange
and projection maps. Private comparison and coefficient-congruence tools share this
module so the concrete item need not recompile them. Its public signature uses the
canonical structures, outside the scope of the private proof caches. This adds no
new hole. The existing finite helper's change record is
`coord/changes/G3-finite-private-projection-api.md`.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
