## What changed

Wrote the complete assembly proof of
`AlgebraicGeometry.ProEtale.CondensedRing.integralProperDirectImageAndFormulas`
with its signature and all seven public imports unchanged. Its first clause follows from
internal direct-image limits, the internal residue criterion, and the existing
`proper_integralModel_bounded` proof. Its second clause uses first-reduction Nakayama.
For both proper formulas, proved completeness of the endpoints and applied the
first-reduction isomorphism criterion.

The new private helper `integral_pull_complete` handles arbitrary base-changed schemes:
restrict to affine charts, apply bounded constructible pullback and the qcqs completeness
proof, and use the strict completion unit and covering conservativity to descend completeness.
It does not impose new finiteness assumptions on the base-changed schemes. The projection
endpoints use the existing integral tensor-closure statement.

Isolated exactly the finite-coefficient subargument in source paragraph (3) as the public
`integralResidueProperFormulas` in its own module and node. It assumes only Dctf first
reductions, and neither asserts integral completeness nor concludes the integral formulas.
The main theorem combines it with the independently proved completeness and Nakayama steps.
The remaining proof work is assembling the normalized coefficient-presentation transport
with the quotient comparison equations and the finite theorem. Scratch checks compiled the
integral monoid equality (`integralPointMon_eq`), the finite-topology identification using
`DerivedNakayama.quotientDiscrete`, the sheafified-constant/continuous coefficient isomorphism
using `FiniteDiscreteOrdinary.pointRingConstants`, cancellation of the exchange rectangle, exact scalar equivalence via its right adjoint,
and invertibility of scalar/geometric mates along coefficient isomorphisms.
A later scratch check also compiled equality of the complete bundled quotient arrows,
using equality of both topologies; it preserves scalar actions and actual quotient maps.
A full assembly draft was tested. Its latest finite coefficient-isomorphism helper is
present in the source checkout but not yet recognized by the compile server's green
library. The draft also needs final endpoint and canonical-arrow transport checks; later
diagnostics isolated the projection comparison's distinct monoidal instance presentations
and the remaining definitional equalities as elaboration work, not hypotheses that
may be omitted. A minimal probe then proved the equality of `moduleObjectProjectionMap`
and the evaluated `actualProjection` by unfolding the functor wrappers, in 5.1 seconds.
The bundled exchange/reduction transports still need efficient kernel checking.
These scratch examples are excluded from the delivery. The new statement module imports
only what its signature uses; its planned proof dependencies are recorded in its node.

Repaired an existing import collision between the Sheaf extraction `FiniteIndexSplitting`
and the adopted source `Adic.UnitMatrix`. Renamed only the extracted declarations' namespace
to `FiniteIndexSplitting` and changed the qualified reference in the public abbreviation of
`ContinuousFieldMatrixElimination`. Both constructions expand to the same equivalence.
The adopted source tree is untouched. Change record:
`coord/changes/finite-index-splitting-namespace.md`.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.integralProperDirectImageAndFormulas`
(node `det-thm-sfb-proper-base-change-integral`). The item module contains zero sorry.
The current main proof, including both private completeness helpers and all four clauses,
compiled in its profiling copy in 33.7 seconds. The complete four-file packet then
compiled with `lcompile.py --all`, exit code 0: finite-index extraction 0.0 seconds,
residue statement 53.3 seconds, adapted matrix consumer 0.0 seconds, and the item
93.5 seconds in that server run (including server overhead). Final packet validation is performed by
deliver3.py. The first five delivery invocations ended with `DELIVERY BUSY` and exit code 75,
without compiling the packet or pushing it. Further invocations retry that transient
capacity limit.

Added one hole:
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidueProperFormulas`
(node `lem-sfb-integral-residue-proper-formulas`). This is a decomposition, not a net
hole closure: one upper hole closed and one strictly smaller finite-reduction step added.
The retained theorem has a complete source proof in its docstring and DAG node. The
finite-ring statement was checked on empty schemes, zero complexes and integral complexes
with zero first reduction but without completeness. The ambient comparison equations apply
to these cases without any completeness hypothesis.

The namespace-repair modules retain their complete proofs and add zero holes.

## No longer needed

Removed these direct private imports from the item:

- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `Sheaf.AlgebraicGeometry.IntegralConstantCompletion`
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.BasicOperationsCoefficientReduction`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.DerivedNakayamaResolution`
- `Sheaf.Paper.FiniteProperBaseChange`
- `Sheaf.Paper.IntegralCriterionReductions`
- `Sheaf.Paper.IntegralModels`
- `Sheaf.Paper.ProjectionFormulaBaseChangeNaturality`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`

The new residue statement also omits unused proof imports of
`Sheaf.Paper.FiniteProperBaseChange`, `Sheaf.Paper.IntegralQuotientExchangeComparison` and
`Sheaf.Paper.IntegralQuotientProjectionComparison`; their planned uses remain in its node.

The corresponding original planned dependencies are no longer direct steps of the parent
proof (some remain needed transitively by the reused finiteness proof or residue lemma):

- `def-weil-l-adic-coefficient-extension`
- `lem-weil-l-adic-extension-integers-dvr`
- `lem-weil-pbc-standard-quotients-perfect`
- `det-prop-sfb-qlbar-colimit-x-integral-limit`
- `sk-prop-sfb-cartesian-coefficients`
- `sk-lem-integral-models`
- `det-prop-integral-criterion-constant-coefficients`
- `det-prop-integral-criterion-reductions`
- `prop-weil-pbc-direct-image-limits`
- `lem-sfb-integral-quotient-direct-image-comparison`
- `det-thm-sfb-proper-base-change-finite`
- `sk-thm-pe-constructible-comparison`
- `lem-weil-pbc-proper-fp-permanence`
- `lem-sfb-integral-quotient-exchange-comparison`
- `lem-sfb-integral-quotient-projection-comparison`
- `lem-sf-direct-image-tor-amplitude-noetherian`

The unit's finite-to-integral route remains: the residue lemma uses
`det-thm-sfb-proper-base-change-finite` and the two quotient comparison nodes. No source
library declarations or modules are withdrawn. No entire library module is claimed pruned;
only direct proof dependencies and imports are reduced. The remaining residue lemma
is needed by both canonical-formula clauses, so it is retained and not listed as
a pruned module.

## Where the brief, the DAG or earlier work was wrong

The original DAG endpoint-completeness step said that the base-changed schemes are standing
schemes by permanence. The theorem quantifies over arbitrary X-prime and Y-prime. Properness
of p-prime cannot make an arbitrary Y-prime finite type over k. The proof now uses affine
cover descent for completeness, while internal direct-image limits applies to any morphism.
The target statement is preserved.

The two quotient-comparison modules use `IntegralQuotient.integral` and
`IntegralQuotient.finite`, whereas the item uses `DerivedNakayama.integerRing` and
`DerivedNakayama.quotientRing`. These presentations are not definitionally equal. The private `integralPointMon_eq`
proof in `IntegralCriterionReductions` supplies equality of the integral monoid objects, using
equality of the norm topologies. The finite proper theorem also uses a sheafified constant ring rather than the continuous ring.
The new residue lemma explicitly retains these coefficient identifications and the actual
canonical-map equalities; it does not silently identify their endpoints or scalar actions.

The earlier extraction of finite-index splitting left duplicate public declaration names
in the adopted source and the extracted Sheaf module. Combining the imports produced an
actual compiler error. The namespace repair preserves the source-library boundary and the
expanded definitions. The downstream declaration search found one qualified reference needing
adaptation; the other reported matches use an unchanged abbreviation or independent private
definitions. Both modified modules are unclaimed in the local claim snapshot.

## New nodes

`lem-sfb-integral-residue-proper-formulas` records the finite-reduction part of paragraph (3)
of the integral proof, before completeness and Nakayama. It is strictly smaller than the
item: only reduced arrows are proved invertible, for inputs constrained only by their
finite reductions; neither direct-image constructibility nor integral invertibility nor
completeness is included. The item node now records the actual completeness and Nakayama
assembly and the new dependency. The finite-index-splitting node records the namespace
repair and its complete citer audit; see
`coord/changes/finite-index-splitting-namespace.md`.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
