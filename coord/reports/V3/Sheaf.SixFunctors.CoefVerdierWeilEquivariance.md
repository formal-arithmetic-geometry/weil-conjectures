## What changed

The original theorem is assembled from a one-scheme normalized Weil-duality result
(existential in the duality, see the reviewer correction below), a normalized
left-exchange result that also normalizes the target duality, and an exceptional-adjunction compatibility
result. The relative data and its exceptional-duality formula are chosen together with
the left exchanges from the normalized coefficient construction. The categorical
argument then retains these very underlying adjunctions.

The existing records were extracted into `Sheaf.SixFunctors.CoefVerdierWeilData` so
that separate lemmas can state their conclusions without importing their parent.
The original module publicly reexports them. Finite and common accessors cache the
actual functors, adjunctions and comparison endpoints. Every normalization is retained.
To avoid repeating the concrete coefficient types in generated projections,
`Coefficients`, `FrobeniusAdjunctions` and `Adjunctions` specialize generic record
containers. The scalar, stage and normalization predicates have cached endpoint
types; their equations are retained. `finiteMu`, `commonMu` and `scalarFrobenius` explicitly
name their pullback, tensor and scalar endpoints, with the same canonical comparisons as their bodies. The
finite functors use the definitionally equal raw category as their endpoint type;
all adjunction and coefficient comparison types refer to these named functors.
`fiberInclusion` caches the same finite-to-common inclusion with raw category
endpoints, preventing conversion from unfolding its stage-system implementation.
The left-only and exceptional records share the finite/common left-exchange
types and normalization predicates in the data module; the latter applies those
predicates to its left projections. `Adjunctions` explicitly supplies the categories, pullbacks, functors and adjunctions
to `ExceptionalComparison`, avoiding repeated inference through the original systems.
The private generic `pinByLeft` transports normalization along equations of the
left components before specializing to geometric adjunctions. The constructed
exceptional family also has named left-projection equations, so
the coefficient proof uses that API rather than unfolding the full mate construction.
The extraction change record gives the resulting definitions verbatim:
`coord/changes/coef-verdier-weil-data-extraction.md`.

`CoefWeilExceptionalCompatibility` contains a complete categorical calculation. Its
private `mate_scalar_square` transposes a right coefficient square, cancels the
invertible left comparison, and uses the original coefficient counit equation.
`exceptionalOfLeft` constructs the right mate with `IsoAlgebra.mateIso` and reuses
the proved original-unit and original-counit equations. A second helper applies
naturality to arbitrary Weil structures. The finite proof retains the shift instances returned by the existing coefficient
comparison, and the common-stage specialization uses the prescribed counit descent.
These give the exceptional result from the
strictly smaller geometric left-exchange assertion, at finite and common coefficients.
The new `CompatibleLeftExchanges` record takes cached exchange types and compatibility
predicates. The geometric specialization retains the same functors, actual
normalization predicates and every scalar/inclusion equation. Naming these endpoint
types prevents projections from re-elaborating a large family of category instances.

## Proved and sorry left

The original hole `WeilConjectures.coef_verdier_weil_equivariance` is closed by a real
assembly proof. This is a decomposition, not a net proof of the full mathematical
assertion: one original hole is closed and two separate holes are added.

The delivery's remaining holes are exactly:

- `WeilConjectures.coef_weil_normalized_duality`, node
  `lem-coef-weil-normalized-duality`: some duality on one scheme, with its internal-Hom and
  dualizing identifications, its actual
  evaluation and biduality, and the structure-morphism dualizing normalization.
- `WeilConjectures.CoefVerdierWeil.coef_weil_left_exchange_compatibility`, node
  `lem-coef-weil-left-exchange-compatibility`: a chosen normalized relative exceptional
  system and its left compact-support exchanges, with their finite-scalar and
  finite-to-common squares. It contains no right Frobenius exchange or Weil unit/counit equation.

`WeilConjectures.coef_weil_exceptional_compatibility` has a complete proof from the
left-exchange result and the existing Frobenius-equivalence theorem. All helpers are
proved; there is no sorry in a definition, private declaration, or partial proof.

## No longer needed

The main theorem uses the one-scheme normalization result,
the existential left-exchange construction and the proved mate assembly.
The old direct proof imports removed from it are:
`WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius`,
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`,
`Sheaf.Paper.IsomorphismDerivedPullback`,
`Sheaf.CategoryTheory.MateIsoAlongEquivalences`,
`Sheaf.SixFunctors.IntegralVerdier`,
`Sheaf.Paper.FiniteFreeCoefficientExtension`, `Sheaf.Paper.IntegralResidueTor`,
`Sheaf.SixFunctors.IntegralDualizing`, `Sheaf.Paper.SemilinearDerivedSections`,
`Sheaf.Paper.CompletedTensorHomTranspose`,
`Sheaf.Paper.IntegralDerivedOperationsOnSlices`,
`Sheaf.SixFunctors.CoefIntegralFiniteExtension`,
`Sheaf.Paper.IntegralOperationsScalarComparisons`, and
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.

The holed component modules have only the public data import: their planned proof
dependencies remain recorded in their nodes, and unused private proof imports were
removed (`GeometricFrobeniusInternalHomComparison`, `IsomorphismFieldTransport`,
`FrobeniusExchangeEquivalence`, and the upstream `WeilEquivariance`).

At the original node, `lem-fix-weil-operations` is no longer used: its live pairing
statement does not construct this package. Its upstream declaration remains untouched.

For completeness, the former direct dependencies are now accounted for as follows.
`thm-coef-qbar-verdier` supplies the underlying duality inside the two holed component
lemmas (it is no longer cited directly by the item). Its underlying
coefficient construction retains `thm-coef-rational-verdier`,
`lem-coef-rational-operations`, `thm-coef-integral-verdier`,
`lem-coef-finite-free-extension`, `lem-coef-integral-residue-tor`,
`prop-coef-integral-dualizing`, `lem-coef-integral-finite-extension`,
`lem-pur-integral-operations-scalar-extension`, and
`def-pur-integral-derived-operations` where needed below that interface.
The Frobenius subarguments retain isomorphism transport
(`lem-weil-proetale-isomorphism-inverse-image`,
`lem-weil-isomorphism-derived-pullback`, and `lem-coef-semilinear-derived-sections`),
canonical operations (`def-weil-derived-pullback-tensor-hom`,
`lem-pur-derived-pullback-tensor-iso`, and `def-weil-weil-sheaf-complex`),
inverse exchange (`lem-coef-frobenius-exchange-equivalence`), mates
(`def-weil-pbc-adjunction-mate` and `lem-weil-mate-iso-along-equivalences`),
`lem-coef-completed-tensor-hom-transpose`, and
`def-weil-algebraically-closed-coefficients`. These are not global pruning claims.

The normalized-duality node still needs the internal-Hom, dualizing-mate and transpose
parts of the original argument. The left-exchange node retains inverse-Frobenius
exchange, coefficient-square and common-stage descent. These dependencies are moved
to the appropriate subargument, not claimed globally unnecessary. The old unit route
has no statement or proof-step realization that is bypassed. No upstream declaration
or module is removed, and no module is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The return for reviewed head `4fd08121de8` reports a landing metadata error:
reviewer C-4fd08 answered FIX (not PASS), but `--apply-fixes` refused the report fix
named `Sheaf.SixFunctors.CoefVerdierWeilEquivariance.md`, so none of the reviewer's
corrected files landed. The stage-3 landing interface accepts a report fix named
`Sheaf.SixFunctors.CoefVerdierWeilEquivariance.report.md`; its repository destination
is `coord/reports/V3/Sheaf.SixFunctors.CoefVerdierWeilEquivariance.md`.
The re-delivery c479cde21817 resubmitted the unreviewed Lean and node files of
4fd08121de8 unchanged; the reviewer of c479cde21817 re-applied the earlier correction
(see `## Reviewer correction` below).

The retained attempt stopped on a compile-service disk-space failure, which has
cleared. This session repaired conversion costs by caching finite and common functor
endpoints, supplying explicit category arguments, and using generic containers whose
fields take cached types and predicates. Sharing the actual left-normalization
predicates removes the costly conversion between separately expanded realization
equations. The private construction, its projection equations, the categorical mate
calculation and both geometric counit helpers compiled. All five delivery modules and all six current downstream consumers compiled
cleanly with lcompile.py. The consumers required no adaptations; their temporary
unchanged copies were removed from the delivery sandbox after validation.
No launcher script was changed.

The live attachment of `lem-fix-weil-operations` is
`AlgebraicGeometry.Etale.isWeilPairing_mixedSupportCupProduct`. That pairing assertion
does not itself construct the actual finite/common coefficient duality records of
this item. The source-library boundary is respected: the declaration is untouched.

A draft left-exchange lemma was overgeneralized to every exceptional system A.
Its fields permit independent realization choices whose coefficient normalization
need not agree; the corrected statement chooses the system and its coherent
realizations together. The original target is existential in precisely these data.

The generic mate lifting already exists, proved, in the adopted source's
`IsoAlgebraAdjunction`; no new holed generic mate theorem is needed. The scalar right
square still needs the explicit counit calculation included here.

The current blueprint proof is read from `literature/blueprint/latest/`. Its direct
field-coefficient internal-Hom argument is the source of the normalized-duality
result; finite stable integral lattices are never assumed. A point with structure
multiplication by a uniformizer is permitted, and the contravariant structure uses
its inverse. Identity scalar extensions and empty schemes do not require exceptions.
The new left-exchange statement chooses the system and its realizations together.
It is tested without a Weil structure on its input;
its equations have matching functor endpoints, including identity field extensions.

## New nodes

`def-coef-verdier-weil-data` owns the extracted public records and wrappers. The
existing `def-pod-verdier-weil-conclusion` attachment moves to the defining data module.
The definitions and the Conclusion predicate retain their meanings. The definition
change reopens the statement review for targets using them under AGENTS.md §4.

`lem-coef-weil-normalized-duality` isolates the one-scheme internal-Hom and dualizing
argument of source proof paragraphs 1–3. It does not assert a relative exceptional
adjunction for arbitrary morphisms.

`lem-coef-weil-left-exchange-compatibility` isolates the left compact-support
exchange and its coefficient squares. The source is proof paragraphs 1 and 3,
with the actual whole-system exchange coefficient descent as a dependency.

`lem-coef-weil-exceptional-compatibility` records the now-proved mate and scalar
assembly from left exchange and the prescribed adjunctions. It adds no hole.

Change record: `coord/changes/coef-verdier-weil-data-extraction.md`.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer correction (stage-3 review of 4fd08121de80, re-applied at c479cde21817)

As delivered, `coef_weil_normalized_duality` asserted a normalized Weil structure for
every duality `B` with internal-Hom and dualizing identifications. The interface
`CoefQbarVerdier.Duality` fixes the finite biduality through
`IntegralVerdier.SignedSymmetry`, whose swap is pinned only on literal K-flat pairs.
The swap used by delta at (RHom(K, ω), K) is therefore free. Twisting it by a locally
constant sign u, for example (1, -1) on X = Spec(𝔽_{q²} ⊗ k), whose two points
geometric Frobenius exchanges, gives an admissible B with biduality u·δ. For that B the
biduality equation θ_K ≫ uδ_K = P(uδ_K) ≫ θ_DDK would force u = g^*u, so no W exists.
The same looseness was found at B6 RationalVerdier 06a6.

The reviewer therefore made the duality existential:
- `coef_weil_normalized_duality` is now `∃ B, hI ∧ hω ∧ ∃ W, DualizingNormalization B W`.
- `coef_weil_left_exchange_compatibility` additionally returns
  `∃ WY, DualizingNormalization BY WY` for the `BY` it chooses.

Each new statement follows from the delivered ones together with `coef_qbar_verdier`, so
nothing is strengthened. The item proof takes BX from the first lemma and WY from the
second. `thm-coef-qbar-verdier` left the item's proof_deps, and `def-coef-verdier-weil-data`
was added to them. The node statements, `lean.statement` and the proof_deps of both
component nodes were updated to match.

