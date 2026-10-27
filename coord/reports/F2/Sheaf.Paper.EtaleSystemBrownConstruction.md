## What changed

Replaced the body of `AlgebraicGeometry.etaleSystemBrownConstruction` by a Lean
assembly of coefficient arithmetic, the existing compact-support construction,
componentwise Grothendieck/derived properties, coproduct preservation, and Brown
representability. Both original structure declarations and the theorem signature
are byte-for-byte unchanged. The nonzero nonunit parameter is not replaced by a
uniformizer, and no separatedness assumption on X or Y over the field is added.

Added `Padic.nonunit_coefficient_stages`, with a complete proof: a nonzero nonunit
generates a positive power of the maximal ideal, finite residue gives finite
quotients, l in the maximal ideal gives prime-power torsion, quotient representatives
give surjectivity, and the positive power defines the same complete adic topology.

Added explicit proper/open singleton insertions, their proved conjugacy equations,
the actual proper singleton mate, a proof that its evaluations above n are maps
between zero objects, a construction upgrading below-level invertibility by joint
detection, and the explicit composite compact-support left-extension isomorphism.

The complete item assembly and its new geometric helpers compile without warnings.
The remaining geometric realization/projection argument is isolated in
`etaleBrownGeometricComparisons`. It is the source's separate Lemma 5.13 / Lemma 5.16
comparison argument, without the coefficient arithmetic, categorical Grothendieck
assertions, coproduct preservation, linear Brown adjunction, shifts or exactness.
The retained comparison equations identify the actual published compactScalarMap;
no unspecified replacement comparison is used.

Narrowed public imports of the two existing construction/scalar modules
to `StrictEtaleSystemInterfaces`; their declarations and proof bodies are unchanged.
Change record: `coord/changes/F2-etale-brown-construction-imports.md`.
The existing direct consumer `EtaleTowerBrownAdjunction` compiles with these imports
(46.2 seconds). Full packet compilation is recorded by the delivery tool.

## Proved and sorry left

Original item: one hole, in `AlgebraicGeometry.etaleSystemBrownConstruction`.
Its body has been replaced by a complete proof from existing declarations and the
separate geometric comparison lemma. The new arithmetic theorem
`Padic.nonunit_coefficient_stages` is proved, with no sorry.

Also proved:

- `AlgebraicGeometry.strictEtaleBrownProperInsertion_conjugate`.
- `AlgebraicGeometry.strictEtaleBrownOpenInsertion_conjugate`.
- `AlgebraicGeometry.strictEtaleBrownProperInsertionMap_above`.
- `AlgebraicGeometry.strictEtaleBrownEvaluation_detectsIso`.

One new hole remains:
`AlgebraicGeometry.etaleBrownGeometricComparisons`, node
`lem-pur-etale-brown-geometric-comparisons`. This is a decomposition (one original
hole closed, one new hole added), not a net one-hole proof. Its full source proof
is in the docstring and its node. Below n it remains to transport the normalized
proper projection and paste its scalar/singleton transpose equations; above n and
the joint-detection/composite assembly are implemented. No sorry occurs inside any
definition or private helper.

The two adapted modules retain their existing, unmodified holes:
`AlgebraicGeometry.etaleCompactSupport_construction`
(`lem-pur-etale-compact-support-construction`),
`AlgebraicGeometry.etaleCompactSupport_scalarAction`
(`lem-pur-etale-compact-support-scalar-action`). They are existing dependencies, not
newly added holes.

## No longer needed

Removed these direct proof imports from the item:

- `Mathlib.Algebra.Homology.DerivedCategory.Linear`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`.
- `Sheaf.CategoryTheory.KInjectiveTotalDerivedLinear`.
- `Sheaf.CategoryTheory.LinearRightAdjoint`.
- `Sheaf.CategoryTheory.SystemSingleDerivedEvaluation`.
- `Sheaf.NumberTheory.Padics.AdicLimitFiniteModules`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Sheaf.NumberTheory.Padics.LocalFieldCoefficientStages`.
- Plain `import Sheaf.Paper.CoefficientSystemDerivedComparison` (the needed private
  helper import `import all` is retained).
- `Sheaf.Paper.SemilinearDerivedSections`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`.

The scalar transfer for the right adjoint is a direct Hom-transpose calculation;
the generic linear-right-adjoint theorem is unnecessary. Exactness is transferred
from exact inverse-image models through adjunction, avoiding a separate K-injective
triangulated proof. Arithmetic uses finite_quotient_pow and equality of adic
topologies, so the local-field coefficient-stage theorem is unnecessary on this
route. The proper coproduct step transports the published finite-coefficient theorem through
the normalized realization equivalences, avoiding the unfinished etale coefficient
wrapper `lem-pur-etale-coefficient-proper-coproducts`.

The following old direct proof dependencies are removed from this node (some remain
transitive dependencies of the stated interfaces, arithmetic or geometric lemma;
this delivery does not claim they are globally unused):

- `def-weil-pbc-adjunction-mate`.
- `lem-coef-semilinear-derived-sections`.
- `lem-pc-right-derived-functor-triangulated`.
- `lem-pod-adic-limit-finite-modules`.
- `lem-pur-etale-system-coefficient-projection`.
- `lem-pur-local-field-coefficient-stages`.
- `lem-pur-system-level-left-extension`.
- `lem-pur-system-single-derived-evaluation`.
- `lem-sbc-linear-right-adjoint`.
- `lem-weil-kinjective-total-derived-linear`.
- `lem-weil-l-adic-extension-integers-dvr`.
- `lem-weil-linear-abelian-derived-category`.
- `lem-weil-pbc-conjugate-iso-unit-equation`.
- `lem-weil-pbc-exact-functor-derived-factorization`.
- `lem-weil-pbc-kinjective-total-derived`.
- `lem-weil-pbc-mate-pasting`.

Removed the obsolete direct tool_uses entries for:

- `lem-coef-semilinear-derived-sections`.
- `lem-pod-adic-limit-finite-modules`.
- `lem-pur-local-field-coefficient-stages`.
- `lem-sbc-linear-right-adjoint`.
- `lem-weil-l-adic-extension-integers-dvr`.
- `lem-weil-pbc-kinjective-total-derived`.

In `EtaleCompactSupportConstruction` and `EtaleCompactSupportScalarAction`, the public import of
`EtaleCoefficientSystemAdjoint` is replaced by the definition owner
`StrictEtaleSystemInterfaces`. No Lean module is withdrawn. No declaration under
`WeilConjectures` is deleted or changed. The unit's route is retained.

## Where the brief, the DAG or earlier work was wrong

The planned generic lemmas do not directly expose the specialized normalized
constant-coefficient realization needed by this item's large conclusion record.
In particular, evaluation of derived morphisms is not assumed faithful: all
insertions are defined by adjunction before evaluation, and evaluation is used
only for joint detection of invertibility. The new comparison lemma isolates the
missing normalization glue rather than asserting faithfulness.

The older tower Brown result has stronger base-separatedness and uniformizer
hypotheses, so it cannot simply be applied here. Its private categorical arguments
were adapted in the item; its theorem is not imported. The old rework row's
quarantine reason does not authorize deleting this item, which is present in the
current source. No quarantine file is removed.

Edge cases checked: t a positive uniformizer power is covered; t a unit and t=0 are
excluded only by the original hypotheses. Zero coefficient quotients and identity
coefficient transitions are allowed by the geometric statement. The empty coproduct
is included. Above the singleton level both evaluated objects are zero; no
boundedness or flatness of quotient maps is introduced.

## New nodes

`lem-pur-nonunit-coefficient-stages`: the fully proved arithmetic clause for any
nonzero nonunit parameter. It is independent of schemes and of Brown adjunctions.

`lem-pur-etale-brown-geometric-comparisons`: normalized constant-coefficient
realization, coefficient projection and the below-level singleton comparison. Its
module constructs all insertion maps and proves their conjugacy equations, above-level
invertibility, joint-detection upgrade and composite left extension. The remaining
source result is the normalization of the below-level projection maps.

Change record: `coord/changes/F2-etale-brown-construction-imports.md`.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
