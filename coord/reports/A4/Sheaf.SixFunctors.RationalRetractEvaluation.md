## What changed

Replaced the sorry in `WeilConjectures.coef_rational_retract_evaluation` with a complete
categorical assembly. Private proved helpers establish two-input transpose naturality,
the explicit inverse of an intertwining split restriction, both restricted adjoints,
canonical evaluation restriction, Verdier evaluation and bidual restriction, and preservation
of both adjoint isomorphisms under finite coefficient extension. Full Hom closure comes
from `coef_rational_operations` at the actual finite field, using its arbitrary FieldStage
interface. Every existing definition and theorem signature is unchanged.

Added four proof-only imports and four separate statement modules. Each new theorem has
its own source, proof in words and DAG node. These expose distinct missing normalized-map
interfaces rather than rename the assigned conclusion. Updated the parent proof route.
The unit route (canonical evaluation, split inverse calculations, scalar transport, and
local perfect-complex biduality) is retained. No definition repair or forced adaptation. The change record
`coord/changes/A4-rational-retract-private-proof-scope.md` documents two local
commands that the static interface scanner records, each scoped to one private helper.

Validation: the full item compiled without warnings in 14.2 seconds after import pruning.
The split statements were each compiled earlier. A subsequent dry run exposed slow
unfolding in statement elaboration; local irreducibility of the chosen normalized maps
was extended to all four new modules. The site-perfect statement then compiled in
19.9 seconds and the symmetry statement in 19.5 seconds (under one second of measured
elaboration and kernel checking). Local irreducibility of the chosen tensor,
Hom, closed structure and Hom comparison prevents elaboration from unfolding their
existence-and-uniqueness constructions; the scalar statement compiled in 6.1 seconds. No sorry remains in the item itself.

## Proved and sorry left

Closed: `WeilConjectures.coef_rational_retract_evaluation` (1 original hole).
Added: four holes, exactly one in each of:

- `WeilConjectures.rationalTensorSymmetry_laws`, node
  `lem-coef-rational-tensor-symmetry-laws`.
- `WeilConjectures.rationalHomScalar_transpose`, node
  `lem-coef-rational-hom-scalar-transpose`.
- `WeilConjectures.rationalVerdier_evaluation_adjoints`, node
  `lem-coef-rational-verdier-evaluation-adjoints`.
- `WeilConjectures.sitePerfect_rational_bidual`, node
  `lem-coef-site-perfect-rational-bidual`.

This is a decomposition, not a net hole reduction: 1 closed minus 4 added equals -3
before the ledger's full import-closure accounting. All private helpers are proved.
No sorry appears inside a definition. The remaining results separately assert symmetry
laws, comparison equations, or one bidual component's invertibility; none asserts the
original conjunction of retract, evaluation, Verdier, perfect-unit and extension clauses.

## No longer needed

Removed these direct proof imports from the assigned module:

- `Sheaf.Paper.RationalizationIdempotentComplete`.
- `Sheaf.Paper.IntegralOperationsScalarComparisons`.
- `Sheaf.SixFunctors.CoefIntegralFiniteExtension`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`.
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.Algebra.Homology.HomComplex`.
- `Sheaf.CategoryTheory.CoefficientBidualTriangles`.
- `Sheaf.CategoryTheory.ScalarLocalizationTriangulated`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `Sheaf.CategoryTheory.ScalarLocalization`.
- `Sheaf.Paper.SfIntegralConstructibleTriangulated`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`.
- `Mathlib.RingTheory.Localization.BaseChange`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `Sheaf.Paper.DerivedCompleteOnSlices`.
- `WeilConjectures.CategoryTheory.TruncationTriangle`.

The chosen splittings are hypotheses, so `lem-weil-rationalization-idempotent-complete`
and `Sheaf.Paper.RationalizationIdempotentComplete` are unnecessary for this argument.
There is no need to construct images, lift idempotents, or enlarge the raw category.
The old scalar-transpose node `lem-coef-rational-scalar-transpose-compatibility` is not
used: its interface fixes Verdier targets and literal coefficient inclusions, whereas
the assigned ScalarExtension predicate permits arbitrary W and algebra embeddings.
The new Hom scalar theorem records precisely the two equations needed for that interface.
The old approved direct tool use `lem-pur-integral-operations-scalar-extension` is
withdrawn from the parent; it remains an explicit dependency of the new scalar lemma.
The other old analytic/triangulated dependencies remain needed by the new site-perfect
bidual node, not by the parent's categorical calculation. Removing their direct imports
does not claim that these entire modules are pruned from the targets' closure.
All six original public imports are retained because the existing statements use their
category, operation, transpose and site-perfect definitions.

## Where the brief, the DAG or earlier work was wrong

The DAG's elementary transpose step concealed naturality in the internal-Hom variable
and compatibility with the specified signed symmetry. The completed transpose theorem
supplies the former after symmetry transport, while the normalized rational swap laws
need a separate interface. Verdier evaluation adjoints likewise require identifying the
recorded completed transpose with the integral-normalized Datum evaluation and bidual;
being isomorphic to some abstract Hom functor does not give these equations alone.
The existing scalar transpose statement does not cover the actual arbitrary-target,
arbitrary-embedding predicate in this module. The source's local site-perfect argument
also needs the actual global coefficient bidual map, rather than an arbitrary local
isomorphism. The four new nodes make these obligations explicit without weakening the
assigned statement. Edge checks: zero and identity splittings use the same explicit
inverse equations; the empty scheme and zero complex satisfy biduality; identity scalar
extension has the same normalized maps; shifts use the degree-r sign in double evaluation.

The session was repeatedly resumed after provider errors. The supplied .budget metadata
was left unchanged by the worker. The earlier retained start was 1792436020.222187;
on resumption it is 1792457345.076051, and the dry run now reports 46/120 minutes
instead of the many hours of earlier proof work. This is the reference-clock reset
mentioned in the brief; launcher metadata needs independent correction. No delivery was started before this packet's dry run.

## New nodes

`lem-coef-rational-tensor-symmetry-laws` identifies naturality and involutivity of the
specified rational swap by its integral/coherent normalization, including rational arrows.

`lem-coef-rational-hom-scalar-transpose` states transpose transport for a general target
and the scalar/symmetry square. It is independent of retracts and of perfectness.

`lem-coef-rational-verdier-evaluation-adjoints` identifies both recorded Verdier evaluation
transposes with the natural Hom identification and the recorded bidual component.

`lem-coef-site-perfect-rational-bidual` isolates the coefficient-unit second adjoint for a
site-perfect object, with the local signed model, finite-cover descent and annihilator
argument. It asserts neither retract closure nor scalar extension. The private proof-scope change record is
`coord/changes/A4-rational-retract-private-proof-scope.md`; no existing statement,
definition or public import changed.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
