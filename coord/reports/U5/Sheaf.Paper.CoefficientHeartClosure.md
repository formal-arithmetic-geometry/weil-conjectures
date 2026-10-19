## What changed

Proved `AlgebraicGeometry.ProEtale.coefficientHeart_closure` in
`Sheaf.Paper.CoefficientHeartClosure`, preserving its complete signature and all six
public imports. Added proved private helpers for local free/constant models, property
closure classes, the abelian full subcategory and exact inclusion, and constructibility
of zero and isomorphic objects. The conditional closure helper is fully proved for any
coefficient ring satisfying the stated local-freeness criterion.

The shorter route reuses the existing, proved private API of
`Sheaf.AlgebraicGeometry.CondensedConstructibleSerre` with `import all`:
`finite_lf`, `algcl_lf`, `lfp_serre_of_locally_free`,
`condensed_constructible_serre_of_locally_free`, and `freeEpiLocalSplitting`, together
with their coefficient-isomorphism transport lemmas. These are genuine local results
and generic conditional glue, rather than a new renamed copy of the item. The proof
identifies lisse and locally finitely presented modules, then identifies the finite
constant-model predicate with the existing stratified local-presentation predicate.
Mathlib supplies the abelian full-subcategory and exact-inclusion constructions.

Updated the existing DAG node's proof, proof dependencies and proof origin to this
route, and removed obsolete top-level tool approvals. No definitions, public
statements, consumer modules or target statements changed. No new nodes or holes.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.coefficientHeart_closure`
(node `det-lem-coefficient-heart-closure`). One hole closed, zero holes added,
zero holes left in the delivered module; no decomposition.
The imported library's remaining proof obligations are unchanged.

## No longer needed

Removed these 25 direct proof imports (their transitive availability, when another
retained dependency requires them, is not claimed as global pruning):

- `Mathlib.CategoryTheory.Sites.EpiMono`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`
- `WeilConjectures.CategoryTheory.ModuleObjects.Abelian`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Sheaf.CategoryTheory.SheafTensor`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility`
- `Sheaf.AlgebraicGeometry.CondensedFieldContinuousRealization`
- `Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback`
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs`
- `Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized`
- `Sheaf.Paper.EtaleLocalMonodromyRealization`
- `Sheaf.RepresentationTheory.ContinuousCoefficientSubquotients`
- `Sheaf.Paper.CoefficientFiniteDescentLisse`
- `Sheaf.Paper.CondensedFlatCoefficientCalculus`
- `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`
- `WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`
- `WeilConjectures.CategoryTheory.ModuleObjects.MapMod`
- `Mathlib.CategoryTheory.Monoidal.Mod`
- `Sheaf.Paper.CompletedCondensedCoefficients`
- `Sheaf.CategoryTheory.Monoidal.ModuleEqualizerInternalHom`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `Sheaf.Paper.CartesianCoefficients`

The old node no longer directly uses these proof dependencies:

- `lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`
- `sk-prop-sfb-cartesian-coefficients`
- `lem-sfb-modobj-cokernels`
- `lem-weil-pbc-site-sheaves-enough-injectives`
- `sk-def-sfb-sheaf-tensor`
- `def-sfb-subfield-coefficient-ring`
- `lem-weil-pbc-condensed-field-continuous-realization`
- `def-weil-pbc-lisse-lattice-coefficients`
- `lem-sfb-etale-local-monodromy-realization`
- `lem-sfb-continuous-representation-subquotients`
- `det-lem-coefficient-finite-descent-lisse`
- `lem-weil-pbc-condensed-flat-coefficient-calculus`
- `sk-def-sfb-change-of-scalars`
- `sk-prop-sfb-qlbar-colimit-x`
- `def-sfb-modobj-internal-hom`
- `lem-weil-pbc-ring-sheaves-grothendieck`
- `det-lem-coefficient-heart-common-stratification`
- `lem-sfb-modobj-abelian`

The common-stratification module stays publicly imported because it reexports the lisse
predicate used in the theorem's signature. The finite local-model module stays publicly
imported and its local-finite-presentation lemma is used. The new proof needs no
monodromy realization, representation-subquotient construction, finite-stage descent of
an actual lisse morphism, flat coefficient calculus, completed coefficient comparison,
or internal-Hom duality. Existing generic Serre glue already proves local closure by
finite presentations and basis lifts and globalization by intersections of strata.
The original unit's closure, local extension splitting, common-stratification
argument and finite-stratification characterization are all retained.

Withdrew the six obsolete top-level `tool_uses` approvals:
`lem-weil-pbc-condensed-field-continuous-realization`,
`def-weil-pbc-lisse-lattice-coefficients`,
`det-lem-coefficient-finite-descent-lisse`,
`lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective`,
`sk-prop-sfb-cartesian-coefficients`, and
`lem-weil-pbc-condensed-flat-coefficient-calculus`.

## Where the brief, the DAG or earlier work was wrong

The old detailed node plan required rebuilding coefficient-specific closure through
monodromy, lisse finite descent and duality. Existing local-triviality results and the
proved conditional helpers in CondensedConstructibleSerre give a shorter route.
The theorem statement and the unit-level mathematical assertions need no repair.
The retained attempt was unfinished: two private helpers omitted the scheme binder,
and the abelian-subcategory exactness proof needed an explicit binary-biproduct
instance. The resumed session also fixes the zero-object proof by explicitly applying the
stratum and cover pullback functors, and pins the lisse predicate when constructing
its closure classes. The theorem docstring now describes the implemented shorter route.
The theorem signature was compared textually with the current repository and is identical.
The earlier concrete coefficient alias caused expensive definitional comparisons in the
final stratification clause. The conditional closure argument now works with an abstract
coefficient ring, and the public theorem applies it directly before specializing its
local-freeness hypothesis. The geometric stratification conversion is stated for an
arbitrary predicate on immersions, keeping pullback constructions out of that conversion.
No underlying definition or public interface changed. Removed the retained attempt's
global `open ZeroObject`; the zero witness now comes directly from `HasZeroObject.zero`
inside the proof. This keeps all existing public commands identical and resolves the
earlier preflight complaint without an interface change. The resumed delivery passed `deliver3.py --no-push` against current sources on
2026-10-19: compilation and preflight both passed (review class CODEX for the node
update). Its sole theorem signature is textually identical to the current repository,
and the file has no `sorry` or lines over 100 characters. The node differs only in
`proof`, `proof_deps`, `proof_origin` and removal of obsolete `tool_uses` entries.
No Lean repair was needed after this final resume; the retained completed proof is
the delivery, rather than a rebase of an already delivered repair.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
