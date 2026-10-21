## What changed

Completed `AlgebraicGeometry.ProEtale.det_brown_hypotheses_small` in
`lean/Sheaf/SixFunctors/BrownHypothesesSmall.lean`. Its signature, universe,
six coefficient alternatives, and every public import are unchanged.
There are no source-tree edits or interface/definition changes.

The proof follows the Brown unit's heart-and-ambient-Postnikov route:

1. Finite coefficients: use the normalized ordinary encoding and
   `FiniteDiscreteOrdinary.encoding_constructibility`. Prove that its ordinary
   stratified predicate equals `IsConstructible` over `ULift A`, explicitly
   enlarging/restricting cover indices between the two universes. Reuse the
   proved fixed-coefficient Serre helpers, supply zero, and apply
   `weakSerre_bounded_homology_thick`. Pull back along the triangulated termwise
   derived encoding.
2. Integral coefficients: use
   `isConstantModelConstructible_serre_padicIntegers`, construct the zero
   finite-presentation model, and apply the same weak-Serre theorem.
   Rational field coefficients use
   `constantModelBoundedConstructible_field_triangulated`.
3. Prove transport under the statement's actual ring-object isomorphisms.
   Restriction of scalars along an isomorphism is exact and reflects boundedness;
   its derived homology comparison and `constantModel_comap_iff` identify the
   two constructibility predicates. The normalized bottom-field comparison
   supplies the base `Q_l` and `Z_l` cases.
4. Reuse the fully proved generic private `stratifiedModelsSmall` from
   `CoefficientHeartSmall`: unlike that module's specialized public theorem,
   this helper allows every commutative condensed coefficient object. This is
   the same finite-presentation, covering, adjoint-embedding and subobject
   counting argument as the node's plan, with no new assumption or hole.
   Apply `bounded_homologyProperty_essentiallySmall`, whose proved Postnikov
   induction counts extensions in the ambient derived category.
5. Intersect with finite Tor amplitude using the well-definedness theorem's
   triangulation, repleteness and retract results. Essential smallness passes
   to this smaller property.

`CartesianCoefficients` remains imported as required by the unit-route gate.
The scope and synthesis-size options of the private helpers are local to those
helpers; the original public command layout is preserved.

The four `import all` directives expose already proved private proof helpers:
`stratifiedModelsSmall`, `constructible_iso`/`constantModel_comap_iff`,
`Scheme.CoefficientSerre`'s fixed-coefficient closure/encoding helpers, and
`Scheme.coefficientConstructible_of_isZero`. They are used only in theorem
proofs. No public signature or definition refers to a private declaration.
All seven new local helper theorems are private and completely proved.

Updated only `proof`, `proof_deps`, and `proof_origin` of
`det-brown-hypotheses-small.json` to describe this implementation. The
statement and the Brown unit's route remain unchanged. New proof imports
for normalized comparisons and the proved generic derived results replace
manual expansions of the same subarguments.

Validation: the final file compiled cleanly on the project compile server in
11.4 seconds, with no warnings. Delivery preflight will perform its independent
compilation and axiom checks.
Every added proof import passed `tools/import_direction.py may`; no cycle.
The main signature was compared verbatim with the shared source.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.det_brown_hypotheses_small`
(node `det-brown-hypotheses-small`).

Sorries left in the item: zero. Holes added anywhere: zero. Split-off
statements: zero. The local helpers `ordinary_constructible_iff`,
`bounded_retract_inverseImage`, `small_bounded_constant_models`,
`constant_heart_zero`, `thick_of_heart_closure`, `thick_coefficient_iso`,
and `finite_bounded_thick` have complete proofs.

As intended in stage 3, this proves the item from existing declarations,
including the separately assigned
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.encoding_constructibility`
(node `lem-sf-finite-discrete-encoding-constructibility`) and
`Profinite.base_coefficient_condensed_identification`
(node `lem-sfb-base-coefficient-condensed-identification`). Those existing
holes are not introduced, duplicated, or claimed closed by this delivery.

## No longer needed

The following 23 direct proof imports were removed:

- `Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`
- `Sheaf.AlgebraicGeometry.NoetherianStratumDetection`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `Sheaf.CategoryTheory.SheafTensorStructure`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.Paper.CoefficientHeartClosure`
- `Sheaf.Paper.CohomologyInWeakSerreSubcategory`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `Sheaf.Paper.FiniteDiscreteCoefficientEncoding`
- `Sheaf.Paper.FiniteDiscreteCondensedRing`
- `Sheaf.Paper.FiniteDiscreteConstructibleEncoding`
- `Sheaf.Paper.FiniteDiscreteRestrictionEncoding`
- `Sheaf.Paper.FiniteDiscreteSchemeRing`
- `Sheaf.Paper.FiniteRingConstructibleSheafOrigin`
- `Sheaf.Paper.InternalModuleAbEquivalence`
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`
- `WeilConjectures.AlgebraicGeometry.ConstructibleAffineFreePresentationGeneral`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `WeilConjectures.CategoryTheory.TruncationTriangle`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`

`CoefficientHeartSmall` and `IntegralConstantModelHeartClosure` remain
imports, now with `import all` to reuse their proved generic proof helpers.
Their public theorem statements are not replaced or weakened.

The following old direct DAG proof dependencies are no longer separately
invoked by the item's proof; their roles are now carried by the named
encoding, closure, smallness, or bounded-homology results above:

- `lem-weil-pbc-sheaf-tensor-closed` (`WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`)
- `lem-sf-module-object-ordinary-coefficient-equivalence` (`Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`)
- `def-weil-pbc-internal-abelian-sheaf-module-equivalence` (`Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`)
- `lem-weil-pbc-finite-discrete-coefficient-sections` (`Sheaf.Paper.FiniteDiscreteCoefficientSections`)
- `det-lem-coefficient-heart-closure` (`Sheaf.Paper.CoefficientHeartClosure`)
- `lem-sfb-locally-prescribed-modules-small` (`Sheaf.CategoryTheory.LocallyPrescribedModulesSmall`)
- `det-def-sfb-constructible-local-model` (`Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`)
- `lem-weil-proetale-weakly-etale-localization` (`Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`)
- `lem-sfb-joint-adjunction-model-embedding` (`Sheaf.CategoryTheory.JointAdjunctionModelEmbedding`)
- `sk-def-sfb-module-pushforward-pullback` (`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`)
- `lem-weil-pbc-noetherian-stratum-detection` (`Sheaf.AlgebraicGeometry.NoetherianStratumDetection`)
- `def-weil-sheaf-of-modules-category` (`Sheaf.CategoryTheory.RingedSiteModules`)
- `def-constructible-stratification` (`Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`)
- `lem-weil-pbc-truncation-triangle` (`WeilConjectures.CategoryTheory.TruncationTriangle`)
- `def-weil-abstract-derived-category` (`Mathlib.Algebra.Homology.DerivedCategory.Basic`)
- `lem-sfb-small-triangulated-extension-classes` (`WeilConjectures.CategoryTheory.Triangulated.ExtensionProductEssentiallySmall`)

In particular, `lem-sfb-locally-prescribed-modules-small` and
`lem-sfb-joint-adjunction-model-embedding` need no additional import or proof
here: the proved `CoefficientHeartSmall` helper already implements these
counting and embedding arguments. Likewise
`lem-sfb-small-triangulated-extension-classes` is not imported: the proved
bounded-homology theorem already performs the extension counting and
ambient Postnikov induction. The older affine-free-presentation/etale-origin
finite-coefficient route is not needed for smallness, which is uniform.

These are removals from this item's direct imports and dependency list.
Some modules remain used transitively by the reused library proofs or by
other parents; no module is withdrawn, no source declaration is removed,
and no global pruning count is claimed. Existing maintainer `tool_uses`
approvals are retained conservatively because their underlying generic
arguments may still be used transitively.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The original Lean docstring
still described thirteen expanded steps while the current DAG already
had a seven-step re-split; both are replaced by the actual shorter assembly.
The source-library and Mathlib search found existing proved smallness and
bounded-thickness implementations, so the recently split generic counting
lemmas need not be reproved here. The public coefficient-heart smallness
theorem is specialized to rational coefficients, but its private proved
`stratifiedModelsSmall` has precisely the uniform coefficient signature
needed by this item.

The finite-ordinary predicates use covers in different index universes;
they are not treated as definitionally identical. The proof explicitly
uses `ULift` and `restrictIndexOfSmall`, which also handles empty covers.
For derived functors the canonical shift instance must be preserved:
the finite encoding is written as the termwise derived functor of the
composite underived equivalence and its triangulated instance is supplied
with `inferInstanceAs`.

Edge cases checked in the argument: empty schemes and zero rings require
no nonemptiness or nonzero assumption; zero is constructed from a genuine
rank-zero presentation. No finite Tor bound is imposed on all constructible
finite-ring modules (which would fail, for example, over Z/4). Boundedness
and finite Tor amplitude remain separate intersected predicates. The
nilpotence hypothesis is retained verbatim although this structural proof
does not need it. The final smallness universe stays exactly `u + 1`.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
