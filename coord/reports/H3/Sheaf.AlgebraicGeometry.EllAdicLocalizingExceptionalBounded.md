## What changed

Repaired the return's duplicate: the boundedness module now privately imports
`Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructibleCohomology` and reuses
its `affine_restriction_boundedConstructible`. Removed the unlanded standalone duplicate
`Sheaf.AlgebraicGeometry.EllAdicAffineRestrictionBoundedConstructible` from the sandbox.
It is absent from main, so no landed module needs withdrawal.

Current main had meanwhile taken out the A4 cohomology delivery in be47c38950. Merely
changing the import would compile against stale retained outputs while leaving the source
dependency absent. This delivery therefore restores A4's seven source modules from the
returned base dd86fa917 at their original paths, including the unique affine restriction
helper in the cohomology module. These modules are unclaimed. A4 retains authorship of
its proofs; H3's repair restores and reuses them, rather than declaring the same fact twice.
The change record is `coord/changes/H3-reuse-affine-restriction.md`.

The supplied-adjoint boundedness proof takes common bounds on a finite affine cover and
uses exact pullback and open/closed zero detection to make them global. The canonical
adjoint case specializes this theorem to the given `IsLeftAdjoint` witness. No existing
public signature or target statement changes. All eight source modules compile through
lcompile.py after deleting stale sandbox outputs. Each file stays below 60 seconds. The unchanged direct consumer
`Sheaf.AlgebraicGeometry.EllAdicLocalizingExceptionalConstructible` also compiles against
this restored sandbox overlay. The exact `tools/import_prune_check.py` gate that
returned the earlier delivery passes for all eight delivered modules; no duplicate
declaration or identical-statement collision remains. The delivery dry run passes.

## Proved and sorry left

The item originally has one direct hole. Closed
`AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_canonical_rightAdjoint_obj_isBounded`.
Its supplied-adjoint theorem
`AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_rightAdjoint_obj_isBounded`
is also sorry-free, with its former circular reliance on the canonical case replaced.
The item has zero direct holes.

Restored A4's complete proof of
`AlgebraicGeometry.ProEtale.CondensedRing.ellAdic_localizing_rightAdjoint_obj_homology_constructible`,
closing the hole reintroduced by batch take-out in that unclaimed module.
Also restored its sorry-free affine restriction, affine compact-support representability,
closed-support representability, compact-support composition, affine projection
representability and closed-support projection duality proofs.

One named direct hole is added relative to current main:
`AlgebraicGeometry.ProEtale.CondensedRing.affineLine_compactSupport_isLeftAdjoint`, node
`lem-sfb-adic-affine-line-adjunction`, module
`Sheaf.AlgebraicGeometry.EllAdicAffineLineRepresentable`.
This is the geometric hole already isolated by A4, now restored with its proof plan.
It needs the ordinary condensed-module projective-line trace and diagonal calculation,
the two triangle identities, composition with the affine-chart open adjunction, and
bounded constructibility of the smooth pullback/twist/shift formula. Integral torsion
and finite-subextension algebraic-closure coefficients are retained. The larger affine
restriction hole from the returned H3 sandbox has been removed, not renamed.

Thus the delivery closes two current-main holes and restores one strictly lower geometric
hole: a decomposition with net one fewer direct hole. The item alone closes one of one
holes. No additional unfinished proof occurs in a definition or private helper.

## No longer needed

Removed the returned standalone duplicate module
`Sheaf.AlgebraicGeometry.EllAdicAffineRestrictionBoundedConstructible` and its import;
its node now records the single helper in the cohomology module. There is no second
copy of that declaration. Removed the item's old proof import
`Sheaf.AlgebraicGeometry.EllAdicLocalizingBrownRepresentability`; no second choice or
comparison of Brown adjoints is required for the finite-cover argument.

The old supplied/canonical circular proof dependency is removed. The supplied node uses
the affine restriction node, abelian closed support and profinite-point module pullback.
The canonical node uses only the supplied boundedness theorem.

The restored cohomology proof removes these old direct imports:

- `Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality`.
- `Sheaf.Paper.CondensedQbarLfpLocalTriviality`.
- `Sheaf.Paper.IntegralLfpLocalTorsionCharts`.
- `Sheaf.Paper.IntegralLfpLocallyFreeResolution`.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleLocalizingClosure`.
- `Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`.
- `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.

Some definitions remain available through needed imports. The closed-support calculation
still uses the field and integral Serre inputs; those are not globally pruned.
The old cohomology route's following nodes and modules are unnecessary to the written
proof, which uses generator detection directly:

- `det-def-sfb-constructible-local-model`: `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`.
- `lem-sfb-integral-lfp-constant-model-comparison`:
  `Sheaf.Paper.IntegralLfpConstantModelComparison`.
- `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`.
- `sk-def-sfb-bounded-constructible`: `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible`.
- `det-def-localizing-closure-ctf-equals-bc`: `Sheaf.Paper.LocalizingClosureCtfEqualsBc`.
- `sk-def-localizing-closure`: `Sheaf.Paper.LocalizingAdmissibleCoefficients`.
- `sk-prop-sf-existence`: `Sheaf.Paper.LocalizingExceptionalAdjoint`.
- `det-cor-existence-ii-restriction`: `Sheaf.Paper.ProperExceptionalRestriction`.
- `sk-thm-restriction`: `Sheaf.Paper.RationalExceptionalRestriction`.
- `det-prop-int-brown-adjoint`: `Sheaf.SixFunctors.IntegralBrownAdjoint`.
- `sk-thm-int-restriction`: `Sheaf.SixFunctors.IntegralExceptionalRestriction`.

Also unnecessary as direct cohomology proof dependencies are
`det-sp-unique-right-adjoint`, `def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`, and the old coefficient-predicate
comparisons. Their old top-level tool approvals are pruned, keeping finite-type
Noetherianity. In the boundedness node all old top-level tool approvals are removed;
its proof uses the actual affine helper and the two named sheaf tools instead.
Definitions required by unchanged statements remain statement dependencies.

The restored finite-coordinate induction makes `det-cor-affine-space-rational-induction`
and `Sheaf.Paper.AffineSpaceRationalInduction` unnecessary as a projection proof dependency.
The rational/integral affine-line trace calculation is still needed.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified a duplicated fact, not a need for a new name. The repaired
proof imports the original cohomology declaration and its node points there. Its duplicate
standalone source is not delivered.

The returned head contains the cohomology proof, while current main has rolled it back.
The retained .lbuild also contained old cohomology outputs. Those were deleted before
recompiling every delivered source, so validation does not rely on an unlanded ghost
module. Restoring the unclaimed source proofs and recording their consumers is necessary
to make the return's requested reuse concrete on current main.

The recorded rational and integral restriction-line modules belong to `newtargets-dag`
and their source files are absent here. The finite-ring small-etale smooth adjunction and
derived-complete reconstruction interfaces use different categories and do not discharge
the ordinary condensed-module affine-line statement. They are not substituted by adding
a completeness hypothesis. The remaining line theorem is strictly a part of the argument:
it covers only the one-dimensional projection, independently of supplied G, closed
support, finite-coordinate induction and the finite-cover globalization, all of which
have complete Lean proofs in the restored sources.

## New nodes

Seven previously taken-out A4 nodes are restored, with H3 delivery metadata and their
original statements and proof plans. A4 is credited for their proofs:

- `lem-sfb-adic-affine-restriction-bounded-constructible`: proved helper in the cohomology
  module, reused by boundedness; no standalone duplicate.
- `lem-sfb-adic-affine-compact-support-representable`: proved affine closed factorization
  and composition of natural Hom bijections.
- `lem-sfb-adic-closed-support-representable`: proved localization calculation, including
  integral torsion.
- `lem-sfb-adic-bounded-compact-support-composition`: proved refinement/exchange comparison
  for all three coefficients, without importing the exceptional parent.
- `lem-sfb-adic-affine-projection-representable`: proved finite empty/option induction from
  the affine-line adjunction, including dimension zero.
- `lem-sfb-adic-affine-projection-closed-support-duality`: proved compact-support comparison
  and naturality transport on closed supports.
- `lem-sfb-adic-affine-line-adjunction`: the sole remaining geometric proof obligation,
  described under Proved and sorry left.

Change record: `coord/changes/H3-reuse-affine-restriction.md`.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
