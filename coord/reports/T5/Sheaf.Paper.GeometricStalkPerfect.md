## What changed

Filled the four theorem bodies of `Sheaf.Paper.GeometricStalkPerfect`, preserving all
signatures and the construction `fieldGeometricStalkComplex`. The finite-coefficient
proofs transport bounded flat models through exact stalks, obtain finitely generated
cohomology from constructibility, and apply the local-ring perfectness criterion.
The common-stage proof extends the rational bounded model along the coefficient field
inclusion and uses the actual composition isomorphism for extension of scalars.

For the rational assertion, added `Sheaf.Paper.IntegralStalkRoosControl`, proving that
an integral stalk is bounded and derived complete from the sheaf completeness triangle
and the common reduction bounds. The proof verifies exactness, countable products,
constant scalar compatibility and levelwise nilpotence. Added the separate residue
comparison statement `Sheaf.Paper.IntegralStalkResidueFinite`. Its conclusion controls
only the uniformizer cone of an arbitrary integral stalk, with no completeness or
boundedness hypothesis. Combining it with the proved Roos control, derived-complete
Nakayama, completeness of the coefficient DVR and flat scalar extension proves the
rational assertion. This is a real reduction of the remaining comparison, not a
renaming of the rational theorem.

All three sandbox modules compile together through `lcompile.py --all`. The original
declaration signatures and the full field-stalk definition are unchanged.

## Proved and sorry left

Closed the original holes in:

- `AlgebraicGeometry.Scheme.finiteTorConstructible_proEtale_stalk_finiteFree`.
- `AlgebraicGeometry.Scheme.finiteTorConstructible_etale_stalk_finiteFree`.
- `WeilConjectures.commonStageConstructible_stalk_perfect` (from the rational theorem).
- `WeilConjectures.rationalConstructible_stalk_perfect` (reduced using the new residue
  comparison).

Also proved `WeilConjectures.integralStalk_roos_control` and all its private helpers.
The item module has zero remaining holes. Added one hole:
`WeilConjectures.integralStalk_residue_finite`, node
`lem-t5-integral-stalk-residue-finite`. Thus three original theorem bodies are proved
and the rational body is decomposed, with four holes closed and one added (net three).
The residue comparison proof was checked against the existing principal-reduction
API. That API assumes exact sections at a final object, so it cannot be instantiated
with arbitrary global sections on Y. Reusing it would require the strict-localization
slice comparison, or factoring out its coefficient/tensor exact-sequence calculation.
The remaining lemma is strictly smaller: it identifies finite cohomology of one
uniformizer cone, without constructing a perfect model or using derived completeness.

## No longer needed

The following original proof imports were removed:

- `Sheaf.Paper.DerivedComplete`.
- `Sheaf.Paper.IntegralDerivedReduction`.
- `Sheaf.AlgebraicGeometry.ProEtaleClassicalStalk`.
- `Mathlib.CategoryTheory.Sites.Abelian`.
- `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`.
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk`.
- `Sheaf.Paper.ProEtaleCanonicalTensorPullback`.
- `Sheaf.RingTheory.RlimPerfectComplete`.
- `Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact`.
- `Mathlib.RingTheory.AdicCompletion.Basic`.
- `Mathlib.RingTheory.Ideal.Quotient.PowTransition`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRings`.
- `Sheaf.AlgebraicGeometry.GeometricStalkToposPoint`.
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`.
- `Sheaf.CategoryTheory.DerivedCategory.FiniteTorAmplitudePerfect`.
- `Sheaf.Paper.DerivedCompleteOnSlices`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.Paper.SfRationalizationKaroubi`.

The finite-coefficient proof does not need the explicit ringed-topos tensor-pullback
construction, `lem-fix-geometric-stalk-topos-point`, or
`lem-pod-etale-stalk-tensor-scalar`: flat-model transport through the geometric point
supplies its Tor interval. The rational proof no longer needs
`lem-weil-pbc-rlim-perfect-complete`: derived completeness and finite residue
cohomology give finite cohomology directly. Removed the corresponding obsolete
maintainer tool-use entries for the
ringed-topos tensor comparison, etale tensor comparison, perfect-tower reconstruction
and direct constant-etale-stalk argument; the geometric-topos-point node was a direct
proof dependency rather than a tool-use entry. The constant pro-etale stalk, K-flat
change of rings, exact products and
coefficient DVR results remain needed through the new helpers or the intrinsic
stalk API. No library declaration or module was withdrawn; source-library declarations
remain intact. These are pruned direct dependencies, not claims that every such
module is unreachable from all other project targets.

## Where the brief, the DAG or earlier work was wrong

The old plan is mathematically usable, but its general derived ringed-topos and
perfect-tower reconstruction route is longer than the available flat-model and
complete-module APIs. The new node proof records the route actually used.
The point-sections comparison is specific to a final algebraically closed field
point; it cannot be applied directly to a geometric stalk over arbitrary Y.
Only its proved category-theoretic private lemmas are reused, and the missing
geometric-stalk residue comparison is stated separately with its own source and proof.

## New nodes

`lem-t5-integral-stalk-roos-control` realizes the integral reconstruction and common
bounds part of `fix-lem-finite-tor-perfect`. Its new module proves the theorem.
`lem-t5-integral-stalk-residue-finite` realizes the finite residue-reduction part;
its new module records the one remaining named theorem hole with a complete proof
in words. Whole-blueprint and Mathlib searches found no duplicate. Neither new
statement changes the unit route or any existing definition or target signature.
The proof elaboration commands are documented in
`coord/changes/t5-geometric-stalk-proof-elaboration.md`. No existing statement or
definition changes; instance attributes are scoped to each theorem command.

## Second reading by T5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
