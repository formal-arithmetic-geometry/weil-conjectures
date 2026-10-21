## What changed

Restored the quarantined item from the current rework archive and proved
`AlgebraicGeometry.Scheme.isIso_classicalProEtaleExchange_of_isProper` without changing its
signature or the definition of `classicalProEtaleExchange`.

The proof restricts to constant scalar sections, descends K along the classical comparison
counit, reflects local torsion to the etale origin, and applies the existing arbitrary-ring
etale proper-base-change theorem. The existing qcqs etale/pro-etale exchange comparison then
transfers invertibility. The final source comparison and the exchange isomorphism establish
both endpoint boundedness and classicality. All four sandbox modules compile with no warnings
through lcompile.py --all.

`ProEtaleConstantDerivedEncoding` proves the exact scalar-restriction API, including its
cohomology comparison, reflection of lower bounds, equivalence of classicality predicates,
and invariance under isomorphisms. `ComparisonReflectsTorsion` proves torsion descent using
actual pro-etale geometric germs and the already proved comparison-stalk theorem.
`ProEtaleConstantExchangeEncoding` states the remaining independent coefficient-encoding
compatibility result, with a full proof in words. It retains the actual ambient selector;
it does not substitute the different chosen constant-ring compositor.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.isIso_classicalProEtaleExchange_of_isProper`
(node `sk-thm-properbasechange`). The item itself has zero sorries.

Added one hole:
`AlgebraicGeometry.Scheme.proEtaleConstantExchange_encoding`
(node `lem-pe-constant-exchange-encoding`). This is a decomposition: one upper hole closed,
one separate lower hole added, net zero. It asserts functoriality of the specified exchange
under constant-module encoding for all complexes and all squares, without properness,
classicality, boundedness or torsion. It neither assumes nor restates proper base change.
The unfinished calculation is the compatibility of the normalized ringed pullback square
with the fixed-scalar pullback square under the derived coefficient equivalences. The
remaining unit/square/counit calculation is described in its docstring and node.

New proved declarations:

- `AlgebraicGeometry.ProEtale.comparisonUpperStar_reflects_local_torsion`.
- `AlgebraicGeometry.Scheme.proEtaleModuleRestriction_additive`.
- `AlgebraicGeometry.Scheme.proEtaleModuleRestriction_equivalence`.
- `AlgebraicGeometry.Scheme.proEtaleDerivedModuleRestrictionHomologyIso`.
- `AlgebraicGeometry.Scheme.proEtaleDerivedModuleRestriction_isGE_iff`.
- `AlgebraicGeometry.Scheme.proEtaleDerivedModuleRestriction_classical_iff`.
- `AlgebraicGeometry.Scheme.proEtaleFixedClassical_iso_iff`.

Their modules have zero sorries. No new axiom or definition hole is present. The existing
comparison theorem and classical-equivalence dependencies are used as declared, whether
or not their own proofs are finished.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `Sheaf.AlgebraicGeometry.TorsionEtaleSheaf`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Sheaf.AlgebraicGeometry.TorsionAssembly`.
- `WeilConjectures.CategoryTheory.TruncationTriangle`.
- `WeilConjectures.SixFunctors.BaseChange.DerivedComparison`.
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`.
- `WeilConjectures.CategoryTheory.RightDerivedFunctorTruncationIso`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact`.
- `Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`.
- `Sheaf.CategoryTheory.ThreeStepAdjunctionComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison`.
- `Sheaf.Paper.CondensedAmbientExchange`.

The etale truncation/forget-coefficients induction is already supplied by
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`; it is not duplicated in this
proof. Its projective-line, proper-reduction and torsion-assembly unit route remains below
the reused theorem. These imports may remain transitively needed there; no source module
or declaration is withdrawn.

The item no longer directly needs the planned kernel-colimit proof of torsion reflection:
`lem-weil-pbc-left-adjoint-preserves-colimits` and
`lem-weil-pbc-module-sheaves-colimits-forgetful`. Its corresponding tool-use entry for the
latter is removed. Torsion descent instead uses
`lem-cbc-proetale-comparison-stalk` and the conservative etale geometric points.
The direct truncation dependencies are replaced in this node by
`thm-weil-pbc-bounded-below`: `lem-weil-pbc-truncation-cohomology`,
`lem-weil-pbc-derived-plus-iso-on-cohomology`, `lem-weil-pbc-truncation-triangle`,
`lem-weil-pbc-derived-exchange-triangulated`, `lem-sf-triangle-two-out-of-three`,
`def-weil-pbc-derived-inverse-image`, `lem-weil-pbc-derived-direct-image-triangulated`,
`lem-weil-pbc-abelian-etale-sheaves-grothendieck`, `lem-weil-pbc-direct-image-left-exact`,
`def-weil-pbc-direct-image`, `lem-weil-pbc-derived-functor-truncation-iso`,
`prop-weil-pbc-inverse-image-exact`, and `lem-weil-pbc-exchange-forget-coefficients`.
The two direct triangulation tool-use entries are removed. None of these nodes is claimed
unnecessary to the full library: the source proper theorem retains its proof.

No module is withdrawn and no deleted.txt is submitted.

## Where the brief, the DAG or earlier work was wrong

The assigned source is quarantined, not withdrawn. Its rework attachment and dependencies
are retained through restoration and explicit route updates. The old nine-step plan
rebuilds an arbitrary-ring bounded-below etale result that the adopted source library
already proves. The current source also supplies the qcqs transport equation for arbitrary
commutative rings, despite the historical FiniteCoefficient directory names.

The source classicality predicates use two different derived localization models. Their
comparison must be explicit; definitional identification would miss ShrinkHoms. The new
proved encoding API handles this by the localization universal property.

There is a genuine additional coefficient-presentation comparison: the ringed ambient
exchange is not definitionally the fixed-scalar exchange. In particular, the previous
review explicitly rejected replacing the published ambient compositor by another choice.
The new split preserves that distinction and records exactly the missing normalization
calculation. The input and output statements were checked on the zero ring, zero complex,
empty schemes, identity squares, negative lower bounds, and unbounded local torsion orders;
none introduces finiteness or a uniform annihilator. No statement is disputed.

## New nodes

`lem-pe-constant-derived-encoding` attaches the proved exact restriction API to
`ProEtaleConstantDerivedEncoding`; the original constant-module equivalence is reused.

`lem-pe-comparison-reflects-local-torsion` attaches the proved sheaf-level torsion descent
to `ComparisonReflectsTorsion`. It is independent of properness and derived base change.

`lem-pe-constant-exchange-encoding` attaches the one remaining coefficient-encoding mate
comparison to `ProEtaleConstantExchangeEncoding`. Its source is the module/pro-etale
comparison passages and Stacks 07A7, 093I, 03CY and 0D6D. Its proof is complete in words;
the Lean proof remains sorry. This is an independent functoriality result about the
specified maps, not a renamed instance of the target.

No definition or existing statement was changed, so no change record is required.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
