## What changed

Canonicalize `WeilConjectures.coefficientTwistPower` as an abbreviation of the
existing general-site tensor power. Its zero, one and successor equations agree
with the old recursive construction; the change record lists all consumers and
reopens semantic review of affected targets. Three equality proofs in the unclaimed
`IntegralLineReductionDefinitions` become reflexive. The returned delivery is repaired
by adding the forced `ScalarExtensionFunctor` consumer adaptation: its degree-one
`simpa only` now unfolds the canonical tensor power. No source-library declaration
or target signature changes.

Construct the normalized root and coefficient comparisons directly. The root
comparison uses finite-root site comparison. The coefficient ring lift uses
pullback/forget comparison and its unit normalization. The rational comparison
comes from the scalar-extension adjunction and the ordinary integral comparison.

Construct the finite coefficient comparison from the root comparison and scalar
extension, retaining its pure-tensor and Kummer normalizations. Extend every
degree-one comparison to signed powers and unbounded derived twists using the
normalized signed-line theorem and the common compatible-root cover.

The non-finite comparison uses the projection-normalized integral map, ordinary
scalar extension for rational coefficients, and a filtered-colimit isomorphism for
algebraic-closure coefficients. Field-extension naturality follows from uniqueness
of the coefficient extensions, the limit projections and the scalar-extension
quotient. For Qbar, prove the action identity at a common finite stage, then obtain
a module morphism whose underlying map is exactly the colimit comparison. This
characterization determines the morphism uniquely by faithfulness of forgetting;
no arbitrary module data are chosen. The proof uses the existence theorem directly.
General point-coefficient existence lemmas also construct the ordinary integral and
rational lifts, with their exact underlying-map and quotient equations. Eliminating
these existentials in the final proof avoids repeatedly unfolding concrete p-adic
module structures; it changes no public definition or statement.

Validation: all five packet modules compile through `lcompile.py --all` in this
repair session. The item takes 59.4 seconds as an importable compiled module and
51.3 seconds in the single-file check, with zero literal holes. Its unchanged retained version
reached the 60-second limit on this session's first checks. Command timing located
repeated expansion in the signed-comparison and scalar-extension interfaces.
The signed-comparison structure now locally treats its pullback and adjunction as
irreducible and respects transparency. Field-map normalization proofs respect their
existing irreducibility annotations, with the rational quotient proof retaining its
original settings. The integral twist is made locally irreducible before applying
the rational scalar-extension comparison. These changes only control elaboration;
all public statements, definition bodies and proof arguments are unchanged.
Temporary profiling modules and settings were removed. All 11 original public signatures and all public data
bodies were checked against the source and are unchanged. Fixed-universe private
category abbreviations, cached propositional instances and explicit normalization
APIs keep the Hom equivalences, tensor maps and ordinary comparison isomorphisms
abstract. Generic equality transport normalizes scalar extensions and module actions
before they are applied to the concrete p-adic objects. The
separate native-integral limit-preservation result is one new node. Diagnostic
sources are excluded from the delivery.

## Proved and sorry left

Four original holes have complete proof bodies:

- `AlgebraicGeometry.ProEtale.spRoots_cartesian`.
- `AlgebraicGeometry.ProEtale.spCoefficientIso_existsUnique`.
- `AlgebraicGeometry.ProEtale.spRationalComparison_existsUnique`.
- `AlgebraicGeometry.ProEtale.spFiniteTwists_cartesian`.

The fifth original hole, `AlgebraicGeometry.ProEtale.spTwists_cartesian`, has a
complete assembly from the separate native-integral result below. This is a
decomposition. The item module contains zero literal `sorry` bodies and its complete compiler
check passed. Declaration bodies closed: five; new hole: one.
The pinned sorry ledger determines the effect on the target closure.

The one new hole is:

- `AlgebraicGeometry.ProEtale.spIntegralTwist_inverseImage_isLimit`.

The tensor-power definition repair closes and adds zero holes. The following
20 existing holes in `Sheaf.Paper.CoefficientTwistsDetailed` are unchanged:

- `WeilConjectures.coefficientTwistLine_exact`.
- `WeilConjectures.integralComplexTwist_linear_statement`.
- `WeilConjectures.integralCoefficientTwist_constructible`.
- `WeilConjectures.integralComplexTwist_constructible`.
- `WeilConjectures.integralConstructibleComplexTwistFunctor_linear_statement`.
- `WeilConjectures.integralConstructibleComplexTwistFunctor_additive_statement`.
- `WeilConjectures.rationalComplexTwistFunctor_obj`.
- `WeilConjectures.rationalComplexTwistFunctor_map`.
- `WeilConjectures.twistScalarMaps_existsUnique`.
- `WeilConjectures.twistLineScalarIso_existsUnique`.
- `WeilConjectures.twistSheafScalarComparison_existsUnique`.
- `WeilConjectures.twistIntegralScalarComparison_existsUnique`.
- `WeilConjectures.twistRationalOrdinaryComparison_existsUnique`.
- `WeilConjectures.twistScalarMaps_identity`.
- `WeilConjectures.twistScalarMaps_composition`.
- `WeilConjectures.rationalTwistScalarComparison_unit`.
- `WeilConjectures.rationalCoefficientTwist_scalarExtension`.
- `WeilConjectures.coefficientTwistStageComparison_coherent`.
- `WeilConjectures.algebraicClosureComplexTwistFunctor_obj`.
- `WeilConjectures.algebraicClosureComplexTwistFunctor_map_exists`.

`Sheaf.Paper.IntegralLineReductionDefinitions` has zero holes before and after
its three proof adaptations. `Sheaf.SecSmoothPurity.ScalarExtensionFunctor` has zero
holes before and after its one forced proof adaptation. No hole is introduced into
any definition.


## No longer needed

The proof uses the normalized finite-root comparison, pullback/forget unit mates,
scalar-extension universal properties, and the signed-line base-change theorem.
It does not construct the generic adic-system or torsion-system interfaces from
the earlier plan. The main node's proof dependencies now follow these arguments.
No module is globally withdrawn: a dependency removed here can still be used by
another proof or by the new native-integral limit node.

Removed proof imports (including redundant imports supplied by statement imports):

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison`.

- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.

- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
- `Mathlib.AlgebraicGeometry.Scheme`.
- `Sheaf.RingTheory.IndEtaleUniverseTransport`.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`.
- `Sheaf.Paper.TateTwistLocallyFree`.
- `Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit`.
- `Sheaf.AlgebraicGeometry.ProEtaleCoefficientComparisonsPullback`.
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`.
- `Sheaf.Paper.PurInverseImageCompatibleFreeTower`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FiniteFreeDualPullback`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale`.
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Sheaf.RingTheory.IndEtaleStability`.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`.
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`.
- `WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`.

Original planned dependency nodes not used directly by this proof:

- `lem-pur-proetale-inverse-image-tensor-comparison`.

- `det-prop-sfb-qlbar-colimit-x-pullback`.

- `def-weil-pbc-ind-etale-algebra`.
- `lem-asd-affine-roots-representability`.
- `lem-pur-adic-line-system-base-change`.
- `lem-pur-site-representable-algebraic-pullback`.
- `lem-pur-torsion-line-system-base-change`.
- `lem-sbc-root-split-away-cover-etale`.
- `lem-weil-pbc-ind-etale-stability`.
- `lem-weil-pbc-morphism-into-affine-scheme`.
- `lem-weil-pbc-proetale-subcanonical`.
- `lem-weil-pbc-weakly-etale-composition-base-change`.
- `lem-weil-proetale-weakly-etale-localization`.
- `prop-weil-pbc-proetale-constant-ring-map`.

## Where the brief, the DAG or earlier work was wrong

The native integral levels are internal O_E-modules whose underlying abelian
sheaves are B_E,n tensor_Z mu_(ell^(n+1)). Their stated comparison with finite
balanced tensor lines only supplies individual isomorphisms, without equations
on generators or transitions. It cannot by itself supply compatible bases for
the adic-system interface. The native tower preservation result records this
specific missing bridge as a separate mathematical result.
The existing compatible-free-tower API also fixes coefficients one universe
above its small-site universe. The native pro-etale site and abelian coefficients
are both in universe u+1, so that interface needs a universe transport or a more
general universe convention before direct use here.

## New nodes

`lem-pur-native-integral-tate-tower-limit`, attached to
`AlgebraicGeometry.ProEtale.spIntegralTwist_inverseImage_isLimit`.
It isolates only preservation of the displayed native inverse-limit cone.
It says nothing about rational coefficients, finite-extension naturality,
filtered colimits, signed degrees, dual evaluation, or derived twists.

## Forced adaptations

`Sheaf.Paper.IntegralLineReductionDefinitions` was unclaimed. Compiling its original
proof against the tensor-power abbreviation fails at line 91 with
`maximum recursion depth has been reached`: its induction-hypothesis rewrite is
now reflexive. Replace the proof of `scalar_power_eq` by `rfl`, and the proofs of
`power_eq_coefficient` and `finitePower_eq_coefficient` by integer cases and `rfl`.
All three signatures, their visibility, and the module's definitions are unchanged.
The adapted module recompiles in 14.7 seconds in this repair session. The change record is
`coord/changes/P2-canonical-coefficient-tensor-powers.md`.


`Sheaf.SecSmoothPurity.ScalarExtensionFunctor` is unclaimed. Its byte-identical
original, copied from the current shared source, fails against the delivered
tensor-power abbreviation in 30.4 seconds at line 583:6:

```text
Type mismatch: After simplification, term d
```

The inferred isomorphism has right tensor functor
`(SheafOfModules.scalarTensorPower R L 1).siteSheafTensorRight`, but the expected
isomorphism has `SheafOfModules.siteSheafTensorRight L`. At lines 583-585, add only
`SheafOfModules.scalarTensorPower` to the existing `simpa only` list in
`scalarExtensionFunctor_line`. This reduces the degree-one tensor power to `L`.
All signatures, visibility, imports and public data definitions are unchanged.
The current source was compared with the retained packet; this module was missing
from returned head `78a5acd199b` and is now included. The adapted consumer compiles
in 36.0 seconds. The repair adds zero holes.
The earlier change-record row claiming this original consumer passed was wrong
and has been corrected in `coord/changes/P2-canonical-coefficient-tensor-powers.md`.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
