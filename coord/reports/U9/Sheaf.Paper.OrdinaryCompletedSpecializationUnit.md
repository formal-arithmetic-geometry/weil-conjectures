## What changed

Replaced the hole in
`WeilConjectures.IntegralOnSlice.ordinaryCompletedSpecializationUnit`
by the actual unit calculation, preserving its signature verbatim. The coefficient
adjunct is invertible by the closed-immersion case of `qcqsOrdinaryRestrictionExact`.
The independent-universe abelian specialization calculation gives the abelian unit
bijection. The proved ringed-site transfer then gives bijectivity of the specified
`ordinaryAdjunction` unit.

Added two proved modules:
`Sheaf.AlgebraicGeometry.ProEtaleAbelianSpecializationOfUniverses` and
`Sheaf.AlgebraicGeometry.ProEtaleModuleUnitFromAbelianOfUniverses`.
The first generalizes the existing affine-coordinate, closed-counit,
finite-coproduct/sheafification, affine-basis and localization proofs. The second
reindexes actual ring, abelian and module adjunctions to coefficient-sized small
models and retains their unit equations through the scalar-action comparison.
The underlying schemes stay in universe `t`; all section groups and Yoneda tests
use `max u (t+1)`.

The categorical comparison is first proved for arbitrary ring sheaves, keeping
completed coefficient definitions out of its definitional-equality calculations.
Profiling identified these transports and the ring-to-set comparison as expensive.
After that improvement, the combined module still exceeded the delivery time
limit, so the proved comparison was moved into its own module. The item now
contains the completed-coefficient application. No time limit was raised and no
transparency option was disabled. Both original public imports are preserved.
No existing signature, definition, attribute or public import is changed.

## Proved and sorry left

Closed the original one hole:
`WeilConjectures.IntegralOnSlice.ordinaryCompletedSpecializationUnit`
(node `lem-fix-ordinary-completed-specialization-unit`).

Both new declarations are proved:
`AlgebraicGeometry.Scheme.proEtale_abelian_unit_bijective_of_specialization`
(node `lem-u9-proetale-abelian-specialization-universes`) and
`AlgebraicGeometry.Scheme.proEtale_module_unit_bijective_of_abelian`
(node `lem-u9-proetale-module-unit-from-abelian-universes`).
Every private helper is proved. No holes are added; no `sorry` remains in any of
the three delivered modules. Imported theorems retain their existing obligations.

Validation: the final `lcompile.py --all` compiled all three modules without warnings,
in 45.3 s (abelian specialization), 40.0 s (module transfer) and 59.2 s (item).

## No longer needed

No original Lean import is removed. No existing module or declaration is withdrawn.
The item no longer directly performs the affine closed-site geometry: that argument
is proved in the new abelian module, which still uses
`lem-weil-pbc-affine-closed-site-functor-properties`. Thus this dependency remains
needed transitively and is not claimed as a pruned module.

The wrapper `lem-weil-pbc-module-inverse-image-unit-comparison`
(`Sheaf.CategoryTheory.ModuleInverseImageUnitComparison`) is unnecessary for this
proof. The underlying proved theorem
`SheafOfModules.inverseImage_underlying_of_ring_presentation`
(`lem-weil-pbc-module-inverse-image-action-adjunction`) supplies both the comparison
and its precise unit equation. The transfer node records that dependency and
`lem-weil-pbc-sheaf-pullback-forget-comparison`.

The fixed-universe specialization modules
`ProEtaleSpecializationAffineCoordinates`, `ProEtaleSpecializationCounit`,
`ProEtaleSpecializationUnitComparison`, `ProEtaleSpecializationRestrictionSections`,
and `ProEtaleModuleSpecializationUnit` are not imported by this proof. Their
geometric and categorical arguments are retained and generalized in the new
proved module; their existing declarations remain untouched.

## Where the brief, the DAG or earlier work was wrong

The stated module-unit comparison uses small sites and coefficients in the same
universe. The existing specialization theorem uses coefficients of universe
`t+1`. Neither can simply be applied to coefficients of universe `max u (t+1)`
on the original sites. The proof supplies the coefficient-sized small models and
retains the comparison's unit equation. The existing independent-universe
`proEtale_ringedPullback_underlying_of_isIso` supplies an underlying natural
isomorphism but omits unit normalization. That is insufficient for the actual
unit assertion; the new transfer proof retains the lower comparison's equation.
No identification of `u` with `t`, statement change, or restatement of a hole is used.

In Stacks Tag 09AC, the surjectivity argument uses stability of a flat morphism's
image under generalization. The source text says specialization at this point;
the Lean argument uses `Flat.generalizingMap`, as does the earlier proved
closed-counit argument. Empty schemes, zero rings and empty finite covers require
no nonemptiness assumptions in this argument.

## New nodes

`lem-u9-proetale-abelian-specialization-universes` records the proved abelian
inverse-image calculation before coefficient rings, modules or completion enter.
It allows any abelian left adjoint to actual direct image, with its actual unit.
Its proof follows Stacks Tags 09AC and 09BL (1),(2). Blueprint searches for
`compute-i-star` and `specialization` found no independent-universe formulation;
the existing fixed-universe Lean theorem was inspected and retained. The generic
inverse-mate equivalence is a categorical tool for transporting the affine-basis
computation. The single-cover criterion and flat generalization lifting are
recorded explicitly. No unit-level route is changed.

`lem-u9-proetale-module-unit-from-abelian-universes` records the proved transfer
from bijectivity of the abelian unit to bijectivity of the module unit when the
coefficient adjunct is invertible. It imposes no closed immersion, affine,
specialization or completeness condition. Its source is Stacks Tags 03D2 and
03D3. The blueprint search for `module inverse image` found generic operations
nodes, and the project independent-universe comparison was inspected; its
missing unit normalization is addressed by using the lower normalized comparison.
There are no change records or forced adaptations.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
