## What changed

Proved `CategoryTheory.perfectRingHom_tensorDual_degree_isIso` with its original signature.
Evaluation at the unique object identifies the internal Hom with linear maps and the
sheaf tensor with the module tensor. Projection identifies each dual term with the module
dual. The normalization identifies every diagonal block with `dualTensorHomEquiv`, followed
by a sign unit and the specified degree transport. A finite sum of block inverses is a
two-sided inverse, checked against tensor inclusions and Hom projections.

Repaired the return on head `48e8ce496`: deleted the duplicate private theorems
`homObj_zero_source`, `homObj_zero_target`, and `ringHomComplex_isLimit`, together with
the now-unused `point_isZero` helper. The cited existing theorems are private, so they
cannot be called from an importing module. Instead, both zero-object steps now apply the
public Mathlib theorem `CategoryTheory.Functor.map_isZero`, using local proofs that the
relevant Hom functor preserves zero morphisms. The contravariant step imports and uses
`PresheafOfModules.homObjMap_zero_left` from the source library. Both product-limit steps
now directly use the existing public theorem `homComplex_projections_exists`; the
specialized limit statement is no longer restated. No duplicate theorem was renamed or
moved elsewhere. All remaining helpers are private and proved.

No existing definition, theorem signature, visibility, or public import changed.
The node records the existing projection API and the explicit finite-sum inverse.
The repaired module compiled independently without errors or warnings in 47.5 seconds.
Delivery validation also compiles it with the axiom probe and runs the stage-3 checks.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.perfectRingHom_tensorDual_degree_isIso`
(node `lem-pc-perfect-ring-hom-tensor-degree-isiso`).

One of one original holes proved; zero holes added; zero split off; zero sorries left in
the delivery. The retained returned proof already had zero textual holes; this repair
removes the duplicate facts without adding any hole. The argument includes empty
support, zero modules, the zero ring, and unbounded `Q` without extra hypotheses.

## No longer needed

Removed the redundant direct proof import
`Sheaf.Algebra.Homology.PerfectRHomBaseChangeMap`: the proof uses the shared ring-site
and Hom-projection definitions already exported by the normalization interface, and no
derived base-change construction. This does not remove the module from the transitive
import closure. No planned mathematical dependency, node, or module is pruned.

Replaced the direct proof import `Sheaf.Algebra.Homology.HomComplex` with
`Sheaf.Algebra.Homology.HomComplexProjections`, which imports that construction and
provides its chosen-projections interface. Added the proof imports
`Mathlib.LinearAlgebra.Contraction`, `Mathlib.Data.Int.Interval`, and
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHomUnit`.

Removed the redundant direct proof import
`Sheaf.Algebra.Homology.PerfectRingDualTermFlat`: the normalization interface already
publicly imports it and supplies the definition `perfectRingDual`. The flatness assertion
`perfectRingDual_term_isFlat` is not used, but the module remains in the import closure
for its actual dual definition. The three duplicate private theorems and unused
`point_isZero` helper were removed as described above. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The returned proof repeated three private statements already present in other modules.
Their privacy prevents direct reuse by importing those modules. The repair uses the
public, more general zero-object and projection APIs, so those specialized statements
are no longer declared or proved here. The mathematical route and interfaces are unchanged.

The earlier search service returned `dualTensorHomEquiv_tmul`, but that lemma is absent
from the pinned Mathlib source; the pure-tensor formula follows directly from the
definition of `dualTensorHomEquiv` instead. The node describes the explicit inverse sum
rather than passing through an abstract biproduct.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
