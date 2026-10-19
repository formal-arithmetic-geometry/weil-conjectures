## What changed

Replaced the original hole in
WeilConjectures.exceptionalFiniteSupportExtensionMap_isIso by componentwise
application of the constant-coefficient projection formula. All existing signatures,
definitions, visibility and public imports in the item are unchanged. G6's previously
landed scalar-adjunction proof is retained without credit.

Proved the shift compatibility and unit law of the canonical derived tensor
comparison, using flat resolutions and the existing oplax-of-lax-square construction.
Proved finite_support_projection for arbitrary unbounded K and arbitrary constant
modules over a finite ring, assuming the compact-support functor is a left adjoint.
The open projection isomorphism makes the relevant proper projection target a
left adjoint too. The already proved source-library theorem
DerivedCategory.isIso_of_isIso_app_singleFunctor_obj_self then supplies the D(R)
generation argument. No separate finite-resolution development is imported.

The coefficient proof transports the supplied support adjunction through the
realization equivalences, applies projection at the restricted target ring B,
and reflects isomorphisms through realization and exact scalar restriction.
The remaining normalization result identifies the two canonical arrows. It assumes
no support adjunction and does not assert that either arrow is invertible.

## Proved and sorry left

Closed one original hole:
WeilConjectures.exceptionalFiniteSupportExtensionMap_isIso. The item has zero holes.
Added one hole:

- WeilConjectures.support_scalar_projection_identification, in
  Sheaf.Paper.SupportScalarProjectionIdentification, node
  lem-sf-support-scalar-projection-identification.

This is a decomposition with net hole change zero. The generic derived monoidal
comparison, its shift compatibility and invertible unit, the constant projection
formula, adjunction transport and conservativity are proved. The remaining hole
is the scalar/tensor normalization calculation, strictly part of the argument.
No definition contains sorry or chooses arbitrary data from an unproved mere
existence statement.

The new proved declarations are GenericDerivedTensorShift.commShift,
GenericDerivedTensorShift.exists_kFlatMap_iso,
GenericDerivedTensorShift.oplaxMonoidal, GenericDerivedTensorShift.isIso_unit,
AlgebraicGeometry.ProEtale.compactSupportProjectionComponent_eq,
AlgebraicGeometry.ProEtale.finite_support_projection,
WeilConjectures.projectionRealizationInverse_eq,
WeilConjectures.projectionRealizationInverse_reflects and
WeilConjectures.supportCoefficient_isIso_of_projection.

The canonical compact-support projection component has an irreducible named
definition, with an explicit equation to the published projection map. This keeps
large composed functor data out of subsequent conversion checks. A named realization
inverse fixes the coefficient category to the ring structure underlying its monoidal
structure, with a proved equation to the published realization and a proved
conservativity instance. This avoids repeated large conversions between the two
definitionally equal ring structures on ULift A. The projection module also uses
the source library's atomic commutative-ring Grothendieck instance (ModuleCat/AB),
matching the intrinsic realization imports and avoiding expensive proof abstraction
in derived tensor data. The full sandbox compile passed for all five modules
without errors or warnings; every rebuilt file stayed below 60 seconds. The axiom
probe confirms that the new generic comparison, projection formula and realization
API use only propext, Classical.choice and Quot.sound. The bridge and original item
also depend on sorryAx through the explicitly reported normalization lemma.

Edge cases checked mathematically include zero rings, zero sheaves,
empty schemes, nonflat quotient maps and unbounded complexes. No finite Tor
amplitude, constructibility or etale-origin hypothesis is introduced.

## No longer needed

No existing library module or node is pruned. Seven provisional modules are absent
from the delivery and preserved under scratchpad/retained-unused with their node
records:

- Sheaf.Paper.SupportCoefficientSingle
- Sheaf.Paper.SupportCoefficientLocus
- Sheaf.Paper.SupportCoefficientRestrictionShift
- Sheaf.Paper.ProEtaleSingleGeneration
- Sheaf.Paper.ProEtaleBoundedTelescope
- Sheaf.Paper.ProEtaleSequentialTelescope
- Sheaf.Paper.FiniteCoefficientDevissage

The corresponding provisional nodes are lem-sf-support-coefficient-single,
lem-sf-support-coefficient-locus, lem-sf-support-coefficient-restriction-shift,
lem-sf-proetale-single-generation, lem-sf-proetale-bounded-telescope,
lem-sf-proetale-sequential-telescope and lem-sf-finite-coefficient-devissage.
These records never entered the shared DAG. No existing project node or Lean
file is withdrawn or deleted.

The coefficient-variable projection argument eliminates generation by arbitrary
sheaves on the site. The whole compact-support adjunction supplies all coproducts,
so the existing D(R) generation theorem also eliminates the provisional finite
free-resolution lemma, whose complete proof is preserved in the scratchpad.

Replaced the retained packet's proof imports of SupportCoefficientLocus,
SupportCoefficientRestrictionShift and ProEtaleSingleGeneration in the item.
Removed FiniteCoefficientDevissage from the projection module and imported the
existing ModuleCatGeneration instead. BoundedConstructibleTower remains for G6's
scalar-adjunction proof. SfOpenExceptionalBaseChange is not imported: the needed
realization comparison is constructed using the equivalence unit, derived
composition comparisons and intrinsic direct-image comparison. No blueprint
unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The shared item has one original hole; the earlier two-hole description predates
G6's independent scalar-adjunction proof. That proof is not counted here.

The retained route used degree-zero sheaf inputs and generation on the site.
The source library already proves generation of D(R) by R[0]. Applying that result
with the coefficient as variable and K fixed gives a shorter route when the whole
compact-support functor has its supplied right adjoint. No coproduct hypothesis
on the proper direct image alone is needed.

The first final preflight found that LeanFinder and Loogle had been counted as
separate search categories. Completed the required LeanSearch queries and retained
the actual eight-hit results alongside the existing semantic, type and source
searches. They give generic tools, including the constant-sheaf adjunction already
used, but no exact statement.

The earlier provider-resumption clock failures were not treated as a new tool
failure. The initial required dry run was performed and this session substantially
changed and proved the projection argument. Retained work is preserved. No launcher
script or budget metadata was edited. There is no change to an existing statement,
definition or interface, and no consumer adaptation or change record is required.

## New nodes

lem-sf-derived-monoidal-comparison-shift realizes
Sheaf.CategoryTheory.DerivedMonoidalComparisonShift. Its shift theorem, oplax
structure and invertible unit are proved from the existing flat-resolution APIs.

lem-sf-finite-support-projection realizes Sheaf.Paper.FiniteSupportProjection.
Its component definition is the actual published canonical projection, with a
computation theorem. The projection theorem is proved using existing D(R) generation.

lem-sf-support-scalar-projection-identification realizes
Sheaf.Paper.SupportScalarProjectionIdentification and is the sole new open theorem.
Its source calculation was checked in literature/stacks-project/more-etale.tex,
Remark Rf-lower-shriek-change-of-rings (0GL6), and sites-cohomology.tex,
Section Projection formula. Only identification of arrows is used from that
calculation; no etale projection-isomorphism conclusion is assumed for arbitrary
pro-etale inputs. Its docstring gives the full normalization argument.

lem-sf-support-coefficient-by-projection realizes
Sheaf.Paper.SupportCoefficientByProjection, combining the preceding results with
proved adjunction transport and scalar conservativity. The original item node
records the componentwise application of this theorem.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
