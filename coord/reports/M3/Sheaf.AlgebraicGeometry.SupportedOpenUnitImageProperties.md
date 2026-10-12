## What changed

Proved `AlgebraicGeometry.supported_open_unit_image_properties` in
`Sheaf.AlgebraicGeometry.SupportedOpenUnitImageProperties`, keeping its entire signature
and visibility unchanged. The proof follows the existing DAG's two steps.

For quasi-coherence, derive `Scheme.Modules.overEquiv U`, compare the supplied right
adjoint with derived open direct image by uniqueness of right adjoints, and use
`schemeDerivedQCoh_openRestriction_iff` and
`schemeDerivedDirectImage_preserves_QCoh`. Compactness of U and quasi-separatedness of X
supply quasi-compactness of the open immersion; its separatedness is inferred.

For support, the proved private stalk comparison identifies homology stalks after exact
open restriction with the original stalks. Thus the restricted input is supported on
the inverse image of T. The proved private `direct_image_support` applies
`supported_derived_restriction_zero` on the inverse image of the open complement of T,
then `schemeDerivedDirectImage_openRestriction`, additivity of derived direct image,
and the stalk comparison. Finally transport both conclusions through the comparison
isomorphism to R. All chosen derived categories on auxiliary open schemes are constructed
with `HasDerivedCategory.standard`; no arbitrary data are selected from existence.

Added proof-only imports of `DerivedOpenRestrictionMaps`, right-derived adjunction and
additivity, and Mathlib's additive stalks and
zero groups. Added a module docstring and proved private helpers. No definitions or
statements of the library were changed. No other module was adapted.

Validation: local single-file compilation passes without errors or warnings. The empty
open, empty support, and full support require no special cases: restriction and direct
image preserve zero, and the complement construction works unchanged. There is no
boundedness assumption and the original localization universe w stays arbitrary; auxiliary
open scheme categories use their standard universe u + 1.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.supported_open_unit_image_properties`
(node `lem-pc-supported-open-unit-image-properties`).

Holes closed: 1. Holes added: 0. No `sorry` remains in the delivered module, and no
new theorem with `sorry` is introduced. The proof uses the library declarations of
all four existing proof-dependency nodes; those declarations' upstream dependencies
are outside this delivery. This is a proof from the existing planned dependencies,
not a decomposition into new unproved statements.

## No longer needed

Removed the redundant added proof-only import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`: the required
right-derived adjunction module publicly imports it already. All four original
proof-only imports and their four DAG proof-dependency nodes remain necessary.
No module or node is pruned, and the unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error was found. The existing affine right-adjoint
comparison in `DerivedOpenUnitCone` provided the categorical pattern, which extends
to this quasi-separated scheme and compact open. No change to the DAG proof route
was necessary. The assigned unit's `realized.statement` is empty and its sole
`realized.steps` entry is empty; no unit realization was bypassed.


## Second reading by M3

1. Compared the complete module with the repository version and independently ran
   the declaration-diff parser: no existing signature changed, no public import
   changed, and the only original hole closed is
   `AlgebraicGeometry.supported_open_unit_image_properties`. No change record or
   forced adaptation is needed. Verdict: pass.
2. Compiled the delivered proof locally, then compiled a scratch copy with
   `#print axioms` for all three private helpers and the public theorem. The helpers
   use only `propext`, `Classical.choice`, and `Quot.sound`; the public theorem also
   uses `sorryAx` through existing imported proof dependencies. There is no local
   `sorry`, forbidden declaration, or hollow definition. Auxiliary derived-category
   instances use the real standard construction, and the private stalk isomorphism
   is a composition of constructed isomorphisms. Verdict: pass with upstream holes.
3. No statement was split off and no hole was added. Read the private helpers:
   exact restriction identifies homology stalks; additive stalk and homology
   functors preserve zero; complement base change preserves support. Empty opens,
   empty support, full support, arbitrary degree and unbounded complexes cause no
   exceptional case. Searched independently for homology stalks, stalk vanishing
   and support of pushforwards using `msearch.py grep` and `rg` over both library
   roots. Found underived Mathlib stalk detection and related private comparisons,
   but no available public lemma replacing this argument. Verdict: pass.
4. Reviewed from the public theorem downward. Right-adjoint uniqueness is used
   before the support and quasi-coherence arguments; all four planned dependencies
   occur in the proof. The standard auxiliary universe avoids choosing an arbitrary
   derived-category witness. Read the unit record: its `realized.statement` and
   sole `realized.steps` entry are empty; no realized unit step is bypassed.
   Removed one redundant added exact-functor import (already public through the
   adjunction import), and checked the repaired file by compilation. No original
   dependency node or module can be pruned. Verdict: pass.
5. Read `lem-pc-supported-open-unit-image-properties` and its dependency signatures.
   The two recorded steps and their four `proof_deps` agree with the actual proof;
   the direct-image support helper applies supported restriction directly on the
   inverse image of the complement, which realizes the recorded intersection
   argument. The documented Stacks proof origin remains appropriate. No new nodes
   are needed. Verdict: pass.

Second reading changed only the redundant proof import and this report; the proof
terms, existing signatures, public imports, and node records needed no repair.
