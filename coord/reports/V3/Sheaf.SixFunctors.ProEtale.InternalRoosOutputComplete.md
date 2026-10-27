## What changed

Completed the proof body of
`AlgebraicGeometry.ProEtale.AdicCompletion.isDerivedComplete_roos` in
`Sheaf.SixFunctors.ProEtale.InternalRoosOutputComplete`, with its statement and public
imports unchanged. Added two proof imports, one per genuine intermediate assertion,
and the source library K-flat-resolution proof import. Updated only `proof`,
`proof_deps` and `proof_origin` of the existing node.

The combination is an explicit categorical argument. Resolve the quotient Roos
output by a K-flat complex R, identify Q(R) with the principal cone output of P,
and extend that isomorphism across the principal unit v of R using the Hom
bijection. This constructs a left inverse s. Injectivity into the principal cone
output of R proves s v = 1, so v is invertible. The normalized comparison for R
then proves invertibility of its actual quotient augmentation. R and its resolution
are the witnesses in the unchanged definition of IsDerivedComplete.

The three sandbox modules compile together through lcompile.py; the proof of the
item contains no sorry. There are no adaptations, deletions, definition changes or
changes to adopted source-library declarations. No change record is required.

## Proved and sorry left

Original hole count: 1. Removed the whole-proof sorry of
`AlgebraicGeometry.ProEtale.AdicCompletion.isDerivedComplete_roos`.
Its proof now compiles from the two assertions below. This is a decomposition,
not an axiom-free proof: holes closed 1, holes added 2, local net -1.

The delivery leaves exactly these two whole-proof public theorem holes:

- `AlgebraicGeometry.ProEtale.AdicCompletion.internal_principal_cone_hom_reflection`
  in `Sheaf.SixFunctors.ProEtale.InternalPrincipalConeHomReflection`, node
  `lem-pe-internal-principal-cone-hom-reflection`.
- `AlgebraicGeometry.ProEtale.AdicCompletion.internal_quotient_principal_cone_comparison`
  in `Sheaf.SixFunctors.ProEtale.InternalQuotientPrincipalConeComparison`, node
  `lem-pe-internal-quotient-principal-cone-comparison`.

Each has a source, full argument in its docstring and node, and its own module.
The first is the Hom extension step for principal cone complexes and says nothing
about quotient Roos output or IsDerivedComplete. The second identifies the two
strict tower constructions with their units and says nothing about reflected
output or unit invertibility. Neither is the original statement renamed.
Neither requires choosing data inside a definition. The proof of the original
statement applies them both and proves the two inverse identities explicitly.

Edge checks: P or Q zero gives zero cone completion and singleton Hom sets.
For the empty scheme the category is zero. The principal cone statement requires
no K-flatness because singleton Koszul factors are finite free; the quotient
comparison requires K-flatness precisely to preserve the coefficient resolution
quasi-isomorphism. Positive level n means exponent n+1. Keeping the augmentation
equality rules out an arbitrary triangle isomorphism as a substitute.

## No longer needed

No original public import was removed. The new modules omit the redundant public
Monoidal import, which DerivedCompletion already exports. No module was withdrawn.

The existing item's proof no longer directly uses these old planned dependencies:

- `lem-pc-kflat-resolution`: use the already proved native source theorem
  `CochainComplex.exists_quasiIso_flat_kFlat` instead, recorded by
  `lem-pc-source-module-kflat-resolution`.
- `lem-sf-regular-roos-koszul-unit` / `Sheaf.SixFunctors.RegularRoosKoszulUnit`:
  its stronger TFAE and regular quotient unit criterion are unnecessary. The two
  separate comparison and Hom-reflection assertions suffice.
- `lem-pe-kflat-roos-representative-invariance` /
  `Sheaf.Algebra.Homology.KFlatRoosRepresentativeInvariance`: no replacement of
  the input P is used. Resolve the output, then supply that resolution as the
  witness in the existential completeness definition. There is no appeal to the
  sectionwise representative-invariance theorem.

The section tensor comparison, scalar adjunction, coefficient resolution and
ringed Koszul reflector remain needed in the new nodes' arguments, so they are
not claimed as globally pruned. The complete-library closure may retain any of
the above nodes via other parents; this report only removes these edges from
this item's route. No adopted upstream declaration or proof was removed.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The old plan did not provide the normalized
internal quotient-to-principal-cone comparison as a declaration. The available
`integralPrincipalConeQuotientComparison` uses sectionwise completed coefficients,
not the native internal category of this item. Likewise, the existing generic
principal cone criterion and the private smallPrincipalHom argument of
OpenRoosUnitAdjunction are section-module statements. Their tensor/equivalence
transport is real work, now isolated in explicit internal statements rather than
hidden by an arbitrary isomorphism of homotopy-limit vertices.

A shortest-route search covered the source tree, Sheaf and Mathlib (LeanSearch,
LeanFinder/Loogle and source grep). Mathlib returned ordinary adic completion and
mapping-cone APIs, with no exact internal derived result. Whole-blueprint searches
for principal cone and Koszul quotient found no duplicate of either new assertion.
The unit route in sk-prop-integral-criterion is retained: these are steps of the
existing final completeness interpretation, below the unit level.

A read-only dependency audit found the pre-existing cycle
`lem-pc-ring-hom-extension-differential` ->
`lem-pc-ring-hom-extension-differential-adjacent` ->
`lem-pc-ring-hom-extension-differential`. This delivery does not modify those
nodes. Every new dependency exists, each proof_deps is exactly the union of
step uses, and a separate return-path check found no cycle involving any
new or edited node.

The new node sketches use the exact-equivalence principal cone comparison, the
small-site principal criterion, normalized regular quotient augmentation, and
the smallPrincipalHom proof in OpenRoosUnitAdjunction as generic tools. They do
not import or assert the integral criterion itself. If route approval is needed
for these tools, it belongs to the maintainer; no tool_uses approval was added.

## New nodes

`lem-pe-internal-principal-cone-hom-reflection` records precomposition bijectivity
for maps from a principal cone output into another principal cone output. Its
proof reconstructs section modules, uses the normalized singleton Koszul
reflector, and transports the Hom bijection through the fully faithful derived
equivalences. Stacks 099B and 0A0E are its source. It is strictly the reflection
step of the original plan, independent of quotient-tower comparison.

`lem-pe-internal-quotient-principal-cone-comparison` records the derived
isomorphism between the principal cone and actual internal quotient Roos complex,
with its augmentation equality. Its proof tensors the regular coefficient
resolution, retains transition and zero-homotopy normalization, and uses exact
products to pass to the signed Roos complex. It is strictly the comparison step
of the original plan, independent of completeness or Hom reflection.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
