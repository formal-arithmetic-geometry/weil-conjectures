## What changed

Filled the eleven theorem proofs in
`Sheaf.AlgebraicGeometry.RelativeExtensionCohomologyNormalization`. The Ext declarations now pass the already available `HasExt` instances explicitly
to avoid repeatedly expanding large sheaf-category instance terms. The normalization predicate becomes a one-field Prop structure carrying exactly the
original cocycle condition, so that elaboration can use its constructor and projection
without unfolding the entire formula. The enlargement restriction has its source and target objects explicitly typed.
The enlargement complex now has its explicit,
definitionally identical relative-complex arrow type. Other definition bodies are preserved.
All added proof helpers are private and proved. The complete module compiled in 57.5 seconds;
Ext constructors are kept folded locally, and the resolution sign calculation uses a
proved generic private helper. The lifts and framed cocycle are abstracted after their
construction, preventing repeated expansion of their data in the normalization proof.
The kernel inclusion, comparison equivalence and cone cycle are abstracted with their defining
equations. Private instances supply the additive self-forgetful functor and its homology
properties; all are constructed or proved from the identity functor.

The integral open-closed sections theorem supplies the framed extension characterization.
A natural additive identification of supported Hom with the kernel of restriction, the
resolution cocycle comparison, and the normalized relative-cone realization construct and
uniquely characterize the comparison in every nonnegative degree. The first resolution
extension computes the minus sign. Free torsor presentation morphisms prove coefficient,
etale pullback, support enlargement and ordinary extension compatibility; the lifting
torsor equivalence gives the fibre assertion on every object. The raw framed class and
its forgetful formula give the positive ordinary H1 normalization.

Updated the existing node's proof, proof dependencies, proof origin and obsolete tool-use
entries to match these arguments. Added no nodes, no declarations in the source library,
and no changes to the mathematical conditions. The support-enlargement homology map
uses its explicit additive-hom projection to avoid a costly coercion search. The interface change and consumer scan are recorded
in `coord/changes/relative-extension-ext-instance-parameters.md`.

Repair of returned head `31cb6da8e2a`, reviewed by C-31cb6: the proof was accepted,
but landing rejected a reviewer correction whose basename lacked the required
`.change.md` suffix. The delivery record remains at its standard
`coord/changes/relative-extension-ext-instance-parameters.md` path; a reviewer override
must use `relative-extension-ext-instance-parameters.change.md`. Rebuilt the record's
old/new sections from current source and the retained Lean file, covering all fourteen
changed declarations verbatim and all changed definition bodies. This corrects its
stale `def` excerpt for the new structure, omitted enlargement signatures, and implicit
homology-map coercion excerpt. The retained proof has eleven closed holes and no new
holes. The delivery tool rebuilds this packet on freshly fetched `sheaf-dag` and runs
server compilation and preflight before pushing. The current consumer scan also finds
`CartierPairTensorAddition` and its transitive consumer `RamifiedCartierSupportedPurity`;
both are now listed in the change record.

## Proved and sorry left

Closed all eleven original holes, each belonging to
`lem-pur-relative-extension-cohomology-normalization`:

- `AlgebraicGeometry.Etale.relativeExtension_existsUnique`
- `AlgebraicGeometry.Etale.relativeExtensionComparison_existsUnique`
- `AlgebraicGeometry.Etale.relative_extension_cohomology_normalization`
- `AlgebraicGeometry.Etale.relative_extension_coefficient`
- `AlgebraicGeometry.Etale.relativeExtensionExchange_isIso`
- `AlgebraicGeometry.Etale.relative_extension_pullback`
- `AlgebraicGeometry.Etale.relativeExtensionSupportMap_existsUnique`
- `AlgebraicGeometry.Etale.relativeExtensionEnlarge_square`
- `AlgebraicGeometry.Etale.relative_extension_enlarge`
- `AlgebraicGeometry.Etale.relative_extension_fibre`
- `AlgebraicGeometry.Etale.relative_extension_forget`

No holes remain in the delivered module. Added zero holes and split off zero statements.
The proof uses existing declared dependencies; their own proofs remain their respective
items where unfinished. This report counts the eleven local theorem bodies, not closure
axioms inherited from dependencies.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.DivisorTorsorBoundarySigns`
- `Sheaf.AlgebraicGeometry.ClosedSupportHom`
- `Sheaf.CategoryTheory.Abelian.RHomDerivedRoof`
- `Sheaf.AlgebraicGeometry.SupportedKummerSupportHomNaturality`
- `WeilConjectures.CategoryTheory.PushoutShortExactSequence`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.OpenClosed.Exact`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`

The last three general open-closed/exactness tools are supplied through the existing
integral-sections theorem and exact inverse-image instances, rather than explicitly
applied here. This does not claim to remove those dependencies from that theorem or
from the whole library.

Removed direct proof-dependency edges:

- `lem-weil-pbc-open-closed-short-exact` and
  `lem-weil-pbc-extension-by-zero-adjunction`: use the already normalized integral
  open-closed sections interface instead.
- `lem-weil-pbc-abelian-exact-epi-cokernel`: use the Mathlib short-exact cokernel API
  directly; it remains represented by the generic exactness used in the argument.
- `lem-sc-p1-rhom-hom-derived-roof` and `lem-amb-closed-support-hom`: the natural
  supported-Hom identification and `exists_ext_rightDerived_cocycle_comparison`
  compute precisely the required comparison.
- `lem-pur-divisor-torsor-boundary-signs`: use explicit framed cycle coordinates
  and the first-resolution-row sign.
- `lem-weil-pbc-pushout-short-exact-sequence` and
  `def-sc-contracted-product-presentation`: the free extension's universal property
  produces a morphism of extensions directly.
- `prop-weil-pbc-inverse-image-modules-exact`: abelian inverse image exactness is
  already available as a functor instance; no module-coefficient comparison is needed.
- `lem-asd-supported-kummer-support-hom-naturality`: prove the exchange unit square
  explicitly and use framed-torsor transfer naturality.
- `lem-amb-relative-torsor-cohomology`: retain its public import for the section,
  transfer and forgetful map definitions, but use the precise cocycle-coordinate and
  class-naturality interfaces in proofs instead of its existential classification.

The unit's realized statements and steps are retained. No module is withdrawn, and no
upstream declaration is removed or altered.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan's general supported-Hom and contracted-product
interfaces were unnecessary for this particular comparison: direct integral Hom and free
presentation morphisms give the specified normalization and naturality. The existing
sandbox candidate was resumed, checked against current public signatures and the Stacks
03AJ/0A45 argument, and subjected to fresh compilation. The sign check uses
`extMk_firstCycles`, not a convention imposed on the extension class.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
