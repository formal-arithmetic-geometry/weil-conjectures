## What changed

Replaced the proof hole in
`AlgebraicGeometry.Scheme.adicResidue_koszul_coefficient_cone_comparison`
without changing its signature. Replaced its public import of
`AdicResidueKoszulCoefficientAugmentation` by the required
`AdicResidueQuotientTensorTower`; the augmentation-existence proof is unused here.
The sole direct importer independently imports the augmentation module. Added proof imports for
`Sheaf.Paper.AdicResidueExactCoefficientRealization`,
`Sheaf.CategoryTheory.ExteriorKoszulScalarRealization`, and
`Sheaf.CategoryTheory.AdditiveConeFamilyComparison`. The last module contains a
complete, generic finite categorical assembly proof, including the additive-cone
calculation adapted from `PrincipalConeExactEquivalence` and the proved private
level-cone helper from `FlatConstantTensorProZeroCones`. Principal-completion
theory is not imported, avoiding its fifty additional import dependencies.

The proof constructs quotient-complex comparisons from the standard
extension and single-complex isomorphisms. It proves augmentation compatibility by
the supplied degree-zero formula and the two unit normalizations, proves the
algebraic augmentations epimorphic, cancels them to obtain quotient-transition
compatibility, and proves naturality of the resulting cone isomorphisms. Proved
helpers in the generic assembly module establish additive cone naturality,
identify the strict cofiber map with the native cone map, and construct
the natural cone isomorphism induced by a square of isomorphisms.

The remaining work is separated into two independent, strictly smaller statements.
The first has no Koszul data or cones: it asks for exact scalar realization and
regular-module/quotient normalizations. The second concerns an arbitrary additive
scalar-compatible functor and only unaugmented finite exterior Koszul complexes;
it has no quotient, augmentation, cone, exactness or Noetherian assumptions. Neither
is the assigned cone comparison under another name. Their sources, full proofs in
words, edge cases, Lean statements, and DAG records are included. The sole direct importer,
`Sheaf.Paper.AdicResidueKoszulTensorConeProZero`, also has a proof-only timing repair
with its public interface unchanged; it was unclaimed. No other existing module
is changed. After local irreducibility and import
pruning, the combined file still took 67.6 seconds. Its fully proved generic cone
assembly was isolated into the new module so that each file can be checked within
the unchanged 60-second limit. No further hole was introduced by this split.

Validation: the compilation service accepted all five delivered Lean files
without warnings, including the direct consumer, after the timing repairs.
The assigned theorem and the consumer retain their original signatures.

## Proved and sorry left

Closed the one original syntactic hole:
`AlgebraicGeometry.Scheme.adicResidue_koszul_coefficient_cone_comparison`
(node `lem-sfb-adic-residue-koszul-coefficient-cone-comparison`). The combination
proof has no `sorry`. The new generic
`CategoryTheory.additiveConeFamilyComparison`
(node `lem-sfb-additive-cone-family-comparison`) is also completely proved.

Added two holes, each the complete body of a named public theorem in its own module:

- `AlgebraicGeometry.Scheme.adicResidue_exact_coefficient_realization`
  (node `lem-sfb-adic-residue-exact-coefficient-realization`).
- `CategoryTheory.exteriorKoszul_scalar_realization`
  (node `lem-sfb-exterior-koszul-scalar-realization`).

This is a decomposition, not a completed proof free of new assumptions: one hole
closed, two added, net minus one. No definition or private declaration contains a
hole. The new statements were checked on rank zero, zero rings, zero/unit ideals
where applicable, and empty sites/slices. They use finite coordinates only.

## No longer needed

Removed the public import of `AdicResidueKoszulCoefficientAugmentation`, replacing
it by its needed quotient-tower dependency. Its existence theorem and negative
Koszul proof modules are not needed by this assembly. The sole direct importer
already imports the augmentation module independently; no module is withdrawn or
claimed globally pruned. Removed trial proof imports of `RingedNegativeKoszulDuality` and
`RingedNegativeKoszulLowDegrees` from the assigned module; its combination proof
needs neither directly. The new exact-realization statement also does not import
`CommutativeSiteDerivedConstantModuleFunctor`: that dependency belongs to its future
proof, not its signature.

The assigned node no longer directly uses
`lem-weil-pbc-constant-completion-equivalence`,
`def-sfb-site-derived-constant-module-functor`, or
`lem-route-ringed-internal-hom-restriction`; these are now proof dependencies of the
scalar/quotient realization node. Similarly,
`lem-weil-pbc-ringed-negative-koszul-duality` and
`lem-cbc-signed-koszul-finite-coordinates` belong to the independent finite-coordinate
node. They remain mathematically needed below the new statements and are not
withdrawn. The old augmentation-existence node remains a statement dependency, but
its existence theorem is not used: the assigned statement supplies an arbitrary
normalized augmentation, and the proof uses that normalization directly.

No algebraic pro-zero theorem, derived inverse-limit assertion, tensoring by an
arbitrary complex, or principal-completion theorem is used in this finite assembly.
Only `levelConeTowerIso` is imported from the generic cone module. The trial import
of `PrincipalConeExactEquivalence` was removed after profiling; its finite
`mapCone_natural` calculation and supporting identities are proved in the generic
assembly module. The original quotient normalization
hypothesis `hqA` is redundant in the assembly: quotient-transition compatibility
follows from the given strict squares, augmentation surjectivity, and Koszul
transition compatibility. Its binder and statement remain verbatim.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was found. The planned finite proof is
valid, but its dependencies do not directly supply projection-normalized scalar
realization on the coefficient-model slice or the unaugmented exterior comparison
in the arbitrary `max v (u + 1)` coefficient universe. Existing completed/exterior
comparison modules specialize to another coefficient datum and a successor
universe. Their signatures cannot simply be instantiated here. The two new
statements isolate exactly these gaps rather than repeating the full cone theorem.

A dependency audit found the pre-existing cycle
`lem-pc-ring-hom-extension-differential` ->
`lem-pc-ring-hom-extension-differential-adjacent` ->
`lem-pc-ring-hom-extension-differential`. It is reachable from the original node
before this delivery as well. None of the new direct dependencies reaches back
to the assigned node; these unrelated node records are left untouched.

The unit route in `sk-lem-integral-models` is preserved. The original theorem,
its hypotheses (including rank zero), conclusion, and definitions are unchanged.
The one public-import pruning is documented in
`coord/changes/M4-adic-residue-cone-imports.md`. The sole direct importer initially
failed the 60-second limit (62 seconds). Its proof-only repair is documented in
`coord/changes/M4-adic-residue-cone-consumer-timing.md`: exact-functor transfer and
cone construction are proved with abstract category parameters, universes are
explicit, and coefficient/transpose definitions stay locally irreducible.
The degree-zero compatibility calculation is a proved private lemma over
abstract abelian categories, preventing repeated unfolding of the concrete completed
coefficient category. All transparency changes are local; shared definitions and
the consumer retains every existing signature, public import and exported attribute.

## New nodes

`lem-sfb-adic-residue-exact-coefficient-realization`, in
`Sheaf.Paper.AdicResidueExactCoefficientRealization`, isolates proof step 1 of the
assigned node. Its source is the scalar-extension and finite-quotient part of
Stacks 099M together with module sheafification. The required isomorphisms are
normalized by multiplication and projection; no arbitrary data is defined from
an unproved existence statement.

`lem-sfb-exterior-koszul-scalar-realization`, in
`Sheaf.CategoryTheory.ExteriorKoszulScalarRealization`, isolates proof step 2.
Its source is the finite ordered Koszul tensor construction (Stacks 0664 and
0A0E). Additivity preserves finite biproducts; scalar compatibility identifies
the contraction and diagonal matrices, and finite-free duality identifies the
empty coordinate with the ringed dual unit. It is independent of the first new
statement and of all quotient and cone data.

`lem-sfb-additive-cone-family-comparison`, in
`Sheaf.CategoryTheory.AdditiveConeFamilyComparison`, is completely proved. It
isolates the finite categorical assembly, with explicit epimorphic augmentations,
source comparisons and strict squares as inputs. It derives target naturality by
cancellation and constructs the natural cone comparisons. It has no Koszul,
coefficient or sheaf assumptions. This module was isolated after profiling;
it introduces no `sorry` and is not counted among the two split-off holes.

Change record: `coord/changes/M4-adic-residue-cone-imports.md`.

Consumer timing change record: `coord/changes/M4-adic-residue-cone-consumer-timing.md`.

## Second reading by M4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
