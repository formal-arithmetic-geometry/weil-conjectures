## What changed

Proved `SheafOfModules.ringIso_tensor_transport` with its existing statement and all
`RingIsoTensorTransport` fields. The ordinary equivalence is the actual restriction functor
in both directions. Its braided structure is transported from scalar extension along the
inverse isomorphism using uniqueness of left adjoints. A private generic inverse-tensor
constructor proves the unit coherence before specializing to module sheaves. The adjunction
unit fixes the comparison on pure sections; the identity-site restriction unit is the
identity on sections. Right unitality fixes the unit map to the inverse ring map.
The existing direct-sum cochain comparison supplies the total isomorphism and every summand
formula. A private generic signed-summand lemma supplies the cochain braided equation,
following the proved source argument in
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided`. Keeping this helper
private avoids that module's competing homotopy-category instances. Exact faithful restriction
gives the acyclicity comparison. A monoidal equivalence
preserves flat objects, and lifting acyclic complexes through its inverse gives K-flatness
in both directions. A private abstract K-flat criterion in the homotopy category proves
the two quasi-isomorphism tests, using the existing total-tensor colimit assumptions.

Added `CategoryTheory.braidedLocalizationSquare` in its own module. It compares two derived
bifunctors with the same counit target, using the K-flat resolving-subcategory criterion.
Their unique natural comparison is invertible. The existing lax-square construction proves
monoidal coherence, and cancellation on resolving models proves braiding. Applied directly
to the cochain localizations, this supplies the derived field with independent localization
universes and the specified normalization. Both new symmetric derived tensors have invertible
unit comparisons and tensor comparisons on all K-flat pairs.

Updated the item's proof, proof dependencies and proof origin, and added the generic
localization-square node. Existing public declaration signatures, attributes and public imports are unchanged.
The bodies of `ringIsoCochainMonoidal` and `ringIsoCochainMonoidalStruct` now name their
Mathlib constructors explicitly,
avoiding repeated instance search. Private diagnostics confirmed both replacements are
definitionally equal by `rfl`. No other existing Lean module is adapted.

## Proved and sorry left

Closed the one original hole, `SheafOfModules.ringIso_tensor_transport` (node
`lem-sfb-ring-isomorphism-tensor-transport`). Added zero holes. No `sorry` remains in either
Lean module. The new `CategoryTheory.braidedLocalizationSquare` is fully proved; no admitted
statement is split off. This is a proof, not a decomposition into admitted statements.

Validation: `lcompile.py --all` compiled both modules cleanly in import order.
The generic localization module was cached (0.0 seconds); the complete item compiled in
59.6 seconds, with no warnings or errors.
The twelve downstream consumers are documented in the change records and require no adaptation.

A private theorem packages the native monoidal localization, descended symmetry, braided
localization functor, unit invertibility and K-flat tensor invertibility. The scalar proof
uses these witnesses abstractly. Another private theorem proves flatness transport for an
abstract monoidal equivalence, before applying it to the scalar equivalence. The K-flat
criterion is likewise proved before specializing the tensor category. A private predicate-transport
lemma lifts tensor tests through an abstract monoidal equivalence. K-flat derivability
uses the existing tensor colimit-preservation theorem directly. These proved helpers avoid
repeatedly constructing the same concrete monoidal data.

## No longer needed

Removed these original proof imports:

- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`;
- `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`;
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`;
- `Sheaf.Algebra.Homology.KFlatTotalTensorModel`;
- `Mathlib.CategoryTheory.Localization.Predicate`;
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`;
- `Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal`.

The original proof dependencies `lem-pc-sheaf-modules-tensor-closed`,
`lem-pur-quasi-iso-cone-acyclic`, `lem-pc-tensor-mapping-cone-iso`,
`lem-weil-pbc-site-derived-tensor-descent`, `lem-pur-kflat-total-tensor-model` and
`lem-sf-ringed-derived-closed-symmetric-monoidal` are no longer direct steps of this proof.
The first is replaced by the normalized scalar-extension tensor APIs; the cone argument is
already encapsulated by the categorical K-flat criterion; the last three are replaced by
direct native cochain localization and derived-bifunctor uniqueness. The corresponding old
`tool_uses` approvals are removed from this node when no longer used. This makes no claim
that these modules are unused by other declarations or absent from every transitive import.
The separate presheaf-sheafification import is redundant with the public sheaf tensor
imports and contributes no direct step. No source-library declaration or module is withdrawn. The blueprint unit and its realized
steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The planned argument is valid. The existing closed derived-Hom theorem is formulated with
coefficients in the maximum of the site universes; it cannot be specialized directly to this
item's independent coefficient universe. The native derived-monoidal APIs themselves have
no such restriction. Functorial flat resolutions and exact countable colimits give their
hypotheses here, and localizing cochain complexes directly avoids any comparison between
localization universes. No statement repair was needed.

Compilation intermittently returned exit 124 because the server was busy. Those attempts
were retried. Other complete versions exceeded the 60-second compile limit; profiling led
to the explicit cache constructors and the private abstract helpers described above.
No launcher script or compile limit was changed. Private diagnostic proofs checked both
cache replacements by `rfl`; they are omitted from the delivered source. The cache repair
is recorded in `coord/changes/ringIsoCochainMonoidalExplicit.md`.

## New nodes

`lem-sfb-braided-localization-square` records
`CategoryTheory.braidedLocalizationSquare`, the generic normalized descent result used only
for the derived comparison. It is strictly a part of the original argument: it assumes
monoidal localization data and invertibility on resolving models, and constructs the
cross-functor braided structure. It makes no assertion about scalar restriction, module
flatness, ordinary pure tensors or direct-sum cochain summands. Its hypotheses are checked
in the item's proof. It adds no `sorry`. The statement works for identity localizations and
zero categories; it does not assume either localization is strong monoidal on arbitrary
objects. The command-only change record is
`coord/changes/ringIsoTensorTransportPrivateProof.md`; it documents local proof settings,
private helpers and the unchanged interfaces of the twelve downstream consumers.

The first delivery preflight requested the missing LeanSearch kind in the new node
(the earlier Loogle and LeanFinder searches belong to the same search kind). Added an
actual LeanSearch query and its results; the Lean source is unchanged.

The definitionally identical cache construction is recorded in
`coord/changes/ringIsoCochainMonoidalExplicit.md`.

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
