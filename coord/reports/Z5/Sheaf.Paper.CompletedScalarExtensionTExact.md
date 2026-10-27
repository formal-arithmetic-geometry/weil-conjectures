## What changed

Filled the two ordinary scalar-extension exactness instances and the strict-tower
t-exactness theorem in `Sheaf.Paper.CompletedScalarExtensionTExact`.
The finite-free comparison supplies the finite coefficient basis; the existing
`scalarFiniteExact` helper applies to the canonical completed scalar cochain model.
The proved arbitrary-scheme `scalar_exact_comparison` helper of the point-derived
sections-descent module supplies the normalized ordinary-derived comparison via
uniqueness of the left derived functor. Intrinsic/legacy derived completeness makes the published scalar
comparison invertible on each constructible input. Its composite with the ordinary
comparison gives the required epsilon, including its exact inverse formula.
Mathlib transfers shifts and triangulatedness along the fully faithful inclusion,
and the exact derived functor preserves both ambient cohomological bounds.

No public definition, theorem statement, public import, or source-library module
changes. Explicit universe arguments merely specify the equal scheme/coefficient
universes already fixed by the statements. Added private proof imports for the
published finite-free helpers, intrinsic completeness comparison, and exact-derived
and universal-derived APIs. Updated the existing node's proof route accordingly.

## Proved and sorry left

Closed three holes, all belonging to `lem-pod-completed-scalar-extension-texact`:

- `WeilConjectures.podCompletedOrdinaryScalarExtension_preservesFiniteLimits`.
- `WeilConjectures.podCompletedOrdinaryScalarExtension_preservesFiniteColimits`.
- `WeilConjectures.podCompletedScalarExtension_tExact`.

No holes added or split off. No sorry remains in the delivered Lean module.
Existing dependencies retain their own proof status.

Validation: the delivered module compiles through `lcompile.py` in 16.8 seconds,
with exit code zero and no diagnostics. The final delivery preflight also checks
the generated declaration/axiom probe and preservation of existing signatures.

## No longer needed

Removed the private proof imports `Sheaf.Paper.IntegralTStructure` and
`Sheaf.Paper.IntegralStratifiedPerfectCharacterization`. The corresponding nodes
`prop-weil-pbc-integral-tstructure` and
`lem-weil-pbc-integral-stratified-perfect-characterization` are unnecessary for this
proof: the conclusion is already stated using ambient `DerivedCategory.IsLE` and
`DerivedCategory.IsGE`. Their modules may still be needed by other consumers.

The finite coordinate calculation is reused from the proved strict-tower transport
helper, so the proof no longer directly uses `def-pur-sheaf-tensor-product`,
`def-weil-sheaf-of-modules-category`, or `def-pc-sheaf-restrict-scalars` as separate
proof dependencies. These notions remain in the statements and underlying APIs.
Also removed redundant private imports
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses` and
`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`; the imported finite-free
helpers already supply these proof interfaces. All public imports are retained. No module or declaration is withdrawn, and no
unit realization is bypassed (`sk-lem-finite` records no realization by this node).

## Where the brief, the DAG or earlier work was wrong

Step 1 of the old plan was unnecessary for the actual Lean statement, which already
uses ambient bounds; constructing the integral t-structures would add no needed
information. The actual missing bridge for the canonical scalar comparison is
`sfDerivedComplete_iff_legacy`, now recorded explicitly as a dependency.
The noetherian, dimension, and invertibility assumptions remain unchanged, though
the proof does not use them: the imported constructibility and comparison APIs
apply to arbitrary schemes.

The current blueprint places `prop-constructible-truncations` under
`sec-poincare-duality/sk-thm-frobenius` and now discusses rational coefficient
stages. This item is the existing integral argument extracted from the older
corrected blueprint; its unchanged integral statement is proved from the recorded
Bhatt--Scholze and Stacks interfaces. The source is present despite the historical
node's old blueprint path.

The rework row records an earlier quarantine due to a transitive
`ProjectiveLineGenusZero` import. The item source is currently restored in `lean/`;
this delivery preserves every declaration and repairs its three actual holes.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
