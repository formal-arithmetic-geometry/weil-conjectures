## What changed

Proved `WeilConjectures.constructibleIntegralScalarExtension_smul` directly from
`integralScalarExtensionWellDefined` and the canonical coefficient-action formulas.
Proved `WeilConjectures.integralScalarCompletionChain_existsUnique` by transporting
`completedScalarChainComparison` along the natural isomorphism between the two
ordinary sheafified tensor presentations. The coefficient maps agree by uniqueness
of their finite quotient projections. Tensor generation, product projection
extensionality and the mapping-cocone biproduct identity prove uniqueness with both
cone coordinates fixed. All added helpers are private and proved.

Added the proof import `Sheaf.Paper.FiniteFreeCompletedScalarComparison`, retained both
public imports, and updated the owning node's proof, proof dependencies and proof origin.
No existing theorem signature or definition body changes. Private tensor helpers use
explicit sheafification instances; large change-of-rings definitions are locally
irreducible only during the tensor-model isomorphism construction. The earlier unused
finite-reduction lemma and node drafts remain preserved under scratchpad and are not
delivered. The former server disk failure no longer prevents Lean from starting.

## Proved and sorry left

Original holes: five. Closed two, with zero holes added and zero split-off statements:

- `WeilConjectures.constructibleIntegralScalarExtension_smul`.
- `WeilConjectures.integralScalarCompletionChain_existsUnique`.

Three original holes remain unchanged, all attached to
`lem-weil-integral-scalar-extension-constructible`:

- `WeilConjectures.integralScalarExtension_constructible`.
- `WeilConjectures.integralOrdinaryDerivedScalar_constructible`.
- `WeilConjectures.integralConstructibleScalarComparison_existsUnique`.

The completed proofs use the existing published dependency declarations; this is a
partial proof delivery, not a claim that the whole constructibility node is closed.
The complete delivered file compiled cleanly through lcompile.py in 28.7 seconds
(exit code zero, no Lean warnings). All ten existing declaration signatures were
compared with the current source and are identical.

## No longer needed

The completion-chain proof uses the already stated canonical completed-scalar chain
comparison. It needs no new finite-filtration theorem, normalized-tower construction,
Roos derived-limit comparison or new cone lift. Their nodes remain needed by the
unchanged constructibility holes and are retained in the owning node's plan. No
library module or DAG node is withdrawn and no whole-module pruning is claimed.

Removed these direct proof imports; the declarations actually needed for the new
proof are available from the retained public interfaces and the one new proof import:

- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`.
- `Sheaf.Paper.DerivedCompleteIntegralDetailed`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`.
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`.
- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`.
- `Sheaf.Paper.IntegralScalarExtensionWellDefined`.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`.
- `Mathlib.Algebra.Homology.HomologicalComplexLimits`.
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic`.

## Where the brief, the DAG or earlier work was wrong

The node's current primary Lean attachment is the intrinsic wrapper, which imports
this legacy item. Importing that wrapper here would create a cycle. The delivery
preserves the primary attachment and the intrinsic compatibility proof, and appends
the two completed legacy arguments to the node. The unit record has no realized
statement or proof steps that this transport would bypass.

The earlier completion-chain attempt treated an irreducible chosen definition as
its existential witness without unfolding its name. Explicit specification transport
repairs that mismatch. The zero shifted coordinate also needs degree arithmetic
before the natural-transformation composition can be compared. The unused draft
finite-reduction theorem was not needed for either completed proof, so it is not
added as an unrelated new hole.

## Second reading by V5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
