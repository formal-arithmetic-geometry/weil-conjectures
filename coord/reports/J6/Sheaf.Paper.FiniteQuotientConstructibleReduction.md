## What changed

Proved `AlgebraicGeometry.Scheme.finiteQuotient_constructible_reduction` in
`Sheaf.Paper.FiniteQuotientConstructibleReduction`. The theorem statement, both
public coefficient definitions, and all public imports are unchanged verbatim.
All added helpers are private and proved; there are no new public statements.

First, `coefficientSquare` proves compatibility of inverse image with the canonical
quotient coefficient map by transposing the ring maps through their adjunctions.
`pullbackRestrictIso` combines this square with the existing
`AlgebraicGeometry.ProEtaleTensorComparison.scalarIdentification` and the
extension/restriction adjunction. It identifies pullback of the restricted sheaf
with restriction of the quotient-coefficient pullback. The proof imports
`Sheaf.AlgebraicGeometry.ProEtaleInverseImageTensorComparison` and uses private,
already proved adjunction helpers through `import all
Sheaf.AlgebraicGeometry.ProEtaleOperations`; no copied or new adjunction data are
postulated. Please register the tensor-comparison node as a generic tool use if
its cross-unit use requires maintainer approval. No new approval was inserted.

Second, `quotientChart` works directly over the restricted constant coefficient
rings on the slice. Transpose the given chart to a map from the constant module
presheaf. Its kernel contains `I • ⊤`, by linearity and induction on that submodule.
Descend to the actual Mathlib quotient, prove quotient-ring linearity by lifting
scalars, and transpose back through module sheafification. The quotient map is
pointwise surjective. Its composite with the descended map is locally bijective,
so cancellation makes the descended map locally bijective. Its sheafification is
therefore an isomorphism, and forgetting module structure reflects isomorphisms.
This works without any nonemptiness assumption and does not infer `IM = 0`.

Finally retain the original stratification and every original cover member, use
these quotient charts, and transfer finite stalks through the pullback comparison.
Scalar restriction leaves the underlying additive stalk unchanged. Finiteness of
an explicitly specified quotient label follows from surjectivity of its quotient
map. The identical construction proves the specified-chart clause.

Updated the item's DAG proof, proof dependencies and proof origin to this route.
File-local transparency options support elaboration of the two presentations of
scalar actions; a local heartbeat allowance is confined to `quotientChart`.
The unused-variable linter is disabled only at the unchanged public theorem,
whose nested label type has an unused index binder. No other module is adapted.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.finiteQuotient_constructible_reduction`
(node `lem-exc-finite-quotient-constructible-reduction`).

Added 0 holes, split off 0 statements, and left 0 holes in the delivered Lean file.
The private helpers contain no `sorry`; no definition contains a hole. This is a
proof from existing declarations, not a decomposition into new unfinished lemmas.

## No longer needed

Removed the original private proof imports:

- `Sheaf.Paper.ProEtaleBoundedConstructibleTriangulated`: the canonical constant-ring
  comparison already exists in `ProEtaleConstantRingOperations`, reached through the
  unchanged public interface; the duplicate `constantComparison_isIso` is unused.
- `Sheaf.CategoryTheory.FiniteTypeConstantExact`: local bijectivity of the descended
  quotient map replaces the exact-sequence argument entirely.
- `Mathlib.CategoryTheory.Sites.CoverLifting`: the proof uses the rings restricted
  from the original site directly, avoiding an identification with independently
  constructed constant ring sheaves of the slice.

Correspondingly removed `lem-pur-proetale-constant-coefficient-comparison`,
`lem-weil-pbc-finite-type-constant-exact`, and
`lem-pur-ring-presheaf-sheafification-localization` from this node's proof
requirements. Removed the first two nodes' obsolete top-level `tool_uses` approvals.
The first mathematical fact is supplied by the existing ordinary-operations
interface; the latter two facts are not used. This is pruning of this item's
route, not a claim that these modules have no other consumers. No module is
withdrawn and no unit statement or realized unit proof step is bypassed.

An exploratory import of
`Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization` was also removed.

## Where the brief, the DAG or earlier work was wrong

The original exactness-based plan is mathematically valid but longer than needed:
local surjectivity of `M → M/IM` and local bijectivity of its composite suffice.
Working over the restricted coefficient rings also removes the localized-ring
comparison step. In particular no claim that an arbitrary label on an empty
member is annihilated by `I` is needed or made.

The current blueprint proof of `thm-exc-explicit-preservation`, paragraph 2, no
longer spells out the quotient-label argument attributed to that paragraph by
the inherited source metadata. The assigned, already reviewed quotient-label
statement remains unchanged; the updated proof origin records its direct
constant-presheaf/sheafification argument (Stacks 093I and 093J). No target,
statement, public definition, adopted-source declaration, or unit route is changed.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
