## What changed

Proved `CategoryTheory.InternalModuleInverseImage.internalModuleInverseImageComparison` in
`Sheaf.CategoryTheory.InternalModuleInverseImageComparison`, with its statement unchanged.
The proof implements node steps 4–6 after taking the tensor normalization and mate identity
from the existing `inverseBraided_existsUnique` declaration (node steps 1–3).

Private, proved helpers construct the universal generalized pair of sections using the
inverse product comparison. The addition graph, tensor pairing graph, and constant-one
graph transport the normalization equations to arbitrary ring multiplication and module
scalar-action maps. The ring comparison is explicitly additive, multiplicative and unital;
its underlying isomorphism reflects to an isomorphism of ring sheaves. The module comparison
is explicitly additive and semilinear, respects restriction maps, and is natural in module
morphisms. Its underlying map satisfies the prescribed ULift formula. Applying the natural
isomorphism to complexes proves the differential equations; whiskering with the derived
localization gives exactly the required derived comparison. Preservation of zero morphisms
comes from the supplied abelian adjunction and transport across the module isomorphism.

Added the private proof import `Mathlib.CategoryTheory.Sites.CartesianMonoidal` for the actual
product comparisons and sectionwise products. All public imports, original definitions,
public signatures, universes and hypotheses are retained. No source-library files or
consumers are changed. The node's existing six-step route and unit realization are retained;
there are no new mathematical dependencies, public declarations, or nodes.

Change record: `coord/changes/internal-module-inverse-image-private-scopes-H3.md`. The static
checker requests this record for declaration-scoped `omit ... in` commands on the private
helpers. It lists every downstream module and explains why no adaptation is required.

## Proved and sorry left

Closed 1 of the 3 original holes:

- `CategoryTheory.InternalModuleInverseImage.internalModuleInverseImageComparison`.

Added 0 holes; split off 0 statements. The following 2 original named theorem holes remain
unchanged, both belonging to `lem-sfb-internal-module-inverse-image-comparison`:

- `CategoryTheory.InternalModuleInverseImage.directLax_existsUnique` (step 1).
- `CategoryTheory.InternalModuleInverseImage.inverseBraided_existsUnique` (steps 2–3).

The completed comparison uses the second declaration's conclusions; this delivery therefore
proves the comparison from the retained tensor-structure existence/uniqueness statements.
Every new private declaration is proved. There is no new `sorry` in a definition or proof.
The final file compiled cleanly through `lcompile.py` in 32.4 seconds after removing unused
imports and a dead private helper. Delivery checks compile and audit the packet again.

## No longer needed

Removed these unused private proof imports:

- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
- `Mathlib.CategoryTheory.Monoidal.CommGrp_`.
- `Mathlib.CategoryTheory.Adjunction.Limits`.
- `Mathlib.CategoryTheory.Sites.Sheafification`.

The completed comparison uses the given normalized tensor structure directly. It does not
need a new tensor universal-property argument, a new lifted algebraic adjunction, or another
sheafification construction. No DAG node or module is withdrawn: the original tensor
universal-property, adjunction and sheafification dependencies remain relevant to the two
retained construction holes, so their dependencies and tool approval are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement error or route change was found. The general site-induced pullback tensor
results found by search do not directly apply to an arbitrary geometric morphism with the
specified abelian presentation. The proof uses the actual product comparison on set sheaves
and all generalized sections; it never assumes a section of a sheafified tensor is globally
a pure tensor. The ULift comparisons require explicit inverse maps and explicit carrier
annotations when assembling ring and linear maps; these are implementation details and do
not change any statement.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
