## What changed

Prove `SheafOfModules.scalarExtension_constraint_coherence` using the existing normalized binary
scalar-extension isomorphism and scalar-multiplication unit isomorphism in
`Sheaf.Paper.ScalarExtensionBinaryCoherence`. Private identity comparisons identify the two
presentations of scalar extension and identify the explicit site tensor with the existing
localization tensor. Their section formulas transport the library's forward and inverse formulas.
Private generator equality tests prove uniqueness and naturality. The existing proved
`tensor_trilinear_universal` supplies the equality test for nested tensors. The actual monoidal associator
and unitors give the three oplax equations; cancellation gives the three lax equations.

All existing public definitions, signatures and fields are preserved. The construction chooses
no arbitrary witness. The DAG and theorem proof explanation record the route actually used.

## Proved and sorry left

Closed: `SheafOfModules.scalarExtension_constraint_coherence`, the item's original single hole.
Holes added: none. Holes left in the delivered module: none. No new statement is split off.
The complete single-module proof compiled without errors or warnings in 38.2 seconds.
The final module's axiom check and delivery validation are recorded by the delivery tool.

## No longer needed

Removed direct imports:

- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`.
- `Mathlib.LinearAlgebra.TensorProduct.Map`.
- The temporary proof import `Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction`
  is also unnecessary after reusing the library comparison.

This proof does not use the declarations of
`lem-pc-sites-sheaf-tensor-bilinear-universal`,
`lem-pc-sites-module-sheafification-bilinear-extension`, or
`lem-pc-sheaf-modules-tensor-closed`. The first two are replaced by the existing proved binary
comparison and direct sheafification equality tests. The monoidal API from
`CochainTensorUniverses` supplies the associator and unitors, without the closed tensor-Hom
package. The closed tensor node remains a statement dependency for the canonical conventions.
All three nodes are removed only from this item's proof requirements, and their obsolete
top-level tool-use approvals are pruned. No source declaration is removed and no global withdrawal is claimed.

The final construction also needs no separate presheaf inverse pairing or separate proof of
its inverse identities: the proved binary scalar-extension isomorphism already contains them.

## Where the brief, the DAG or earlier work was wrong

The planned bilinear helper statements have more restrictive universe conventions than this
item. The existing binary comparison and site-tensor presentation work with independent site
and coefficient universes and give a shorter route. The seven mathematical steps remain
represented. Nested equality follows by transporting the existing proved trilinear equality criterion,
without assuming that arbitrary sheaf sections are global sums of pure tensors.

The formulas cover identity coefficient maps, zero rings and modules, non-flat coefficient maps,
empty sites and empty covers. No extra hypothesis is introduced.

## Second reading by H7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
