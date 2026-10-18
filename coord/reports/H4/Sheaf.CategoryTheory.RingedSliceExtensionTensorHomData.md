## What changed

Proved `SheafOfModules.ringedSlice_extension_tensor_hom_data` by composing the
extension adjunction, module sheafification adjunctions, a direct-sum tensor Hom
equivalence, and tensor descent through the sheafification unit. Both naturality
laws are proved, including simultaneous maps in the two module parameters.
The two public functor definitions and theorem signature are unchanged.

The direct-sum construction is generalized privately to the theorem's independent
object universe. Its bilinear map has an irreducible implementation with a proved
generator formula, avoiding repeated unfolding of that construction.
The proof imports `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses`.
The DAG proof and dependency list now follow this route. A private natural
isomorphism identifies the two restriction models by identity maps on section
tensors; this avoids unfolding sheafification when comparing the public functors.
The complete module compiled standalone in 50.1 seconds. The final delivery compile
and axiom probe subsequently passed at normal limits after the unit and coefficient
annotations were simplified. Preflight requested a record of the new proof scopes:
`coord/changes/h4-ringed-slice-tensor-hom-private-scopes.md` documents their private
scope and all 13 downstream consumers. No consumer is changed. The existing public
definitions and theorem signature were compared verbatim with the originals.

## Proved and sorry left

Closed 1 original hole: `SheafOfModules.ringedSlice_extension_tensor_hom_data`
(node `new-ringed-slice-extension-tensor-hom-data`). Added 0 holes; split off 0
obligations. No `sorry` remains in the delivered module. Every private helper is
proved or explicitly constructed.

## No longer needed

Removed these proof imports and their planned dependencies for this item:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed`, node
  `lem-pc-sheaf-modules-tensor-closed`: the sectionwise bilinear construction
  replaces tensor-Hom currying through an internal Hom sheaf.
- `Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact`, node
  `lem-pur-site-restriction-module-adjunction-exact`: only an adjunction is needed,
  and its direct-sum proof is generalized privately to the present universes.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`, node
  `def-pur-sheaf-hom`: the proof never forms internal Hom or its restriction
  comparison.

The blueprint unit's statement and realized steps are unchanged. These removals
are dependencies of this item; other targets may still need those modules.

## Where the brief, the DAG or earlier work was wrong

The original planned tensor-closed interface fixes the site object universe to the
coefficient universe. The localized-module exact-adjunction interface additionally
uses a small site presented by a precoverage. The assigned theorem has neither
restriction. The direct-sum adjunction and generator construction apply under its
actual hypotheses and avoid changing any statement. Existing tensor-local-bijection
descent already supports the independent universes needed for the last comparison.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
