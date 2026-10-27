## What changed

Filled the eight theorem proofs in `Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent`.
The word computation is proved first by induction, using the existing pullback preservation
and resolving-counit theorems. A single flat-term K-flat resolution then computes every word.
Private proved helpers extend normalized comparison maps through the homotopy category and its
localization. The expression induction proves identities, composition, both whiskerings,
associators and unitors; uniqueness gives all finite pasting equations and invertibility.

For the scalar formulas, the ordinary comparison is the uniqueness isomorphism between the
normalized extension/restriction adjunctions. Its transpose equation evaluates the map on
local pure tensors. The same localization helper constructs and uniquely characterizes the
derived comparison, with independent source, middle and target localization universes.
Added private proof imports supply the tensor presentation, ordinary scalar adjunction,
K-flat scalar preservation, and adjoint uniqueness. The DAG proof and dependencies record
this scalar route. All public signatures, public imports and definitions are preserved.
Private instance caches, direct equality compositions, and module-local priorities for
Mathlib's existing sheaf-composition instances avoid repeated expensive
instance searches and dependent rewrites; no typeclass attribute is exported. The four
instance-caching proofs use `letI` deliberately: inlining the canonical instances avoids
expensive dependent reduction that occurs with `let`. The corresponding style warning is
suppressed only on those declarations.

## Proved and sorry left

Closed the eight original holes, with no holes added and no split-off statements:

- `CategoryTheory.RingedKFlatWord.simultaneous_resolution`
- `CategoryTheory.RingedKFlatWord.word_computation`
- `CategoryTheory.RingedKFlatWord.descent_existsUnique`
- `CategoryTheory.RingedKFlatWord.determined_on_resolving`
- `CategoryTheory.RingedKFlatWord.cell_normalized`
- `CategoryTheory.RingedKFlatWord.word_comparison_descent`
- `CategoryTheory.RingedKFlatWord.scalar_associator`
- `CategoryTheory.RingedKFlatWord.scalar_unit`

There are no remaining `sorry` declarations in the delivered module and no new modules.

## No longer needed

Removed the unused private imports
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor` and
`Mathlib.LinearAlgebra.TensorProduct.Tower`.

The scalar proof does not use the direct construction through
`lem-pc-sites-module-sheafification-tensor` or
`lem-weil-pbc-module-tensor-cancel-base-change`; it uses the existing normalized ordinary
adjunction instead. These two dependencies and the direct tensor-construction dependency
`def-pur-sheaf-tensor-product` are removed from this node's proof dependency list. They are
not withdrawn from the library: other declarations may still need them, and the tensor
construction remains part of the definitions used by the scalar interfaces.
No node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No disputed statement or signature repair was needed. The resolution API expresses
termwise flatness through the monoidal tensor; the stated `IsFlatOnSite` predicate uses
the sectionwise presentation. Exactness is transported through the existing
`siteSheafTensorRightIso`. The scalar route in the original DAG is valid but unnecessary:
the normalized adjunction already provides the required ordinary map and pure-tensor
formula. The implementation retains the independent derived-category universes in the
original scalar statements.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
