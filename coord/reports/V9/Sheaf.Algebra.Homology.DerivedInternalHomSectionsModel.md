## What changed

Proved `CategoryTheory.DerivedInternalHomSectionsModel.tensorRightAdjoint_iso`
with its original signature, retaining the inherited proof. Choose a K-flat representative
of K and use `ringedDerived_closed_symmetric_monoidal` and its natural tensor comparison.
Fully faithful precomposition with derived localization identifies T with tensorLeft K;
symmetry and uniqueness of right adjoints identify H with the recorded internal Hom.
Updated the proof docstring and the existing node's proof, proof_deps and proof_origin.
On resumption, checked the current signatures and compiled the delivered module cleanly
with lcompile.py (9.3 seconds). Removed the superseded tensor-Hom/Yoneda proof steps
from the node; the open sections argument retains its own full proof plan.
No definition, statement, universe, visibility or target changed.

The existing closed monoidal theorem (node
`lem-sf-ringed-derived-closed-symmetric-monoidal`) is used as a generic tool for its
already stated adjunction and one-K-flat tensor comparison. It has no import path back
to this item. This use preserves the unit's tensor-Hom argument; no unit statement or
step is replaced. No maintainer tool approvals were edited.

## Proved and sorry left

Closed: `CategoryTheory.DerivedInternalHomSectionsModel.tensorRightAdjoint_iso`,
node `lem-sfb-derived-internal-hom-sections-model`.

Unchanged hole:
`CategoryTheory.DerivedInternalHomSectionsModel.derived_internalHom_sections_model`,
node `lem-sfb-derived-internal-hom-sections-model`. It still needs the natural
representative and full derived-sections comparisons. Its source and proof in words
remain in the declaration docstring. The saved scratchpad contains an experimental
global-cochain comparison and all-degree assembly, but those experiments are outside
the delivery and introduce no declarations or holes into the library.

Original holes: two. Closed: one. Added: zero. Delivered holes: one.

## No longer needed

Removed direct proof imports `Sheaf.Algebra.Homology.QuasiIsoHomComplexMap`,
`Sheaf.Algebra.Homology.KInjectiveHomComplex`,
`Sheaf.Algebra.Homology.HomComplexGlobalHomotopy`,
`Sheaf.Algebra.Homology.HomTensorTotal`,
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`,
`Mathlib.Algebra.Homology.BifunctorShift`, and
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`.
The tensor proof uses the stated closed monoidal theorem instead of reconstructing its
adjunction. Nodes `lem-pur-rhom-well-defined`, `lem-pur-hom-kflat-into-kinjective`,
`lem-pur-hom-complex-global-homotopy`, `lem-sc-derived-hom-tensor-total`, and
`prop-pur-kinjective-resolutions-exist` are not used directly by this tensor proof;
the invariance, K-injectivity, global-homotopy and resolution nodes remain
dependencies of the open sections argument.
The node no longer directly depends on `lem-sc-derived-hom-tensor-total` or
`def-pc-tensor-complex-sheaves` for its proof, since the closed theorem supplies the
adjunction. The former approval was removed from `tool_uses`; it is still used
transitively by the imported closed theorem, and the tensor-complex definition remains
a statement dependency. The obsolete direct tensor-Hom and Yoneda proof steps were removed.
No existing module or node is claimed globally unnecessary or withdrawn.
The provisional `KInjectiveInternalHomComparisons` module and node are retained only
in scratchpad and are excluded from the delivery.

## Where the brief, the DAG or earlier work was wrong

The existing closed monoidal theorem already provides the tensor comparison and
adjunction needed for the first theorem, giving a shorter proof than reconstructing
the tensor-Hom bijection. The DAG now records that route and retains the original
sections argument for the unchanged open theorem. The delivery closes one existing
hole and adds none; it does not claim completion of the full sections comparison.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
