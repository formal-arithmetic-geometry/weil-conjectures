# SheafOfModules.scalarTensor_inverse_formulas: private proof support commands

## Reason

The theorem is proved without changing its type. The static preflight reports the new
`open scoped`, section `variable`, elaborator settings and changed local irreducibility
commands as an interface change and requires this record. These commands support proved
private helpers. The added variables are confined to `section Calculus`; all added
helper declarations are private. The two elaborator options and local reducibility
attributes affect elaboration of this file. No public signature, public definition,
instance or public import changes. No downstream statement changes meaning.

## Old

The original command block before the theorem was:

```lean
open CategoryTheory

namespace SheafOfModules

attribute [local irreducible] changeOfRingsOfUniverses siteSheafTensorRight
  scalarExtensionRingIsoTmul siteSheafTensorTmul
```

The theorem `scalarTensor_inverse_formulas` then had its original signature and a
single `sorry` body.

## New

The existing `open CategoryTheory` and namespace are retained. The private proof
calculus is scoped by these commands (private declarations occur between them):

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open scoped ChangeOfRings TensorProduct
```

```lean
section Calculus
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
```

```lean
end Calculus

attribute [local irreducible] siteSheafTensorRight
```

The existing theorem has exactly the original signature, checked after whitespace
normalization, and now has a complete proof. Scalar-extension objects and pure-tensor
sections remain transparent for the unit computation; the tensor functor stays locally
irreducible to keep statement elaboration small. The private helpers construct actual
presheaf morphisms and factor them using the sheafification adjunction.

The unused private proof import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal` is replaced
by the directly used
`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafifyBilinearExtUniqueness`.
The bilinear extension import and all original public imports are retained.

## Users

`tools/downstream.py` lists one downstream module and only the item's own declaration
as a textual user of `scalarTensor_inverse_formulas`.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarTensorInverseFormulas | G6 | The original statement is proved; all supporting declarations are private. |
| Sheaf.SecSmoothPurity.CoefficientComparisonsBalancedConstruction | unclaimed (current queue) | It imports the item but does not yet mention the theorem; all statements and definitions remain identical. No adaptation. Compiled unchanged against this proof. |

No public definition changes and no target statement re-review is needed. The DAG
update changes only the proof route, dependencies, origin and removal of the unused
tensor-universal tool approval; it does not change any statement.

## Status

landed 20261022T202021-L-1249687 2026-10-22 (merge of deliver/G6/Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarTensorInverseFormulas)
