# PresheafOfModules.sheafification_tensorHom_isIso

## Reason

The descent node cites the sheaf tensor definition for its sectionwise presheaf tensor.
That notion belongs to `def-pur-presheaf-tensor-product`. Correcting this citation also
avoids a spurious cycle when the sheaf monoidal localization proof uses the descent theorem.
No Lean signature, definition, visibility, or public import changes.

## Old

Verbatim old node statement:

```text
Let C be a category, J a Grothendieck topology on C, R a presheaf of commutative rings whose underlying ring presheaf is a J-sheaf, and P,Q,N presheaves of R-modules [def-weil-sheaf-of-modules-category]. All site, ring and module universes are independent. Suppose $f:P\to Q$ is locally injective and locally surjective for J. Assume weak sheafification of abelian-group-valued presheaves in the module universe and that J-local equivalences of such presheaves are exactly the locally bijective maps. Then the module sheafification [def-weil-presheaf-modules-sheafification] of f tensor id_N, for the sectionwise tensor product [def-pur-sheaf-tensor-product], is an isomorphism.
```

Its corresponding statement/proof edges include `def-pur-sheaf-tensor-product`.

## New

Verbatim new node statement:

```text
Let C be a category, J a Grothendieck topology on C, R a presheaf of commutative rings whose underlying ring presheaf is a J-sheaf, and P,Q,N presheaves of R-modules [def-weil-sheaf-of-modules-category]. All site, ring and module universes are independent. Suppose $f:P\to Q$ is locally injective and locally surjective for J. Assume weak sheafification of abelian-group-valued presheaves in the module universe and that J-local equivalences of such presheaves are exactly the locally bijective maps. Then the module sheafification [def-weil-presheaf-modules-sheafification] of f tensor id_N, for the sectionwise tensor product [def-pur-presheaf-tensor-product], is an isomorphism.
```

The sectionwise tensor citation and those edges are `def-pur-presheaf-tensor-product`.
All mathematical content and the declaration `PresheafOfModules.sheafification_tensorHom_isIso`
are unchanged. Its existing four DAG citers remain valid, as recorded in statement_change.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses | unclaimed | Its Lean file and signature are unchanged. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses | C2 | Uses the proved descent theorem; all six original signatures and public imports are unchanged. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses | unclaimed | Identical Lean dependency; no effect. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses | unclaimed | Identical Lean dependency; no effect. |
| Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses | unclaimed | Identical Lean dependency; no effect. |
| Sheaf.CategoryTheory.RingedSliceExtensionTensorHomData | unclaimed | Identical Lean dependency; no effect. |

No consumer adaptation is needed: only a DAG definition citation changes. All other users
continue importing the identical compiled descent declaration.

## Status

landed 20261018T145053-L-3636203 2026-10-18 (merge of deliver/C2/Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses)
