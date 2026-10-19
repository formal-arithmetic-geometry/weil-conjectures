# CategoryTheory.derivedLocalHomRestriction_laws

## Reason

The delivery checker classifies section-scoped `variable` commands for new private proof
helpers as an interface change and requires this record. These variables are all inside closed
sections before the original namespace. The original variables and all public signatures are
unchanged. The helpers establish exact-functor identity/associativity coherence and conjugation
calculations used to prove the existing restriction laws. Additional fully proved private
helpers establish the binary sheafification extension universal property and construct local
Hom/Isom composition maps; no private declaration occurs in a public signature or definition.

## Old

No private exact-functor coherence helper sections in this module. The six affected theorem
bodies were `by sorry`.

## New

Private helper sections `ExactFunctors`, `ExactAssociativity`, and `ExactIdentity`, with their
scoped variables, precede the original `CategoryTheory` namespace. Each section closes before
that namespace; no helper variables enter any public declaration. All existing signatures,
visibility, definitions and instance attributes remain identical. The only added import is
proof-only: `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DerivedMorphismPresheaf | C7 | Six theorem proofs completed; no public signature changed. |
| Sheaf.AlgebraicGeometry.DerivedMorphismSheafComparison | unchanged consumer | Imports and public signatures remain identical; no adaptation required. |
| Sheaf.AlgebraicGeometry.DerivedMorphismWeaklyContractibleEvaluation | unchanged consumer | Imports and public signatures remain identical; no adaptation required. |

## Status

landed 20261019T002519-L-2145463 2026-10-19 (merge of deliver/C7/Sheaf.CategoryTheory.DerivedMorphismPresheaf)
