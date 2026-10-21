# CochainComplex.exists_subcategory_left_resolution

## Reason

The proof adds a namespace for proved private helpers, a section variable command,
`omit [Abelian A] in`, and two declaration-local transparency options. Preflight
conservatively classifies these commands as an interface change. This record documents
their scope and every downstream module. The public theorem signature and public imports
are identical; every added declaration is private. All definitions construct their data
explicitly, and all helper theorems have complete proofs. No consumer needs adaptation.

## Old

```lean
theorem exists_subcategory_left_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (P : C → Prop) (hzero : ∃ Z : C, P Z ∧ IsZero Z)
    (hcover : ∀ X : C, ∃ (Y : C) (p : Y ⟶ X), P Y ∧ Epi p)
    (a : ℤ) (K : CochainComplex C ℤ)
    (hK : ∀ n : ℤ, a < n → IsZero (K.X n)) :
    ∃ (L : CochainComplex C ℤ) (f : L ⟶ K),
      QuasiIso f ∧ (∀ n : ℤ, P (L.X n)) ∧ (∀ n : ℤ, Epi (f.f n)) ∧
        (∀ n : ℤ, a < n → IsZero (L.X n))
```

The body is `by sorry`. There is no `SubcategoryResolution` helper namespace.
Public imports are `Mathlib.CategoryTheory.Abelian.Basic` and
`Mathlib.Algebra.Homology.DerivedCategory.Basic`.

## New

```lean
theorem exists_subcategory_left_resolution
    {C : Type u} [Category.{v} C] [Abelian C]
    (P : C → Prop) (hzero : ∃ Z : C, P Z ∧ IsZero Z)
    (hcover : ∀ X : C, ∃ (Y : C) (p : Y ⟶ X), P Y ∧ Epi p)
    (a : ℤ) (K : CochainComplex C ℤ)
    (hK : ∀ n : ℤ, a < n → IsZero (K.X n)) :
    ∃ (L : CochainComplex C ℤ) (f : L ⟶ K),
      QuasiIso f ∧ (∀ n : ℤ, P (L.X n)) ∧ (∀ n : ℤ, Epi (f.f n)) ∧
        (∀ n : ℤ, a < n → IsZero (L.X n))
```

The body is now fully proved. Public imports are the same. The added commands are scoped
within the closed namespace `CochainComplex.SubcategoryResolution`:

```lean
variable {A : Type u} [Category.{v} A] [Abelian A]
```

`omit [Abelian A] in` applies only to the private `cover_transport` theorem.
`set_option backward.isDefEq.respectTransparency false in` applies separately only to the
private `indexed_augmentation` and `indexed_differential` theorems. No global option,
notation, attribute, instance or public declaration is added. The existing outer universe,
open and `autoImplicit` commands are unchanged.

## Users

`tools/downstream.py Sheaf.Algebra.Homology.SubcategoryLeftResolution --uses
CochainComplex.exists_subcategory_left_resolution` lists the eight downstream modules below;
the declaration-name text search additionally lists the item itself. Direct importers are
SubcategoryTruncationResolutionSystem and RingDerivedDualizablePerfect. Existing statements,
definitions and proof requirements retain their meaning because the theorem's full signature
and public imports do not change. All helper commands have scope ending before that theorem.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.SubcategoryLeftResolution | Z7 | One proof completed; no signature change. |
| Sheaf.Algebra.Homology.SubcategoryTruncationResolutionSystem | K7 | No adaptation. |
| Sheaf.AlgebraicGeometry.CondensedDualizableLocalPerfectModels | unclaimed | No adaptation. |
| Sheaf.AlgebraicGeometry.CondensedHenselianLisseRigidity | unclaimed | No adaptation. |
| Sheaf.AlgebraicGeometry.CondensedWContractibleLisseEvaluation | unclaimed | No adaptation. |
| Sheaf.AlgebraicGeometry.ContractibleLisseEvaluation | unclaimed | No adaptation. |
| Sheaf.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect | K7 | No adaptation. |
| Sheaf.CategoryTheory.DerivedCategory.UnboundedKFlatResolution | F7 | No adaptation. |
| Sheaf.Paper.TAdmissibleDualizableTruncations | unclaimed | No adaptation. |

No target signature or definition used in a target statement changes. The consumer source
files are not included in this packet.

## Status

landed 20261021T130246-L-2664556 2026-10-21 (merge of deliver/Z7/Sheaf.Algebra.Homology.SubcategoryLeftResolution)
