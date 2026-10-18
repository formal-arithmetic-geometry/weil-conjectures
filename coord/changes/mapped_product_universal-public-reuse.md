# CategoryTheory.mapped_product_universal

## Reason

The returned U1 delivery copied two private proved lemmas from
`Sheaf.CategoryTheory.ColimitSiteCechTransport`. Expose its existing
`mapped_product_universal` theorem and import it in the acyclicity proof.
Delete both duplicate private lemmas from the item module. The transport module
is unclaimed (checked against coord/claims on 2026-10-18). Its existing proof and
all hypotheses and conclusions are unchanged; only this theorem's visibility
changes. `product_ext` remains private in its original module. A source docstring
is added to the exposed theorem.

## Old

```lean
private theorem mapped_product_universal {C D : Type u} [Category C] [Category D]
    {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
    (S : SiteCechComplex f hom) (A : C ⥤ D)
    (hp : ∀ (t : T) (Z : C) (g : Z ⟶ U), PreservesLimit (cospan (hom t) g) A)
    (p : ℕ) (t : Fin (p + 1) → T) (Z : D)
    (a : ∀ k, Z ⟶ A.obj (f (t k)))
    (ha : ∀ k, a k ≫ A.map (hom (t k)) = a 0 ≫ A.map (hom (t 0))) :
    ∃! b : Z ⟶ A.obj (S.W p t), ∀ k, b ≫ A.map (S.pr p t k) = a k
```

## New

```lean
theorem mapped_product_universal {C D : Type u} [Category C] [Category D]
    {T : Type u} {U : C} {f : T → C} {hom : ∀ t, f t ⟶ U}
    (S : SiteCechComplex f hom) (A : C ⥤ D)
    (hp : ∀ (t : T) (Z : C) (g : Z ⟶ U), PreservesLimit (cospan (hom t) g) A)
    (p : ℕ) (t : Fin (p + 1) → T) (Z : D)
    (a : ∀ k, Z ⟶ A.obj (f (t k)))
    (ha : ∀ k, a k ≫ A.map (hom (t k)) = a 0 ≫ A.map (hom (t 0))) :
    ∃! b : Z ⟶ A.obj (S.W p t), ∀ k, b ≫ A.map (S.pr p t k) = a k
```

## Users

`tools/downstream.py Sheaf.CategoryTheory.ColimitSiteCechTransport --uses
mapped_product_universal` reports only its declaring module. There are seven
transitive downstream modules, and only `ColimitSiteCechComplex` imports this
module directly. No existing downstream statement or definition changes meaning.
The acyclicity module is the new consumer and uses the universal property to
construct the image Cech complex.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.ColimitSiteCechTransport | unclaimed | expose existing proved helper |
| Sheaf.CategoryTheory.Sites.DirectImageInjectiveEvaluationAcyclic | U1 | import shared helper; remove duplicates |

The existing direct consumer `Sheaf.CategoryTheory.ColimitSiteCechComplex` is
compiled unchanged against the modified transport module. All target signatures
and definitions retain their meaning; no target statement review is reopened.

## Status

landed 20261018T071231-L-1680332 2026-10-18 (merge of deliver/U1/Sheaf.CategoryTheory.Sites.DirectImageInjectiveEvaluationAcyclic)
