# Shared affine comparison geometric helpers

## Reason

The returned delivery duplicated `affineProEt_cechNerve` and
`affineProEt_finite_refinement`, whose existing proofs belong to
`Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing`. That module is unclaimed
at repair time. Remove `private` from these two theorems in place so the categorical
vanishing module can import and reuse them. Their new public signatures require the explicit public import
`WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale` and
`WeilConjectures.CategoryTheory.Sites.CechComplex`, which were previously
available only privately. Apart from this public import and their visibility, the binders,
conclusions, proof bodies and existing abelian-group vanishing theorem are identical.
No target statement or definition changes.

## Old

The module did not publicly import `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`
or `WeilConjectures.CategoryTheory.Sites.CechComplex`.

```lean
private theorem affineProEt_cechNerve (Y : Scheme.{u}) [IsAffine Y]
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ i, proAffineEtale (U i).left.hom) (k : ℕ)
    (y : Fin (k + 1) → Fin n) :
    proAffineEtale (Presheaf.cechNerveObj U y).left.hom
```

```lean
private theorem affineProEt_finite_refinement (Y : Scheme.{u}) [IsAffine Y]
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    (R : Sieve V) (hR : R ∈ Scheme.ProEt.topology Y V) :
    ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ i, proAffineEtale (U i).left.hom) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
        Scheme.ProEt.topology Y V
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import WeilConjectures.CategoryTheory.Sites.CechComplex
```

```lean
theorem affineProEt_cechNerve (Y : Scheme.{u}) [IsAffine Y]
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    {n : ℕ} (U : Fin n → Over V)
    (hU : ∀ i, proAffineEtale (U i).left.hom) (k : ℕ)
    (y : Fin (k + 1) → Fin n) :
    proAffineEtale (Presheaf.cechNerveObj U y).left.hom
```

```lean
theorem affineProEt_finite_refinement (Y : Scheme.{u}) [IsAffine Y]
    (V : Y.ProEt) (hV : proAffineEtale V.hom)
    (R : Sieve V) (hR : R ∈ Scheme.ProEt.topology Y V) :
    ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ i, proAffineEtale (U i).left.hom) ∧ (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈
        Scheme.ProEt.topology Y V
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing --direct
--uses affineProEt_finite_refinement` finds no existing direct importer and only the
module's own uses. Searching for `affineProEt_cechNerve` likewise finds only its own
uses. The new categorical consumer is delivered and compiled in the same sandbox.
No existing consumer requires adaptation. The item theorem's signature is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineComparisonInjectiveVanishing | unclaimed | Publicly import the helper signature dependency and remove private from the two helpers; proofs and internal uses unchanged. |
| Sheaf.AlgebraicGeometry.AffineComparisonInjectiveDerivedVanishing | H4 | Remove duplicate private helpers and import the existing public helpers. |

## Status

landed 20261016T090411-L-1838030 2026-10-16 (merge of deliver/H4/Sheaf.AlgebraicGeometry.AffineComparisonInjectiveDerivedVanishing)
