# WeilConjectures.CartesianSectionAdjoint.normalizedSupportEtalePresentation

## Reason

The existing normalized/enriched realization theorem does not assert the étale-origin
presentation required by CartesianSectionAdjointMates. Split that geometric transport
step from the comparison of arbitrary right adjoints. The new lemma assumes only the
actual proper/open support and its normalized left restriction; it does not assume the
assigned theorem, a normalized right adjoint, or an enriched isomorphism.

## Old

No declaration of this name or module existed. Every existing public signature,
definition body, attribute, and public import is preserved.

## New

```lean
theorem normalizedSupportEtalePresentation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] (c : Compactification f)
    {SX : CoefficientDerivedSystemCalculus l E X}
    {SZ : CoefficientDerivedSystemCalculus l E c.Z}
    {SY : CoefficientDerivedSystemCalculus l E Y}
    (S : Support l E c SX SZ SY)
    (F : (domain l E X).FullSubcategory ⥤ (domain l E Y).FullSubcategory)
    (e : F ⋙ (domain l E Y).ι ≅ (domain l E X).ι ⋙ S.functor) :
    ∃ (source : CartesianSectionData.Representability l E (X ↘ Spec (.of D.k)))
      (target : CartesianSectionData.Representability l E (Y ↘ Spec (.of D.k)))
      (support : Etale.SystemProjection.Support c (SystemInternalHom.coefficients l E))
      (right : SystemInternalHom.Et l E Y ⥤ SystemInternalHom.Et l E X)
      (adj : support.F ⊣ right)
      (left : F ⋙ (domain l E Y).ι ⋙ target.comparison.R ≅
        (domain l E X).ι ⋙ source.comparison.R ⋙ support.F)
      (counitIso : ∀ M : (domain l E X).FullSubcategory,
        IsIso (source.comparison.derivedAdjunction.counit.app M.obj))
      (preserves : ∀ N : (domain l E Y).FullSubcategory,
        domain l E X
          (source.comparison.P.obj (right.obj (target.comparison.R.obj N.obj))))
      (a : F ⊣ (domain l E X).lift
        ((domain l E Y).ι ⋙ target.comparison.R ⋙ right ⋙ source.comparison.P) preserves),
      ∀ (M : (domain l E X).FullSubcategory) (N : (domain l E Y).FullSubcategory)
        (h : F.obj M ⟶ N),
        (a.homEquiv M N h).hom =
          (@inv _ _ _ _ (source.comparison.derivedAdjunction.counit.app M.obj)
            (counitIso M)) ≫
          source.comparison.P.map
            (adj.homEquiv _ _ (left.inv.app M ≫ target.comparison.R.map h.hom))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CartesianSectionAdjointMates | Z5 | Private proof import. The proof constructs EtaleOrigin by right-adjoint uniqueness and the exact Hom formula. Its existing signatures and all conclusion clauses stay unchanged. |

The unchanged assigned module is imported by `Sheaf.Paper.RamifiedScalarSystemTranspose`;
its public interface remains identical and no adaptation is required.
There are no pre-existing users of this newly introduced declaration. No target
statement or definition changes. No consumer adaptation is necessary.

## Status

landed 20261025T102017-L-3767539 2026-10-25 (merge of deliver/Z5/Sheaf.Paper.CartesianSectionAdjointMates)
