# WeilConjectures.PurityFiniteSetting.FiniteTensorLineComparisonNormalized

## Reason

The signed-line family assembly took 41--68 seconds in kernel checking its concrete
normalization, even with the adjunction and object families supplied explicitly.
Its complete transpose equation needs a shared actual-data interface. Construct
`finiteTensorLineComparisonData` from exactly the original actual adjunction and the
entire original single-complex/restriction morphism. The generic `Pointwise` predicate
states the full original heterogeneous equality; `Normalized` is its conjunction over
all exponents. The normalization, pointwise witness and unique comparison theorem now
share that one datum. The full family assembly remains in the assigned item.
No equation, map, object, hypothesis or uniqueness assertion is dropped or weakened.
No data are chosen from an unproved theorem. `finiteTensorFixedLineMap` and its signature
and body stay verbatim.

## Old

```lean
def FiniteTensorLineComparisonNormalized (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) (c : P.FiniteTensorLineMaps m hm hmn T)
    (b : ∀ r : ℤ, (P.finiteTensorReduction m hm hmn T).obj (P.finiteTensorFixedLine T r) ≅
      (P.finiteReductionSetting m hm).finiteTensorFixedLine T r) : Prop :=
  ∀ r : ℤ,
    HEq ((P.finiteTensorAdjunction m hm hmn T).homEquiv _ _ (b r).hom)
    ((_root_.DerivedCategory.singleFunctor.{u + 1} _ 0).map
      (P.finiteTensorFixedLineMap m hm hmn T c r) ≫
    (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1}
      (sfFixedRestriction.{u, u + 1, u + 1} T
        (P.finiteReductionRingHom m hm hmn)) 0).inv.app
      ((sfIntrinsicModuleEquivalence T (P.finiteReductionSetting m hm).Ring).inverse.obj
        ((P.finiteReductionSetting m hm).finiteTensorLine T r)))
```

## New

```lean
@[irreducible] def finiteTensorLineComparisonData (P : PurityFiniteSetting.{u}) (m : ℕ)
    (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u}) :
    TransposedFamilyData (P.finiteTensorReduction m hm hmn T)
      (ProEtale.SupportedEtaleTensorOrigin.fixedRestriction
        (P.finiteReductionRingHom m hm hmn) T)
      (P.finiteTensorFixedLine T)
      ((P.finiteReductionSetting m hm).finiteTensorFixedLine T)
      (P.FiniteTensorLineMaps m hm hmn T) where
  adjunction := P.finiteTensorAdjunction m hm hmn T
  valueType := fun _ ↦ _
  value := fun c r ↦
    (_root_.DerivedCategory.singleFunctor.{u + 1} _ 0).map
      (P.finiteTensorFixedLineMap m hm hmn T c r) ≫
    (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1}
      (sfFixedRestriction.{u, u + 1, u + 1} T
        (P.finiteReductionRingHom m hm hmn)) 0).inv.app
      ((sfIntrinsicModuleEquivalence T (P.finiteReductionSetting m hm).Ring).inverse.obj
        ((P.finiteReductionSetting m hm).finiteTensorLine T r))

def FiniteTensorLineComparisonNormalized (P : PurityFiniteSetting.{u}) (m : ℕ) (hm : 1 ≤ m)
    (hmn : m ≤ P.level) (T : Scheme.{u}) (c : P.FiniteTensorLineMaps m hm hmn T)
    (b : ∀ r : ℤ, (P.finiteTensorReduction m hm hmn T).obj (P.finiteTensorFixedLine T r) ≅
      (P.finiteReductionSetting m hm).finiteTensorFixedLine T r) : Prop :=
  (P.finiteTensorLineComparisonData m hm hmn T).Normalized c b
```

Unfolding the actual record and the generic predicates recovers the old entire
formula: the very same `finiteTensorAdjunction.homEquiv`, `singleFunctor.map` of
`finiteTensorFixedLineMap`, and `mapDerivedCategorySingleFunctor.inv.app`. Its value
and value type are constructed from these actual terms. The generic pointwise uniqueness
API is proved by the same hom-equivalence injectivity and Iso.ext argument as before.
This definition is used by targets, so its meaning review is reopened.

The two existing pointwise statements below change only the representation of that
identical equation. The existence witness retains its existing named proof hole; it
is not counted as a proof or a newly introduced hole. Its source and natural-language
proof remain in the original docstring and node.

Old FiniteTensorLineDerivedExistenceWitness:

```lean
theorem exists_finiteTensorLineDerivedComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c) (r : ℤ) :
    ∃ b : (P.finiteTensorReduction m hm hmn T).obj (P.finiteTensorFixedLine T r) ≅
        (P.finiteReductionSetting m hm).finiteTensorFixedLine T r,
      HEq ((P.finiteTensorAdjunction m hm hmn T).homEquiv _ _ b.hom)
        ((_root_.DerivedCategory.singleFunctor.{u + 1} _ 0).map
          (P.finiteTensorFixedLineMap m hm hmn T c r) ≫
        (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1}
          (sfFixedRestriction.{u, u + 1, u + 1} T
            (P.finiteReductionRingHom m hm hmn)) 0).inv.app
          ((sfIntrinsicModuleEquivalence T (P.finiteReductionSetting m hm).Ring).inverse.obj
            ((P.finiteReductionSetting m hm).finiteTensorLine T r)))
```

New FiniteTensorLineDerivedExistenceWitness:

```lean
theorem exists_finiteTensorLineDerivedComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c) (r : ℤ) :
    ∃ b : (P.finiteTensorReduction m hm hmn T).obj (P.finiteTensorFixedLine T r) ≅
        (P.finiteReductionSetting m hm).finiteTensorFixedLine T r,
      (P.finiteTensorLineComparisonData m hm hmn T).Pointwise c r b
```

Old FiniteTensorLineDerivedExistence:

```lean
theorem existsUnique_finiteTensorLineDerivedComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c) (r : ℤ) :
    ∃! b : (P.finiteTensorReduction m hm hmn T).obj (P.finiteTensorFixedLine T r) ≅
        (P.finiteReductionSetting m hm).finiteTensorFixedLine T r,
      HEq ((P.finiteTensorAdjunction m hm hmn T).homEquiv _ _ b.hom)
        ((_root_.DerivedCategory.singleFunctor.{u + 1} _ 0).map
          (P.finiteTensorFixedLineMap m hm hmn T c r) ≫
        (Functor.mapDerivedCategorySingleFunctor.{u + 1, u + 1}
          (sfFixedRestriction.{u, u + 1, u + 1} T
            (P.finiteReductionRingHom m hm hmn)) 0).inv.app
          ((sfIntrinsicModuleEquivalence T (P.finiteReductionSetting m hm).Ring).inverse.obj
            ((P.finiteReductionSetting m hm).finiteTensorLine T r)))
```

New FiniteTensorLineDerivedExistence:

```lean
theorem existsUnique_finiteTensorLineDerivedComparison (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) (T : Scheme.{u})
    [T.Over (Spec (.of P.field.k))]
    (c : P.FiniteTensorLineMaps m hm hmn T)
    (hc : P.FiniteTensorLineMapsNormalized m hm hmn T c) (r : ℤ) :
    ∃! b : (P.finiteTensorReduction m hm hmn T).obj (P.finiteTensorFixedLine T r) ≅
        (P.finiteReductionSetting m hm).finiteTensorFixedLine T r,
      (P.finiteTensorLineComparisonData m hm hmn T).Pointwise c r b
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TransposedFamilyData | J2, new | Actual generic data, full pointwise and family predicates, proved pointwise uniqueness. |
| Sheaf.Paper.FiniteTensorReductionData | unclaimed | Constructs the actual shared transpose datum and uses its unchanged complete equation. |
| Sheaf.Paper.FiniteTensorSignedReduction | J2 | Same public signature and complete family assembly, using the shared predicate. |
| Sheaf.Paper.FiniteTensorLineDerivedExistenceWitness | unclaimed | Same full pointwise existence statement via the actual data; existing hole retained. |
| Sheaf.Paper.FiniteTensorLineDerivedExistence | unclaimed | Same unique comparison statement via the actual data; generic pointwise uniqueness proves the former argument. |

These are the direct identifier consumers found by repository search. All were
unclaimed when the interface repair began, except the assigned item held by J2.
No adopted source-library declaration or target signature changes. All original public
imports and docstrings are preserved; the parent adds the public generic-data import
needed by its new actual data definition. No new sorry is introduced by this repair.

## Status

landed 20261026T070008-L-3329438 2026-10-26 (merge of deliver/J2/Sheaf.Paper.FiniteTensorSignedReduction)
