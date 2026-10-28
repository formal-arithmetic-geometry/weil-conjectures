# AlgebraicGeometry.Scheme.lisseTower_localized_constants_normalization

## Reason

Repair the false universal claim already diagnosed by X8. A family of arbitrary
objectwise model isomorphisms carries no compatibility; negating one level changes
one side of the square. Levelwise naturality alone does not solve that problem.
The repaired theorem proves the localization and naturality step from natural
models and their coefficient identity on represented complexes. The parent obtains
those two pieces of data together. Its signature is unchanged.

## Old

```lean
theorem lisseTower_localized_constants_normalization
    {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (model : ∀ (n : ℕ)
      (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n))),
      ((ProEtale.upperStar
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) b).mapDerivedCategory ⋙
          lisseTowerFixedRealization g d n).obj
        ((localProEtaleComparison a (lisseTowerEtaleRing d n)).obj
          ((normalizationConstant S.smallEtaleTopology).obj E)) ≅
        (constantAdicQuotientRealization g d n).obj E) :
    ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection g d j)
    let c (j : ℕ) (N : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))) :=
      (H j).mapIso (model j N) ≪≫
        ((constantAdicQuotientRightIso g d j).app N).symm
    (H (n + 1)).map ((
      (ProEtale.upperStar
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) b).mapDerivedCategory ⋙
        lisseTowerFixedRealization g d (n + 1)).map
      (localProEtaleNormalization a (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow S.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k))) ≫
      (lisseTowerPulledScalarIso g b d n).hom.app
      ((localProEtaleComparison a
        (lisseTowerEtaleRing d n)).obj
          ((normalizationConstant S.smallEtaleTopology).obj E')) ≫ (c n E').hom =
      (c (n + 1) E).hom ≫
        (constantAdicFiniteRealization g d).map (lisseTowerAlgebraArrow d n k)
```

## New

```lean
theorem lisseTower_localized_constants_normalization
    {X Z T S : Scheme.{u}} (g : Z ⟶ X) (a : T ⟶ S) (b : Z ⟶ T)
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (model : ∀ n : ℕ,
      lisseTowerConstantInput g a b d n ≅ constantAdicQuotientRealization g d n)
    (hmodel : ∀ (n : ℕ)
      (K : CochainComplex (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)) ℤ),
      ((lisseTowerConstantScalarIso g a b d n) ≪≫
        lisseTowerConstantModelIso g a b d n (model n)).hom.app (DerivedCategory.Q.obj K) =
      (Functor.isoWhiskerLeft (normalizationModuleRestrict (lisseTowerEtaleQuotient d n))
          (lisseTowerConstantModelIso g a b d (n + 1) (model (n + 1))) ≪≫
        Functor.isoWhiskerRight (lisseTowerAlgebraRestrictIso d n)
          (constantAdicFiniteRealization g d)).hom.app (DerivedCategory.Q.obj K)) :
    ∀ (n : ℕ)
    (E : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))))
    (E' : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d n)))
    (k : E ⟶ (normalizationModuleRestrict (lisseTowerEtaleQuotient d n)).obj E'),
    let H (j : ℕ) := pbcDerivedRestrict (constantAdicFiniteProjection g d j)
    let c (j : ℕ) (N : DerivedCategory (ModuleCat.{u + 1} (lisseTowerEtaleRing d j))) :=
      (H j).mapIso ((model j).app N) ≪≫
        ((constantAdicQuotientRightIso g d j).app N).symm
    (H (n + 1)).map ((
      (ProEtale.upperStar
        (ModuleCat.{u + 1} (lisseTowerEtaleRing d (n + 1))) b).mapDerivedCategory ⋙
        lisseTowerFixedRealization g d (n + 1)).map
      (localProEtaleNormalization a (lisseTowerEtaleQuotient d n)
        (normalizationConstantArrow S.smallEtaleTopology (lisseTowerEtaleQuotient d n)
          k))) ≫
      (lisseTowerPulledScalarIso g b d n).hom.app
      ((localProEtaleComparison a
        (lisseTowerEtaleRing d n)).obj
          ((normalizationConstant S.smallEtaleTopology).obj E')) ≫ (c n E').hom =
      (c (n + 1) E).hom ≫
        (constantAdicFiniteRealization g d).map (lisseTowerAlgebraArrow d n k)
```

The item's module also adds four concrete composition definitions and the general
categorical pasting helper `lisseTowerPasteConstantScalar`, all without holes.
The old private sign diagnostics and their proof-only ZMod import are removed;
the X8 report retains their counterexample and the original faulty signature.

`Sheaf.Paper.LisseTowerConstantComplexComparisons` adds the remaining construction
lemma, with one named hole. It supplies natural models and tests only identity
coefficient arrows at Q(K). The proved criterion handles every other derived k.
This is a decomposition and interface repair, not a proof of the false statement.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.LisseTowerLocalizedConstantsNormalization | H3 | Corrected theorem and explicit natural coefficient paths; no holes remain. |
| Sheaf.Paper.LisseTowerLocalizedConstants | unclaimed | Same signature; obtain jointly coherent natural comparisons and take components. |
| Sheaf.Paper.LisseTowerConstantComplexComparisons | new in this delivery | States the remaining canonical construction and identity coefficient equation on represented complexes. |

`tools/downstream.py --uses` finds the first two existing modules as the only
users of the changed theorem name. The only existing direct importer of the item
is LisseTowerLocalizedConstants. Its direct importer is LisseTowerLocalizedRealization.
Their theorem signatures, target statements, existing definitions, instances and
attributes are unchanged. The parent and its unchanged direct consumer both compiled against this packet
(14.2 and 20.3 seconds). The temporary unchanged consumer copy was removed.
The delivery also runs the related-module check.

The old model-existence module is held by X7 and is not edited. Its import and DAG
proof dependency are pruned from the parent because objectwise nonemptiness is
insufficient for this argument. No source-library declaration is changed.

## Status

landed 20261028T072415-L-1943844 2026-10-28 (merge of deliver/H3/Sheaf.Paper.LisseTowerLocalizedConstantsNormalization)
