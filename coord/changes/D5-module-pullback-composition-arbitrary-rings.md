# AlgebraicGeometry.Scheme.proEtaleConstantRingModulePullbackComposition

## Reason

The existing finite-ring restriction prevents reuse for AbsoluteFrobeniusSite,
whose statement allows every commutative coefficient ring. The complete existing
proof never uses finiteness. Stacks Tag 03D8, `lemma-push-pull-composition-modules`
(lines 1235--1250 of sites-modules.tex), applies to arbitrary ringed topoi.
The module is unclaimed. This is a generalization of a proved theorem, with its
proof and every other declaration unchanged; no hole is added or closed here.

## Old

```lean
theorem proEtaleConstantRingModulePullbackComposition
    {X Y Z : Scheme.{u}} (g : Z ⟶ X) (f : X ⟶ Y)
    (Λ : Type u) [CommRing Λ] [Finite Λ] :
    ∃ (a : proEtaleConstantRingPullback Λ (g ≫ f) ≅
        proEtaleConstantRingPullback Λ f ⋙ proEtaleConstantRingPullback Λ g),
      ∃ (d : proEtaleConstantRingPushforward Λ g ⋙
          proEtaleConstantRingPushforward Λ f ≅
          proEtaleConstantRingPushforward Λ (g ≫ f)),
        (∀ (N : proEtaleRingModules Z (proEtaleConstantRing Z Λ))
            (U : Y.ProEt)
            (m : ((proEtaleConstantRingPushforward Λ g ⋙
              proEtaleConstantRingPushforward Λ f).obj N).val.obj (Opposite.op U)),
          (d.hom.app N).val.app (Opposite.op U) m =
            N.val.map ((MorphismProperty.Over.pullbackComp g f).hom.app U).op m) ∧
        conjugateIsoEquiv
            ((proEtaleConstantRingAdjunction Λ f).comp
              (proEtaleConstantRingAdjunction Λ g))
            (proEtaleConstantRingAdjunction Λ (g ≫ f)) a = d
```

## New

```lean
theorem proEtaleConstantRingModulePullbackComposition
    {X Y Z : Scheme.{u}} (g : Z ⟶ X) (f : X ⟶ Y)
    (Λ : Type u) [CommRing Λ] :
    ∃ (a : proEtaleConstantRingPullback Λ (g ≫ f) ≅
        proEtaleConstantRingPullback Λ f ⋙ proEtaleConstantRingPullback Λ g),
      ∃ (d : proEtaleConstantRingPushforward Λ g ⋙
          proEtaleConstantRingPushforward Λ f ≅
          proEtaleConstantRingPushforward Λ (g ≫ f)),
        (∀ (N : proEtaleRingModules Z (proEtaleConstantRing Z Λ))
            (U : Y.ProEt)
            (m : ((proEtaleConstantRingPushforward Λ g ⋙
              proEtaleConstantRingPushforward Λ f).obj N).val.obj (Opposite.op U)),
          (d.hom.app N).val.app (Opposite.op U) m =
            N.val.map ((MorphismProperty.Over.pullbackComp g f).hom.app U).op m) ∧
        conjugateIsoEquiv
            ((proEtaleConstantRingAdjunction Λ f).comp
              (proEtaleConstantRingAdjunction Λ g))
            (proEtaleConstantRingAdjunction Λ (g ≫ f)) a = d
```

The only code change removes `[Finite Λ]`; the docstring now says "any" ring. The comparison directions, section formula and
conjugation normalization are identical. FiniteSystemPullbackCoherence applies
the theorem to `h`, `k`, and `A n`, without an explicit finiteness argument, so its
existing specialization and all its signatures remain valid. Its chosen comparison
still has exactly the same section normalization; that normalization determines
the direct-image map by sectionwise extensionality and the pullback map by the
conjugation bijection. No definition is weakened or supplied arbitrary data.

## Users

The textual-use query of `tools/downstream.py --uses` lists the first two modules;
the third is this delivery's new consumer. Public imports and all other signatures
are unchanged. No importer or consumer needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProEtaleModulePullbackComposition | unclaimed | Remove one unused hypothesis; retain the complete proof. |
| Sheaf.Paper.FiniteSystemPullbackCoherence | M3 | Its finite-ring use is still valid, unchanged. |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite | D5 | Reuse the normalized comparison for arbitrary rings. |

The DAG citers are lem-pod-finite-system-pullback-coherence,
lem-pur-completed-operation-tower-substitution, lem-pur-flag-pullback-injective,
lem-weil-proetale-constructible-exact-closure, and the new dependency from
lem-trf-absolute-frobenius-site. Their existing conclusions remain valid: every
previous finite-ring application is a specialization of the generalized theorem.
No consumer statement or definition is changed.

## Status

landed 20261020T221121-L-4146761 2026-10-20 (merge of deliver/D5/Sheaf.AlgebraicGeometry.AbsoluteFrobeniusSite)
