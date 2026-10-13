# AlgebraicGeometry.Scheme.picard_termwise_target_coherence

## Reason

Stage-3 preflight classifies changes to section commands conservatively as interface
changes. This delivery names the existing instance-family binders for explicit proof
applications, adds backward-unification settings, and registers the existing additive
functor theorem as a local instance. The settings support the explicit proof. The new
helpers and transported-complex definition are private. The theorem signature and both
public imports are unchanged, and all new imports are proof imports.

The explicit comparison family is constructed in Lean. Avoiding elimination recursors
into the large dependent existential and caching the transported complex keeps the
single-file compile within the existing 60-second limit; the limit was not changed.

## Old

Existing section instance binders:

```lean
variable [∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

variable [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
  (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
```

Existing theorem signature, verbatim:

```lean
theorem picard_termwise_target_coherence
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (U : W.Opens)
    (K : CochainComplex
      (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect W U K)
    (hE : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    ∃ b : ∀ {T : Scheme.{v}} (t : T ⟶ W) (s : T ⟶ U.toScheme),
        s ≫ U.ι = t → ((derivedPullback t).obj E ≅
          DerivedCategory.Q.obj (picardTermwiseModel W U K s)),
      ∀ {T T' : Scheme.{v}} (i : T' ⟶ T) (t : T ⟶ W) (t' : T' ⟶ W)
        (s : T ⟶ U.toScheme) (s' : T' ⟶ U.toScheme)
        (ht : i ≫ t = t') (hs : i ≫ s = s')
        (hf : s ≫ U.ι = t) (hf' : s' ≫ U.ι = t'),
      let c := (Classical.choose (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition)))) i t ≪≫
          eqToIso (congrArg (fun g : T' ⟶ W ↦ derivedPullback g) ht)
      (b t' s' hf').hom ≫
          DerivedCategory.Q.map (picardTermwiseModelRestrictionIso W U K i s s' hs).hom =
        c.inv.app E ≫ (derivedPullback i).map (b t s hf).hom ≫
          (picardTermwiseCounit i).app (picardTermwiseModel W U K s)
```

## New

The existing instance families now have names, and the additive registration is local:

```lean
variable [d : ∀ Y : Scheme.{v},
  HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]

variable [dO : ∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
  (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]

attribute [local instance] Functor.additive_of_preserves_binary_products
```

The following settings are used while checking this module:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The theorem retains exactly the signature shown in Old. Its proof constructs the
comparison isomorphisms and uses the new categorical counit equation. `omit d dO in`
and `omit dO in` keep unnecessary section variables out of private helper types.
These commands add no exported instance, notation, or declaration attribute.

## Users

`tools/downstream.py --direct --uses picard_termwise_target_coherence` found the
following direct importer and declaration uses. No consumer is edited or needs an
adaptation; the unchanged statement and public imports preserve its elaboration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PicardTermwiseTargetCoherence | E2 | Explicit proof and private helpers; existing public statement unchanged. |
| Sheaf.AlgebraicGeometry.PicardTermwiseModelComparison | unclaimed | Uses the unchanged coherence theorem; no adaptation needed. |

The new `PicardTermwiseCompositeCounit` module is introduced in the same delivery and
is imported only for the proof. The five Challenge target statements are untouched;
no definition used by them is changed, so their meaning does not reopen.

## Status

landed 20261013T152728-L-1015127 2026-10-13 (merge of deliver/E2/Sheaf.AlgebraicGeometry.PicardTermwiseTargetCoherence)
