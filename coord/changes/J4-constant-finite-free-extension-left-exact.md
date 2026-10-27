# CategoryTheory.constantFiniteFree_extensionLeftExact

## Reason

The assigned scalar_exact theorem uses independent site-object, site-morphism and
coefficient universes. The existing public constantFiniteFree_sectionBasis and
constantFiniteFree_underlyingPowerIso statements use coefficients in the maximum
of these universes. Add the ordinary left-exactness consequence with the actual
EssentiallySmall hypothesis. Its private basis construction follows the existing
section-basis proof, while the tensor-coordinate maps reuse proved private helpers
of ConstantFiniteFreePowerIso. No existing signature or definition changes.

## Old

No declaration of this name existed.

## New

```lean
theorem CategoryTheory.constantFiniteFree_extensionLeftExact
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{r}]
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (A B : CommRingCat.{r}) [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (E : modules (constantRing J A) ⥤ modules (constantRing J B))
    (h : ∀ M, E.obj M = SheafOfModules.changeOfRings
      ((constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom (algebraMap A B))) M)
    (hm : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom
        ((constantSheaf J CommRingCat.{r}).map (CommRingCat.ofHom (algebraMap A B)))
          M f ≫ eqToHom (h N).symm) : PreservesFiniteLimits E
```

The new theorem is proved completely. The assigned scalar_exact theorem applies
it, obtains finite-colimit preservation from the ordinary tensor/restriction
adjunction, and applies the universal property of localization to its derived
counit through a proved private generic localization lemma. Local instance priorities
prefer the existing stored site-composition witnesses to rebuilding them. No new
instances or attributes are exported by an existing module.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ToposFiniteFreeCompactConstituents | J4 | Private proof imports and helper; local priorities for stored witnesses; scalar_exact retains its signature. |

There are no pre-existing consumers of the new module. Existing public imports,
statements and definitions of the assigned module are unchanged. The other
module bodies are unchanged.

## Status

landed 20261025T213307-L-317420 2026-10-25 (merge of deliver/J4/Sheaf.CategoryTheory.ToposFiniteFreeCompactConstituents)
