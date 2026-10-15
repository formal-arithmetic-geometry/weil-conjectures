# Constructibility transport helpers shared with extension by zero

## Reason

The returned delivery (head 683fc35eb) was refused by `import_prune_check.py` because
`ProEtaleModuleConstructibleExtensionByZero` copied ten transport lemmas already proved in
`ProEtaleModuleConstructiblePullback`. Those copies had identical statements, including their
ambient variables. They are removed, together with the copied finite-free constructions and
additivity instance. The existing proof-only pullback import now supplies the shared facts.
The following four proved lemmas and the proved pullback-composition instance change visibility. The remaining six presentation lemmas,
two finite-free constructions, and additivity instance stay private in the pullback module.
No statement, hypothesis, universe, definition, or target changes.

## Old

```lean
private lemma localFinitePresentation_of_iso {M N : Mod _ R} (e : M ≅ N)
    (hM : AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented R M) :
    AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented R N

private lemma localFinitePresentation_of_comap (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    {M : Mod _ R}
    (hM : AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented S ((Mod.comap φ).obj M)) :
    AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented R M

private lemma constructible_of_iso {M N : Mod _ R} (e : M ≅ N)
    (hM : AlgebraicGeometry.ProEtale.IsConstructibleModuleObject R M) :
    AlgebraicGeometry.ProEtale.IsConstructibleModuleObject R N

private lemma constructible_comap (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    {M : Mod _ R} (hM : AlgebraicGeometry.ProEtale.IsConstructibleModuleObject R M) :
    AlgebraicGeometry.ProEtale.IsConstructibleModuleObject S ((Mod.comap φ).obj M)
```

The pullback module also had:

```lean
private instance upperStarComp_inv_monoidal {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f g).inv
```

## New

```lean
lemma localFinitePresentation_of_iso {M N : Mod _ R} (e : M ≅ N)
    (hM : AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented R M) :
    AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented R N

lemma localFinitePresentation_of_comap (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    {M : Mod _ R}
    (hM : AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented S ((Mod.comap φ).obj M)) :
    AlgebraicGeometry.ProEtale.IsLocallyFinitelyPresented R M

lemma constructible_of_iso {M N : Mod _ R} (e : M ≅ N)
    (hM : AlgebraicGeometry.ProEtale.IsConstructibleModuleObject R M) :
    AlgebraicGeometry.ProEtale.IsConstructibleModuleObject R N

lemma constructible_comap (φ : S ⟶ R) [IsMonHom φ] [IsIso φ]
    {M : Mod _ R} (hM : AlgebraicGeometry.ProEtale.IsConstructibleModuleObject R M) :
    AlgebraicGeometry.ProEtale.IsConstructibleModuleObject S ((Mod.comap φ).obj M)
```

The instance is now public as well:

```lean
instance upperStarComp_inv_monoidal {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    NatTrans.IsMonoidal (upperStarComp Ab.{u + 1} f g).inv
```

All five proofs are unchanged. Extension by zero also drops its now-unused proof import of
`WeilConjectures.CategoryTheory.Monoidal.Conjugate`. The item also reuses `constructible_of_iso` instead of its
separate private proof of the same fact; its three uses supply the now implicit ring by
inference or `(R := R)`.

## Users

The two helper modules are new, unlanded modules of this E4 delivery. There are no existing
external importers or users of their private declarations. Their exact users in the delivered
sources are listed below. No module held by another group is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback | E4, new module | Export four proved lemmas and the monoidal comparison instance; keep their proofs and signatures. |
| Sheaf.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero | E4, new module | Delete the copied support block and monoidal comparison proof; use all four helpers through the existing proof import. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible | E4 | Delete the duplicate private constructibility-isomorphism proof and use the shared helper. |

The pullback node's `lean.declarations` records the five supporting declarations corresponding
to its existing scalar/isomorphism transport proof steps. These are completed proofs, with no
new mathematical obligation or `sorry`. The unit route and the two main helper statements stay
unchanged.

## Status

landed 20261015T181522-L-748402 2026-10-15 (merge of deliver/E4/WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible)
