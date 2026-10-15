# isIso_proEtaleUnit_sections_of_closedSiteCounit

## Reason

The stage-3 preflight conservatively records any added namespace, section, open or variable command as an interface change. This delivery adds a private AffineProEt helper namespace and a Localization section to prove the existing theorem. It therefore supplies the requested record, although the public theorem signature and public imports are unchanged. The continuity instances are explicitly `local instance`, confined to the Localization section; no global instance is added. All helper declarations are private.

## Old

The only public declaration has the following signature and a postponed proof:

```lean
theorem isIso_proEtaleUnit_sections_of_closedSiteCounit
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
 :
    let A := Γ(V.left, ⊤)
    let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
    let B := AffineProEt.ofEtale (𝟙 (Spec A))
    (∀ (P Q : Sheaf (AffineProEt.topology (Spec A)) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B))) →
    ∀ adj : AffineProEt.closedSiteLift A I ⊣ AffineProEt.closedSiteBaseChange A I,
      IsIso (adj.counit.app B) →
      IsIso (Functor.whiskerRight (proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit
        ((sheafSections (ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op V)))
```

The file had no auxiliary namespaces or sections inside `AlgebraicGeometry.Scheme`.

## New

The public declaration has exactly the same signature:

```lean
theorem isIso_proEtaleUnit_sections_of_closedSiteCounit
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
 :
    let A := Γ(V.left, ⊤)
    let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
    let B := AffineProEt.ofEtale (𝟙 (Spec A))
    (∀ (P Q : Sheaf (AffineProEt.topology (Spec A)) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B))) →
    ∀ adj : AffineProEt.closedSiteLift A I ⊣ AffineProEt.closedSiteBaseChange A I,
      IsIso (adj.counit.app B) →
      IsIso (Functor.whiskerRight (proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit
        ((sheafSections (ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op V)))
```

Its proof is complete. Added scope commands are `namespace AffineProEt` (closed before Localization), `section Localization` (closed before the coordinate lemmas), its coefficient and square variables, a fresh universe, and opens needed by its private helpers. The two continuity instances are local to that section. No definition or statement used by a target changes meaning. All original public imports are retained. Consequently no importer needs adaptation, and target-statement review is not reopened.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleSpecializationUnitComparison --uses isIso_proEtaleUnit_sections_of_closedSiteCounit` finds the following direct textual users. The first is the item itself; no other module is delivered or adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleSpecializationUnitComparison | D3 | Existing signature unchanged; proof completed using private helpers. |
| Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections | unclaimed | Existing use and public signature are unaffected; no adaptation. |

The remaining downstream modules only receive the same public declaration and imports, so their interfaces and proofs are unaffected.

## Status

landed 20261015T211840-L-1945748 2026-10-15 (merge of deliver/D3/Sheaf.AlgebraicGeometry.ProEtaleSpecializationUnitComparison)
