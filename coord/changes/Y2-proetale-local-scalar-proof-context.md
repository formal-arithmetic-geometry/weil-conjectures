# AlgebraicGeometry.Scheme.proEtaleLocalScalarHomologyIso

## Reason

The conservative command-interface check sees the new scoped instance and reducibility
attributes and the additional `Functor` namespace open. They support proved private helpers
for the completed proof. No existing public signature, definition, attribute, instance,
public import, canonical map, or target meaning changes. No private helper occurs in a
public signature or in the body of a public definition.

## Old

The file opened `CategoryTheory` and `CategoryTheory.Limits` and contained no private
comparison helpers. Its only theorem had the following signature and proof `by sorry`:

```lean
theorem proEtaleLocalScalarHomologyIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (U : Y.ProEt) (K K' : DerivedCategory (proEtaleRingModules X R))
    (e : sfbLocalRestriction i R U K ≅ sfbLocalRestriction i R U K') (q : ℤ) :
    Nonempty
      (((ProEt.topology Y).overPullback AddCommGrpCat.{u + 1} U).obj
          ((proEtaleSheafInverseImage i AddCommGrpCat.{u + 1}).obj
            ((SheafOfModules.toSheaf ((adicLisseForget X).obj S)).obj
              ((DerivedCategory.homologyFunctor _ q).obj
                ((completedAdicDerivedChange X φ).obj K)))) ≅
        ((ProEt.topology Y).overPullback AddCommGrpCat.{u + 1} U).obj
          ((proEtaleSheafInverseImage i AddCommGrpCat.{u + 1}).obj
            ((SheafOfModules.toSheaf ((adicLisseForget X).obj S)).obj
              ((DerivedCategory.homologyFunctor _ q).obj
                ((completedAdicDerivedChange X φ).obj K')))))
```

## New

The theorem has exactly the same signature:

```lean
theorem proEtaleLocalScalarHomologyIso {X Y : Scheme.{u}} (i : Y ⟶ X)
    {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (U : Y.ProEt) (K K' : DerivedCategory (proEtaleRingModules X R))
    (e : sfbLocalRestriction i R U K ≅ sfbLocalRestriction i R U K') (q : ℤ) :
    Nonempty
      (((ProEt.topology Y).overPullback AddCommGrpCat.{u + 1} U).obj
          ((proEtaleSheafInverseImage i AddCommGrpCat.{u + 1}).obj
            ((SheafOfModules.toSheaf ((adicLisseForget X).obj S)).obj
              ((DerivedCategory.homologyFunctor _ q).obj
                ((completedAdicDerivedChange X φ).obj K)))) ≅
        ((ProEt.topology Y).overPullback AddCommGrpCat.{u + 1} U).obj
          ((proEtaleSheafInverseImage i AddCommGrpCat.{u + 1}).obj
            ((SheafOfModules.toSheaf ((adicLisseForget X).obj S)).obj
              ((DerivedCategory.homologyFunctor _ q).obj
                ((completedAdicDerivedChange X φ).obj K')))))
```

Its proof is complete. The file additionally opens `CategoryTheory.Functor`. All new
helpers are private and proved. Their local instance hints provide exactness of the
local functor and the standard derived category of the slice. The imported specialized
site-size and slice-derived instances are excluded only while checking these proofs;
explicit universes retain the original small pro-etale site and coefficient sizes.
Local irreducibility attributes and transparency-respecting elaboration keep the chosen
tensor/derived witnesses and the large inverse-image construction folded. The noncomputable
section supports these private data constructions. Sequential elaboration checks their proof
constraints before the later concrete comparisons.
The private slice derived-pair interface states the complete universal property and
K-flat computation before selecting the functor and counit. The global adjunction
and counit use the existing normalized API in `BoundedConstructibleTower`.
The standard instance environment is retained for importers. All added imports are proof imports, including `import all`
for existing private adjunction and resolution-descent helpers.

## Users

A source search in both library roots found the theorem's only external textual use in
`Sheaf.Paper.AdicPerfectModelLocalResidueBounds`. Its application is unaffected because
the theorem's signature, visibility and public imports are unchanged. No downstream
module requires adaptation and no target meaning review is reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProEtaleLocalScalarHomologyIso | Y2 | One proof completed; private proof context only. |
| Sheaf.Paper.AdicPerfectModelLocalResidueBounds | unclaimed | Identical theorem application; no adaptation. |

## Status

landed 20261026T071525-L-3945153 2026-10-26 (merge of deliver/Y2/Sheaf.Paper.ProEtaleLocalScalarHomologyIso)
