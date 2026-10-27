# AlgebraicGeometry.ProEtale.FreeParameterEvaluation.scalarPullComparison

## Reason

Express the same normalized comparison by its inverse scalar-mate component.
This lets its invertibility proof use the existing universally normalized
comparison and avoids expensive unfolding of the equivalent adjunct construction.
The returned delivery omitted the two necessary consumer adaptations; this
packet includes them. No existing signature, public import, visibility or global
attribute changes. The generic inverse-mate component identity proves that the
new definition equals the old scalar-unit transpose, so target meanings and
normalizations are unchanged.

## Old

```lean
def scalarPullComparison {Y X : Scheme.{u}} (f : Y ⟶ X)
    (M : DerivedCategory (Modules R X)) :
    (Mod.extendScalars (coefficientMap φ Y)).leftDerivedFunctor.obj
      ((CondensedRing.upperStar R.X f).mapDerivedCategory.obj M) ⟶
    (CondensedRing.upperStar S.X f).mapDerivedCategory.obj
      ((Mod.extendScalars (coefficientMap φ X)).leftDerivedFunctor.obj M) :=
  ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ Y)).homEquiv _ _).symm
    ((CondensedRing.upperStar R.X f).mapDerivedCategory.map
      ((Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ X)).unit.app M) ≫
      (CondensedRing.derivedComapUpperStarIso φ f).inv.app _)
```

The companion definition originally inferred the comparison object:

```lean
def scalarPushMap (X : Scheme.{u}) (P : Profinite.{u})
    (N : DerivedCategory (PointModules R)) (N' : DerivedCategory (PointModules S))
    (n : N ⟶ (restrictPoint R S φ).mapDerivedCategory.obj N') :
    (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).obj
      ((pointPullD R (testScheme X P)).obj N) ⟶
    (restrictScheme R S φ X).mapDerivedCategory.obj
      ((CondensedRing.moduleObjectDerivedPushforward S.X (projection X P)).obj
        ((pointPullD S (testScheme X P)).obj N')) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ X)).homEquiv _ _
    ((projectionAdjunction S X P).homEquiv _ _
      (inv (scalarPullComparison R S φ (projection X P) _) ≫
        (Mod.extendScalars (coefficientMap φ (testScheme X P))).leftDerivedFunctor.map
          ((projectionAdjunction R X P).counit.app _) ≫
        ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (coefficientMap φ (testScheme X P))).homEquiv _ _).symm
          ((pointPullD R (testScheme X P)).map n ≫
            (restrictPointPullD R S φ (testScheme X P)).hom.app N')))
```

## New

```lean
def scalarPullComparison {Y X : Scheme.{u}} (f : Y ⟶ X)
    (M : DerivedCategory (Modules R X)) :
    (Mod.extendScalars (coefficientMap φ Y)).leftDerivedFunctor.obj
      ((CondensedRing.upperStar R.X f).mapDerivedCategory.obj M) ⟶
    (CondensedRing.upperStar S.X f).mapDerivedCategory.obj
      ((Mod.extendScalars (coefficientMap φ X)).leftDerivedFunctor.obj M) :=
  ((mateEquiv
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ X))
      (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ Y))).symm
    (TwoSquare.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso φ f).inv)).natTrans.app M
```

The same pushforward formula now supplies that determined object explicitly:

```lean
def scalarPushMap (X : Scheme.{u}) (P : Profinite.{u})
    (N : DerivedCategory (PointModules R)) (N' : DerivedCategory (PointModules S))
    (n : N ⟶ (restrictPoint R S φ).mapDerivedCategory.obj N') :
    (CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).obj
      ((pointPullD R (testScheme X P)).obj N) ⟶
    (restrictScheme R S φ X).mapDerivedCategory.obj
      ((CondensedRing.moduleObjectDerivedPushforward S.X (projection X P)).obj
        ((pointPullD S (testScheme X P)).obj N')) :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap φ X)).homEquiv _ _
    ((projectionAdjunction S X P).homEquiv _ _
      (inv (scalarPullComparison R S φ (projection X P)
          ((CondensedRing.moduleObjectDerivedPushforward R.X (projection X P)).obj
            ((pointPullD R (testScheme X P)).obj N))) ≫
        (Mod.extendScalars (coefficientMap φ (testScheme X P))).leftDerivedFunctor.map
          ((projectionAdjunction R X P).counit.app _) ≫
        ((Mod.derivedExtendMapDerivedCategoryAdjunction
          (coefficientMap φ (testScheme X P))).homEquiv _ _).symm
          ((pointPullD R (testScheme X P)).map n ≫
            (restrictPointPullD R S φ (testScheme X P)).hom.app N')))
```

This replaces only the object placeholder `_` by its previously inferred value.
The fully elaborated pushforward formula and its signature are unchanged.

The identity `unit_mateEquiv_symm` (equivalently the generic component lemma
`inverseMate_app` used by the integral consumer) says that applying the scalar
adjunction to this component gives precisely pullback of the scalar unit followed
by `derivedComapUpperStarIso.inv`. Injectivity of that adjunction proves equality
with the old definition for every ring map, geometric map and derived object.
This includes zero coefficients and empty schemes and requires no flatness.

## Users

A transitive `tools/downstream.py --uses scalarPullComparison` search finds the
four external users below; the additional direct importer of the item is also
listed. Only the two returned unfolding proofs require changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FreeParameterScalarMaps | J4 | Equivalent comparison definition; complete invertibility proof. |
| Sheaf.AlgebraicGeometry.PerfectScalarChangeModel | unclaimed | Uses only the resulting isomorphism; unchanged. |
| Sheaf.Paper.FiniteModelQuotientChartComparison | unclaimed | Uses only the resulting isomorphism; unchanged. |
| Sheaf.Paper.FreeParameterEvaluationCoherence | unclaimed | Direct importer; unchanged. |
| Sheaf.SixFunctors.ProEtale.IntegralReductionPullbackNormalization | unclaimed | Component equality now follows by reflexivity. |
| Sheaf.SixFunctors.ScalarSixDerivedPullbackNormalization | unclaimed | Remove the final term after simplification already closes the component equality. |

In the integral consumer the original `exact inverseMate_app ...` fails with
`Type mismatch`: its right side is the old adjunction transpose. Replacing only
that proof term by `rfl` matches the new definition. In the scalar-six consumer,
the original `exact scalarSixMateApp ...` fails with `No goals to be solved`
after `dsimp only`; removing only that redundant term repairs the proof.
Every existing declaration signature and visibility in both consumers is intact.
These are the two errors and forced changes explicitly requested by the return.

## Status

landed 20261026T070051-L-3360719 2026-10-26 (merge of deliver/J4/Sheaf.Paper.FreeParameterScalarMaps)
