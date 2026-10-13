# AlgebraicGeometry.Etale.higherDirectImageRawOverPullback

## Reason

The comparison repeatedly exceeded the 60-second limit while the kernel expanded the restricted single complexes and the coefficient composite. Share those exact data in named definitions with explicit source and target types, and use them in the three existing raw-over constructions. The report records compilation of the final repaired delivery and all users. These definitions contain the original constructions, with no new choices or assumptions. Every existing signature and visibility stays identical. The resulting constructions are definitionally equal to the old versions; no target meaning changes. The targets whose import closure contains this module should retain their existing semantic review after checking these definitional equalities.

## Old

```lean
noncomputable abbrev higherDirectImageRawOverPresheaf
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (B : Over W) :=
  higherDirectImagePresheaf Λ (B.hom ≫ k) q
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G))

noncomputable abbrev higherDirectImageRawOverComparison
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (B : Over W) :
    higherDirectImageRawOverPresheaf Λ k G q B ⟶
      (higherDirectImage Λ (B.hom ≫ k) q
        (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G)).obj ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
  higherDirectImagePresheafToSheaf Λ (B.hom ≫ k) q
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G))

noncomputable def higherDirectImageRawOverPullback
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U) :=
  higherDirectImageRawTrianglePullback Λ f.left (B.hom ≫ k) (A.hom ≫ k)
    (by rw [← Category.assoc, Over.w]) q _ _
    ((((f.left)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0).hom.app _ ≫
      (DerivedCategory.Plus.singleFunctor _ 0).map
        ((upperStarComp (ModuleCat.{u + 1} Λ) f.left B.hom A.hom
          (Over.w f).symm).inv.app G)) U z
```

## New

```lean
noncomputable abbrev higherDirectImageRawOverPresheaf
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (B : Over W) :=
  higherDirectImagePresheaf Λ (B.hom ≫ k) q
    (higherDirectImageRawOverComplex Λ G B)

noncomputable abbrev higherDirectImageRawOverComparison
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (B : Over W) :
    higherDirectImageRawOverPresheaf Λ k G q B ⟶
      (higherDirectImage Λ (B.hom ≫ k) q
        (((B.hom)^*[ModuleCat.{u + 1} Λ]).obj G)).obj ⋙
          forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} :=
  higherDirectImagePresheafToSheaf Λ (B.hom ≫ k) q
    (higherDirectImageRawOverComplex Λ G B)

@[implicit_reducible]
noncomputable def higherDirectImageRawOverPullback
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U) :=
  higherDirectImageRawTrianglePullback Λ f.left (B.hom ≫ k) (A.hom ≫ k)
    (by rw [← Category.assoc, Over.w]) q _ _
    (higherDirectImageRawOverCoefficient Λ G f) U z
```

The new public import of `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverCoefficient` supports the shared construction; its own public import provides the complex definition.

The shared complex and coefficient are semireducible `def`s with proved public
equations `higherDirectImageRawOverComplex_eq` and
`higherDirectImageRawOverCoefficient_heq`. Their bodies construct the exact original
data. The raw pullback wrapper becomes an `implicit_reducible` definition so the existing identity proof
can unfold the wrapper without unfolding these large data. Its type is unchanged.
This setting also permits the affine-image module's existing local irreducibility
attribute (an `abbrev` would forbid that attribute). The unchanged identity module
compiles in 49.7 seconds. No identity-module adaptation is delivered.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.HigherDirectImageColimitComparisonEpi | unclaimed | Definitionally identical data; hypotheses and conclusions are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageLocalClassVanishing | unclaimed | Definitionally identical data; hypotheses and conclusions are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineClassVanishing | unclaimed | Definitionally identical data; hypotheses and conclusions are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawAffineImageRep | unclaimed | Definitionally identical data; hypotheses and conclusions are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram | unclaimed | Definitionally identical data; hypotheses and conclusions are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackComposition | unclaimed | Definitionally identical data; hypotheses and conclusions are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula | unclaimed | Forced proof adaptation to the shared objects; existing signature and visibility unchanged. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackIdentity | unclaimed | Definitionally identical data; hypotheses and conclusions are unchanged; no adaptation. |
| Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality | P3 | Uses the shared constructions and proves the comparison. |

## Forced adaptation

`Sheaf.AlgebraicGeometry.HigherDirectImageRawPullbackCompositionFormula` is
unclaimed. Its original proof compiled against the published baseline in 40.1 seconds.
Against the final changed dependencies, the original fails in 4.5 seconds at
line 60 with `Type mismatch: After simplification, term h`. Its expanded complexes
and coefficients do not match the shared data in the expected pullbacks; Lean also
reports unexposed `equivShrink`. This is a compiler error, not a timeout.

The adaptation adds `set_option backward.isDefEq.respectTransparency true` and
local irreducibility for the shared complex and coefficient. A proved private
`restrictedCoefficient_comp` transports the original coefficient composition identity
by congruence, using `higherDirectImageRawOverComplex_eq` and
`higherDirectImageRawOverCoefficient_heq`. After `funext z` and `change`, the public
proof applies `congrArg` to that identity, reverses the resulting equality and
composes it with `higherDirectImageRawTrianglePullback_comp`. The expanded
complex/coefficient lets, `dsimp`, `rw [hc]` and final `simpa` are replaced by this
proof. Existing signatures, visibility, imports and docstrings are unchanged.

## Status

landed 20261013T215608-L-899550 2026-10-13 (merge of deliver/P3/Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality)
