# AlgebraicGeometry.ProEtale.CondensedRing.identity_open_underived_square_normalization

## Reason

Fill the theorem's single proof hole while preserving its statement and all three
public definitions verbatim. The static visibility check flags added proof commands:
module elaboration options, `open Lean Meta in` attached to private metaprograms,
and section-local irreducibility attributes. These support ordinary kernel-checked
proof construction and control elaboration cost. They introduce no new public
notation, instances, attributes, or mathematical declarations. All public imports
are unchanged. The required unit-route CartesianCoefficients import is retained.
No source-library module is edited.

## Old

The original theorem signature, verbatim:

```lean
theorem identity_open_underived_square_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    {D Z U D' Z' U' : Scheme.{u}}
    [D.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [D'.Over (Spec (.of k))] [Z'.Over (Spec (.of k))] [U'.Over (Spec (.of k))]
    [LocallyOfFiniteType (D ↘ Spec (.of k))] [QuasiCompact (D ↘ Spec (.of k))]
    [IsSeparated (D ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (D' ↘ Spec (.of k))] [QuasiCompact (D' ↘ Spec (.of k))]
    [IsSeparated (D' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z' ↘ Spec (.of k))] [QuasiCompact (Z' ↘ Spec (.of k))]
    [IsSeparated (Z' ↘ Spec (.of k))]
    [LocallyOfFiniteType (U' ↘ Spec (.of k))] [QuasiCompact (U' ↘ Spec (.of k))]
    [IsSeparated (U' ↘ Spec (.of k))]
    (h : D ⟶ Z) (j : U ⟶ Z) (i : U ⟶ D)
    [h.IsOver (Spec (.of k))] [j.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion i]
    (hi : i ≫ h = j) (hU : IsPullback i (𝟙 U) h j)
    (v : Z' ⟶ Z) (h' : D' ⟶ Z') (w : D' ⟶ D)
    [v.IsOver (Spec (.of k))] [h'.IsOver (Spec (.of k))] [w.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare w h' h v)
    (vU : U' ⟶ U) (j' : U' ⟶ Z') (i' : U' ⟶ D')
    [vU.IsOver (Spec (.of k))] [j'.IsOver (Spec (.of k))] [i'.IsOver (Spec (.of k))]
    [IsOpenImmersion j'] [IsOpenImmersion i']
    (hi' : i' ≫ h' = j') (sqU : ChosenCartesianSquare vU j' j v)
    (hw : vU ≫ i = i' ≫ w) :
    IsPullback i' (𝟙 U') h' j' ∧
    IdentityOpenUnderivedNormalization Λ j i h hi ∧
    IdentityOpenUnderivedNormalization Λ j' i' h' hi' ∧
    (∀ A : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ Z),
      (identityOpenSquareLeft Λ h i v h' w vU j' i' hi' sq.toCommSq hw).hom.app A =
        (identityOpenSquareRight Λ h j i hi v vU j' sqU.toCommSq).hom.app A) ∧
    (∀ P : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ Z)) ℤ,
      (NatIso.mapHomologicalComplex
          (identityOpenSquareLeft Λ h i v h' w vU j' i' hi' sq.toCommSq hw)
            (.up ℤ)).hom.app P =
        (NatIso.mapHomologicalComplex
          (identityOpenSquareRight Λ h j i hi v vU j' sqU.toCommSq) (.up ℤ)).hom.app P) ∧
    (∀ A : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ Z)),
      (Functor.mapDerivedCategoryNatIso
          (identityOpenSquareLeft Λ h i v h' w vU j' i' hi' sq.toCommSq hw)).hom.app A =
        (Functor.mapDerivedCategoryNatIso
          (identityOpenSquareRight Λ h j i hi v vU j' sqU.toCommSq)).hom.app A)
```

Its proof was `by sorry`. The original module options were:

```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
```

## New

The theorem has the identical signature:

```lean
theorem identity_open_underived_square_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    {D Z U D' Z' U' : Scheme.{u}}
    [D.Over (Spec (.of k))] [Z.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [D'.Over (Spec (.of k))] [Z'.Over (Spec (.of k))] [U'.Over (Spec (.of k))]
    [LocallyOfFiniteType (D ↘ Spec (.of k))] [QuasiCompact (D ↘ Spec (.of k))]
    [IsSeparated (D ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (D' ↘ Spec (.of k))] [QuasiCompact (D' ↘ Spec (.of k))]
    [IsSeparated (D' ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z' ↘ Spec (.of k))] [QuasiCompact (Z' ↘ Spec (.of k))]
    [IsSeparated (Z' ↘ Spec (.of k))]
    [LocallyOfFiniteType (U' ↘ Spec (.of k))] [QuasiCompact (U' ↘ Spec (.of k))]
    [IsSeparated (U' ↘ Spec (.of k))]
    (h : D ⟶ Z) (j : U ⟶ Z) (i : U ⟶ D)
    [h.IsOver (Spec (.of k))] [j.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))]
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion i]
    (hi : i ≫ h = j) (hU : IsPullback i (𝟙 U) h j)
    (v : Z' ⟶ Z) (h' : D' ⟶ Z') (w : D' ⟶ D)
    [v.IsOver (Spec (.of k))] [h'.IsOver (Spec (.of k))] [w.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare w h' h v)
    (vU : U' ⟶ U) (j' : U' ⟶ Z') (i' : U' ⟶ D')
    [vU.IsOver (Spec (.of k))] [j'.IsOver (Spec (.of k))] [i'.IsOver (Spec (.of k))]
    [IsOpenImmersion j'] [IsOpenImmersion i']
    (hi' : i' ≫ h' = j') (sqU : ChosenCartesianSquare vU j' j v)
    (hw : vU ≫ i = i' ≫ w) :
    IsPullback i' (𝟙 U') h' j' ∧
    IdentityOpenUnderivedNormalization Λ j i h hi ∧
    IdentityOpenUnderivedNormalization Λ j' i' h' hi' ∧
    (∀ A : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ Z),
      (identityOpenSquareLeft Λ h i v h' w vU j' i' hi' sq.toCommSq hw).hom.app A =
        (identityOpenSquareRight Λ h j i hi v vU j' sqU.toCommSq).hom.app A) ∧
    (∀ P : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ Z)) ℤ,
      (NatIso.mapHomologicalComplex
          (identityOpenSquareLeft Λ h i v h' w vU j' i' hi' sq.toCommSq hw)
            (.up ℤ)).hom.app P =
        (NatIso.mapHomologicalComplex
          (identityOpenSquareRight Λ h j i hi v vU j' sqU.toCommSq) (.up ℤ)).hom.app P) ∧
    (∀ A : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ Z)),
      (Functor.mapDerivedCategoryNatIso
          (identityOpenSquareLeft Λ h i v h' w vU j' i' hi' sq.toCommSq hw)).hom.app A =
        (Functor.mapDerivedCategoryNatIso
          (identityOpenSquareRight Λ h j i hi v vU j' sqU.toCommSq)).hom.app A)
```

Its proof is complete. Added module-local elaboration settings:

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The private normalization proof section has:

```lean
attribute [local irreducible] upperStar identityOpenRestriction identityOpenPullbackComparison
```

The private compositor proof section restores the two transparency settings to `true`
and has:

```lean
attribute [local irreducible] upperStar upperStarComp pullbackCompTo
```

Both sections end before the public theorem. The three `open Lean Meta in` commands
are scoped to private metaprogram definitions. The one local linter option is scoped
to the private normalization lemma. The additional helpers are private, proved, and
have no effect on exported signatures or definitions. Explicit equality transport
uses only Subsingleton.elim, congrArg and Eq.mp, with ordinary kernel checking.

## Users

`tools/downstream.py` reports zero downstream modules and only this module as a
textual user of each of the four published declaration names. DAG parents with
unfinished proofs continue to use the same declaration and statement; no adaptation
is needed. No other group's module is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IdentityOpenUnderivedSquareNormalization | H2 | One theorem proof filled; public signatures and definitions unchanged. |

## Status

landed 20261022T002413-L-1926204 2026-10-22 (merge of deliver/H2/Sheaf.Paper.IdentityOpenUnderivedSquareNormalization)
