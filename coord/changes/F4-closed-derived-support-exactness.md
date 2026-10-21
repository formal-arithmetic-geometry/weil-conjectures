# Closed derived support constructions: explicit direct-image exactness

## Reason

Restore the F4 item listed in `coord/rework.tsv` from its quarantine source, repairing
its actual elaboration failure. The archived `closedPullbackDerivedAdjunction`,
`closedSupportProjection`, and `closedSupportHomMap` use termwise closed pushforward
without a `PreservesFiniteColimits (lowerStar Λ i)` instance. Restoring the archive alone
fails at those uses. The existing theorem `closedSupport_lowerStarExact` supplies that
instance for a complementary quasi-compact open immersion.

The two general closed constructions now take exactness explicitly. The closed Hom map
and the three complementary-pair theorems install that proved instance in their types
and bodies, so their geometric hypotheses and mathematical conclusions do not change.
No statement of `Challenge.lean` changes. No new axiom, theorem hole, tensor construction,
or arbitrary data choice is introduced. The source-library root is untouched.

The three quarantined direct consumers of the maps module and the closed tensor
projection consumer are restored and adapted in the same packet. Their earlier proofs
remain intact. For the closed tensor projection theorem the only code change relative
to its archive is `let := closedSupport_lowerStarExact Λ f j hij` after constructing the
quasi-compact open complement. Its public signature stays verbatim.

## Old

The live paths were absent; the old interfaces below are read from the preserved archives.

```lean
noncomputable def closedPullbackDerivedAdjunction {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] :
    (supportPullback Λ i).mapDerivedCategory ⊣ (lowerStar Λ i).mapDerivedCategory
```

```lean
noncomputable def closedSupportProjection {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (P : DerivedCategory (supportModules Λ Z))
    (T : DerivedCategory (supportModules Λ X)) :
    ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj T ⟶
      (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedTensor Λ Z).obj P).obj ((supportPullback Λ i).mapDerivedCategory.obj T))
```

```lean
noncomputable def closedSupportHomMap {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (P : DerivedCategory (supportModules Λ Z)) (N : DerivedCategory (supportModules Λ X))
    (χ : (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedTensor Λ Z).obj P).obj
          ((supportPullback Λ i).mapDerivedCategory.obj
            (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N))) ⟶
      ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj
        (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N)) :
    (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N) ⟶
      (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedHom Λ Z).obj (op P)).obj ((closedSupport Λ i j).rightDerivedFunctor.obj N))
```

```lean
theorem condensedSupportDerivedLocalization {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    (∀ L, IsIso ((openSupportDerivedAdjunction Λ j).unit.app L)) ∧
    (∀ P, IsIso ((closedPullbackDerivedAdjunction Λ i).counit.app P)) ∧
    (∀ M : DerivedCategory (supportModules Λ X),
      IsZero ((supportPullback Λ j).mapDerivedCategory.obj M) →
        IsIso ((closedPullbackDerivedAdjunction Λ i).unit.app M)) ∧
    (∀ L, IsZero ((supportPullback Λ i).mapDerivedCategory.obj
      ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))) ∧
    (∀ P, IsZero ((supportPullback Λ j).mapDerivedCategory.obj
      ((lowerStar Λ i).mapDerivedCategory.obj P))) ∧
    (∀ {M N : DerivedCategory (supportModules Λ X)} (f : M ⟶ N),
      IsIso ((supportPullback Λ i).mapDerivedCategory.map f) →
      IsIso ((supportPullback Λ j).mapDerivedCategory.map f) → IsIso f)
```

```lean
theorem openClosedSupportProjectionFormula {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    (∀ P T, IsIso (closedSupportProjection Λ i P T)) ∧
    (∀ L T, IsIso (openSupportProjection Λ j L T))
```

```lean
theorem openClosedInternalHomFormulas {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    ∃ (p : ∀ (P : DerivedCategory (supportModules Λ Z))
        (T : DerivedCategory (supportModules Λ X)),
        ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj T ≅
          (lowerStar Λ i).mapDerivedCategory.obj
            (((derivedTensor Λ Z).obj P).obj
              ((supportPullback Λ i).mapDerivedCategory.obj T)))
      (o : ∀ (L : DerivedCategory (supportModules Λ U))
        (N : DerivedCategory (supportModules Λ X)),
        (((derivedHom Λ X).obj
          (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))).obj N) ≅
        (lowerStar Λ j).rightDerivedFunctor.obj
          (((derivedHom Λ U).obj (op L)).obj
            ((supportPullback Λ j).mapDerivedCategory.obj N)))
      (c : ∀ (P : DerivedCategory (supportModules Λ Z))
        (N : DerivedCategory (supportModules Λ X)),
        (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N) ≅
        (lowerStar Λ i).mapDerivedCategory.obj
          (((derivedHom Λ Z).obj (op P)).obj
            ((closedSupport Λ i j).rightDerivedFunctor.obj N))),
      (∀ P T, (p P T).hom = closedSupportProjection Λ i P T) ∧
      (∀ L N, (o L N).hom = openSupportHomMap Λ j L N) ∧
      (∀ P N, (c P N).hom = closedSupportHomMap Λ i j hij P N
        (p P (((derivedHom Λ X).obj
          (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N)).inv) ∧
      (∀ (L L' : DerivedCategory (supportModules Λ U))
          (N N' : DerivedCategory (supportModules Λ X)) (a : L' ⟶ L) (b : N ⟶ N'),
        (((derivedHom Λ X).map
          ((openImmersionLowerShriek Λ j).mapDerivedCategory.map a).op).app N ≫
          ((derivedHom Λ X).obj
            (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L'))).map b) ≫
          (o L' N').hom =
        (o L N).hom ≫ (lowerStar Λ j).rightDerivedFunctor.map
          (((derivedHom Λ U).map a.op).app
              ((supportPullback Λ j).mapDerivedCategory.obj N) ≫
            ((derivedHom Λ U).obj (op L')).map
              ((supportPullback Λ j).mapDerivedCategory.map b))) ∧
      (∀ (P P' : DerivedCategory (supportModules Λ Z))
          (N N' : DerivedCategory (supportModules Λ X)) (a : P' ⟶ P) (b : N ⟶ N'),
        (((derivedHom Λ X).map ((lowerStar Λ i).mapDerivedCategory.map a).op).app N ≫
          ((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P'))).map b) ≫
          (c P' N').hom =
        (c P N).hom ≫ (lowerStar Λ i).mapDerivedCategory.map
          (((derivedHom Λ Z).map a.op).app ((closedSupport Λ i j).rightDerivedFunctor.obj N) ≫
            ((derivedHom Λ Z).obj (op P')).map
              ((closedSupport Λ i j).rightDerivedFunctor.map b)))
```

## New

Restored interfaces, with explicit/scoped exactness:

```lean
noncomputable def closedPullbackDerivedAdjunction {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [PreservesFiniteColimits (lowerStar Λ i)] :
    (supportPullback Λ i).mapDerivedCategory ⊣ (lowerStar Λ i).mapDerivedCategory
```

```lean
noncomputable def closedSupportProjection {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [PreservesFiniteColimits (lowerStar Λ i)]
    (P : DerivedCategory (supportModules Λ Z))
    (T : DerivedCategory (supportModules Λ X)) :
    ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj T ⟶
      (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedTensor Λ Z).obj P).obj ((supportPullback Λ i).mapDerivedCategory.obj T))
```

```lean
noncomputable def closedSupportHomMap {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (P : DerivedCategory (supportModules Λ Z)) (N : DerivedCategory (supportModules Λ X)) :
    letI := closedSupport_lowerStarExact Λ i j hij
    ∀ (_χ : (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedTensor Λ Z).obj P).obj
          ((supportPullback Λ i).mapDerivedCategory.obj
            (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N))) ⟶
      ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj
        (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N)),
    (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N) ⟶
      (lowerStar Λ i).mapDerivedCategory.obj
        (((derivedHom Λ Z).obj (op P)).obj ((closedSupport Λ i j).rightDerivedFunctor.obj N))
```

```lean
theorem condensedSupportDerivedLocalization {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    let := closedSupport_lowerStarExact Λ i j hij
    (∀ L, IsIso ((openSupportDerivedAdjunction Λ j).unit.app L)) ∧
    (∀ P, IsIso ((closedPullbackDerivedAdjunction Λ i).counit.app P)) ∧
    (∀ M : DerivedCategory (supportModules Λ X),
      IsZero ((supportPullback Λ j).mapDerivedCategory.obj M) →
        IsIso ((closedPullbackDerivedAdjunction Λ i).unit.app M)) ∧
    (∀ L, IsZero ((supportPullback Λ i).mapDerivedCategory.obj
      ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))) ∧
    (∀ P, IsZero ((supportPullback Λ j).mapDerivedCategory.obj
      ((lowerStar Λ i).mapDerivedCategory.obj P))) ∧
    (∀ {M N : DerivedCategory (supportModules Λ X)} (f : M ⟶ N),
      IsIso ((supportPullback Λ i).mapDerivedCategory.map f) →
      IsIso ((supportPullback Λ j).mapDerivedCategory.map f) → IsIso f)
```

```lean
theorem openClosedSupportProjectionFormula {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    let := closedSupport_lowerStarExact Λ i j hij
    (∀ P T, IsIso (closedSupportProjection Λ i P T)) ∧
    (∀ L T, IsIso (openSupportProjection Λ j L T))
```

```lean
theorem openClosedInternalHomFormulas {Z U X : Scheme.{u}}
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ) :
    let := closedSupport_lowerStarExact Λ i j hij
    ∃ (p : ∀ (P : DerivedCategory (supportModules Λ Z))
        (T : DerivedCategory (supportModules Λ X)),
        ((derivedTensor Λ X).obj ((lowerStar Λ i).mapDerivedCategory.obj P)).obj T ≅
          (lowerStar Λ i).mapDerivedCategory.obj
            (((derivedTensor Λ Z).obj P).obj
              ((supportPullback Λ i).mapDerivedCategory.obj T)))
      (o : ∀ (L : DerivedCategory (supportModules Λ U))
        (N : DerivedCategory (supportModules Λ X)),
        (((derivedHom Λ X).obj
          (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L))).obj N) ≅
        (lowerStar Λ j).rightDerivedFunctor.obj
          (((derivedHom Λ U).obj (op L)).obj
            ((supportPullback Λ j).mapDerivedCategory.obj N)))
      (c : ∀ (P : DerivedCategory (supportModules Λ Z))
        (N : DerivedCategory (supportModules Λ X)),
        (((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N) ≅
        (lowerStar Λ i).mapDerivedCategory.obj
          (((derivedHom Λ Z).obj (op P)).obj
            ((closedSupport Λ i j).rightDerivedFunctor.obj N))),
      (∀ P T, (p P T).hom = closedSupportProjection Λ i P T) ∧
      (∀ L N, (o L N).hom = openSupportHomMap Λ j L N) ∧
      (∀ P N, (c P N).hom = closedSupportHomMap Λ i j hij P N
        (p P (((derivedHom Λ X).obj
          (op ((lowerStar Λ i).mapDerivedCategory.obj P))).obj N)).inv) ∧
      (∀ (L L' : DerivedCategory (supportModules Λ U))
          (N N' : DerivedCategory (supportModules Λ X)) (a : L' ⟶ L) (b : N ⟶ N'),
        (((derivedHom Λ X).map
          ((openImmersionLowerShriek Λ j).mapDerivedCategory.map a).op).app N ≫
          ((derivedHom Λ X).obj
            (op ((openImmersionLowerShriek Λ j).mapDerivedCategory.obj L'))).map b) ≫
          (o L' N').hom =
        (o L N).hom ≫ (lowerStar Λ j).rightDerivedFunctor.map
          (((derivedHom Λ U).map a.op).app
              ((supportPullback Λ j).mapDerivedCategory.obj N) ≫
            ((derivedHom Λ U).obj (op L')).map
              ((supportPullback Λ j).mapDerivedCategory.map b))) ∧
      (∀ (P P' : DerivedCategory (supportModules Λ Z))
          (N N' : DerivedCategory (supportModules Λ X)) (a : P' ⟶ P) (b : N ⟶ N'),
        (((derivedHom Λ X).map ((lowerStar Λ i).mapDerivedCategory.map a).op).app N ≫
          ((derivedHom Λ X).obj (op ((lowerStar Λ i).mapDerivedCategory.obj P'))).map b) ≫
          (c P' N').hom =
        (c P N).hom ≫ (lowerStar Λ i).mapDerivedCategory.map
          (((derivedHom Λ Z).map a.op).app ((closedSupport Λ i j).rightDerivedFunctor.obj N) ≫
            ((derivedHom Λ Z).obj (op P')).map
              ((closedSupport Λ i j).rightDerivedFunctor.map b)))
```

## Users

`tools/downstream.py` with `--allow-missing` reports no live downstream modules for the
four absent modules. An additional scan of all quarantined Lean files finds the users
below. No quarantine archive is deleted or rewritten.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps | F4 (item) | Restored and repaired; two general closed constructions take exactness explicitly, and the closed Hom type/body supplies it from the complementary pair. |
| Sheaf.AlgebraicGeometry.CondensedSupportDerivedLocalization | no local claim record | Restored; two private helpers take exactness, and the existing theorem installs the proved instance in its type and proof. |
| Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula | no local claim record | Restored; the existing theorem installs the proved exactness instance in its type and proof. |
| Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHom | no local claim record | Restored; two private naturality helpers take exactness, their explicit application supplies it, and the theorem installs it in type and proof. |
| Sheaf.SixFunctors.ClosedImmersionTensorProjection | no local claim record | Restored; supplies the proved instance after constructing its quasi-compact complement; public signature unchanged. |
| Sheaf.SixFunctors.OpenImmersionTensorProjection | no local claim record | Quarantined transitive consumer; checked unchanged against the restored modules; no adaptation needed. |
| Sheaf.Paper.ConstructibleInternalHomContinuity | no local claim record | Quarantined importer of the internal-Hom theorem; does not mention any of the changed closed map, adjunction, projection, or theorem names; no adaptation. |

All three DAG citers of `def-sfb-open-closed-internal-hom-comparisons` already assume a
complementary quasi-compact open. Their hypotheses therefore supply the explicit
exactness through the existing support theorem. Their mathematical statements and
proof dependency routes stay intact; their Lean statement records include the scoped
instance where required. The definition node records this correction in
`statement_change`, with all three citers checked as holding.

## Status

landed 20261021T061103-L-1698743 2026-10-21 (merge of deliver/F4/Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps)
