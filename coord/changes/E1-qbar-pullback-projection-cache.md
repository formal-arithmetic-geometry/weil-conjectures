# AlgebraicGeometry.ProEtale.CondensedRing.constructibleToQbar_pullback_cube

## Reason

The proof uses the full-subcategory projection and the existing scalar functor.
Four old private projection helpers are unused. The returned delivery additionally
copied four private diagram lemmas already stated in
`Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct`. Those duplicate copies and the
local generalized `inverse_mapped_square` are removed. The proof imports and uses the
existing `mapped_iso_rectangle` and `inverse_mapped_square` from that module instead.
The public cube signature is textually unchanged. No target definition or mathematical
statement changes. The four retained private coherence signatures are reflowed only to
obey the 100-column rule; their token sequences are unchanged.

## Old

```lean
section RestrictionAPI
variable {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
  [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]

private lemma qbar_map_hom {K M : PadicSubfieldConstructible T ℓ E} (v : K ⟶ M) :
    ((constructibleToPadicAlgCl T ℓ E).map v).hom =
      L(Mod.extendScalars
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) T)).map v.hom := rfl

private lemma qbar_obj_obj (K : PadicSubfieldConstructible T ℓ E) :
    ((constructibleToPadicAlgCl T ℓ E).obj K).obj =
      L(Mod.extendScalars
        (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) T)).obj K.obj := rfl

private lemma upper_map_hom
    {K M : PadicAlgClConstructible U ℓ} (v : K ⟶ M) :
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (h.asOver (Spec (.of k)))).map v).hom =
      L((h)^*⟦Profinite.padicAlgClRingObj ℓ⟧).map v.hom := rfl

private lemma upper_obj_obj (K : PadicSubfieldConstructible U ℓ E) :
    ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (h.asOver (Spec (.of k)))).obj K).obj =
      L((h)^*⟦Profinite.continuousMapRingObj E⟧).obj K.obj := rfl
end RestrictionAPI
```

The proof imports were `import all Sheaf.Paper.ContinuousIntegralPullComposition` and
`import all Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct`.

### Retained private signatures (before line wrapping)

```lean
private theorem qbarPullIso_comp
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {V : Scheme.{u}} [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (j : U ⟶ V) [j.IsOver (Spec (.of k))]
    (K : PadicSubfieldConstructible V ℓ E) :
    (constructibleToPadicAlgCl T ℓ E).mapIso
        ((boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).app K) ≪≫
      constructibleToQbarPullIso ℓ k E h
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (j.asOver (Spec (.of k)))).obj K) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (h.asOver (Spec (.of k)))).mapIso
        (constructibleToQbarPullIso ℓ k E j K) =
    constructibleToQbarPullIso ℓ k E (h ≫ j) K ≪≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).app
        ((constructibleToPadicAlgCl V ℓ E).obj K)
```

```lean
private lemma qbarPull_eq
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    (j : T ⟶ U) [j.IsOver (Spec (.of k))] (w : h = j)
    (K : PadicSubfieldConstructible U ℓ E) :
    (constructibleToPadicAlgCl T ℓ E).mapIso
        ((eqToIso (by subst j; rfl) :
          boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (h.asOver (Spec (.of k))) ≅
            boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (j.asOver (Spec (.of k)))).app K) ≪≫
      constructibleToQbarPullIso ℓ k E j K =
    constructibleToQbarPullIso ℓ k E h K ≪≫
      (eqToIso (by subst j; rfl) :
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (h.asOver (Spec (.of k))) ≅
          boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (j.asOver (Spec (.of k)))).app
          ((constructibleToPadicAlgCl U ℓ E).obj K)
```

```lean
private lemma qbarPull_square_cube_iso
    (sq : CommSq g' f' f g) (M : PadicSubfieldConstructible Y ℓ E) :
    (constructibleToPadicAlgCl X' ℓ E).mapIso
        ((boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ (sq.asOver (Spec (.of k)))).app M) ≪≫
      constructibleToQbarPullIso ℓ k E g'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (f.asOver (Spec (.of k)))).obj M) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (g'.asOver (Spec (.of k)))).mapIso
        (constructibleToQbarPullIso ℓ k E f M) =
    constructibleToQbarPullIso ℓ k E f'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g.asOver (Spec (.of k)))).obj M) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f'.asOver (Spec (.of k)))).mapIso
        (constructibleToQbarPullIso ℓ k E g M) ≪≫
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ (sq.asOver (Spec (.of k)))).app
          ((constructibleToPadicAlgCl Y ℓ E).obj M)
```

```lean
private lemma qbarPull_square_cube
    (sq : CommSq g' f' f g) (M : PadicSubfieldConstructible Y ℓ E) :
    (constructibleToPadicAlgCl X' ℓ E).map
        ((boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ (sq.asOver (Spec (.of k)))).hom.app M) ≫
      (constructibleToQbarPullIso ℓ k E g'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (f.asOver (Spec (.of k)))).obj M)).hom ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (g'.asOver (Spec (.of k)))).map
        (constructibleToQbarPullIso ℓ k E f M).hom =
    (constructibleToQbarPullIso ℓ k E f'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g.asOver (Spec (.of k)))).obj M)).hom ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (f'.asOver (Spec (.of k)))).map
        (constructibleToQbarPullIso ℓ k E g M).hom ≫
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ (sq.asOver (Spec (.of k)))).hom.app
          ((constructibleToPadicAlgCl Y ℓ E).obj M)
```

## New

The four private projection helpers are removed. Both original proof imports remain:
`import all Sheaf.Paper.ContinuousIntegralPullComposition` supplies the existing private
composition and bounded-component calculations; `import all
Sheaf.Paper.ContinuousIntegralExchangeTargetAdjunct` supplies the existing rectangle and
inverse cancellation calculations. Neither imported module is changed.

The five original cube-module holes are replaced with proofs. The only new private
diagram lemma is `coefficientCube_of_iso`, proved by the imported
`inverse_mapped_square` and `congrArg Iso.hom`. It retains the generic cube predicate
through concrete specialization, avoiding expensive concrete category comparisons.
Local irreducibility settings protect derived functors, bounded composition constraints
and the cube predicate. The repair removes all four reported duplicate statements
(`rectangle`, `mapped_rectangle`, `mapped_iso_rectangle`, `inverse_square`) rather than
proving or renaming them again. It also removes the now-unneeded local generalized
`inverse_mapped_square`.

### Retained private signatures (after line wrapping)

```lean
private theorem qbarPullIso_comp
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    {V : Scheme.{u}} [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))] (j : U ⟶ V) [j.IsOver (Spec (.of k))]
    (K : PadicSubfieldConstructible V ℓ E) :
    (constructibleToPadicAlgCl T ℓ E).mapIso
        ((boundedConstructibleUpperStarComp (Profinite.continuousMapRingObj E) ℓ
          (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).app K) ≪≫
      constructibleToQbarPullIso ℓ k E h
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (j.asOver (Spec (.of k)))).obj K) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (h.asOver (Spec (.of k)))).mapIso
        (constructibleToQbarPullIso ℓ k E j K) =
    constructibleToQbarPullIso ℓ k E (h ≫ j) K ≪≫
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ
        (h.asOver (Spec (.of k))) (j.asOver (Spec (.of k)))).app
        ((constructibleToPadicAlgCl V ℓ E).obj K)
```

```lean
private lemma qbarPull_eq
    {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]
    (j : T ⟶ U) [j.IsOver (Spec (.of k))] (w : h = j)
    (K : PadicSubfieldConstructible U ℓ E) :
    (constructibleToPadicAlgCl T ℓ E).mapIso
        ((eqToIso (by subst j; rfl) :
          boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (h.asOver (Spec (.of k))) ≅
            boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
              (j.asOver (Spec (.of k)))).app K) ≪≫
      constructibleToQbarPullIso ℓ k E j K =
    constructibleToQbarPullIso ℓ k E h K ≪≫
      (eqToIso (by subst j; rfl) :
        boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (h.asOver (Spec (.of k))) ≅
          boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (j.asOver (Spec (.of k)))).app
          ((constructibleToPadicAlgCl U ℓ E).obj K)
```

```lean
private lemma qbarPull_square_cube_iso
    (sq : CommSq g' f' f g) (M : PadicSubfieldConstructible Y ℓ E) :
    (constructibleToPadicAlgCl X' ℓ E).mapIso
        ((boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
          (sq.asOver (Spec (.of k)))).app M) ≪≫
      constructibleToQbarPullIso ℓ k E g'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (f.asOver (Spec (.of k)))).obj M) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (g'.asOver (Spec (.of k)))).mapIso
        (constructibleToQbarPullIso ℓ k E f M) =
    constructibleToQbarPullIso ℓ k E f'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (g.asOver (Spec (.of k)))).obj M) ≪≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (f'.asOver (Spec (.of k)))).mapIso
        (constructibleToQbarPullIso ℓ k E g M) ≪≫
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        (sq.asOver (Spec (.of k)))).app
          ((constructibleToPadicAlgCl Y ℓ E).obj M)
```

```lean
private lemma qbarPull_square_cube
    (sq : CommSq g' f' f g) (M : PadicSubfieldConstructible Y ℓ E) :
    (constructibleToPadicAlgCl X' ℓ E).map
        ((boundedConstructiblePullbackSquareComparison (Profinite.continuousMapRingObj E) ℓ
          (sq.asOver (Spec (.of k)))).hom.app M) ≫
      (constructibleToQbarPullIso ℓ k E g'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (f.asOver (Spec (.of k)))).obj M)).hom ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (g'.asOver (Spec (.of k)))).map
        (constructibleToQbarPullIso ℓ k E f M).hom =
    (constructibleToQbarPullIso ℓ k E f'
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (g.asOver (Spec (.of k)))).obj M)).hom ≫
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
        (f'.asOver (Spec (.of k)))).map
        (constructibleToQbarPullIso ℓ k E g M).hom ≫
      (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
        (sq.asOver (Spec (.of k)))).hom.app
          ((constructibleToPadicAlgCl Y ℓ E).obj M)
```

## Users

Private helpers had no external users. The public cube signature is textually identical;
no consumer signature or proof needs adapting.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedQbarPullbackCube | E1 | Five completed proofs; unused private projection helpers removed; existing diagram lemmas reused. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | unclaimed | Public statement unchanged; no adaptation. |

## Status

landed 20261017T024327-L-1173448 2026-10-17 (merge of deliver/E1/Sheaf.Paper.CondensedQbarPullbackCube)
