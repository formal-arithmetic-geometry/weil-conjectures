# constructibleToQbarPullIso, constructibleToQbarPushHom, constructibleToQbarSourceHom, constructibleToQbarTargetHom

## Reason

Move the four existing comparison constructions, with identical names, signatures, visibility,
docstrings and definition bodies, to `Sheaf.Paper.CondensedQbarComparisons`. The item publicly
imports that module. The separate new exchange-coherence theorem can then use the specified
comparisons without importing the theorem that uses it. There is no change to an object,
morphism, mathematical hypothesis or conclusion. The original public imports remain publicly
reachable: ChosenCartesianSquare directly from the item, and the other three through the new
comparisons module. No target meaning changes; no statement review
is reopened by this relocation.

## Old

In `Sheaf.Paper.CondensedQbarBaseChangeCompatibility`:

```lean
section Edge

variable {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
  [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]

/-- The canonical pullback comparison restricted to bounded constructible objects, in the
orientation `T_T l_{h,E} ≅ l_{h,Ω} T_U`. Source: ChangeOfCoefficients.lean, `derivedPullIso`;
TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarPullIso (K : PadicSubfieldConstructible U ℓ E) :
    (constructibleToPadicAlgCl T ℓ E).obj
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k h).obj K) ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k h).obj
        ((constructibleToPadicAlgCl U ℓ E).obj K) :=
  ObjectProperty.isoMk _
    ((derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h).app K.obj)

/-- The specified pushforward comparison restricted to bounded constructible objects.
Source: ChangeOfCoefficients.lean, `derivedPushHom`, the mate of restriction/pushforward;
TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarPushHom (K : PadicSubfieldConstructible T ℓ E) :
    (constructibleToPadicAlgCl U ℓ E).obj
        ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k h).obj K) ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k h).obj
        ((constructibleToPadicAlgCl T ℓ E).obj K) :=
  ObjectProperty.homMk
    ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h).app K.obj)

end Edge

section Square

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- The specified source comparison `S_K`: first the pull comparison for `g`, then the
pullback of the push comparison for `f`. Source: TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarSourceHom (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgCl Y' ℓ E).obj
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g).obj
          ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k f).obj K)) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g).obj
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f).obj
          ((constructibleToPadicAlgCl X ℓ E).obj K)) :=
  (constructibleToQbarPullIso ℓ k E g
      ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k f).obj K)).hom ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g).map
      (constructibleToQbarPushHom ℓ k E f K)

/-- The specified target comparison `U_K`: first the push comparison for `f'`, then the
pushforward of the pull comparison for `g'`. Source: TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarTargetHom (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgCl Y' ℓ E).obj
        ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k f').obj
          ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g').obj K)) ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f').obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g').obj
          ((constructibleToPadicAlgCl X ℓ E).obj K)) :=
  constructibleToQbarPushHom ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g').obj K) ≫
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f').map
      (constructibleToQbarPullIso ℓ k E g' K).hom

```

## New

In `Sheaf.Paper.CondensedQbarComparisons`, verbatim:

```lean
section Edge

variable {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
  [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]

/-- The canonical pullback comparison restricted to bounded constructible objects, in the
orientation `T_T l_{h,E} ≅ l_{h,Ω} T_U`. Source: ChangeOfCoefficients.lean, `derivedPullIso`;
TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarPullIso (K : PadicSubfieldConstructible U ℓ E) :
    (constructibleToPadicAlgCl T ℓ E).obj
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k h).obj K) ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k h).obj
        ((constructibleToPadicAlgCl U ℓ E).obj K) :=
  ObjectProperty.isoMk _
    ((derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h).app K.obj)

/-- The specified pushforward comparison restricted to bounded constructible objects.
Source: ChangeOfCoefficients.lean, `derivedPushHom`, the mate of restriction/pushforward;
TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarPushHom (K : PadicSubfieldConstructible T ℓ E) :
    (constructibleToPadicAlgCl U ℓ E).obj
        ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k h).obj K) ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k h).obj
        ((constructibleToPadicAlgCl T ℓ E).obj K) :=
  ObjectProperty.homMk
    ((derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h).app K.obj)

end Edge

section Square

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- The specified source comparison `S_K`: first the pull comparison for `g`, then the
pullback of the push comparison for `f`. Source: TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarSourceHom (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgCl Y' ℓ E).obj
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g).obj
          ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k f).obj K)) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g).obj
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f).obj
          ((constructibleToPadicAlgCl X ℓ E).obj K)) :=
  (constructibleToQbarPullIso ℓ k E g
      ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k f).obj K)).hom ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g).map
      (constructibleToQbarPushHom ℓ k E f K)

/-- The specified target comparison `U_K`: first the push comparison for `f'`, then the
pushforward of the pull comparison for `g'`. Source: TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarTargetHom (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgCl Y' ℓ E).obj
        ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ k f').obj
          ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g').obj K)) ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f').obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ k g').obj
          ((constructibleToPadicAlgCl X ℓ E).obj K)) :=
  constructibleToQbarPushHom ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ k g').obj K) ≫
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ k f').map
      (constructibleToQbarPullIso ℓ k E g' K).hom

```

The item replaces the four local declarations with
`public import Sheaf.Paper.CondensedQbarComparisons`, while retaining its direct public import
of ChosenCartesianSquare. The equality module imports the same
data module. All four declarations retain their full names and their elaborated types.

## Users

`tools/downstream.py Sheaf.Paper.CondensedQbarBaseChangeCompatibility --uses
constructibleToQbarPullIso constructibleToQbarPushHom constructibleToQbarSourceHom
constructibleToQbarTargetHom` lists the three downstream modules below. It finds direct uses
of the four moved names only in the item's module. No downstream source needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | C1 | Definitions stay publicly available through the new data module; statement unchanged. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | A2 | Uses the compatibility theorem; its statement and the four data definitions are unchanged. No edit. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Transitively imports the item; all exposed mathematical data are identical. No edit. |
| TargetsCheck | unclaimed | Imports the targets; all target statements and used definitions remain identical. No edit. |

## Status

landed 20261015T154155-L-159521 2026-10-15 (merge of deliver/C1/Sheaf.Paper.CondensedQbarBaseChangeCompatibility)
