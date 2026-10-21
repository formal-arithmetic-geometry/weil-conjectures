# constructibleToQbarPullIso, constructibleToQbarPushHom, constructibleToQbarSourceHom, constructibleToQbarTargetHom

## Reason

Restore `Sheaf.Paper.CondensedQbarComparisons` from the archive explicitly named in
`coord/rework.tsv`. Its live library file is absent after the cluster restore; the archive
is not a withdrawn mathematical dependency. This delivery makes the four specified comparison
constructions importable again. The archived source compiles with fourteen long-line warnings;
the restored source wraps those lines, preserving every whitespace-separated token. This is a
missing-module restoration with zero proof holes, rather than a new proof or a change of data.

The pull isomorphism remains `ObjectProperty.isoMk` of the component of `derivedPullIso`.
The push map remains `ObjectProperty.homMk` of the component of `derivedPushHom`.
The source and target maps remain their specified two-step composites. No choice of data,
coefficient category, morphism, hypothesis or target meaning changes.

## Old

There is no live `lean/Sheaf/Paper/CondensedQbarComparisons.lean`. The rework archive
`quarantine/Sheaf/Paper/CondensedQbarComparisons.lean` contains, verbatim:

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.OverSquare

public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs


/-! # Specified condensed finite-to-Qbar comparison maps

The four comparison constructions are moved verbatim from
`Sheaf.Paper.CondensedQbarBaseChangeCompatibility`, so the exchange coherence lemma can use them
without an import cycle (blueprint: def-weil-pbc-qbar-condensed-comparisons).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

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
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (h.asOver (Spec (.of k)))).obj K) ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (h.asOver (Spec (.of k)))).obj
        ((constructibleToPadicAlgCl U ℓ E).obj K) :=
  ObjectProperty.isoMk _
    ((derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h).app K.obj)

/-- The specified pushforward comparison restricted to bounded constructible objects.
Source: ChangeOfCoefficients.lean, `derivedPushHom`, the mate of restriction/pushforward;
TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarPushHom (K : PadicSubfieldConstructible T ℓ E) :
    (constructibleToPadicAlgCl U ℓ E).obj
        ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ (h.asOver (Spec (.of k)))).obj K) ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ (h.asOver (Spec (.of k)))).obj
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
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g.asOver (Spec (.of k)))).obj
          ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ (f.asOver (Spec (.of k)))).obj K)) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (g.asOver (Spec (.of k)))).obj
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ (f.asOver (Spec (.of k)))).obj
          ((constructibleToPadicAlgCl X ℓ E).obj K)) :=
  (constructibleToQbarPullIso ℓ k E g
      ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ (f.asOver (Spec (.of k)))).obj K)).hom ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (g.asOver (Spec (.of k)))).map
      (constructibleToQbarPushHom ℓ k E f K)

/-- The specified target comparison `U_K`: first the push comparison for `f'`, then the
pushforward of the pull comparison for `g'`. Source: TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarTargetHom (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgCl Y' ℓ E).obj
        ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ (f'.asOver (Spec (.of k)))).obj
          ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of k)))).obj K)) ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ (f'.asOver (Spec (.of k)))).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (g'.asOver (Spec (.of k)))).obj
          ((constructibleToPadicAlgCl X ℓ E).obj K)) :=
  constructibleToQbarPushHom ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ (g'.asOver (Spec (.of k)))).obj K) ≫
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ (f'.asOver (Spec (.of k)))).map
      (constructibleToQbarPullIso ℓ k E g' K).hom

end Square

end AlgebraicGeometry.ProEtale.CondensedRing
```

## New

The live library path is restored with the following source. Only whitespace differs from
the archive; all declaration names, signatures, bodies, visibility, imports and docstrings stay.
The existing node attachment is retained. Its `lean.statement` text is refreshed to include
the already-archived `h.asOver (Spec (.of k))` spelling of the restricted pullback argument.
The node's mathematical statement and dependency sets are unchanged.

```lean
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Sheaf.AlgebraicGeometry.OverSquare

public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs


/-! # Specified condensed finite-to-Qbar comparison maps

The four comparison constructions are moved verbatim from
`Sheaf.Paper.CondensedQbarBaseChangeCompatibility`, so the exchange coherence lemma can use them
without an import cycle (blueprint: def-weil-pbc-qbar-condensed-comparisons).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))

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
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (h.asOver (Spec (.of k)))).obj K) ≅
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (h.asOver (Spec (.of k)))).obj
        ((constructibleToPadicAlgCl U ℓ E).obj K) :=
  ObjectProperty.isoMk _
    ((derivedPullIso (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E) h).app K.obj)

/-- The specified pushforward comparison restricted to bounded constructible objects.
Source: ChangeOfCoefficients.lean, `derivedPushHom`, the mate of restriction/pushforward;
TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarPushHom (K : PadicSubfieldConstructible T ℓ E) :
    (constructibleToPadicAlgCl U ℓ E).obj
        ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ
            (h.asOver (Spec (.of k)))).obj K) ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (h.asOver (Spec (.of k)))).obj
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
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
            (g.asOver (Spec (.of k)))).obj
          ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ
              (f.asOver (Spec (.of k)))).obj K)) ⟶
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (g.asOver (Spec (.of k)))).obj
        ((boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (f.asOver (Spec (.of k)))).obj
          ((constructibleToPadicAlgCl X ℓ E).obj K)) :=
  (constructibleToQbarPullIso ℓ k E g
      ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ
          (f.asOver (Spec (.of k)))).obj K)).hom ≫
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (g.asOver (Spec (.of k)))).map
      (constructibleToQbarPushHom ℓ k E f K)

/-- The specified target comparison `U_K`: first the push comparison for `f'`, then the
pushforward of the pull comparison for `g'`. Source: TwoColimit.lean, final transport paragraph
(blueprint: prop-weil-pbc-qbar-condensed-basechange-compatibility). -/
noncomputable def constructibleToQbarTargetHom (K : PadicSubfieldConstructible X ℓ E) :
    (constructibleToPadicAlgCl Y' ℓ E).obj
        ((boundedConstructibleLowerStar (Profinite.continuousMapRingObj E) ℓ
            (f'.asOver (Spec (.of k)))).obj
          ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
              (g'.asOver (Spec (.of k)))).obj K)) ⟶
      (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ
          (f'.asOver (Spec (.of k)))).obj
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
            (g'.asOver (Spec (.of k)))).obj
          ((constructibleToPadicAlgCl X ℓ E).obj K)) :=
  constructibleToQbarPushHom ℓ k E f'
      ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E) ℓ
          (g'.asOver (Spec (.of k)))).obj K) ≫
    (boundedConstructibleLowerStar (Profinite.padicAlgClRingObj ℓ) ℓ (f'.asOver (Spec (.of k)))).map
      (constructibleToQbarPullIso ℓ k E g' K).hom

end Square

end AlgebraicGeometry.ProEtale.CondensedRing
```

## Users

The live source tree has no direct importers while this cluster is quarantined. Searching
`quarantine/Sheaf/Paper` gives the five direct importers below. DAG parent references in their
nodes still need these definitions, so none is withdrawn. No consumer signature or proof changes
are part of this delivery. The archived right-adjunct module is used only as a scratch compile
check, not delivered as an adaptation. Both its overlay artifact compile and its single-file
profile attempt time out at 60 seconds; this is an unresolved limitation of that separate
quarantined rework item, not a passing check. No comparison declaration or reduction behavior
has been changed from the archived dependency it already used. A separate importer of only
the restored module checks and applies all four original public result types; it compiles
cleanly against the overlay in 4.4 seconds. `tools/downstream.py --allow-missing` reports
zero live importers and users. The missing live file prevents the ordinary downstream
command from accepting the module unless `--allow-missing` is passed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedQbarComparisons | H4 | Restore its four concrete definitions at the missing library path. |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | quarantined rework item | Definitions and public imports restored verbatim; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | quarantined rework item | Same source and target comparisons; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeLeftAdjunct | quarantined rework item | Same pull, push and source comparisons; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeRightAdjunct | quarantined rework item | Same pull, push and target comparisons; scratch compile times out at 60 seconds. |
| Sheaf.Paper.CondensedQbarPullbackCube | quarantined rework item | Same pull comparison; no adaptation. |

## Status

landed 20261021T020127-L-2588128 2026-10-21 (merge of deliver/H4/Sheaf.Paper.CondensedQbarComparisons)
