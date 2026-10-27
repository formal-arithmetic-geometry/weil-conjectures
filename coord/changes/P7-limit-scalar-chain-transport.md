# AlgebraicGeometry.Scheme.scalarChainTransport

## Reason

The reducible transport/composite abbreviations repeatedly expose the full
module pushforward and scalar-extension constructions during elaboration. The
complete comparison then exceeds the 60-second compile limit. Make the three
functors ordinary definitions, and use the inverse of the supplied coefficient
isomorphism directly instead of reconstructing it through `IsIso`. Supply proved
additivity instances so clients need not unfold the constructions to infer them.
This preserves all parameters, universe levels, result types and mathematical data.

For `W = sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)`,
`IsIso.inv_eq_of_hom_inv_id (W.mapIso c).hom_inv_id` identifies the old
`inv (W.mapIso c).hom` with the new `(W.mapIso c).inv`. Thus the old and new
transport functors are equal, not merely isomorphic. The left and right functors
remain the same composites; only reducibility and the equal inverse expression
change. There is no choice from an existence statement and no new hypothesis.
The node statement and the final theorem signature stay unchanged. The semantic
review required for a definition appearing in a target should check this equality.

## Old

```lean
abbrev scalarChainTransport {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX) :
    CochainPullback.Modules.{max r (t + 1), t + 1, t} RY ⥤
      CochainPullback.Modules.{max r (t + 1), t + 1, t} RX :=
  isoSectionwiseModuleInverseImage.{t, r} g
    (RY := (sheafCompose (ProEt.topology Y) (forget₂ CommRingCat RingCat)).obj RY)
    (RX := (sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).obj RX)
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).mapIso c).hom

abbrev scalarChainLeft {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {RX SX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (cR : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX)
    (jX : RX ⟶ SX) :
    CochainPullback.Modules.{max r (t + 1), t + 1, t} RY ⥤
      CochainPullback.Modules.{max r (t + 1), t + 1, t} SX :=
  scalarChainTransport g cR ⋙ extensionFunctor.{max r (t + 1), t + 1, t} jX

abbrev scalarChainRight {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY SY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {SX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (jY : RY ⟶ SY)
    (cS : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj SY ≅ SX) :
    CochainPullback.Modules.{max r (t + 1), t + 1, t} RY ⥤
      CochainPullback.Modules.{max r (t + 1), t + 1, t} SX :=
  extensionFunctor.{max r (t + 1), t + 1, t} jY ⋙ scalarChainTransport g cS
```

## New

```lean
def scalarChainTransport {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {RX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (c : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX) :
    CochainPullback.Modules.{max r (t + 1), t + 1, t} RY ⥤
      CochainPullback.Modules.{max r (t + 1), t + 1, t} RX :=
  SheafOfModules.pushforward.{max r (t + 1)} (F := proEtaleIsoPostcompose g)
    (((sheafCompose (ProEt.topology X) (forget₂ CommRingCat RingCat)).mapIso c).inv)

def scalarChainLeft {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {RX SX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (cR : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj RY ≅ RX)
    (jX : RX ⟶ SX) :
    CochainPullback.Modules.{max r (t + 1), t + 1, t} RY ⥤
      CochainPullback.Modules.{max r (t + 1), t + 1, t} SX :=
  scalarChainTransport g cR ⋙ extensionFunctor.{max r (t + 1), t + 1, t} jX

def scalarChainRight {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    {RY SY : Sheaf (ProEt.topology Y) CommRingCat.{max r (t + 1)}}
    {SX : Sheaf (ProEt.topology X) CommRingCat.{max r (t + 1)}}
    (jY : RY ⟶ SY)
    (cS : (isoSectionwiseInverseImage g CommRingCat.{max r (t + 1)}).obj SY ≅ SX) :
    CochainPullback.Modules.{max r (t + 1), t + 1, t} RY ⥤
      CochainPullback.Modules.{max r (t + 1), t + 1, t} SX :=
  extensionFunctor.{max r (t + 1), t + 1, t} jY ⋙ scalarChainTransport g cS
```

The new proved public instances are `scalarChainTransportAdditive`,
`scalarChainLeftAdditive`, and `scalarChainRightAdditive`; they are attached to
the same existing node.

## Users

`tools/downstream.py` reports zero downstream modules for the item, and its
`--uses` queries for each changed declaration report only this module. A direct
search of both Lean roots confirms this. No other module is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtale.LimitScalarChainComparison | P7 | Equal coefficient inverse; functors made semireducible; explicit additivity instances; complete proof |

## Status

landed 20261024T190617-L-4158064 2026-10-24 (merge of deliver/P7/Sheaf.AlgebraicGeometry.ProEtale.LimitScalarChainComparison)
