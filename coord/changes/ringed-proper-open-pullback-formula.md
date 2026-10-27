# SheafOfModules.RingedProperOpen.t

## Reason

Kernel checking stalls when matching separate expanded derived-functor composites,
even after the maps are factored definitionally. Move the existing Factorization
structure, its two instance registrations, and t definition verbatim to
Sheaf.Paper.RingedProperOpenPullbackCoefficients. The new coefficient lemma names
t directly, and the item publicly imports its module. This preserves all existing
names, signatures, construction terms and exported visibility while eliminating
the expensive conversion at the lemma boundary.

## Old

```lean
def t {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    {sp : Spatial o} (e : OpenComparisons sp)
    {U V W Z : Over T} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    (d : Factorization k r p i) (R : Rings m T) :
    o.shriek i R ⋙ (o.operation p R).left ⟶
      (o.operation r R).left ⋙ o.shriek k R :=
  (e.beta d.b d.q p i d.pullback R).hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (o.operation d.q R).left (e.pi d.s d.clopen R))
      (o.shriek d.b R) ≫
    Functor.whiskerRight
      ((sp.pullComp d.s d.q R ≪≫
        eqToIso (congrArg (fun f ↦ (o.operation f R).left) d.sq)).hom)
      (o.shriek d.s R ⋙ o.shriek d.b R) ≫
    Functor.whiskerLeft (o.operation r R).left
      (sp.openFactor d.s d.b k d.sb R).hom
```

## New

```lean
def t {m : Mode} {T : Scheme.{u}} {c : Coefficients m T} {o : Calculus c}
    {sp : Spatial o} (e : OpenComparisons sp)
    {U V W Z : Over T} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k.left] [IsOpenImmersion i.left]
    (d : Factorization k r p i) (R : Rings m T) :
    o.shriek i R ⋙ (o.operation p R).left ⟶
      (o.operation r R).left ⋙ o.shriek k R :=
  (e.beta d.b d.q p i d.pullback R).hom ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (o.operation d.q R).left (e.pi d.s d.clopen R))
      (o.shriek d.b R) ≫
    Functor.whiskerRight
      ((sp.pullComp d.s d.q R ≪≫
        eqToIso (congrArg (fun f ↦ (o.operation f R).left) d.sq)).hom)
      (o.shriek d.s R ⋙ o.shriek d.b R) ≫
    Functor.whiskerLeft (o.operation r R).left
      (sp.openFactor d.s d.b k d.sb R).hom
```

The exact old definition above, without any body or signature change, now lives in
lean/Sheaf/Paper/RingedProperOpenPullbackCoefficients.lean. Its Factorization structure
and b_open/s_open instance registrations also move unchanged. The item has a public
import of that module, preserving the declarations available to its importers.

The independent reader must check the verbatim move and its public exposure for
dependent targets. No target statement or mathematical definition changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RingedProperOpenCoefficientSquare | M9 | t and Factorization move to the publicly imported pre-mate module; gamma, left and right retain their meaning |

No external module imports this item or refers to t by name.

## Status

landed 20261025T211954-L-4179387 2026-10-25 (merge of deliver/M9/Sheaf.Paper.RingedProperOpenCoefficientSquare)
