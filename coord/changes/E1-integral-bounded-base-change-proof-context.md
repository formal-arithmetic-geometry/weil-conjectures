# IntegralBoundedStratumBaseChange proof context

## Reason

Restore the quarantined module and repair its compilation cost. The rework row
reports 60.2 seconds against the 60-second per-file limit. Archive profiling
shows repeated typeclass synthesis and 5.26 seconds spent on the last `dsimp`.
Every original public definition body and theorem signature is preserved.
After proof optimization still took 99.2 seconds, the eight public definitions
were moved verbatim to `Sheaf.Paper.CondensedStratumBaseChangeCalculus` and are
publicly reexported by the original module, through the new
`Sheaf.Paper.CondensedBoundedStratumBaseChange`. All original public imports
remain, with this new public import added. The new calculus helpers are proved
public theorems so the two compilation units can use them.
The old mixed-zero proof passed through the total left derived pullback and
`leftDerivedUpperStarIsoMapDerivedCategory`. Its replacement applies the existing
underived support vanishing to each homology object of the exact open extension.

## Old

The data definitions at their original module location, verbatim:

```lean
def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.upperStar Λ f).mapDerivedCategory

def openExtension {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :=
  (CondensedRing.openImmersionLowerShriek Λ f).mapDerivedCategory

def openAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    openExtension Λ f ⊣ pullback Λ f :=
  CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ f

def closedDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ f)] :=
  (CondensedRing.lowerStar Λ f).mapDerivedCategory

def closedAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ f)] :
    pullback Λ f ⊣ closedDirectImage Λ f :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).mapDerivedCategoryAdjunction

def pullbackSquare (sq : CommSq hS a' a h) :
    (pullback Λ a) ⋙
        (pullback Λ hS) ≅
      (pullback Λ h) ⋙
        (pullback Λ a') :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((CondensedRing.upperStarComp Λ hS a).symm ≪≫
        eqToIso (congrArg (CondensedRing.upperStar Λ) sq.w) ≪≫
          CondensedRing.upperStarComp Λ a' h) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

def openMate [IsOpenImmersion a] [IsOpenImmersion a'] (sq : CommSq hS a' a h) :
    (pullback Λ hS) ⋙
        (openExtension Λ a') ⟶
      (openExtension Λ a) ⋙
        (pullback Λ h) :=
  Adjunction.exchangeLeft
    (openAdjunction Λ a)
    (openAdjunction Λ a')
    (pullbackSquare Λ sq)

def closedMate [PreservesFiniteColimits (CondensedRing.lowerStar Λ a)]
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ a')] (sq : CommSq hS a' a h) :
    (closedDirectImage Λ a) ⋙
        (pullback Λ h) ⟶
      (pullback Λ hS) ⋙
        (closedDirectImage Λ a') :=
  Adjunction.exchangeRight
    (closedAdjunction Λ a)
    (closedAdjunction Λ a')
    (pullbackSquare Λ sq).symm
```


The bounded proof runs directly at `integralCoefficientRing l E`. The final
locally closed cancellation proof is verbatim:

```lean
  dsimp [e₀, β, γ, Λ]
  simp only [Category.id_comp]
  simp only [NatIso.isIso_inv_app, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
```

## New

The same data definitions at their new calculus module location, verbatim:

```lean
def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.upperStar Λ f).mapDerivedCategory

def openExtension {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :=
  (CondensedRing.openImmersionLowerShriek Λ f).mapDerivedCategory

def openAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    openExtension Λ f ⊣ pullback Λ f :=
  CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ f

def closedDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ f)] :=
  (CondensedRing.lowerStar Λ f).mapDerivedCategory

def closedAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ f)] :
    pullback Λ f ⊣ closedDirectImage Λ f :=
  (CondensedRing.upperStarLowerStarAdjunction Λ f).mapDerivedCategoryAdjunction

def pullbackSquare (sq : CommSq hS a' a h) :
    (pullback Λ a) ⋙
        (pullback Λ hS) ≅
      (pullback Λ h) ⋙
        (pullback Λ a') :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      ((CondensedRing.upperStarComp Λ hS a).symm ≪≫
        eqToIso (congrArg (CondensedRing.upperStar Λ) sq.w) ≪≫
          CondensedRing.upperStarComp Λ a' h) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

def openMate [IsOpenImmersion a] [IsOpenImmersion a'] (sq : CommSq hS a' a h) :
    (pullback Λ hS) ⋙
        (openExtension Λ a') ⟶
      (openExtension Λ a) ⋙
        (pullback Λ h) :=
  Adjunction.exchangeLeft
    (openAdjunction Λ a)
    (openAdjunction Λ a')
    (pullbackSquare Λ sq)

def closedMate [PreservesFiniteColimits (CondensedRing.lowerStar Λ a)]
    [PreservesFiniteColimits (CondensedRing.lowerStar Λ a')] (sq : CommSq hS a' a h) :
    (closedDirectImage Λ a) ⋙
        (pullback Λ h) ⟶
      (pullback Λ hS) ⋙
        (closedDirectImage Λ a') :=
  Adjunction.exchangeRight
    (closedAdjunction Λ a)
    (closedAdjunction Λ a')
    (pullbackSquare Λ sq).symm
```


The bounded proof runs in the completely proved theorem
`bounded_open_closed_base_change`, parametrized by an arbitrary condensed ring.
It is public in the new bounded module; the underlying support/mate calculus is
public in the new calculus module.
The public proof ends with:

```lean
  exact bounded_open_closed_base_change (integralCoefficientRing l E) hcomp sqU sqZ
```

The final locally closed cancellation proof is:

```lean
  exact stratum_composite_cancel β γ M.obj
```

`stratum_composite_cancel` is a completely proved private categorical identity.
All eight public definition bodies and both original public theorem signatures
remain verbatim; only the constructions' module of origin changes. The original
module publicly reexports the same constants. Public reducibility and attributes
of the eight data constructions do not change. No target definition changes
meaning and no target review reopens. The exact module relocation is from
`lean/Sheaf/Paper/IntegralBoundedStratumBaseChange.lean` to
`lean/Sheaf/Paper/CondensedStratumBaseChangeCalculus.lean`, preserving namespace
`AlgebraicGeometry.ProEtale.IntegralBoundedStratumBaseChange` and names:
`pullback`, `openExtension`, `openAdjunction`, `closedDirectImage`,
`closedAdjunction`, `pullbackSquare`, `openMate`, `closedMate`.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Paper.IntegralBoundedStratumBaseChange` | E1 | Restored; existing API publicly reexported; two theorem signatures unchanged. |
| `Sheaf.Paper.CondensedStratumBaseChangeCalculus` | E1, new | Verbatim data constructions and completely proved unbounded calculus. |
| `Sheaf.Paper.CondensedBoundedStratumBaseChange` | E1, new | Complete bounded proof over arbitrary condensed coefficients. |

The current direct importer scan finds zero modules. Searches in both live roots
and quarantine find no textual outside importer or theorem consumer. No existing
consumer is adapted or withdrawn. The new bounded module directly imports the
new calculus, and the item directly imports the new bounded module. All three
are compiled together in import order against the delivered files.

## Status

landed 20261026T154342-L-1646958 2026-10-26 (merge of deliver/E1/Sheaf.Paper.IntegralBoundedStratumBaseChange)
