# WeilConjectures.CompactSupportCondensedRealization.fieldProperOpenRestriction

## Reason

Naturality requires the original restriction normalization and refinement components
as natural transformations. Checking a separately assembled transformation against
the large original component formula repeatedly expands derived-functor instance
data and exceeds the 60-second limit. Construct each natural transformation once,
then define its original component by evaluation. The components retain exactly the
original maps, order, compositor and counit. Named presentations of the original
derived functors, adjunction and compositor keep that data shared. No target statement, mathematical hypothesis or choice changes.

## Old

```lean
def fieldProperOpenRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)))
      :=
  ((eqToIso (congrArg (fun h : X ⟶ d.Z ↦
      (CondensedRing.upperStar Λ h).leftDerivedFunctor) r.i_hom.symm)) ≪≫
    CondensedRing.leftDerivedUpperStarComp Λ c.i r.hom).hom.app
      ((CondensedRing.lowerStar Λ r.hom).rightDerivedFunctor.obj
        ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K)) ≫
    (CondensedRing.upperStar Λ c.i).leftDerivedFunctor.map
      ((CondensedRing.derivedUpperStarLowerStarAdjunction Λ r.hom).counit.app
        ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K))

def fieldRefinementApp {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ d).obj K.obj ⟶
      (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj K.obj :=
  (CondensedRing.lowerStar Λ d.g).rightDerivedFunctor.map
      (fieldProperOpen Λ r K) ≫
    (fieldPushComp Λ r.hom d.g).hom.app
      ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj) ≫
    (eqToIso (congrArg (fun h : c.Z ⟶ Y ↦
      (CondensedRing.lowerStar Λ h).rightDerivedFunctor) r.hom_g)).hom.app
        ((CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory.obj K.obj)
```

## New

```lean
def fieldDerivedUpperStar (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.upperStar Λ f).leftDerivedFunctor

/-- A named presentation of the original derived direct image.
Source: the existing condensed lower-star construction.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedLowerStar (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (CondensedRing.lowerStar Λ f).rightDerivedFunctor

/-- A named presentation of the original exact open extension.
Source: the existing condensed open extension construction.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedOpenShriek (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :=
  (CondensedRing.openImmersionLowerShriek Λ f).mapDerivedCategory

/-- The original derived adjunction in the named functor presentation.
Source: the archived derived upper-star/lower-star adjunction.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    fieldDerivedUpperStar Λ f ⊣ fieldDerivedLowerStar Λ f :=
  CondensedRing.derivedUpperStarLowerStarAdjunction Λ f

/-- The original pullback compositor in the named functor presentation.
Source: the archived derived upper-star compositor.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldDerivedPullComp
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    fieldDerivedUpperStar Λ (f ≫ g) ≅ fieldDerivedUpperStar Λ g ⋙ fieldDerivedUpperStar Λ f :=
  CondensedRing.leftDerivedUpperStarComp Λ f g

/-- The exact open adjunction expressed using the actual left-derived pullback.
Source: archived open-immersion derived adjunction; blueprint Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldOpenAdjunction {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j] :
    (CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory ⊣
      (CondensedRing.upperStar Λ j).leftDerivedFunctor :=
  (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction Λ j).ofNatIsoRight
    (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory_of_isOpenImmersion Λ j).symm

attribute [local irreducible] CondensedRing.derivedUpperStarLowerStarAdjunction
  CondensedRing.leftDerivedUpperStarComp
attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory

/-- Compose an inverse-image comparison with the proper counit.
Source: blueprint proof Steps 15--16; naturality of the compositor and counit.
(blueprint: def-pur-condensed-compact-support-projection). -/
def counitRestrictionNat
    {C D E : Type*} [Category C] [Category D] [Category E]
    (J : C ⥤ D) {P : E ⥤ D} {R : D ⥤ E} (ad : P ⊣ R)
    (V : D ⥤ C) (U : E ⥤ C) (α : U ≅ P ⋙ V) :
    (J ⋙ R) ⋙ U ⟶ J ⋙ V where
  app K := α.hom.app (R.obj (J.obj K)) ≫ V.map (ad.counit.app (J.obj K))
  naturality {K L} v := by
    have hα : U.map (R.map (J.map v)) ≫ α.hom.app (R.obj (J.obj L)) =
        α.hom.app (R.obj (J.obj K)) ≫ V.map (P.map (R.map (J.map v))) :=
      α.hom.naturality (R.map (J.map v))
    have hε : P.map (R.map (J.map v)) ≫ ad.counit.app (J.obj L) =
        ad.counit.app (J.obj K) ≫ J.map v := ad.counit.naturality (J.map v)
    change U.map (R.map (J.map v)) ≫
        (α.hom.app (R.obj (J.obj L)) ≫ V.map (ad.counit.app (J.obj L))) =
      (α.hom.app (R.obj (J.obj K)) ≫ V.map (ad.counit.app (J.obj K))) ≫ V.map (J.map v)
    rw [← Category.assoc, hα, Category.assoc, ← V.map_comp, hε, V.map_comp,
      Category.assoc]

/-- The original restriction normalization, assembled naturally in the input.
Source: blueprint proof Steps 15--16.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldProperOpenRestrictionNat {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :=
  counitRestrictionNat
    (fieldDerivedOpenShriek Λ c.i)
    (fieldDerivedAdjunction Λ r.hom)
    (fieldDerivedUpperStar Λ c.i)
    (fieldDerivedUpperStar Λ d.i)
    ((eqToIso (congrArg (fun h : X ⟶ d.Z ↦
      (fieldDerivedUpperStar Λ h)) r.i_hom.symm)) ≪≫
      fieldDerivedPullComp Λ c.i r.hom)



attribute [local irreducible] fieldProperOpenRestrictionNat

/-- The restriction normalization of a proper refinement, before its invertibility
is asserted. Source: blueprint proof Steps 15--16
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldProperOpenRestriction {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :=
  (fieldProperOpenRestrictionNat Λ r).app K

def assembleLiftNat
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (F : C ⥤ D) (G : C ⥤ E) (P : E ⥤ D) (R : D ⥤ H) (S : E ⥤ H)
    (lift : F ⟶ G ⋙ P) (cmp : P ⋙ R ⟶ S) : F ⋙ R ⟶ G ⋙ S where
  app K := R.map (lift.app K) ≫ cmp.app (G.obj K)
  naturality {K L} v := by
    change R.map (F.map v) ≫ (R.map (lift.app L) ≫ cmp.app (G.obj L)) =
      (R.map (lift.app K) ≫ cmp.app (G.obj K)) ≫ S.map (G.map v)
    rw [← R.map_comp_assoc, lift.naturality, R.map_comp, Category.assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun z ↦ R.map (lift.app K) ≫ z) (cmp.naturality (G.map v))

/-- The original normalized lift on bounded constructible inputs.
Source: blueprint Step 15.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldProperOpenNat {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :
    (boundedConstructible (condensedRingObj Λ X)).ι ⋙
        (CondensedRing.openImmersionLowerShriek Λ d.i).mapDerivedCategory ⟶
      ((boundedConstructible (condensedRingObj Λ X)).ι ⋙
        (CondensedRing.openImmersionLowerShriek Λ c.i).mapDerivedCategory) ⋙
          (CondensedRing.lowerStar Λ r.hom).rightDerivedFunctor where
  app := fieldProperOpen Λ r
  naturality := fun _ _ v ↦ fieldProperOpen_naturality Λ r v

/-- The original proper/open refinement assembled naturally.
Source: blueprint Step 15.
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldRefinementNat {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d) :=
  assembleLiftNat _ _ _
    (CondensedRing.lowerStar Λ d.g).rightDerivedFunctor
    (CondensedRing.lowerStar Λ c.g).rightDerivedFunctor
    (fieldProperOpenNat Λ r)
    ((fieldPushComp Λ r.hom d.g).hom ≫
      (eqToIso (congrArg (fun h : c.Z ⟶ Y ↦
        (CondensedRing.lowerStar Λ h).rightDerivedFunctor) r.hom_g)).hom)

/-- The canonical refinement component, in the direction from coarser to finer.
Source: blueprint proof Step 15
(blueprint: def-pur-condensed-compact-support-projection). -/
def fieldRefinementApp {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification f} (r : c.Refinement d)
    (K : BoundedConstructible (condensedRingObj Λ X)) :
    (CondensedRing.rightDerivedLowerShriekOfCompactification Λ d).obj K.obj ⟶
      (CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj K.obj :=
  (fieldRefinementNat Λ r).app K
```

`fieldProperOpen_naturality` is proved from the existing unique-normalization
statement. On the binary sum of the two inputs, uniqueness makes the off-diagonal
difference vanish; the adjunction bijection then gives the naturality equation.
The construction `fieldProperOpenNat` uses this proved theorem, and `assembleLiftNat`
applies proper direct image and the natural proper compositor.

The public witness theorems `fieldTensorColimits`, `fieldTensorColimitsRight`,
`fieldGradedTensor`, `fieldGradedFour`, `fieldGradedLeft` and `fieldGradedRight`
are proved from existing instances, and have only local instance registration.
Their types are propositions and they supply no new assumptions or object choices.
All new public declarations attach to the existing construction node.

New private imports are `Sheaf.Paper.ConstructibleCokernelsExtensions`,
`WeilConjectures.ConstructibleSheaf.ProEtaleModule.IsoClosed` and
`Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`. The retained shift proof
uses generic proved mate/pasting lemmas and explicit canonical shift bindings.
The retained identity proof uses generic proved adjunction identities before
specializing to the existing pullback unit laws. Local irreducibility of the derived preadditive structure and derived operations controls
elaboration without changing exported attributes. All original public imports
and statement types are preserved up to definitional equality.

The named presentations are also used throughout the refinement section:
`fieldOpenAdjunction`, `fieldProperOpenRestriction`, `fieldProperOpen`,
`fieldPushComp`, `fieldProperOpenNat`, `fieldRefinementNat` and their proof
signatures. Every occurrence of `(CondensedRing.upperStar Λ f).leftDerivedFunctor`,
`(CondensedRing.lowerStar Λ f).rightDerivedFunctor` or
`(CondensedRing.openImmersionLowerShriek Λ j).mapDerivedCategory` there is written
as `fieldDerivedUpperStar Λ f`, `fieldDerivedLowerStar Λ f` or
`fieldDerivedOpenShriek Λ j`, respectively. The adjunction and pullback compositor
are likewise written using `fieldDerivedAdjunction` and `fieldDerivedPullComp`.
Expanding these five definitions gives exactly the original expressions; this
shares their instance arguments without changing the functors or maps.

## Users

`tools/downstream.py` reports zero live downstream modules, and this module alone
uses `fieldProperOpenRestriction` and `fieldRefinementApp`. The quarantined parent
imports the item but mentions neither helper; its archive and dependencies stay
intact. No other module needs adaptation. The target meanings remain the original
proper/open coefficient and refinement constructions.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedCompactSupportProjection | U8 | Same component formulas, assembled naturally; naturality proved; retained proofs adapted. |
| Sheaf.Paper.CompactSupportCondensedRealization | unclaimed | Quarantined parent preserved; no helper use or adaptation. |

## Status

landed 20261024T191441-L-366717 2026-10-24 (merge of deliver/U8/Sheaf.Paper.CondensedCompactSupportProjection)
