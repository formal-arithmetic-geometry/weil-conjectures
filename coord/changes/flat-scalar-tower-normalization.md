# CategoryTheory.FlatScalarTowerExchange normalization definitions

## Reason

The original derived interfaces repeatedly compared large inherited category structures
and transported comparison records through two equalities and four heterogeneous
identifications. These conversions exceeded the single-file compile limit. The delivery
keeps all original conditions and gives the actual functors fixed interfaces.

`Corner.Restriction` directly contains the original functor and localization factor.
Unfold `complexFunctor`; fieldwise construction and projection identify it with
`LocalizedFunctor T.restrict`. The two constructions are inverse by cases and reflexivity.
`NormalizedDerivedAdjunction` retains all eight original fields: L, F, q, eta, adj,
derived, computes and transpose. The actual `complexFunctor` and `complexAdjunction`
constructions are the original degreewise functor and induced adjunction. These helpers
use the abelian parent consistently to supply the zero-morphism structure; all categories
where they are used already have the original abelian hypothesis. Unfold them
in the field types to construct either record from the other, without equality casts;
the two fieldwise constructions are inverse by cases and reflexivity. This equivalence
was separately compiled against an exact copy of the old eight-field record.

`DerivedImage` remains an abbreviation for these same normalized derived operations.
The named inverse/direct diagram functors and their adjunction explicitly construct
termwise whiskering and its original adjunction. `coefficientRing` explicitly constructs
the original forgotten ring sheaf; unfolding it identifies the module categories and
both chosen localizations with the old ones. `Corner.restrict` remains the original
termwise scalar restriction, with an explicit additivity proof. None of these definitions
chooses data from an existence assertion.

The corner abelian names are abbreviations for the inherited instance. `diagramAbelian`
uses Mathlib's canonical functor-category instance with its canonical parents, normalized
by `fast_instance%`. The generic instance registration is suspended only during this
constructor and is restored immediately afterward. The three sheaf-composition instances
cache existing Mathlib preservation properties. `diagramPreadditive` is exactly the
original functor-category preadditive instance. Reflexivity checks separately compiled
that it agrees with the inherited abelian parent and the original instance. For the
single private concrete descent proof, its registration and the generic functor-category
preadditive registration are suspended locally, so both complex functors and localization
factors consistently use that same abelian parent. Both registrations are restored
immediately after this declaration.

For `EdgeNormalized`, substitute the old witness's two restriction-functor equalities
and its four HEq identifications for factors, p and d. Its ordinary, inverse, direct
and adjunct equations are then exactly the new existential's four conditions.
Conversely, construct the original comparison record with the given restrictions,
factors, p and d and the new b0/d0 witnesses; all six identifications are reflexive.
`ordinaryNormalization` is the original ordinary predicate on the actual whiskered
functors. `derivedNormalization` groups the other three unchanged equations; its first is
`inverseNormalization`, the exact original inverse comparison equation. The abstract
localization descent lemma consumes these same named predicates and unfolds them only
in its abstract proof. Its complex-square input likewise uses a private predicate for
the exact pointwise equation. These shared heads avoid repeated comparison of expanded
formulas over concrete sheaf/complex categories without adding or dropping any condition.

`SquareNormalized` retains the same two localization equations. Unfold
`squareNormalization`, `composeFactor` and `complexComparison` at each complex P.
The resulting equation is the symmetry of the old one, with composition reassociated.
`ModuleSquare.diagrams` still applies the supplied ordinary module comparison termwise;
its explicit return type is definitionally equal to the original inferred one after
unfolding the actual diagram-functor constructors. The generic
`LocalizationSquareNormalized` definition is unchanged.

The original theorem's binder, universe and conclusion text is unchanged, checked after
whitespace normalization. These equivalent interfaces require independent semantic
review with the node; no Challenge declaration or adopted source-library module changes.

## Old

```lean
structure Corner where
  site : Type u
  category : SmallCategory site
  topology : GrothendieckTopology site
  R : Sheaf topology CommRingCat.{u}
  S : Sheaf topology CommRingCat.{u}
  a : R ⟶ S
  flat : SheafOfModules.IsFlatOnSite.{u, u, u, u}
    ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose topology (forget₂ CommRingCat RingCat)).map a)).obj
      (SheafOfModules.unit.{u} ((sheafCompose topology (forget₂ CommRingCat RingCat)).obj S)))

  /-- A chosen unbounded localization for the R diagrams, in Hom universe w. -/
  derivedR : HasDerivedCategory.{w} (Index.{u} ⥤ ringedSiteModules.{u}
    ((sheafCompose topology (forget₂ CommRingCat RingCat)).obj R))
  /-- A chosen unbounded localization for the S diagrams, in Hom universe w. -/
  derivedS : HasDerivedCategory.{w} (Index.{u} ⥤ ringedSiteModules.{u}
    ((sheafCompose topology (forget₂ CommRingCat RingCat)).obj S))
```

```lean
abbrev Corner.modulesR (T : Corner.{u, w}) :=
  Index.{u} ⥤ ringedSiteModules.{u}
    ((sheafCompose T.topology (forget₂ CommRingCat RingCat)).obj T.R)
```

```lean
abbrev Corner.modulesS (T : Corner.{u, w}) :=
  Index.{u} ⥤ ringedSiteModules.{u}
    ((sheafCompose T.topology (forget₂ CommRingCat RingCat)).obj T.S)
```

```lean
instance Corner.modulesRAbelian (T : Corner.{u, w}) : Abelian T.modulesR := inferInstance
```

```lean
instance Corner.modulesSAbelian (T : Corner.{u, w}) : Abelian T.modulesS := inferInstance
```

```lean
abbrev Corner.restrict (T : Corner.{u, w}) : T.modulesS ⥤ T.modulesR :=
  (Functor.whiskeringRight Index.{u} _ _).obj (SheafOfModules.restrictScalars.{u}
    ((sheafCompose T.topology (forget₂ CommRingCat RingCat)).map T.a))
```

```lean
abbrev Corner.Restriction (T : Corner.{u, w}) :=
  LocalizedFunctor T.restrict
```

```lean
structure NormalizedDerivedAdjunction
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    (L₀ : A ⥤ B) [L₀.Additive] (F₀ : B ⥤ A) [F₀.Additive] (adj₀ : L₀ ⊣ F₀) where
  L : DerivedCategory A ⥤ DerivedCategory B
  F : DerivedCategory B ⥤ DerivedCategory A
  q : DerivedCategory.Q ⋙ L ≅ L₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  η : F₀.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F
  adj : L ⊣ F
  derived : F.IsRightDerivedFunctor η (HomologicalComplex.quasiIso B (.up ℤ))
  computes : ∀ I : CochainComplex B ℤ, I.IsKInjective → IsIso (η.app I)
  transpose : ∀ (P : CochainComplex A ℤ) (I : CochainComplex B ℤ)
    (f : (L₀.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    adj.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
      (q.hom.app P ≫ DerivedCategory.Q.map f) =
    DerivedCategory.Q.map ((adj₀.mapHomologicalComplex (.up ℤ)).homEquiv P I f) ≫ η.app I
```

```lean
abbrev DerivedImage {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    {RV : Sheaf K CommRingCat.{u}} {RU : Sheaf H CommRingCat.{u}}
    (e : FlatRingedModuleImage RV RU)
    [HasDerivedCategory.{w} (Index.{u} ⥤ ringedSiteModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj RV))]
    [HasDerivedCategory.{w} (Index.{u} ⥤ ringedSiteModules.{u}
      ((sheafCompose H (forget₂ CommRingCat RingCat)).obj RU))] :=
  NormalizedDerivedAdjunction
    ((Functor.whiskeringRight Index.{u} _ _).obj e.inverse.modules)
    ((Functor.whiskeringRight Index.{u} _ _).obj e.morphism.modules)
    (Adjunction.whiskerRight Index.{u} e.adjunction)
```

```lean
def EdgeNormalized {U V : Corner.{u, w}}
    (e : EdgeData U V) (R : DerivedImage e.R) (S : DerivedImage e.S)
    (rU : U.Restriction) (rV : V.Restriction)
    (p : S.L ⋙ rU.functor ≅ rV.functor ⋙ R.L)
    (d : S.F ⋙ rV.functor ≅ rU.functor ⋙ R.F) : Prop :=
  ∃ c : FlatRingedDiagramInput.DerivedRestrictionComparison
      (x := e.input) (J := Index.{u}) R.L R.F R.q R.η R.adj S.L S.F S.q S.η S.adj,
    c.maps.rU = rU.functor ∧ c.maps.rV = rV.functor ∧
    HEq c.maps.qU rU.factor ∧ HEq c.maps.qV rV.factor ∧
    HEq p c.maps.b ∧ HEq d c.maps.d
```

```lean
def ModuleSquare.diagrams
    {CX CY CX' CY' : Type u}
    [SmallCategory CX] [SmallCategory CY] [SmallCategory CX'] [SmallCategory CY']
    {KX : GrothendieckTopology CX} {KY : GrothendieckTopology CY}
    {KX' : GrothendieckTopology CX'} {KY' : GrothendieckTopology CY'}
    {RX : Sheaf KX CommRingCat.{u}} {RY : Sheaf KY CommRingCat.{u}}
    {RX' : Sheaf KX' CommRingCat.{u}} {RY' : Sheaf KY' CommRingCat.{u}}
    {f : FlatRingedModuleImage RY RX} {g : FlatRingedModuleImage RY RY'}
    {fp : FlatRingedModuleImage RY' RX'} {gp : FlatRingedModuleImage RX RX'}
    (s : ModuleSquare f g fp gp) :=
  (Functor.whiskeringRight Index.{u} _ _).mapIso s.modules
```

```lean
def SquareNormalized (s : Square (f := f) (g := g) (fp := fp) (gp := gp))
    (R : gR.L ⋙ fpR.L ≅ fR.L ⋙ gpR.L)
    (S : gS.L ⋙ fpS.L ≅ fS.L ⋙ gpS.L) : Prop :=
  LocalizationSquareNormalized (g.input.inverseR Index.{u}) (fp.input.inverseR Index.{u})
    (f.input.inverseR Index.{u}) (gp.input.inverseR Index.{u}) s.R.diagrams
    gR.L fpR.L fR.L gpR.L gR.q fpR.q fR.q gpR.q R ∧
  LocalizationSquareNormalized (g.input.inverseS Index.{u}) (fp.input.inverseS Index.{u})
    (f.input.inverseS Index.{u}) (gp.input.inverseS Index.{u}) s.S.diagrams
    gS.L fpS.L fS.L gpS.L gS.q fpS.q fS.q gpS.q S
```

## New

```lean
structure Corner where
  site : Type u
  category : SmallCategory site
  topology : GrothendieckTopology site
  R : Sheaf topology CommRingCat.{u}
  S : Sheaf topology CommRingCat.{u}
  a : R ⟶ S
  flat : SheafOfModules.IsFlatOnSite.{u, u, u, u}
    ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose topology (forget₂ CommRingCat RingCat)).map a)).obj
      (SheafOfModules.unit.{u} ((sheafCompose topology (forget₂ CommRingCat RingCat)).obj S)))

  /-- A chosen unbounded localization for the R diagrams, in Hom universe w. -/
  derivedR : HasDerivedCategory.{w} ((Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing R)))
  /-- A chosen unbounded localization for the S diagrams, in Hom universe w. -/
  derivedS : HasDerivedCategory.{w} ((Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing S)))
```

```lean
abbrev Corner.modulesR (T : Corner.{u, w}) :=
  (Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing T.R))
```

```lean
abbrev Corner.modulesS (T : Corner.{u, w}) :=
  (Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing T.S))
```

```lean
abbrev Corner.modulesRAbelian (T : Corner.{u, w}) : Abelian T.modulesR := inferInstance
```

```lean
abbrev Corner.modulesSAbelian (T : Corner.{u, w}) : Abelian T.modulesS := inferInstance
```

```lean
@[irreducible]
def Corner.restrict (T : Corner.{u, w}) : T.modulesS ⥤ T.modulesR := by
  unfold Corner.modulesR Corner.modulesS coefficientRing
  exact (Functor.whiskeringRight Index.{u} _ _).obj (SheafOfModules.restrictScalars.{u}
    ((sheafCompose T.topology (forget₂ CommRingCat RingCat)).map T.a))
```

```lean
structure Corner.Restriction (T : Corner.{u, w}) where
  functor : DerivedCategory.{w} T.modulesS ⥤ DerivedCategory.{w} T.modulesR
  factor : DerivedCategory.Q.{w} (C := T.modulesS) ⋙ functor ≅
    (complexFunctor T.restrict) ⋙ DerivedCategory.Q.{w} (C := T.modulesR)
```

```lean
structure NormalizedDerivedAdjunction
    {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{w} B]
    (L₀ : A ⥤ B) [L₀.Additive] (F₀ : B ⥤ A) [F₀.Additive] (adj₀ : L₀ ⊣ F₀) where
  L : DerivedCategory A ⥤ DerivedCategory B
  F : DerivedCategory B ⥤ DerivedCategory A
  q : DerivedCategory.Q ⋙ L ≅ (complexFunctor L₀) ⋙ DerivedCategory.Q
  η : (complexFunctor F₀) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ F
  adj : L ⊣ F
  derived : F.IsRightDerivedFunctor η (HomologicalComplex.quasiIso B (.up ℤ))
  computes : ∀ I : CochainComplex B ℤ, I.IsKInjective → IsIso (η.app I)
  transpose : ∀ (P : CochainComplex A ℤ) (I : CochainComplex B ℤ)
    (f : (complexFunctor L₀).obj P ⟶ I),
    adj.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
      (q.hom.app P ≫ DerivedCategory.Q.map f) =
    DerivedCategory.Q.map ((complexAdjunction adj₀).homEquiv P I f) ≫ η.app I
```

```lean
abbrev DerivedImage {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {H : GrothendieckTopology D}
    {RV : Sheaf K CommRingCat.{u}} {RU : Sheaf H CommRingCat.{u}}
    (e : FlatRingedModuleImage RV RU)
    [HasDerivedCategory.{w} ((Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing RV)))]
    [HasDerivedCategory.{w} ((Index.{u} ⥤ ringedSiteModules.{u} (coefficientRing RU)))] :=
  NormalizedDerivedAdjunction
    (inverseDiagram e)
    (directDiagram e)
    (diagramAdjunction e)
```

```lean
def EdgeNormalized {U V : Corner.{u, w}}
    (e : EdgeData U V) (R : DerivedImage e.R) (S : DerivedImage e.S)
    (rU : U.Restriction) (rV : V.Restriction)
    (p : S.L ⋙ rU.functor ≅ rV.functor ⋙ R.L)
    (d : S.F ⋙ rV.functor ≅ rU.functor ⋙ R.F) : Prop :=
  ∃ (b₀ : (inverseDiagram e.S) ⋙ U.restrict ≅
    V.restrict ⋙
    (inverseDiagram e.R))
    (d₀ : (directDiagram e.S) ⋙ V.restrict ≅
      U.restrict ⋙
      (directDiagram e.R)),
    ordinaryNormalization e b₀ d₀ ∧
    derivedNormalization
      (QA := DerivedCategory.Q.{w} (C := V.modulesS))
      (QB := DerivedCategory.Q.{w} (C := U.modulesS))
      (QAR := DerivedCategory.Q.{w} (C := V.modulesR))
      (QBR := DerivedCategory.Q.{w} (C := U.modulesR))
      S.q R.q rV.factor rU.factor S.η R.η S.adj R.adj
      (complexComparison b₀) (complexComparison d₀) p d
```

```lean
def ModuleSquare.diagrams
    {CX CY CX' CY' : Type u}
    [SmallCategory CX] [SmallCategory CY] [SmallCategory CX'] [SmallCategory CY']
    {KX : GrothendieckTopology CX} {KY : GrothendieckTopology CY}
    {KX' : GrothendieckTopology CX'} {KY' : GrothendieckTopology CY'}
    {RX : Sheaf KX CommRingCat.{u}} {RY : Sheaf KY CommRingCat.{u}}
    {RX' : Sheaf KX' CommRingCat.{u}} {RY' : Sheaf KY' CommRingCat.{u}}
    {f : FlatRingedModuleImage RY RX} {g : FlatRingedModuleImage RY RY'}
    {fp : FlatRingedModuleImage RY' RX'} {gp : FlatRingedModuleImage RX RX'}
    (s : ModuleSquare f g fp gp) :
    inverseDiagram g ⋙ inverseDiagram fp ≅ inverseDiagram f ⋙ inverseDiagram gp := by
  unfold inverseDiagram coefficientRing
  exact (Functor.whiskeringRight Index.{u} _ _).mapIso s.modules
```

```lean
def SquareNormalized (s : Square (f := f) (g := g) (fp := fp) (gp := gp))
    (R : gR.L ⋙ fpR.L ≅ fR.L ⋙ gpR.L)
    (S : gS.L ⋙ fpS.L ≅ fS.L ⋙ gpS.L) : Prop :=
  squareNormalization fR.q gR.q fpR.q gpR.q
    (complexComparison
      (F := inverseDiagram g.R)
      (G := inverseDiagram fp.R)
      (H := inverseDiagram f.R)
      (K := inverseDiagram gp.R)
      s.R.diagrams) R ∧
  squareNormalization fS.q gS.q fpS.q gpS.q
    (complexComparison
      (F := inverseDiagram g.S)
      (G := inverseDiagram fp.S)
      (H := inverseDiagram f.S)
      (K := inverseDiagram gp.S)
      s.S.diagrams) S
```

Additional explicit helpers in the same module:

`ringSheafCompose`, `commRingSheafCompose`, `groupSheafCompose`, `diagramPreadditive`, `diagramAbelian`, `coefficientRing`, `Corner.restrict_additive`, `inverseDiagram`, `directDiagram`, `inverseDiagram_additive`, `directDiagram_additive`, `diagramAdjunction`, `complexFunctor`, `complexAdjunction`, `complexComparison`, `inverseNormalization`, `derivedNormalization`, `ordinaryNormalization`, `composeFactor`, `squareNormalization`.

## Users

A fresh `tools/downstream.py` check found zero downstream Lean modules. The assigned
module is the only current Lean user of the changed definitions. No parent DAG
attachment or unit route is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.FlatScalarTowerExchange | Y3 | prove the original theorem using equivalent fixed interfaces |

## Status

landed 20261022T025345-L-1292841 2026-10-22 (merge of deliver/Y3/Sheaf.CategoryTheory.FlatScalarTowerExchange)
