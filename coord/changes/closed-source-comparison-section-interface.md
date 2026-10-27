# AlgebraicGeometry.ClosedSourceSiteTensor.comparisonSections

## Reason

Factor the same comparison-section isomorphism through named data constructions
with native section types. `comparisonSectionPullbackIso` is evaluation of the
specified comparison-pullback isomorphism. `terminalComparisonUnitIso` is the
specified comparison unit at the terminal object. Their forward maps are proved
by reflexivity; equality of inverses follows from uniqueness of inverse. Thus
unfolding the wrappers identifies the new composite with the previous composite.
The generic naturality lemma for the terminal unit avoids unfolding the concrete
constant sheaf while checking the diagram. No morphism, hypothesis or universe
changes. This reached definition is flagged for independent statement review.

## Old

```lean
def comparisonSections (A : Type (u + 1)) [CommRing A] {X : Scheme.{u}}
    (F : Modules A false X) (Y : X.ProEt) :
    ((compare A X).obj F).obj.obj (op Y) ≅
      ((pull A false Y.hom).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y.left))) :=
  (((compare A X).obj F).obj.mapIso
    (MorphismProperty.Over.isoMk (Iso.refl Y.left)
      (Category.id_comp Y.hom) :
        (MorphismProperty.Over.map ⊤ Y.prop).obj (Scheme.ProEt.mk (𝟙 Y.left)) ≅ Y).op) ≪≫
    (asIso (((ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} A) Y.hom Y.prop).inv.app ((compare A X).obj F)).hom.app
        (op (Scheme.ProEt.mk (𝟙 Y.left))))) ≪≫
    (asIso (((comparePullback A Y.hom).inv.app F).hom.app
      (op (Scheme.ProEt.mk (𝟙 Y.left))))) ≪≫
    (asIso (((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} A) Y.left).unit.app
      ((pull A false Y.hom).obj F)).hom.app
        (op (Scheme.Etale.mk (𝟙 Y.left))))).symm
```

## New

```lean
/-- The comparison adjunction unit on terminal sections, with native section types.
Source: Stacks 099W, degree zero.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def terminalComparisonUnitIso (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology D) :
    F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) ≅
      ((ProEtale.comparisonUpperStar D X).obj F).obj.obj
        (op (Scheme.ProEt.mk (𝟙 X))) := by
  letI := ProEtale.isIso_comparisonAdjunction_unit D X
  exact asIso (((ProEtale.comparisonAdjunction D X).unit.app F).hom.app
    (op (Scheme.Etale.mk (𝟙 X))))

private lemma terminalComparisonUnitIso_hom (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology D) :
    (terminalComparisonUnitIso D X F).hom =
      ((ProEtale.comparisonAdjunction D X).unit.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 X))) := by
  rfl

private lemma terminalComparisonUnitIso_naturality (D : Type*) [Category.{u + 1} D]
    [Abelian D] [IsGrothendieckAbelian.{u + 1} D] (X : Scheme.{u})
    {F G : Sheaf X.smallEtaleTopology D} (f : F ⟶ G) :
    (terminalComparisonUnitIso D X F).hom ≫
        ((ProEtale.comparisonUpperStar D X).map f).hom.app
          (op (Scheme.ProEt.mk (𝟙 X))) =
      f.hom.app (op (Scheme.Etale.mk (𝟙 X))) ≫
        (terminalComparisonUnitIso D X G).hom := by
  rw [terminalComparisonUnitIso_hom, terminalComparisonUnitIso_hom]
  have h := congrArg (fun a ↦ a.hom.app (op (Scheme.Etale.mk (𝟙 X))))
    ((ProEtale.comparisonAdjunction D X).unit.naturality f)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Functor.id_map, Functor.comp_map, ProEtale.comparisonLowerStar,
    Functor.sheafPushforwardContinuous_map_hom_app, Functor.comp_obj, Functor.id_obj] at h
  convert h.symm using 1 <;> rfl


/-- Terminal evaluation of comparison pullback along an arbitrary scheme map.
Source: Stacks 099R and 0GLZ, the specified coherent comparison.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def genericComparisonSectionIso (A : Type (u + 1)) [CommRing A]
    {X' X : Scheme.{u}} (h : X' ⟶ X) (F : Modules A false X) :
    ((compare A X').obj ((pull A false h).obj F)).obj.obj
        (op (Scheme.ProEt.mk (𝟙 X'))) ≅
      ((pull A true h).obj ((compare A X).obj F)).obj.obj
        (op (Scheme.ProEt.mk (𝟙 X'))) :=
  (((sheafToPresheaf (Scheme.ProEt.topology X') (ModuleCat.{u + 1} A)).mapIso
    ((comparePullback A h).app F)).app (op (Scheme.ProEt.mk (𝟙 X'))))

private lemma genericComparisonSectionIso_hom (A : Type (u + 1)) [CommRing A]
    {X' X : Scheme.{u}} (h : X' ⟶ X) (F : Modules A false X) :
    (genericComparisonSectionIso A h F).hom =
      ((comparePullback A h).hom.app F).hom.app
        (op (Scheme.ProEt.mk (𝟙 X'))) := by
  rfl

/-- Evaluate the prescribed comparison-pullback iso using native section types.
Source: Stacks 099R and 0GLZ; the coherent comparison-pullback construction.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def comparisonSectionPullbackIso (A : Type (u + 1)) [CommRing A] {X : Scheme.{u}}
    (F : Modules A false X) (Y : X.ProEt) :
    ((compare A Y.left).obj ((pull A false (X := Y.left) Y.hom).obj F)).obj.obj
        (op (Scheme.ProEt.mk (𝟙 Y.left))) ≅
      ((pull A true (X := Y.left) Y.hom).obj ((compare A X).obj F)).obj.obj
        (op (Scheme.ProEt.mk (𝟙 Y.left))) :=
  genericComparisonSectionIso A (X' := Y.left) Y.hom F

/-- The canonical comparison section formula. Restrict along a weakly etale object,
commute site comparison with pullback, and invert the comparison unit on terminal sections.
This is the module-valued realization of Tag 0GLZ, normalized by the adjunction unit.
Source: Stacks 0GLZ and 099W, degree zero
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def comparisonSections (A : Type (u + 1)) [CommRing A] {X : Scheme.{u}}
    (F : Modules A false X) (Y : X.ProEt) :
    ((compare A X).obj F).obj.obj (op Y) ≅
      ((pull A false (X := Y.left) Y.hom).obj F).obj.obj (op (Scheme.Etale.mk (𝟙 Y.left))) :=
  (((compare A X).obj F).obj.mapIso
    (MorphismProperty.Over.isoMk (Iso.refl Y.left)
      (Category.id_comp Y.hom) :
        (MorphismProperty.Over.map ⊤ Y.prop).obj (Scheme.ProEt.mk (𝟙 Y.left)) ≅ Y).op) ≪≫
    (asIso (((ProEtale.upperStarIsoLocalizationRestriction
      (ModuleCat.{u + 1} A) Y.hom Y.prop).inv.app ((compare A X).obj F)).hom.app
        (op (Scheme.ProEt.mk (𝟙 Y.left))))) ≪≫
    (comparisonSectionPullbackIso A F Y).symm ≪≫
    (terminalComparisonUnitIso (ModuleCat.{u + 1} A) Y.left
      ((pull A false (X := Y.left) Y.hom).obj F)).symm
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison | J5 | Same canonical comparison section isomorphism, evaluated through its native API. |

## Status

landed 20261026T001858-L-37735 2026-10-26 (merge of deliver/J5/Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison)
