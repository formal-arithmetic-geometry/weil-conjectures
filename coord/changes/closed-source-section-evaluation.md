# AlgebraicGeometry.ClosedSourceSiteTensor.proSupportSections

## Reason

Express the canonical evaluation isomorphism using localization on Y, the standard
weakly etale base-change isomorphism, the supplied coefficient isomorphism, and
terminal direct-image evaluation. The old expression uses localization on the
fibre product instead. Naturality of localization restriction and the universal
property of the two pullbacks identify the composites. Expand the base-change map
using `ProEtale.baseChangeMap_eq`. The localization isomorphism on Y cancels its
inverse. Apply naturality of localization restriction followed by the coefficient
identification along the terminal pullback isomorphism. The resulting composite
of site maps is identity: both projections agree by `pullback.hom_ext` and the
pullback condition. Functoriality of F reduces this to the old restriction formula.
This works for empty and nonreduced supports, with no closedness assumption.
This avoids kernel conversion through constant-sheaf
sheafification when checking the section formula. No target signature, hypothesis,
universe, or canonical map changes. This definition is reached by targets and
requires independent statement review.

## Old

```lean
def proSupportSections (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) (Y : X.ProEt) :
    (supported A true i).obj.obj (op Y) ≅
      (constant A true (pullback Y.hom i)).obj.obj
        (op (Scheme.ProEt.mk (𝟙 (pullback Y.hom i)))) :=
  (asIso (((ProEtale.upperStarIsoLocalizationRestriction
    (ModuleCat.{u + 1} A) (pullback.snd Y.hom i) inferInstance).inv.app
      (constant A true C)).hom.app
        (op (Scheme.ProEt.mk (𝟙 (pullback Y.hom i)))))) ≪≫
    (asIso ((unitIso A true (pullback.snd Y.hom i)).hom.hom.app
      (op (Scheme.ProEt.mk (𝟙 (pullback Y.hom i))))))
```

## New

```lean
/-- Terminal evaluation for a direct image on the pro-etale site.
Source: the pullback of the identity isomorphism; Stacks 099W.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def genericTerminal (D : Type*) [Category.{u + 1} D]
    {C X : Scheme.{u}} (i : C ⟶ X) (F : Sheaf (Scheme.ProEt.topology C) D) :
    ((ProEtale.lowerStar D i).obj F).obj.obj (op (Scheme.ProEt.mk (𝟙 X))) ≅
      F.obj.obj (op (Scheme.ProEt.mk (𝟙 C))) :=
  F.obj.mapIso
    (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 X) i)) (Category.comp_id _) :
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ i).obj
        (Scheme.ProEt.mk (𝟙 X)) ≅ Scheme.ProEt.mk (𝟙 C)).symm.op

/-- Evaluate inverse image along a pro-etale test by localization restriction.
Source: Stacks 099W, degree zero.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def genericLocalization (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D]
    {X : Scheme.{u}} (F : Sheaf (Scheme.ProEt.topology X) D) (Y : X.ProEt) :
    F.obj.obj (op Y) ≅
      ((ProEtale.upperStar D (Z := Y.left) Y.hom).obj F).obj.obj
        (op (Scheme.ProEt.mk (𝟙 Y.left))) :=
  F.obj.mapIso
    (MorphismProperty.Over.isoMk (Iso.refl Y.left) (Category.id_comp Y.hom) :
      (MorphismProperty.Over.map ⊤ Y.prop).obj (Scheme.ProEt.mk (𝟙 Y.left)) ≅ Y).op ≪≫
    asIso (((ProEtale.upperStarIsoLocalizationRestriction
      D Y.hom Y.prop).inv.app F).hom.app
        (op (Scheme.ProEt.mk (𝟙 Y.left))))

/-- The canonical weakly etale base-change isomorphism before evaluation.
Source: Stacks 099W, weakly etale localization base change.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def sectionBaseChangeIso (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {C X : Scheme.{u}} (i : C ⟶ X)
    (Y : X.ProEt) :
    ProEtale.lowerStar D i ⋙ ProEtale.upperStar D (Z := Y.left) Y.hom ≅
      ProEtale.upperStar D (pullback.snd Y.hom i) ⋙
        ProEtale.lowerStar D (pullback.fst Y.hom i) := by
  letI := ProEtale.isIso_baseChangeMap_of_isPullback D
    (IsPullback.of_hasPullback (Z := X) Y.hom i)
  exact asIso (ProEtale.baseChangeMap D
    (IsPullback.of_hasPullback (Z := X) Y.hom i).toCommSq)

/-- The base-change isomorphism has the prescribed mate as its forward map.
Source: the definition of the weakly etale base-change isomorphism.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
lemma sectionBaseChangeIso_hom (D : Type*) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {C X : Scheme.{u}} (i : C ⟶ X)
    (Y : X.ProEt) :
    (sectionBaseChangeIso D i Y).hom =
      ProEtale.baseChangeMap D (IsPullback.of_hasPullback Y.hom i).toCommSq := by
  rfl

/-- Evaluate a sheaf isomorphism between two specified section identifications.
Source: functoriality of evaluation; Stacks 099W, degree zero.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def evaluatedSectionIso
    {S : Type*} [Category S] {J : GrothendieckTopology S}
    {D : Type*} [Category D] {F G : Sheaf J D} {W : Sᵒᵖ}
    {B C : D} (l : B ≅ F.obj.obj W) (r : G.obj.obj W ≅ C)
    (f : F ≅ G) : B ≅ C :=
  l ≪≫ ((sheafSections J D).obj W).mapIso f ≪≫ r

/-- Forward evaluation of a sheaf isomorphism is componentwise composition.
Source: functoriality of evaluation; Stacks 099W, degree zero.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
lemma evaluatedSectionIso_hom
    {S : Type*} [Category S] {J : GrothendieckTopology S}
    {D : Type*} [Category D] {F G : Sheaf J D} {W : Sᵒᵖ}
    {B C : D} (l : B ≅ F.obj.obj W) (r : G.obj.obj W ≅ C)
    (f : F ≅ G) :
    (evaluatedSectionIso l r f).hom = l.hom ≫ f.hom.hom.app W ≫ r.hom := by
  rfl

/-- Canonical section evaluation used in closed-source base change.
Source: Stacks 099W, degree zero and localization.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def terminalSupport (A : Type (u + 1)) [CommRing A]
    (pro : Bool) {C X : Scheme.{u}} (i : C ⟶ X) :
    (supported A pro i).obj.obj (op (match pro with
      | false => Scheme.Etale.mk (𝟙 X)
      | true => Scheme.ProEt.mk (𝟙 X))) ≅
    (constant A pro C).obj.obj (op (match pro with
      | false => Scheme.Etale.mk (𝟙 C)
      | true => Scheme.ProEt.mk (𝟙 C))) := by
  cases pro with
  | false =>
    exact (constant A false C).obj.mapIso
      (MorphismProperty.Over.isoMk (asIso (pullback.snd (𝟙 X) i))
        (Category.comp_id _) :
        (MorphismProperty.Over.pullback @Etale ⊤ i).obj
          (Scheme.Etale.mk (𝟙 X)) ≅ Scheme.Etale.mk (𝟙 C)).symm.op
  | true => exact genericTerminal (ModuleCat.{u + 1} A) i (constant A true C)

/-- Canonical section evaluation used in closed-source base change.
Source: Stacks 099W, degree zero and localization.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def localizationSections (A : Type (u + 1)) [CommRing A]
    {X : Scheme.{u}} (F : Modules A true X) (Y : X.ProEt) :
    F.obj.obj (op Y) ≅
      ((pull A true (X := Y.left) Y.hom).obj F).obj.obj (op (Scheme.ProEt.mk (𝟙 Y.left))) :=
  genericLocalization (ModuleCat.{u + 1} A) F Y

/-- Canonical section evaluation used in closed-source base change.
Source: Stacks 099W, degree zero and localization.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def sectionComposite
    {S : Type*} [Category S] {J : GrothendieckTopology S}
    {D : Type*} [Category D] {F G : Sheaf J D} {W : Sᵒᵖ}
    {B C : D} (l : B ⟶ F.obj.obj W) (r : G.obj.obj W ⟶ C)
    (f : F ⟶ G) : B ⟶ C := l ≫ f.hom.app W ≫ r

/-- The weakly etale exchange with constant coefficients as an isomorphism.
Source: Stacks 099W and canonical constant inverse image.
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def constantSectionExchangeIso (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) (Y : X.ProEt) :
    (pull A true (X := Y.left) Y.hom).obj (supported A true i) ≅
      supported A true (pullback.fst Y.hom i) :=
  (sectionBaseChangeIso (ModuleCat.{u + 1} A) i Y).app (constant A true C) ≪≫
    (push A true (pullback.fst Y.hom i)).mapIso
      (unitIso A true (pullback.snd Y.hom i))

/-- Evaluate a pro-etale constant direct image on a weakly etale test by restriction
of constants to its scheme fibre product. All identifications preserve constant scalars.
Source: Stacks 099W and the constant inverse-image identification
(blueprint: lem-pur-closed-source-site-tensor-comparison). -/
def proSupportSections (A : Type (u + 1)) [CommRing A]
    {C X : Scheme.{u}} (i : C ⟶ X) (Y : X.ProEt) :
    (supported A true i).obj.obj (op Y) ≅
      (constant A true (pullback Y.hom i)).obj.obj
        (op (Scheme.ProEt.mk (𝟙 (pullback Y.hom i)))) :=
  evaluatedSectionIso
    (localizationSections A (supported A true i) Y)
    (terminalSupport A true (X := Y.left) (pullback.fst Y.hom i))
    (constantSectionExchangeIso A i Y)
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison | J5 | Same canonical section map, identified by localization naturality and pullback uniqueness. |

## Status

landed 20261026T001858-L-37735 2026-10-26 (merge of deliver/J5/Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison)
