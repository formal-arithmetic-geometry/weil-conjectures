# Normalized finite descent interfaces

## Reason

The objectwise descent, morphism descent and finite-frame lemmas need the existing
labelled sections and finite-level category, but the main theorem now imports those
lemmas. Move their shared interfaces verbatim to
`Sheaf.AlgebraicGeometry.ConnectedAbelianTowerNormalizedData` to avoid an import cycle.
The original module publicly imports this data module and retains the package structure
and theorem. This is a dependency separation, not a compilation-time workaround: the
complete original assembly compiled in 14.5 seconds.

## Old

The following declarations and variable context were in
`Sheaf.AlgebraicGeometry.ConnectedAbelianTowerNormalizedDescent`:

```lean
/-- Profinite copies of a site object, retained over its original base.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def abelianTowerLabels {U : Scheme.{u}} (W : U.ProEt) : Profinite.{u} ⥤ U.ProEt :=
  profiniteToProEtOf W.left ⋙ MorphismProperty.Over.map ⊤ W.prop

/-- The pointed labelled neighborhood. Its geometric point is the specified label,
not an arbitrary point in the same connected component.
Source: Stacks, definition before Tag 0F6B; Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def abelianTowerLabelNeighbourhood {U : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ U} (W : U.ProEt)
    (w : Over.mk y ⟶ (Scheme.ProEt.forget U).obj W) (P : Profinite.{u}) (q : P) :
    Scheme.ProEtaleGeometricNeighbourhood y :=
  StructuredArrow.mk (Y := (abelianTowerLabels W).obj P)
    (Over.homMk (w.left ≫ Scheme.UniversalCover.profiniteProductSection _ P q) (by
      change w.left ≫ pullback.lift _ (𝟙 _) _ ≫ (pullback.snd _ _ ≫ W.hom) = y
      rw [pullback.lift_snd_assoc, Category.id_comp]
      have hw := w.w
      change w.left ≫ W.hom = y at hw
      exact hw))

/-- A universal finite label's germ in the actual geometric stalk.
Source: Stacks, Tag 0F6B
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def abelianTowerLabelGerm {U : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {y : Spec (.of Ω) ⟶ U} (W : U.ProEt)
    (w : Over.mk y ⟶ (Scheme.ProEt.forget U).obj W)
    (F : Sheaf (Scheme.ProEt.topology U) (Type (u + 1))) (A : FintypeCat.{u})
    (s : F.obj.obj (op ((abelianTowerLabels W).obj (FintypeCat.toProfinite.obj A))))
    (q : A) : Scheme.proEtaleGeometricSetStalk y F :=
  (colimit.ι (Scheme.proEtaleGeometricStalkDiagram y F)
    (op (abelianTowerLabelNeighbourhood W w (FintypeCat.toProfinite.obj A) q))) s

/-- Normalized universal sections are precisely inverse splittings to the finite
constant sheaf with the given fibre labels. Bijectivity is tested on every object
over W, so this predicate specifies an isomorphism of sheaves.
Source: Bhatt--Scholze, Lemmas 4.2.12 and 5.1.2
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def IsAbelianTowerNormalizedSection {U : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ U} (W : U.ProEt)
    (w : Over.mk y ⟶ (Scheme.ProEt.forget U).obj W)
    (F : Sheaf (Scheme.ProEt.topology U) (Type (u + 1))) (A : FintypeCat.{u})
    (e : ULift.{u + 1, u} A ≃ Scheme.proEtaleGeometricSetStalk y F)
    (s : F.obj.obj (op ((abelianTowerLabels W).obj (FintypeCat.toProfinite.obj A)))) :
    Prop :=
  (∀ V : W.left.ProEt, Function.Bijective
    (fun f : V ⟶ (profiniteToProEtOf W.left).obj (FintypeCat.toProfinite.obj A) ↦
      F.obj.map ((MorphismProperty.Over.map ⊤ W.prop).map f).op s)) ∧
    ∀ q : A, abelianTowerLabelGerm W w F A s q = e (ULift.up q)

/-- Transport of a fixed label space along a map of site objects.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def abelianTowerLabelTransport {U : Scheme.{u}} {W W' : U.ProEt}
    (f : W ⟶ W') (P : Profinite.{u}) :
    (abelianTowerLabels W).obj P ⟶ (abelianTowerLabels W').obj P :=
  MorphismProperty.Over.homMk (Scheme.UniversalCover.profiniteProductMap f.left (𝟙 P)) (by
    change Scheme.UniversalCover.profiniteProductMap f.left (𝟙 P) ≫
      (pullback.snd _ _ ≫ W'.hom) = pullback.snd _ _ ≫ W.hom
    simp only [Scheme.UniversalCover.profiniteProductMap, pullback.map, pullback.lift_snd_assoc,
      Category.assoc]
    have hf := f.w
    change f.left ≫ W'.hom = W.hom at hf
    rw [hf])

/-- Finite constancy after the specified inverse image, allowing the empty finite set.
Source: Bhatt--Scholze, Corollary 5.1.5, finite-set version
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def abelianTowerConstantAt {U : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology U) (Type (u + 1))) (W : U.ProEt) : Prop :=
  ∃ A : FintypeCat.{u}, Nonempty
    ((Scheme.proEtaleSheafInverseImage W.hom (Type (u + 1))).obj F ≅
      (constantSheaf (Scheme.ProEt.topology W.left) (Type (u + 1))).obj
        (ULift.{u + 1, u} A))

variable {U : Scheme.{u}} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]

/-- The full category L, with finite constancy required at some actual tower level.
Source: Bhatt--Scholze, Lemma 5.1.2, finite connected cover descent
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def ConnectedAbelianCoverTower.finiteLevel (T : ConnectedAbelianCoverTower U I) :
    ObjectProperty (Sheaf (Scheme.ProEt.topology U) (Type (u + 1))) :=
  fun F ↦ ∃ i : Iᵒᵖ, abelianTowerConstantAt F (T.levels.obj i)

/-- The geometric stalk on L, on maps as well as objects.
Source: Stacks, Tag 0F6B
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def ConnectedAbelianCoverTower.finiteLevelStalk (T : ConnectedAbelianCoverTower U I)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ T.cone.pt.left) :
    T.finiteLevel.FullSubcategory ⥤ Type (u + 1) :=
  ObjectProperty.ι T.finiteLevel ⋙
    sheafToPresheaf (Scheme.ProEt.topology U) (Type (u + 1)) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (Scheme.proEtaleGeometricNeighbourhoodForget (z ≫ T.cone.pt.hom)).op ⋙ colim
```

## New

The same declarations and variable context are in
`Sheaf.AlgebraicGeometry.ConnectedAbelianTowerNormalizedData`; their text is identical:

```lean
/-- Profinite copies of a site object, retained over its original base.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def abelianTowerLabels {U : Scheme.{u}} (W : U.ProEt) : Profinite.{u} ⥤ U.ProEt :=
  profiniteToProEtOf W.left ⋙ MorphismProperty.Over.map ⊤ W.prop

/-- The pointed labelled neighborhood. Its geometric point is the specified label,
not an arbitrary point in the same connected component.
Source: Stacks, definition before Tag 0F6B; Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def abelianTowerLabelNeighbourhood {U : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ U} (W : U.ProEt)
    (w : Over.mk y ⟶ (Scheme.ProEt.forget U).obj W) (P : Profinite.{u}) (q : P) :
    Scheme.ProEtaleGeometricNeighbourhood y :=
  StructuredArrow.mk (Y := (abelianTowerLabels W).obj P)
    (Over.homMk (w.left ≫ Scheme.UniversalCover.profiniteProductSection _ P q) (by
      change w.left ≫ pullback.lift _ (𝟙 _) _ ≫ (pullback.snd _ _ ≫ W.hom) = y
      rw [pullback.lift_snd_assoc, Category.id_comp]
      have hw := w.w
      change w.left ≫ W.hom = y at hw
      exact hw))

/-- A universal finite label's germ in the actual geometric stalk.
Source: Stacks, Tag 0F6B
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def abelianTowerLabelGerm {U : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {y : Spec (.of Ω) ⟶ U} (W : U.ProEt)
    (w : Over.mk y ⟶ (Scheme.ProEt.forget U).obj W)
    (F : Sheaf (Scheme.ProEt.topology U) (Type (u + 1))) (A : FintypeCat.{u})
    (s : F.obj.obj (op ((abelianTowerLabels W).obj (FintypeCat.toProfinite.obj A))))
    (q : A) : Scheme.proEtaleGeometricSetStalk y F :=
  (colimit.ι (Scheme.proEtaleGeometricStalkDiagram y F)
    (op (abelianTowerLabelNeighbourhood W w (FintypeCat.toProfinite.obj A) q))) s

/-- Normalized universal sections are precisely inverse splittings to the finite
constant sheaf with the given fibre labels. Bijectivity is tested on every object
over W, so this predicate specifies an isomorphism of sheaves.
Source: Bhatt--Scholze, Lemmas 4.2.12 and 5.1.2
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def IsAbelianTowerNormalizedSection {U : Scheme.{u}} {Ω : Type u}
    [Field Ω] [IsAlgClosed Ω] {y : Spec (.of Ω) ⟶ U} (W : U.ProEt)
    (w : Over.mk y ⟶ (Scheme.ProEt.forget U).obj W)
    (F : Sheaf (Scheme.ProEt.topology U) (Type (u + 1))) (A : FintypeCat.{u})
    (e : ULift.{u + 1, u} A ≃ Scheme.proEtaleGeometricSetStalk y F)
    (s : F.obj.obj (op ((abelianTowerLabels W).obj (FintypeCat.toProfinite.obj A)))) :
    Prop :=
  (∀ V : W.left.ProEt, Function.Bijective
    (fun f : V ⟶ (profiniteToProEtOf W.left).obj (FintypeCat.toProfinite.obj A) ↦
      F.obj.map ((MorphismProperty.Over.map ⊤ W.prop).map f).op s)) ∧
    ∀ q : A, abelianTowerLabelGerm W w F A s q = e (ULift.up q)

/-- Transport of a fixed label space along a map of site objects.
Source: Bhatt--Scholze, Lemma 4.2.12
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def abelianTowerLabelTransport {U : Scheme.{u}} {W W' : U.ProEt}
    (f : W ⟶ W') (P : Profinite.{u}) :
    (abelianTowerLabels W).obj P ⟶ (abelianTowerLabels W').obj P :=
  MorphismProperty.Over.homMk (Scheme.UniversalCover.profiniteProductMap f.left (𝟙 P)) (by
    change Scheme.UniversalCover.profiniteProductMap f.left (𝟙 P) ≫
      (pullback.snd _ _ ≫ W'.hom) = pullback.snd _ _ ≫ W.hom
    simp only [Scheme.UniversalCover.profiniteProductMap, pullback.map, pullback.lift_snd_assoc,
      Category.assoc]
    have hf := f.w
    change f.left ≫ W'.hom = W.hom at hf
    rw [hf])

/-- Finite constancy after the specified inverse image, allowing the empty finite set.
Source: Bhatt--Scholze, Corollary 5.1.5, finite-set version
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def abelianTowerConstantAt {U : Scheme.{u}}
    (F : Sheaf (Scheme.ProEt.topology U) (Type (u + 1))) (W : U.ProEt) : Prop :=
  ∃ A : FintypeCat.{u}, Nonempty
    ((Scheme.proEtaleSheafInverseImage W.hom (Type (u + 1))).obj F ≅
      (constantSheaf (Scheme.ProEt.topology W.left) (Type (u + 1))).obj
        (ULift.{u + 1, u} A))

variable {U : Scheme.{u}} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]

/-- The full category L, with finite constancy required at some actual tower level.
Source: Bhatt--Scholze, Lemma 5.1.2, finite connected cover descent
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def ConnectedAbelianCoverTower.finiteLevel (T : ConnectedAbelianCoverTower U I) :
    ObjectProperty (Sheaf (Scheme.ProEt.topology U) (Type (u + 1))) :=
  fun F ↦ ∃ i : Iᵒᵖ, abelianTowerConstantAt F (T.levels.obj i)

/-- The geometric stalk on L, on maps as well as objects.
Source: Stacks, Tag 0F6B
(blueprint: lem-sfb-connected-abelian-tower-normalized-descent). -/
def ConnectedAbelianCoverTower.finiteLevelStalk (T : ConnectedAbelianCoverTower U I)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ T.cone.pt.left) :
    T.finiteLevel.FullSubcategory ⥤ Type (u + 1) :=
  ObjectProperty.ι T.finiteLevel ⋙
    sheafToPresheaf (Scheme.ProEt.topology U) (Type (u + 1)) ⋙
    (Functor.whiskeringLeft _ _ _).obj
      (Scheme.proEtaleGeometricNeighbourhoodForget (z ≫ T.cone.pt.hom)).op ⋙ colim
```

The original module now has `public import
Sheaf.AlgebraicGeometry.ConnectedAbelianTowerNormalizedData`. All fully qualified names,
universes, signatures, reducibility, visibility and definition bodies are preserved.
The `ConnectedAbelianTowerNormalizedDescent` structure itself remains in its original
module. No axiom, unknown object or existence choice is introduced into any definition.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ConnectedAbelianTowerNormalizedDescent | Z6 | Imports the shared definitions publicly and proves its existing theorem from the separate lemmas. |
| Sheaf.AlgebraicGeometry.NormalizedFiniteSplittingOperations | unclaimed | Its existing public import still exposes every name unchanged. No adaptation needed. |
| Sheaf.AlgebraicGeometry.ConnectedAbelianTowerDescentObject | new, Z6 | Imports shared data and constructs the two overlap-label maps directly. |
| Sheaf.AlgebraicGeometry.ConnectedAbelianTowerDescentHom | new, Z6 | Imports the object interface and constructs labelMap directly from the stalk map. |
| Sheaf.AlgebraicGeometry.ConnectedAbelianTowerFiniteFrame | new, Z6 | Imports shared data for its finite-constancy statement. |

`tools/downstream.py` reports only `NormalizedFiniteSplittingOperations` as an existing
downstream module. None of its signatures or definitions change. The definition node
`def-sfb-finite-labelled-normalized-section` now points to the shared data module;
its mathematical statement is unchanged.

## Status

landed 20261023T152151-L-457777 2026-10-23 (merge of deliver/Z6/Sheaf.AlgebraicGeometry.ConnectedAbelianTowerNormalizedDescent)
