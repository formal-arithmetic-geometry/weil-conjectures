module

public import Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.EnlargedRingedCompositionLocalization
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Category.ULift

/-! # The pinned enlarged étale face total model

Source: Stacks 03G0, 03G7, 03G8, 09WC, 09WF, 0D70 and 0D72
(blueprint: def-sfb-enlarged-face-ringed-total-model).
The only change of size is the explicit AsSmall presentation and ULift of rings.
No site, topology, structural map, unitor or compositor can be chosen independently.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Bicategory
open CategoryTheory.SemisimplicialRingedTotal AlgebraicGeometry

namespace CategoryTheory.EnlargedFaceRingedTotal

/-- The actual enlarged site with object and arrow sizes made equal.
Source: Stacks 03G0 (blueprint: def-sfb-enlarged-face-ringed-total-model). -/
abbrev Objects {S : Scheme.{u}} (X : AlgebraicSpace S) := AsSmall.{u + 1} X.EnlargedEtaleSite

/-- Projection-preserving base change on the same enlarged objects.
Source: Stacks 03G2 (blueprint: def-sfb-enlarged-face-ringed-total-model). -/
def baseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Objects Y ⥤ Objects X :=
  AsSmall.down ⋙ AlgebraicSpace.enlargedBaseChange f ⋙ AsSmall.up

/-- Identity comparison is the existing projection unitor, with AsSmall wrappers.
Source: Stacks 03G2 (blueprint: def-sfb-enlarged-face-ringed-total-model). -/
def identityIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    baseChange (𝟙 X) ≅ 𝟭 (Objects X) :=
  Functor.isoWhiskerLeft AsSmall.down
    (Functor.isoWhiskerRight (AlgebraicSpace.enlargedIdentityIso X) AsSmall.up)

/-- Composition is precisely the projection-preserving fibre-product comparison.
Source: Stacks 03G2 (blueprint: def-sfb-enlarged-face-ringed-total-model). -/
def compositionIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) : baseChange g ⋙ baseChange f ≅ baseChange (f ≫ g) :=
  Functor.isoWhiskerLeft AsSmall.down
    (Functor.isoWhiskerRight (AlgebraicSpace.enlargedCompositionIso f g) AsSmall.up)

/-- The given covering families, on precisely the same algebraic-space arrows.
Source: Stacks 03G0 (blueprint: def-sfb-enlarged-face-ringed-total-model). -/
def coverage {S : Scheme.{u}} (X : AlgebraicSpace S) : Precoverage (Objects X) where
  coverings T := {R |
    (∀ (U : Objects X) (f : U ⟶ T), R f →
      AlgebraicSpace.IsChartwiseEtale (ULift.down f).hom.left) ∧
    AlgebraicSpace.IsJointlySurjective
      (fun a : R.uncurry ↦ (ULift.down a.1.2).hom.left.hom.hom)}

/-- Explicit ring coefficient lift, on objects and homomorphisms.
Source: Stacks size convention (blueprint: def-sfb-enlarged-face-ringed-total-model). -/
def liftRings : CommRingCat.{u} ⥤ CommRingCat.{u + 1} where
  obj R := CommRingCat.of (ULift.{u + 1} R)
  map f := CommRingCat.ofHom f.hom.ulift
  map_id _ := by ext x; rfl
  map_comp _ _ := by ext x; rfl

/-- Regular functions on enlarged objects, with an explicit coefficient lift.
Source: Stacks 03G7 (blueprint: def-sfb-enlarged-face-ringed-total-model). -/
def ringPresheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (Objects X)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  AsSmall.down.op ⋙ X.enlargedCotangentStructure.obj ⋙ liftRings

/-- The lifted regular functions satisfy exactly the enlarged coverage.
Source: Stacks 03G7, 03H7 (blueprint: def-sfb-enlarged-face-ringed-total-model).
Proof: AsSmall is the identity on the underlying enlarged objects and arrows.
The covering condition is unchanged. The ULift ring functor preserves the
compatible-family equalizers expressing the sheaf condition, so the sheaf
condition is that of enlargedCotangentStructure, with every section lifted. -/
theorem ringPresheaf_isSheaf {S : Scheme.{u}} (X : AlgebraicSpace S) :
    Presheaf.IsSheaf (coverage X).toGrothendieck (ringPresheaf X) := by
  sorry

/-- The actual enlarged ringed site in the dependency's common size convention.
Source: Stacks 03G0, 03G7 (blueprint: def-sfb-enlarged-face-ringed-total-model). -/
def site {S : Scheme.{u}} (X : AlgebraicSpace S) : Site.{u + 1} where
  C := Objects X
  J := (coverage X).toGrothendieck
  ring := ⟨ringPresheaf X, ringPresheaf_isSheaf X⟩

/-- The chart-normalized structural map, lifted on every section.
Its unique characterization is already supplied by the recorded enlarged-site node.
Source: Stacks 03G8 (blueprint: def-sfb-enlarged-face-ringed-total-model). -/
def structuralMap {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ringPresheaf Y ⟶ (baseChange f).op ⋙ ringPresheaf X :=
  Functor.whiskerLeft AsSmall.down.op
    (Functor.whiskerRight
      ((AlgebraicSpace.cotangentStructuralMap_existsUnique f).choose).hom liftRings)

/-- The canonical equivalence induced by equality of the whole ringed site.
There is no freely supplied module equivalence.
Source: Stacks 03D7 (blueprint: def-sfb-enlarged-face-ringed-total-model). -/
def modulesOfEq {X Y : Site.{v}} (h : X = Y) : X.modules ≌ Y.modules := by
  cases h
  exact Equivalence.refl

/-- The functor induced by equality of whole ringed sites.
Source: Stacks 03D7 (blueprint: def-sfb-enlarged-face-ringed-total-model). -/
def objectsOfEq {X Y : Site.{v}} (h : X = Y) : X.C ⥤ Y.C := by
  cases h
  exact 𝟭 _

/-- A fully pinned model of the actual enlarged étale face total category.
Objects, arrows, coverage, regular functions and Cartesian structural maps are
fixed. The face morphisms and their mates are then the dependency's normalized
ones. The augmentation direct image is base-change precomposition; its
comparison is the mate of the projection-preserving direct-image compositor.
Source: Stacks 03G0, 03G8, 09WC, 09WF, 0D70, 0D72
(blueprint: def-sfb-enlarged-face-ringed-total-model). -/
structure Model {S : Scheme.{u}} {Z : AlgebraicSpace S}
    (W : SemiSimplexCategoryᵒᵖ ⥤ Over Z) where
  index : LocallyDiscrete (SemiSimplexCategoryᵒᵖ)ᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1}
  objects : ∀ p : SemiSimplexCategoryᵒᵖ,
    index.obj ⟨op p⟩ = Cat.of (Objects (W.obj p).left)
  arrows : ∀ {p q : SemiSimplexCategoryᵒᵖ} (b : p ⟶ q),
    HEq (index.map b.op.toLoc).toFunctor (baseChange (W.map b).left)
  identities : ∀ p : SemiSimplexCategoryᵒᵖ,
    HEq (Cat.Hom.toNatIso (index.mapId ⟨op p⟩)) (identityIso (W.obj p).left)
  compositions : ∀ {p q r : SemiSimplexCategoryᵒᵖ} (b : p ⟶ q) (c : q ⟶ r),
    HEq (Cat.Hom.toNatIso (index.mapComp c.op.toLoc b.op.toLoc))
      (compositionIso (W.map b).left (W.map c).left).symm
  sites : CoherentSitePseudofunctor SemiSimplexCategoryᵒᵖ index
  coverings : ∀ p : SemiSimplexCategoryᵒᵖ,
    HEq (sites.coverage p) (coverage (W.obj p).left)
  rings : RingDiagram sites
  fibres : ∀ p : SemiSimplexCategoryᵒᵖ, rings.fibre p = site (W.obj p).left
  cartesian_ring : ∀ {p q : SemiSimplexCategoryᵒᵖ} (b : p ⟶ q)
    (V : index.obj ⟨op q⟩),
    HEq (rings.presheaf.map (Pseudofunctor.CoGrothendieck.cartesianLift V b).op)
      ((structuralMap (W.map b).left).app
        (op ((eqToHom (objects q)).toFunctor.obj V)))
  sheaf : Presheaf.IsSheaf sites.totalTopology rings.presheaf
  presentation : Presentation rings sheaf
  augmentation : Augmentation rings (site Z) presentation.face
    presentation.faceId presentation.faceComp
  augmentation_direct : ∀ (p : SemiSimplexCategoryᵒᵖ)
    (T : Sheaf (rings.fibre p).J (Type (u + 1))),
    HEq (((augmentation.map p).direct.obj T).obj)
      ((baseChange (W.obj p).hom).op ⋙
        (objectsOfEq (fibres p).symm).op ⋙ T.obj)
  augmentation_direct_map : ∀ (p : SemiSimplexCategoryᵒᵖ)
    {T U : Sheaf (rings.fibre p).J (Type (u + 1))} (b : T ⟶ U),
    HEq ((augmentation.map p).direct.map b).hom
      (Functor.whiskerLeft
        ((baseChange (W.obj p).hom).op ⋙
          (objectsOfEq (fibres p).symm).op) b.hom)
  augmentation_ring : ∀ (p : SemiSimplexCategoryᵒᵖ) (V : Objects Z),
    HEq (((augmentation.map p).adj.homEquiv _ _ (augmentation.map p).ringMap).hom.app
        (op V))
      ((forget CommRingCat.{u + 1}).map ((structuralMap (W.obj p).hom).app (op V)))
  augmentation_direct_composition : ∀ {p q : SemiSimplexCategoryᵒᵖ} (b : p ⟶ q),
    (presentation.face b).direct ⋙ (augmentation.map q).direct ≅ (augmentation.map p).direct
  augmentation_direct_composition_eq : ∀ {p q : SemiSimplexCategoryᵒᵖ} (b : p ⟶ q)
    (T : Sheaf (rings.fibre p).J (Type (u + 1))) (V : Objects Z),
    HEq (((augmentation_direct_composition b).hom.app T).hom.app (op V))
      (T.obj.map ((objectsOfEq (fibres p).symm).map
        ((compositionIso (W.map b).left (W.obj q).hom).inv.app V)).op)
  augmentation_comparison : ∀ {p q : SemiSimplexCategoryᵒᵖ} (b : p ⟶ q),
    augmentation.comparison b =
      (Adjunction.leftAdjointCompIso (augmentation.map q).adj (presentation.face b).adj
        (augmentation.map p).adj (augmentation_direct_composition b)).symm
  total : AugmentationPresentation presentation (site Z) augmentation

/-- The base is literally the normalized enlarged ringed site of Z.
Source: Stacks 03G0, 0D70 (blueprint: def-sfb-enlarged-face-ringed-total-model). -/
abbrev Model.base {S : Scheme.{u}} {Z : AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} (_G : Model W) := site Z

/-- Component module transport is induced by equality of the whole ringed site.
Source: Stacks 03D7 (blueprint: def-sfb-enlarged-face-ringed-total-model). -/
def Model.componentEquivalence {S : Scheme.{u}} {Z : AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} (G : Model W) (p : SemiSimplexCategoryᵒᵖ) :=
  modulesOfEq (G.fibres p)

end CategoryTheory.EnlargedFaceRingedTotal
