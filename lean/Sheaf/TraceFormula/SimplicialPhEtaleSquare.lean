/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PhEtaleTorsionComparison
public import Sheaf.AlgebraicGeometry.TotalSimplicialEtaleSite
public import Sheaf.CategoryTheory.SliceSiteSimplicialAugmentation
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Sheaf.AlgebraicGeometry.PhSchemeSite
import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.TraceFormula.TotalSiteDerivedComponents

/-!
# The augmented simplicial ph--étale comparison square

Source: Stacks Project, spaces-simplicial.tex, Tags 0DHJ and 0D99
(blueprint: lem-trf-simplicial-ph-etale-square).

The total comparison is induced by the actual inclusion on total sites. The ph
augmentation uses the slice-site construction. The étale augmentation is the
sheafification of the degreewise Kan-extension construction of inverse image.
All comparisons below are normalized by the units of these adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unnecessarySimpa false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.SimplicialPhEtale

/-- Use the already fixed small presentation of the ph site, in every degree.
Source: Stacks, Tag 0DHJ (blueprint: lem-trf-simplicial-ph-etale-square). -/
abbrev modelObject {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :=
  Over.lift U a ⋙ (AsSmall.up : Over X ⥤ Scheme.phSiteModel.{u, u} X)

/-- The total ph topos, on the single ph presentation fixed above.
Source: Stacks, Tags 09WL and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
abbrev PhTotalTopos {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :=
  Sheaf (SimplicialSliceSite.topology (Scheme.phModelTopology.{u, u} X)
    (modelObject a)) (Type (u + 1))

/-- The degreewise ph component in that same presentation.
Source: Stacks, Tags 09WL and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
abbrev PhComponentTopos {X T : Scheme.{u}} (f : T ⟶ X) :=
  Sheaf ((Scheme.phModelTopology.{u, u} X).over
    ((AsSmall.up : Over X ⥤ Scheme.phSiteModel.{u, u} X).obj (Over.mk f)))
    (Type (u + 1))

/-- Component evaluation, including all restriction maps. Source: Stacks, Tag 09WL
(blueprint: lem-trf-simplicial-ph-etale-square). -/
abbrev phRestriction {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (n : ℕ) :=
  SimplicialSliceSite.componentRestriction (Scheme.phModelTopology.{u, u} X)
    (modelObject a) (op (SimplexCategory.mk n)) (Type (u + 1))

/-- Flatten the iterated slice: `(V/X → T/X)` is the scheme `V/T`.
Source: Stacks, Tags 09WL and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def flatten {X T : Scheme.{u}} (f : T ⟶ X) :
    Over ((AsSmall.up : Over X ⥤ Scheme.phSiteModel.{u, u} X).obj (Over.mk f)) ⥤
      Scheme.phSiteModel.{u, u} T :=
  Over.post (AsSmall.down : Scheme.phSiteModel.{u, u} X ⥤ Over X) ⋙
    Over.iteratedSliceForward (Over.mk f) ⋙ AsSmall.up

/-- The inverse of flattening sends `V/T` to `V/X → T/X`.
Source: Stacks, Tags 09WL and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def unflatten {X T : Scheme.{u}} (f : T ⟶ X) :
    Scheme.phSiteModel.{u, u} T ⥤
      Over ((AsSmall.up : Over X ⥤ Scheme.phSiteModel.{u, u} X).obj (Over.mk f)) :=
  AsSmall.down ⋙ Over.iteratedSliceBackward (Over.mk f) ⋙
    Over.post (AsSmall.up : Over X ⥤ Scheme.phSiteModel.{u, u} X)

/-- The canonical slice identification preserves the ph topologies in both directions.
Source: Stacks, Tags 09WL and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square).
Proof: flattening is the iterated-slice equivalence. Localized covers are precisely
underlying covers. Open covering families and proper surjections are unchanged by
flattening, in both directions; transport along `AsSmall` retains this assertion. -/
theorem flatten_continuous {X T : Scheme.{u}} (f : T ⟶ X) :
    (flatten f).IsContinuous
      ((Scheme.phModelTopology.{u, u} X).over (AsSmall.up.obj (Over.mk f)))
      (Scheme.phModelTopology.{u, u} T) ∧
    (unflatten f).IsContinuous (Scheme.phModelTopology.{u, u} T)
      ((Scheme.phModelTopology.{u, u} X).over (AsSmall.up.obj (Over.mk f))) := by
  sorry

/-- Continuity for the canonical flattening. Source: Stacks, Tag 09WL
(blueprint: lem-trf-simplicial-ph-etale-square). -/
instance flatten_isContinuous {X T : Scheme.{u}} (f : T ⟶ X) :
    (flatten f).IsContinuous
      ((Scheme.phModelTopology.{u, u} X).over (AsSmall.up.obj (Over.mk f)))
      (Scheme.phModelTopology.{u, u} T) := (flatten_continuous f).1

/-- Continuity for the canonical inverse identification. Source: Stacks, Tag 09WL
(blueprint: lem-trf-simplicial-ph-etale-square). -/
instance unflatten_isContinuous {X T : Scheme.{u}} (f : T ⟶ X) :
    (unflatten f).IsContinuous (Scheme.phModelTopology.{u, u} T)
      ((Scheme.phModelTopology.{u, u} X).over (AsSmall.up.obj (Over.mk f))) :=
  (flatten_continuous f).2

/-- The slice-topos identification has its canonical restriction adjunction.
Source: Stacks, Tags 09WL and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square).
Proof: the iterated-slice equivalence and the `AsSmall` equivalence give mutually
inverse restrictions on sheaves. Their identity unit and counit give the adjunction.
The identity-on-sections unit uniquely determines the adjunction, since both
functors are equivalences. Thus the chosen datum is fixed by this normalization. -/
theorem flatten_adjunction {X T : Scheme.{u}} (f : T ⟶ X) :
    ∃! adj : (flatten f).sheafPushforwardContinuous (Type (u + 1))
      ((Scheme.phModelTopology.{u, u} X).over (AsSmall.up.obj (Over.mk f)))
      (Scheme.phModelTopology.{u, u} T) ⊣
      (unflatten f).sheafPushforwardContinuous (Type (u + 1))
        (Scheme.phModelTopology.{u, u} T)
        ((Scheme.phModelTopology.{u, u} X).over (AsSmall.up.obj (Over.mk f))),
      ∀ (E : Scheme.PhSheaf.{u, u} T) (V : Scheme.phSiteModel.{u, u} T),
        (adj.unit.app E).hom.app (op V) = 𝟙 (E.obj.obj (op V)) := by
  sorry

/-- Transport from a slice component to the existing big ph topos.
Source: Stacks, Tags 09WL and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def sliceTransport {X T : Scheme.{u}} (f : T ⟶ X) :
    GeometricMorphism (PhComponentTopos f) (Scheme.PhSheaf.{u, u} T) where
  inverse := (flatten f).sheafPushforwardContinuous (Type (u + 1)) _ _
  direct := (unflatten f).sheafPushforwardContinuous (Type (u + 1)) _ _
  adj := (flatten_adjunction f).choose
  leftExact := inferInstance

/-- The component comparison is the published inclusion-induced morphism, transported
along the canonical iterated-slice identification. Source: Stacks, Tag 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def componentComparison {X T : Scheme.{u}} (f : T ⟶ X) :=
  (sliceTransport f).comp (Scheme.phEtaleGeometricMorphism.{u, u} T)

/-- The actual degreewise inclusion into the total ph site. Both arrow components
are retained, so it commutes with every face and degeneracy. Source: Stacks, Tag 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def totalInclusion {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    TotalEtaleSite U ⥤ SimplicialSliceSite.Total (modelObject a) where
  obj W :=
    { left := AsSmall.up.obj (Over.mk (W.obj.hom ≫ a.app W.obj.right))
      right := W.obj.right
      hom := AsSmall.up.map (Over.homMk W.obj.hom) }
  map {W Z} f :=
    { left := AsSmall.up.map (Over.homMk f.hom.left (by
        dsimp
        have hw := f.hom.w
        change f.hom.left ≫ Z.obj.hom = W.obj.hom ≫ U.map f.hom.right at hw
        rw [← Category.assoc, hw, Category.assoc]
        simpa using congrArg (fun t ↦ W.obj.hom ≫ t) (a.naturality f.hom.right)))
      right := f.hom.right
      w := by apply ULift.ext; ext; exact f.hom.w }
  map_id W := by ext <;> rfl
  map_comp f g := by ext <;> rfl

/-- The total inclusion is continuous. Source: Stacks, Tags 0D96 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square).
Proof: coverings are generated in a single degree. The inclusion on that degree
is the continuous ph/étale inclusion, transported by the slice equivalence. Its
commuting-square arrow formula respects base changes and their projections. -/
theorem totalInclusion_continuous {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (totalInclusion a).IsContinuous (totalEtaleTopology U)
      (SimplicialSliceSite.topology (Scheme.phModelTopology.{u, u} X)
        (modelObject a)) := by
  sorry

attribute [instance] totalInclusion_continuous

/-- The total direct image is literal restriction along the total inclusion.
Source: Stacks, Tags 0D96 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
abbrev totalDirect {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :=
  (totalInclusion a).sheafPushforwardContinuous (Type (u + 1))
    (totalEtaleTopology U)
    (SimplicialSliceSite.topology (Scheme.phModelTopology.{u, u} X) (modelObject a))

/-- The canonical sheafified Kan extension is left exact. Source: Stacks, Tag 0D96
(blueprint: lem-trf-simplicial-ph-etale-square).
Proof: the component left adjoints are the inclusion inverse images. Their
base-change comparisons commute with transitions by uniqueness of the maps
preserving the two fibre-product projections. Componentwise transposition is
an adjunction on families; finite limits are computed componentwise. -/
theorem totalDirect_properties {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (totalDirect a).IsRightAdjoint := by
  sorry

attribute [instance] totalDirect_properties

/-- Left exactness of the specified inverse image. Source: Stacks, Tag 0D96
(blueprint: lem-trf-simplicial-ph-etale-square).
Proof: the componentwise adjunction in step 3 identifies this unique left adjoint
with the component inverse images; those preserve finite limits. -/
theorem totalInverse_leftExact {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    PreservesFiniteLimits (totalDirect a).leftAdjoint := by
  sorry

/-- The induced total geometric morphism, determined by the actual total inclusion.
Source: Stacks, Tags 0D96 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def totalComparison {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    GeometricMorphism (PhTotalTopos a) (TotalEtaleTopos U) where
  inverse := (totalDirect a).leftAdjoint
  direct := totalDirect a
  adj := Adjunction.ofIsRightAdjoint _
  leftExact := totalInverse_leftExact a

/-- Lift the augmentation to the slice over the identity of `X/X`.
Source: Stacks, Tags 0D70 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def phAugmentedObject {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    SimplicialObject (Over
      ((AsSmall.up : Over X ⥤ Scheme.phSiteModel.{u, u} X).obj (Over.mk (𝟙 X)))) :=
  Over.lift (modelObject a)
    { app n := AsSmall.up.map (Over.homMk (a.app n))
      naturality {n m} α := by
        apply ULift.ext
        ext
        change U.map α ≫ a.app m = a.app n
        exact (a.naturality α).trans (Category.comp_id _) }

/-- The ph augmentation is exactly the slice-site geometric morphism, with the
canonical transport from the terminal slice to the published ph topos.
Source: Stacks, Tags 0D70 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def phAugmentation {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    GeometricMorphism (PhTotalTopos a) (Scheme.PhSheaf.{u, u} X) :=
  (SimplicialSliceSite.geometricMorphism (Scheme.phModelTopology.{u, u} X)
    (phAugmentedObject a)).comp (sliceTransport (𝟙 X))

/-- Projection of an étale total object to its scheme over `X` in the fixed model.
Source: Stacks, Tags 0D70 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def etaleProjection {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    TotalEtaleSite U ⥤ Scheme.phSiteModel.{u, u} X :=
  totalInclusion a ⋙ SimplicialSliceSite.projection (phAugmentedObject a) ⋙
    flatten (𝟙 X)

/-- The étale augmentation inverse image is the standard sheafified Kan-extension
formula: at `(n,W)` extend the original étale sheaf to the scheme `W → X`, and
then sheafify on the total étale site. Its restriction to degree `n` is `a_n⁻¹`.
Source: Stacks, Tags 0D70, 0D96 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def etaleInverse {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤ TotalEtaleTopos U :=
  sheafToPresheaf _ _ ⋙ (Scheme.phEtaleInclusion.{u, u} X).op.lan ⋙
    (Functor.whiskeringLeft _ _ _).obj (etaleProjection a).op ⋙
    presheafToSheaf (totalEtaleTopology U) (Type (u + 1))

/-- The specified étale augmentation inverse image has a right adjoint and is left
exact. Source: Stacks, Tag 0D70 (blueprint: lem-trf-simplicial-ph-etale-square).
Proof: in degree `n` the Kan-extension formula is the ordinary étale inverse image
along `a_n`; it glues with the canonical base-change transitions. The
componentwise adjunction on compatible families supplies its right adjoint.
Finite limits are computed degreewise and the ordinary inverse images are left exact. -/
theorem etaleInverse_properties {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (etaleInverse a).IsLeftAdjoint ∧ PreservesFiniteLimits (etaleInverse a) := by
  sorry

/-- The right adjoint is determined by the specified augmentation inverse image.
Source: Stacks, Tag 0D70 (blueprint: lem-trf-simplicial-ph-etale-square). -/
instance etaleInverse_isLeftAdjoint {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (etaleInverse a).IsLeftAdjoint := (etaleInverse_properties a).1

/-- The étale augmentation geometric morphism with its canonical inverse image.
Source: Stacks, Tags 0D70 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def etaleAugmentation {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    GeometricMorphism (TotalEtaleTopos U)
      (Sheaf X.smallEtaleTopology (Type (u + 1))) where
  inverse := etaleInverse a
  direct := (etaleInverse a).rightAdjoint
  adj := Adjunction.ofIsLeftAdjoint _
  leftExact := (etaleInverse_properties a).2

/-- The direct-image component comparison is identity on sections of every étale
object. It includes the restriction maps. Source: Stacks, Tag 0D96
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def directComponentIso {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (n : ℕ) :
    phRestriction a n ⋙ (componentComparison (a.app (op (SimplexCategory.mk n)))).direct ≅
      (totalComparison a).direct ⋙ totalEtaleRestriction U n (Type (u + 1)) :=
  NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun V ↦ Iso.refl _)))

/-- The inverse-image component map is the mate of the identity-on-sections direct
comparison. Its invertibility asserts the component inverse-image formula, with
its adjunction normalization. Source: Stacks, Tag 0D96
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def inverseComponentMap {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (n : ℕ) :
    totalEtaleRestriction U n (Type (u + 1)) ⋙
        (componentComparison (a.app (op (SimplexCategory.mk n)))).inverse ⟶
      (totalComparison a).inverse ⋙ phRestriction a n :=
  (((componentComparison (a.app (op (SimplexCategory.mk n)))).adj.whiskerRight
    (TotalEtaleTopos U)).homEquiv _ _).symm
      (whiskerRight (totalComparison a).adj.unit
          (totalEtaleRestriction U n (Type (u + 1))) ≫
        whiskerLeft (totalComparison a).inverse (directComponentIso a n).inv)

/-- The map from the presheaf Kan extension to the actual ph inverse image is
uniquely specified by the published inclusion adjunction's unit. Source: Stacks,
Tags 00WX and 0DHJ (blueprint: lem-trf-simplicial-ph-etale-square). -/
def extensionToPh (X : Scheme.{u}) :
    sheafToPresheaf X.smallEtaleTopology (Type (u + 1)) ⋙
        (Scheme.phEtaleInclusion.{u, u} X).op.lan ⟶
      (Scheme.phEtaleGeometricMorphism.{u, u} X).inverse ⋙
        sheafToPresheaf (Scheme.phModelTopology.{u, u} X) (Type (u + 1)) :=
  ((((Scheme.phEtaleInclusion.{u, u} X).op.lanAdjunction (Type (u + 1))).whiskerRight
    (Sheaf X.smallEtaleTopology (Type (u + 1)))).homEquiv _ _).symm
      (whiskerRight (Scheme.phEtaleGeometricMorphism.{u, u} X).adj.unit
        (sheafToPresheaf X.smallEtaleTopology (Type (u + 1))))

/-- The preliminary square map is induced from `extensionToPh` by projection and
by the universal property of total étale sheafification. Thus its component at
`(n,W)` uses exactly the étale-object inclusion and the map `W → U_n → X`.
Source: Stacks, Tags 0D70 and 0D99
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def squareUnit {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (etaleAugmentation a).inverse ⟶
      (Scheme.phEtaleGeometricMorphism.{u, u} X).inverse ⋙
        (phAugmentation a).inverse ⋙ (totalComparison a).direct :=
  (((sheafificationAdjunction (totalEtaleTopology U) (Type (u + 1))).whiskerRight
    (Sheaf X.smallEtaleTopology (Type (u + 1)))).homEquiv
      (sheafToPresheaf X.smallEtaleTopology (Type (u + 1)) ⋙
        (Scheme.phEtaleInclusion.{u, u} X).op.lan ⋙
        (Functor.whiskeringLeft _ _ _).obj (etaleProjection a).op)
      ((Scheme.phEtaleGeometricMorphism.{u, u} X).inverse ⋙
        (phAugmentation a).inverse ⋙ (totalComparison a).direct)).symm
      (whiskerRight (extensionToPh X)
        ((Functor.whiskeringLeft _ _ _).obj (etaleProjection a).op))

/-- The canonical square comparison is the mate of `squareUnit`, rather than a
choice of a natural isomorphism. Source: Stacks, Tags 0D99 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def squareMap {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (etaleAugmentation a).inverse ⋙ (totalComparison a).inverse ⟶
      (Scheme.phEtaleGeometricMorphism.{u, u} X).inverse ⋙ (phAugmentation a).inverse :=
  (((totalComparison a).adj.whiskerRight
    (Sheaf X.smallEtaleTopology (Type (u + 1)))).homEquiv _ _).symm (squareUnit a)

/-- The component localization inverse image, on the same ph presentation as the
augmentation. Source: Stacks, Tags 09W9 and 0D70
(blueprint: lem-trf-simplicial-ph-etale-square). -/
abbrev phComponentInverse {X T : Scheme.{u}} (f : T ⟶ X) :=
  (sliceTransport (𝟙 X)).inverse ⋙
    (Scheme.phModelTopology.{u, u} X).overMapPullback (Type (u + 1))
      (AsSmall.up.map (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 X)))

/-- The augmentation's canonical component identification, inherited from the
slice-site theorem. Source: Stacks, Tag 0D70
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def phAugmentationComponentIso {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (n : ℕ) :
    (phAugmentation a).inverse ⋙ phRestriction a n ≅
      phComponentInverse (a.app (op (SimplexCategory.mk n))) :=
  isoWhiskerLeft (sliceTransport (𝟙 X)).inverse
    (SimplicialSliceSite.inverseComponentIso (Scheme.phModelTopology.{u, u} X)
      (phAugmentedObject a) (op (SimplexCategory.mk n)) (Type (u + 1)))

/-- At one degree, the étale-object inclusion followed by the augmentation gives
exactly `V/T → V/X`. Source: Stacks, Tags 0D99 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def componentEtaleProjection {X T : Scheme.{u}} (f : T ⟶ X) :
    T.Etale ⥤ Scheme.phSiteModel.{u, u} X :=
  Scheme.phEtaleInclusion.{u, u} T ⋙ unflatten f ⋙
    Over.map (AsSmall.up.map (Over.homMk f : Over.mk f ⟶ Over.mk (𝟙 X))) ⋙
    flatten (𝟙 X)

/-- The degreewise Kan-extension expression used in the total augmentation.
Its normalized identification with the existing ordinary inverse image is below.
Source: Stacks, Tags 00WX and 0D70
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def componentKanExtension {X T : Scheme.{u}} (f : T ⟶ X) :
    Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf T.smallEtaleTopology (Type (u + 1)) :=
  sheafToPresheaf _ _ ⋙ (Scheme.phEtaleInclusion.{u, u} X).op.lan ⋙
    (Functor.whiskeringLeft _ _ _).obj (componentEtaleProjection f).op ⋙
    presheafToSheaf T.smallEtaleTopology (Type (u + 1))

/-- The component square is normalized by the very same inclusion unit as the
total square. Source: Stacks, Tags 0D99 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def componentSquareUnit {X T : Scheme.{u}} (f : T ⟶ X) :
    componentKanExtension f ⟶ (Scheme.phEtaleGeometricMorphism.{u, u} X).inverse ⋙
      phComponentInverse f ⋙ (componentComparison f).direct :=
  (((sheafificationAdjunction T.smallEtaleTopology (Type (u + 1))).whiskerRight
    (Sheaf X.smallEtaleTopology (Type (u + 1)))).homEquiv
      (sheafToPresheaf X.smallEtaleTopology (Type (u + 1)) ⋙
        (Scheme.phEtaleInclusion.{u, u} X).op.lan ⋙
        (Functor.whiskeringLeft _ _ _).obj (componentEtaleProjection f).op)
      ((Scheme.phEtaleGeometricMorphism.{u, u} X).inverse ⋙
        phComponentInverse f ⋙ (componentComparison f).direct)).symm
      (whiskerRight (extensionToPh X)
        ((Functor.whiskeringLeft _ _ _).obj (componentEtaleProjection f).op))

/-- The canonical comparison `θ_n` is the mate of the inclusion-normalized
component unit. Source: Stacks, Tags 0D99 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def componentSquareMap {X T : Scheme.{u}} (f : T ⟶ X) :
    componentKanExtension f ⋙ (componentComparison f).inverse ⟶
      (Scheme.phEtaleGeometricMorphism.{u, u} X).inverse ⋙ phComponentInverse f :=
  (((componentComparison f).adj.whiskerRight
    (Sheaf X.smallEtaleTopology (Type (u + 1)))).homEquiv _ _).symm
      (componentSquareUnit f)

/-- The ordinary étale inverse image maps to the component of the total
augmentation by the unit of total-site sheafification. Source: Stacks, Tag 0D70
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def etaleAugmentationComponentMap {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (n : ℕ) :
    componentKanExtension (a.app (op (SimplexCategory.mk n))) ⟶
      (etaleAugmentation a).inverse ⋙ totalEtaleRestriction U n (Type (u + 1)) :=
  (((sheafificationAdjunction
    (U.obj (op (SimplexCategory.mk n))).smallEtaleTopology (Type (u + 1))).whiskerRight
      (Sheaf X.smallEtaleTopology (Type (u + 1)))).homEquiv
      (sheafToPresheaf X.smallEtaleTopology (Type (u + 1)) ⋙
        (Scheme.phEtaleInclusion.{u, u} X).op.lan ⋙
        (Functor.whiskeringLeft _ _ _).obj
          (componentEtaleProjection (a.app (op (SimplexCategory.mk n)))).op)
      ((etaleAugmentation a).inverse ⋙
        totalEtaleRestriction U n (Type (u + 1)))).symm
    (whiskerRight
      (whiskerLeft
        (sheafToPresheaf X.smallEtaleTopology (Type (u + 1)) ⋙
          (Scheme.phEtaleInclusion.{u, u} X).op.lan ⋙
          (Functor.whiskeringLeft _ _ _).obj (etaleProjection a).op)
        (sheafificationAdjunction (totalEtaleTopology U) (Type (u + 1))).unit)
      ((Functor.whiskeringLeft _ _ _).obj (totalEtaleComponent U n).op))

/-- The projection from the base change of an étale object to that object,
in the fixed ph presentation. Source: Stacks, Tags 0D99 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def componentBaseChangeProjection {X T : Scheme.{u}} (f : T ⟶ X) (V : X.Etale) :
    (componentEtaleProjection f).obj
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V) ⟶
      (Scheme.phEtaleInclusion.{u, u} X).obj V :=
  AsSmall.up.map (Over.homMk (pullback.fst V.hom f) (by
    exact pullback.condition))

/-- Continuity of the existing ordinary small-étale base-change functor.
Source: Stacks, Tags 03Q1 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
instance etaleBaseChange_isContinuous {X T : Scheme.{u}} (f : T ⟶ X) :
    (MorphismProperty.Over.pullback @Etale ⊤ f).IsContinuous
      X.smallEtaleTopology T.smallEtaleTopology :=
  (AlgebraicGeometry.etaleSetInverseImage_exact f).1

/-- The Kan-extension expression is identified with the existing ordinary
small-étale pullback by its unit on every étale object. This normalization
uniquely determines the isomorphism, so no inverse-image functor is replaced by
an arbitrary choice. Source: Stacks, Tags 00WX, 0D70 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square).
Proof: the projection `V ×_X T → V` induces the displayed map from the original
sheaf into the base-change direct image of the Kan expression. Transpose under
the ordinary site adjunction. The universal properties of Kan extension and
sheafification show it is an isomorphism: both constructions sheafify the same
colimit of étale neighborhoods over every `T`-scheme. Transposition also proves
uniqueness from the displayed equation. The projections give naturality in
objects and in composites of scheme maps. -/
theorem componentKanExtension_comparison {X T : Scheme.{u}} (f : T ⟶ X) :
    ∃! e : Functor.sheafPullbackConstruction.sheafPullback
        (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
        X.smallEtaleTopology T.smallEtaleTopology ≅ componentKanExtension f,
      ∀ (G : Sheaf X.smallEtaleTopology (Type (u + 1))) (V : X.Etale),
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
          X.smallEtaleTopology T.smallEtaleTopology).unit.app G).hom.app (op V) ≫
            (e.hom.app G).hom.app
              (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)) =
        ((Scheme.phEtaleInclusion.{u, u} X).op.lanUnit.app G.obj).app (op V) ≫
          ((Scheme.phEtaleInclusion.{u, u} X).op.lan.obj G.obj).map
            (componentBaseChangeProjection f V).op ≫
          ((sheafificationAdjunction T.smallEtaleTopology (Type (u + 1))).unit.app
            ((componentEtaleProjection f).op ⋙
              (Scheme.phEtaleInclusion.{u, u} X).op.lan.obj G.obj)).app
                (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj V)) := by
  sorry

/-- The uniquely unit-normalized identification with the published ordinary
étale inverse image. Source: Stacks, Tags 00WX and 0D70
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def componentKanIso {X T : Scheme.{u}} (f : T ⟶ X) :
    Functor.sheafPullbackConstruction.sheafPullback
      (MorphismProperty.Over.pullback @Etale ⊤ f) (Type (u + 1))
      X.smallEtaleTopology T.smallEtaleTopology ≅ componentKanExtension f :=
  (componentKanExtension_comparison f).choose

/-- The augmentation component map, with the already defined ordinary small-étale
inverse image as its source. Source: Stacks, Tag 0D70
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def ordinaryAugmentationComponentMap {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (n : ℕ) :=
  (componentKanIso (a.app (op (SimplexCategory.mk n)))).hom ≫
    etaleAugmentationComponentMap a n

/-- The specified `θ_n` for the existing ordinary étale inverse image, normalized
by the inclusion unit and the base-change projection. Source: Stacks, Tag 0D99
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def ordinaryComponentSquareMap {X T : Scheme.{u}} (f : T ⟶ X) :=
  whiskerRight (componentKanIso f).hom (componentComparison f).inverse ≫
    componentSquareMap f

/-- The augmented simplicial ph--étale comparison square, for the actual maps
constructed above. Source: Stacks, Tags 0DHJ, 0D96 and 0D99
(blueprint: lem-trf-simplicial-ph-etale-square).

Proof:
1. Regard the augmentation in `Sch/X`, transport it to the fixed ph presentation,
   and apply the slice-site construction. Flattening a slice at `U_n/X` gives
   exactly the ph site of `U_n`, since its Zariski and proper-surjective
   generators are unchanged. Iterated pullback identifications preserve both
   projections, so identities and compositions are coherent.
2. Use the published inclusion-induced `phEtaleGeometricMorphism` in every degree
   and over `X`. For any structure or augmentation map, inclusion followed by
   big base change and small base change followed by inclusion both give
   `V ×_T T'`. Their arrow maps are also the same. Uniqueness of the maps with
   those projections proves compatibility with all compositions.
3. The inclusion on total sites is continuous degreewise. Its direct image is
   restriction, giving `directComponentIso`. Componentwise transposition under
   the inclusion adjunctions respects the transition squares. It therefore
   supplies the total inverse image, and its normalized component mate
   `inverseComponentMap` is invertible.
4. For every augmentation map the same inclusion/base-change calculation gives
   the invertibility of `ordinaryComponentSquareMap`. Its defining unit fixes `θ_n`,
   rather than merely asserting some isomorphism. For every simplicial operator
   the two comparisons preserve the projections to `V` and the new base; hence
   they agree. This includes faces, degeneracies, identities and compositions.
5. Étale augmentation inverse image is the degreewise sheafified Kan extension;
   the ph augmentation is the slice-site inverse image. The compatible `θ_n`
   assemble to `squareMap`, which is consequently invertible. Its displayed
   component equality records the exact normalization. The adjunction mate is
   the isomorphism `a ∘ h ≅ h_X ∘ b`. No properness, surjectivity or hypercover
   assumption is used. -/
theorem simplicial_ph_etale_square {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (∀ n : ℕ, IsIso (inverseComponentMap a n)) ∧
    (∀ n : ℕ, IsIso (ordinaryAugmentationComponentMap a n)) ∧
    (∀ n : ℕ, IsIso (ordinaryComponentSquareMap (a.app (op (SimplexCategory.mk n))))) ∧
    IsIso (squareMap a) ∧
    (∀ n : ℕ,
      whiskerRight (ordinaryAugmentationComponentMap a n)
          (componentComparison (a.app (op (SimplexCategory.mk n)))).inverse ≫
        whiskerLeft (etaleAugmentation a).inverse (inverseComponentMap a n) ≫
        whiskerRight (squareMap a) (phRestriction a n) ≫
        whiskerLeft (Scheme.phEtaleGeometricMorphism.{u, u} X).inverse
          (phAugmentationComponentIso a n).hom =
        ordinaryComponentSquareMap (a.app (op (SimplexCategory.mk n)))) := by
  sorry

/-- The inverse-image component formula for the actual total comparison.
Source: Stacks, Tags 0D96 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def inverseComponentIso {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) (n : ℕ) :
    (totalComparison a).inverse ⋙ phRestriction a n ≅
      totalEtaleRestriction U n (Type (u + 1)) ⋙
        (componentComparison (a.app (op (SimplexCategory.mk n)))).inverse := by
  letI := (simplicial_ph_etale_square a).1 n
  exact (asIso (inverseComponentMap a n)).symm

/-- The canonical inverse-image square, with the normalization stated by the main
theorem. Source: Stacks, Tags 0D99 and 0DHJ
(blueprint: lem-trf-simplicial-ph-etale-square). -/
def inverseSquareIso {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    (etaleAugmentation a).inverse ⋙ (totalComparison a).inverse ≅
      (Scheme.phEtaleGeometricMorphism.{u, u} X).inverse ⋙ (phAugmentation a).inverse := by
  letI := (simplicial_ph_etale_square a).2.2.2.1
  exact asIso (squareMap a)

/-- The isomorphism of geometric morphisms `a ∘ h ≅ h_X ∘ b`, on direct images,
is the adjunction mate of the specified inverse-image square. Source: Stacks,
Tags 0D99 and 0DHJ (blueprint: lem-trf-simplicial-ph-etale-square). -/
def geometricSquareIso {U : SimplicialObject Scheme.{u}} {X : Scheme.{u}}
    (a : U ⟶ (Functor.const SimplexCategoryᵒᵖ).obj X) :
    ((totalComparison a).comp (etaleAugmentation a)).direct ≅
      ((phAugmentation a).comp (Scheme.phEtaleGeometricMorphism.{u, u} X)).direct :=
  (conjugateIsoEquiv ((totalComparison a).comp (etaleAugmentation a)).adj
    ((phAugmentation a).comp (Scheme.phEtaleGeometricMorphism.{u, u} X)).adj)
      (inverseSquareIso a).symm

end AlgebraicGeometry.SimplicialPhEtale
