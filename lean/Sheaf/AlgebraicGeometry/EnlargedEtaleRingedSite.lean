/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
import Sheaf.CategoryTheory.Sites.SliceSubtoposSitePresentation
import Sheaf.CategoryTheory.SpecialCocontinuousSheafEquivalence
import Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects
import Sheaf.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import Sheaf.CategoryTheory.RingedToposMorphism
import Sheaf.AlgebraicGeometry.AlgebraicSpace
import Sheaf.CategoryTheory.RingedSiteModules
import Sheaf.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings

/-!
# Enlarged étale ringed sites of algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 03G0, 03G1, 03H7, 03G2, 03G8,
03LP, 04LY and 04LZ (blueprint: lem-trf-space-enlarged-etale-ringed-site-model).

The enlarged site uses chartwise étaleness, without requiring representability.
Restriction is actual precomposition. All comparisons below retain this normalization.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Chartwise étaleness used in Stacks, Tags 03FR and 03G0:
every representable étale scheme chart remains representable étale after composition.
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def IsChartwiseEtale {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop :=
  ∀ (T : Over S) (a : yoneda.obj T ⟶ X.obj.obj),
    IsEtale a → IsEtale (a ≫ f.hom.hom)

/-- The enlarged site has étale algebraic spaces over `X` and all maps over `X`.
Source: Stacks, Tag 03G0 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
abbrev EnlargedEtaleSite (X : AlgebraicSpace S) :=
  ObjectProperty.FullSubcategory (fun T : Over X ↦ IsChartwiseEtale T.hom)

/-- Coverings are chartwise étale families jointly surjective on point classes.
Source: Stacks, Tag 03G0 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedEtalePrecoverage (X : AlgebraicSpace S) : Precoverage X.EnlargedEtaleSite where
  coverings T := {R |
    (∀ (U : X.EnlargedEtaleSite) (f : U ⟶ T), R f → IsChartwiseEtale f.hom.left) ∧
    IsJointlySurjective (fun a : R.uncurry ↦ a.1.2.hom.left.hom.hom)}

/-- The topology of the enlarged étale site.
Source: Stacks, Tag 03G0 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
abbrev enlargedEtaleTopology (X : AlgebraicSpace S) := X.enlargedEtalePrecoverage.toGrothendieck

/-- Representable scheme sheaves are algebraic spaces.
Source: Stacks, Tag 025Y, used in Tag 03G1
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: represent the diagonal by scheme fibre products. The identity of the scheme is
its surjective étale atlas. The fppf sheaf condition is subcanonicity. -/
theorem schemeSheaf_isAlgebraicSpace (T : Over S) :
    IsAlgebraicSpace ((Scheme.fppfTopology.over S).yoneda.obj T) := by
  sorry

/-- A scheme regarded as an algebraic space, using its actual representable sheaf.
Source: Stacks, Tags 025Y and 03G1
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def schemeSpace (T : Over S) : AlgebraicSpace S :=
  ⟨(Scheme.fppfTopology.over S).yoneda.obj T, schemeSheaf_isAlgebraicSpace T⟩

/-- A representable étale scheme object is chartwise étale.
Source: Stacks, Tags 03FR and 03G1
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: compose its representable étale map with any representable étale scheme chart,
using `isEtale_comp`. -/
theorem schemeObject_chartwise (X : AlgebraicSpace S) (T : X.EtaleSite) :
    IsChartwiseEtale (X := schemeSpace T.obj.left)
      (ObjectProperty.homMk ⟨T.obj.hom⟩ : schemeSpace T.obj.left ⟶ X) := by
  sorry

/-- The inclusion of scheme objects, retaining the underlying Yoneda maps.
Source: Stacks, Tag 03G1 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedSchemeInclusion (X : AlgebraicSpace S) : X.EtaleSite ⥤ X.EnlargedEtaleSite where
  obj T := ⟨Over.mk (ObjectProperty.homMk ⟨T.obj.hom⟩ : schemeSpace T.obj.left ⟶ X),
    schemeObject_chartwise X T⟩
  map f := ObjectProperty.homMk
    (Over.homMk (ObjectProperty.homMk ⟨yoneda.map f.hom.left⟩)
      (by apply ObjectProperty.hom_ext; apply Sheaf.hom_ext; exact f.hom.w))
  map_id T := by
    apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext; apply Sheaf.hom_ext; simp [schemeSpace]
  map_comp f g := by
    apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext; apply Sheaf.hom_ext; simp

/-- The displayed families satisfy the site axioms; the enlarged site has finite limits.
Source: Stacks, Tags 03G0 and 03G2
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: the terminal object is `X/X`. Fibre products are sheaf fibre products, algebraic
by `fibreProduct_isAlgebraicSpace`. Chartwise étaleness is preserved by base change,
composition and cancellation (Tags 03FT--03FV). These facts also prove the identity,
composition and base-change covering axioms, including the empty covering. -/
theorem enlargedEtale_site (X : AlgebraicSpace S) :
    X.enlargedEtalePrecoverage.IsSiteForCoverings ∧ Nonempty (HasFiniteLimits X.EnlargedEtaleSite)
    := by
  sorry

/-- Scheme inclusion is continuous.
Source: Stacks, Tag 03G1 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: the same scheme families cover in both sites, and scheme covering pullbacks
are the same fibre products. Precomposition therefore preserves sheaves. -/
theorem enlargedSchemeInclusion_continuous (X : AlgebraicSpace S) :
    (enlargedSchemeInclusion X).IsContinuous X.etaleTopology X.enlargedEtaleTopology := by
  sorry

attribute [instance] enlargedSchemeInclusion_continuous

/-- Restriction to scheme objects is literal precomposition.
Source: Stacks, Tags 03G1 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedRestriction (X : AlgebraicSpace S) (A : Type w) [Category.{v} A] :
    Sheaf X.enlargedEtaleTopology A ⥤ Sheaf X.etaleTopology A :=
  (enlargedSchemeInclusion X).sheafPushforwardContinuous A _ _

/-- Restriction is an equivalence of topoi, also for ring-valued sheaves.
Source: Stacks, Tags 03G1 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: scheme inclusion is fully faithful by Yoneda. It is continuous and cocontinuous:
refine a cover by choosing scheme atlases of its members. Every enlarged object has a
surjective étale scheme chart. The five comparison conditions therefore hold; apply
`specialCocontinuous_sheafEquivalence`. For rings lift each algebraic operation along
full faithfulness; the ring identities can be checked after faithful restriction
(`sheaves_algebraicStructures_objects`). -/
theorem enlargedRestriction_equivalence (X : AlgebraicSpace S) :
    (enlargedRestriction X (Type (max (u + 1) w))).IsEquivalence ∧
      (enlargedRestriction X RingCat.{u}).IsEquivalence := by
  sorry

/-- The canonical ring extension equivalence, with forward functor restriction.
Source: Stacks, Tag 03H7 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedRingEquivalence (X : AlgebraicSpace S) :
    Sheaf X.enlargedEtaleTopology RingCat.{u} ≌ Sheaf X.etaleTopology RingCat.{u} :=
  @Functor.asEquivalence _ _ _ _ (enlargedRestriction X RingCat.{u})
    (enlargedRestriction_equivalence.{u, 0} X).2

/-- The extended structure sheaf, obtained by the normalized inverse of restriction.
Source: Stacks, Tags 03H7 and 03G7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedStructureSheaf (X : AlgebraicSpace S) : Sheaf X.enlargedEtaleTopology RingCat.{u} :=
  (enlargedRingEquivalence X).inverse.obj X.structureSheaf

/-- Its specified restriction isomorphism.
Source: Stacks, Tag 03H7 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedStructureRestriction (X : AlgebraicSpace S) :
    (enlargedRestriction X RingCat.{u}).obj X.enlargedStructureSheaf ≅ X.structureSheaf :=
  (enlargedRingEquivalence X).counitIso.app X.structureSheaf

/-- Restriction of modules along the normalized structure-ring isomorphism.
Source: Stacks, Tag 03H7 and Modules on Sites, Tag 0409
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedModuleRestriction (X : AlgebraicSpace S) :
    ringedSiteModules.{max (u + 1) w} X.enlargedStructureSheaf ⥤
      ringedSiteModules.{max (u + 1) w} X.structureSheaf :=
  SheafOfModules.pushforward (enlargedStructureRestriction X).inv

/-- The same restriction gives the equivalence of module categories.
Source: Stacks, Tag 03H7 and the paragraph after Tag 03G7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: extend the underlying abelian sheaf by the comparison equivalence. Extend its
module action using preservation of products and full faithfulness. Addition, zero,
inverse, scalar laws and linearity of maps hold after faithful restriction, hence
before restriction. These constructions give inverse functors. -/
theorem enlargedModuleRestriction_equivalence (X : AlgebraicSpace S) :
    (enlargedModuleRestriction.{u, w} X).IsEquivalence := by
  sorry


/-- Extensions with specified restriction are unique up to unique normalized isomorphism.
Source: Stacks, Tags 03G1 and 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: full faithfulness of restriction lifts `e ≫ d⁻¹` uniquely. Faithfulness lifts
its inverse identities, and proves uniqueness with the prescribed restriction. -/
theorem enlargedExtension_unique (X : AlgebraicSpace S)
    (F : Sheaf X.etaleTopology (Type (max (u + 1) w)))
    (G H : Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)))
    (e : (enlargedRestriction X _).obj G ≅ F)
    (d : (enlargedRestriction X _).obj H ≅ F) :
    ∃! a : G ≅ H, (enlargedRestriction X _).map a.hom ≫ d.hom = e.hom := by
  sorry

/-- The extension equalizer on every surjective étale scheme chart.
The value of the bijection is precisely restriction to that chart, followed by `e`.
The displayed square also quantifies over every scheme presentation of the overlap.
Source: Stacks, Tag 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: the chart is a singleton covering. Its overlap is a scheme by
`etale_fibreProduct_isScheme`; the sheaf condition is the equalizer for the two
projections. Transport its two scheme values along `e`. Uniqueness of gluing proves
the restriction formula for every chart; on common refinements it proves naturality
in the enlarged object and in the sheaf. -/
theorem enlargedExtension_equalizer (X : AlgebraicSpace S)
    (F : Sheaf X.etaleTopology (Type (max (u + 1) w)))
    (G : Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)))
    (e : (enlargedRestriction X _).obj G ≅ F)
    (T : X.EnlargedEtaleSite) (T₀ T₁ : X.EtaleSite)
    (a : (enlargedSchemeInclusion X).obj T₀ ⟶ T)
    (ha : IsEtale a.hom.left.hom.hom ∧ IsSurjective a.hom.left.hom.hom)
    (p q : T₁ ⟶ T₀)
    (hsq : IsPullback ((enlargedSchemeInclusion X).map p)
      ((enlargedSchemeInclusion X).map q) a a) :
    ∃ b : G.obj.obj (op T) ≃
        {s : F.obj.obj (op T₀) // F.obj.map p.op s = F.obj.map q.op s},
      ∀ x, (b x).val = e.hom.hom.app (op T₀) (G.obj.map a.op x) := by
  sorry

/-- The sheaf pullback, bundled as an algebraic space.
Source: Stacks, Tags 04T9 and 03G2
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedFibreProduct {X Y Z : AlgebraicSpace S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    AlgebraicSpace S :=
  ⟨Limits.pullback f.hom g.hom, (fibreProduct_isAlgebraicSpace X Y Z f g).1⟩

/-- The first projection of the actual sheaf fibre product.
Source: Stacks, Tag 03G2 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedFibreProductFst {X Y Z : AlgebraicSpace S} (f : X ⟶ Z) (g : Y ⟶ Z) :
    enlargedFibreProduct f g ⟶ X :=
  ObjectProperty.homMk (Limits.pullback.fst f.hom g.hom)

/-- Base change of an enlarged object is again an enlarged object.
Source: Stacks, Tags 03FU and 03G2
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: pull back a scheme chart of the fibre product and then a scheme chart of the
result. Étaleness follows on these scheme tests from scheme base change and the
chartwise definition; it descends along the surjective étale chart. -/
theorem enlargedFibreProduct_chartwise {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (T : Y.EnlargedEtaleSite) :
    IsChartwiseEtale (enlargedFibreProductFst f T.obj.hom) := by
  sorry

/-- The canonical base-change functor `V ↦ X ×_Y V`, including its maps on arrows.
Source: Stacks, Tag 03G2 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedBaseChange {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Y.EnlargedEtaleSite ⥤ X.EnlargedEtaleSite where
  obj T := ⟨Over.mk (enlargedFibreProductFst f T.obj.hom),
    enlargedFibreProduct_chartwise f T⟩
  map {T U} a := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk
    (Limits.pullback.map f.hom T.obj.hom.hom f.hom U.obj.hom.hom
      (𝟙 _) a.hom.left.hom (𝟙 _) (by simp)
      (congrArg InducedCategory.Hom.hom (Over.w a.hom).symm)))
    (by apply ObjectProperty.hom_ext; simp [enlargedFibreProductFst]))
  map_id T := by
    apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext; simp [enlargedFibreProduct]
  map_comp a b := by
    apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    apply Limits.pullback.hom_ext <;> simp

/-- The base-change functor is continuous.
Source: Stacks, Tag 03G2(1)
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: base change preserves chartwise étaleness and joint surjectivity. The
fibre-product universal property identifies covering pullbacks before and after base
change. Thus precomposition preserves the covering equalizers of every sheaf. -/
theorem enlargedBaseChange_continuous {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (enlargedBaseChange f).IsContinuous Y.enlargedEtaleTopology X.enlargedEtaleTopology := by
  sorry

attribute [instance] enlargedBaseChange_continuous

/-- Direct image on enlarged sites is actual evaluation on fibre products.
Source: Stacks, Tag 03G2(1)
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedDirectImage {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (A : Type w) [Category.{v} A] :
    Sheaf X.enlargedEtaleTopology A ⥤ Sheaf Y.enlargedEtaleTopology A :=
  (enlargedBaseChange f).sheafPushforwardContinuous A _ _

/-- The base-change direct image has a left exact left adjoint.
Source: Stacks, Tag 03G2(1),(3)
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: the base-change functor preserves terminal objects and fibre products, hence
finite limits. Its left Kan extension followed by sheafification is left adjoint to
precomposition and left exact (Sites, Tag 00X6). Transfer through restriction to
obtain exactly the small étale geometric morphism of Tag 03G2(3). -/
theorem enlargedDirectImage_geometric {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃ g : GeometricMorphism (Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)))
        (Sheaf Y.enlargedEtaleTopology (Type (max (u + 1) w))),
      g.direct = enlargedDirectImage f _ := by
  sorry


/-- A commuting pair of scheme charts maps canonically to the base-change object.
Source: Stacks, proof of Tag 03G8
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedChartLift {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : X.EtaleSite) (V : Y.EtaleSite) (g : U.obj.left ⟶ V.obj.left)
    (h : yoneda.map g ≫ V.obj.hom = U.obj.hom ≫ f.hom.hom) :
    (enlargedSchemeInclusion X).obj U ⟶
      (enlargedBaseChange f).obj ((enlargedSchemeInclusion Y).obj V) :=
  ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk
    (Limits.pullback.lift (⟨U.obj.hom⟩ : (schemeSpace U.obj.left).obj ⟶ X.obj)
      ((Scheme.fppfTopology.over S).yoneda.map g)
      (by apply Sheaf.hom_ext; exact h.symm)))
    (by
      apply ObjectProperty.hom_ext
      change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst _ _ = _
      simp only [Limits.pullback.lift_fst]
      rfl))

/-- Normalization of the structural ring map: on every pair of commuting scheme charts
it is the usual pullback of regular functions, including the specified restriction isos.
Source: Stacks, Tag 03G8
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def IsEnlargedStructuralMap {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (r : Y.enlargedStructureSheaf ⟶
      (enlargedDirectImage f RingCat.{u}).obj X.enlargedStructureSheaf) : Prop :=
  ∀ (U : X.EtaleSite) (V : Y.EtaleSite) (g : U.obj.left ⟶ V.obj.left)
    (h : yoneda.map g ≫ V.obj.hom = U.obj.hom ≫ f.hom.hom),
    (enlargedStructureRestriction Y).inv.hom.app (op V) ≫
      r.hom.app (op ((enlargedSchemeInclusion Y).obj V)) ≫
      X.enlargedStructureSheaf.obj.map (enlargedChartLift f U V g h).op ≫
      (enlargedStructureRestriction X).hom.hom.app (op U) =
        (forget₂ CommRingCat RingCat).map (Scheme.Γ.map g.left.op)

/-- The canonical ring map exists uniquely with its scheme-chart normalization.
Source: Stacks, Tag 03G8
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: for a scheme `V → Y`, pull functions back to a scheme atlas of `X ×_Y V`.
The two pullbacks on its overlap agree, so the equalizer glues a unique section.
A common refinement proves chart independence, naturality and the ring identities.
Full faithfulness of restriction extends this map to the enlarged site. Its values
on scheme charts force uniqueness by the equalizer and faithful restriction. -/
theorem enlargedStructuralMap_existsUnique {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃! r : Y.enlargedStructureSheaf ⟶
        (enlargedDirectImage f RingCat.{u}).obj X.enlargedStructureSheaf,
      IsEnlargedStructuralMap f r := by
  sorry

/-- The unique structural map specified on charts, in adjoint direct-image form.
Source: Stacks, Tag 03G8 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedStructuralMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Y.enlargedStructureSheaf ⟶
      (enlargedDirectImage f RingCat.{u}).obj X.enlargedStructureSheaf :=
  (enlargedStructuralMap_existsUnique f).choose

/-- Composition comparison is normalized by the two fibre-product projections;
the structural ring maps compose under exactly this comparison.
Source: Stacks, Tags 03G2(2) and 03G8(1)
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: the unique map preserving the projections identifies
`W ×_X (X ×_Y V)` with `W ×_Y V`. Its inverse and naturality follow from the same
universal property. Precomposition identifies direct images; uniqueness of left
adjoints gives the adjunction-compatible inverse-image comparison
(`siteMorphism_composition`). On scheme charts both ring maps pull regular functions
back along the same composite. Their equalizers imply the displayed equality.
For three maps each comparison has the same projections, giving coherence. -/
theorem enlargedBaseChange_composition {W X Y : AlgebraicSpace S}
    (g : W ⟶ X) (f : X ⟶ Y) :
    ∃ c : enlargedBaseChange f ⋙ enlargedBaseChange g ≅ enlargedBaseChange (g ≫ f),
      (∀ V : Y.EnlargedEtaleSite,
        (c.hom.app V).hom.left.hom ≫ Limits.pullback.fst (g ≫ f).hom V.obj.hom.hom =
          Limits.pullback.fst g.hom (enlargedFibreProductFst f V.obj.hom).hom) ∧
      (∀ V : Y.EnlargedEtaleSite,
        (c.hom.app V).hom.left.hom ≫ Limits.pullback.snd (g ≫ f).hom V.obj.hom.hom =
          Limits.pullback.snd g.hom (enlargedFibreProductFst f V.obj.hom).hom ≫
            Limits.pullback.snd f.hom V.obj.hom.hom) ∧
      ∀ V : Y.EnlargedEtaleSite,
        (enlargedStructuralMap f).hom.app (op V) ≫
          (enlargedStructuralMap g).hom.app (op ((enlargedBaseChange f).obj V)) ≫
          W.enlargedStructureSheaf.obj.map (c.inv.app V).op =
            (enlargedStructuralMap (g ≫ f)).hom.app (op V) := by
  sorry

/-- Identity comparison and its structural ring-map normalization.
Source: Stacks, Tags 03G2 and 03G8
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: `X ×_X V → V` is the second projection, with inverse the graph. The
structural map restricts to the identity on every scheme chart; equalizer descent
gives the equality on every enlarged object. -/
theorem enlargedBaseChange_identity (X : AlgebraicSpace S) :
    ∃ c : enlargedBaseChange (𝟙 X) ≅ 𝟭 X.EnlargedEtaleSite,
      (∀ V : X.EnlargedEtaleSite,
        (c.hom.app V).hom.left.hom = Limits.pullback.snd (𝟙 X : X ⟶ X).hom V.obj.hom.hom) ∧
      ∀ V : X.EnlargedEtaleSite,
        (enlargedStructuralMap (𝟙 X)).hom.app (op V) =
          X.enlargedStructureSheaf.obj.map (c.hom.app V).op := by
  sorry

/-- An étale space is an object of the enlarged site.
Source: Stacks, Tags 03G0 and 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedEtaleObject {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    Y.EnlargedEtaleSite := ⟨Over.mk f, hf⟩

/-- Composition of chartwise étale morphisms, for the localization functor.
Source: Stacks, Tags 03FT and 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: each representable étale scheme chart remains representable étale after
composing with the first map, and then with the second, by the two hypotheses. -/
theorem enlargedEtale_comp {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsChartwiseEtale f) (hg : IsChartwiseEtale g) :
    IsChartwiseEtale (f ≫ g) := by
  sorry

/-- Postcomposition by an étale map, retaining the same underlying spaces and arrows.
Source: Stacks, Tags 03LP and 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedPostcompose {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    X.EnlargedEtaleSite ⥤ Y.EnlargedEtaleSite :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Over.map f)
    (fun T ↦ enlargedEtale_comp T.obj.hom f T.property hf)

/-- Postcomposition with an étale map, with its factorization remembered in the slice.
Source: Stacks, Tag 04LY (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedLocalization {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    X.EnlargedEtaleSite ⥤ Over (enlargedEtaleObject f hf) where
  obj T := Over.mk (ObjectProperty.homMk
    (Over.homMk T.obj.hom : ((enlargedPostcompose f hf).obj T).obj ⟶
      (enlargedEtaleObject f hf).obj))
  map a := Over.homMk ((enlargedPostcompose f hf).map a)
    (by apply ObjectProperty.hom_ext; apply Over.OverMorphism.ext; exact Over.w a.hom)
  map_id T := by rfl
  map_comp a b := by rfl


/-- Postcomposition identifies the enlarged site with its localization, preserving
exactly the covering sieves. Source: Stacks, Tag 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: an arrow `T → X` étale over `X` is étale over `Y` by composition. Conversely,
a factorization `T → X → Y` of two objects étale over `Y` has its first arrow étale
by cancellation (Tag 03FV). These functors are inverse before taking representatives.
Their covering families are precisely the same jointly surjective arrows. Passing to
the generated topologies gives the displayed equality of covering sieves. -/
theorem enlargedLocalization_equivalence {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    (enlargedLocalization f hf).IsEquivalence ∧
      ∀ (T : X.EnlargedEtaleSite) (R : Sieve T),
        R ∈ X.enlargedEtaleTopology T ↔
          R.functorPushforward (enlargedLocalization f hf) ∈
            (Y.enlargedEtaleTopology.over (enlargedEtaleObject f hf))
              ((enlargedLocalization f hf).obj T) := by
  sorry

/-- Postcomposition is continuous and therefore defines literal restriction of sheaves.
Source: Stacks, Tag 03LP and Tag 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: both sites have exactly the same coverings on every object of the source.
Covering pullbacks are unchanged. Precomposition preserves their sheaf equalizers. -/
theorem enlargedPostcompose_continuous {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    (enlargedPostcompose f hf).IsContinuous X.enlargedEtaleTopology
      Y.enlargedEtaleTopology := by
  sorry

attribute [instance] enlargedPostcompose_continuous

/-- Restriction along an étale map, i.e. localization inverse image.
Source: Stacks, Tags 03LP and 04LY
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedEtaleRestriction {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : IsChartwiseEtale f) (A : Type w) [Category.{v} A] :
    Sheaf Y.enlargedEtaleTopology A ⥤ Sheaf X.enlargedEtaleTopology A :=
  (enlargedPostcompose f hf).sheafPushforwardContinuous A _ _

/-- Chartwise étaleness suffices for postcomposition on the scheme small sites.
Source: Stacks, Tag 03LP
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def chartwiseEtaleMap {X Y : AlgebraicSpace S} (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    X.EtaleSite ⥤ Y.EtaleSite :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ CostructuredArrow.map f.hom.hom)
    (fun T ↦ hf T.obj.left T.obj.hom T.property)

/-- The scheme inclusions commute with étale postcomposition; the comparison is
identity on underlying scheme sheaves. Source: Stacks, proof of Tag 03LP
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedPostcomposeSchemeIso {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    chartwiseEtaleMap f hf ⋙ enlargedSchemeInclusion Y ≅
      enlargedSchemeInclusion X ⋙ enlargedPostcompose f hf :=
  Iso.refl _

/-- Restriction and base-change direct image are the localization adjunction;
the structural ring map is its unit under the normalized structure-ring identification.
Source: Stacks, Tags 03LP, 04LY and 04LZ
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: `slice_subtopos_site_presentation` identifies inverse image with restriction
and direct image with evaluation on products with `X/Y`. Under `enlargedLocalization`
those products are the fibre products in `enlargedBaseChange`. Sectionwise limits
show that restriction is left exact. The restricted ring and the extended ring of
`X` both evaluate to `Γ(U,O_U)` on every scheme chart, with the same restrictions.
Full faithfulness gives the unique ring isomorphism inducing the identity on these
sections. The ring unit followed by this isomorphism pulls functions back along the
projection on every chart, and so equals the unique structural map globally. -/
theorem enlargedEtale_localization {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : IsChartwiseEtale f) :
    Nonempty (enlargedEtaleRestriction f hf (Type (max (u + 1) w)) ⊣
      enlargedDirectImage f (Type (max (u + 1) w))) ∧
    PreservesFiniteLimits (enlargedEtaleRestriction f hf (Type (max (u + 1) w))) ∧
    ∃ ar : enlargedEtaleRestriction f hf RingCat.{u} ⊣ enlargedDirectImage f RingCat.{u},
      ∃ e : (enlargedEtaleRestriction f hf RingCat.{u}).obj Y.enlargedStructureSheaf ≅
          X.enlargedStructureSheaf,
        (∀ U : X.EtaleSite,
          (enlargedStructureRestriction Y).inv.hom.app (op ((chartwiseEtaleMap f hf).obj U)) ≫
            Y.enlargedStructureSheaf.obj.map ((enlargedPostcomposeSchemeIso f hf).inv.app U).op ≫
            e.hom.hom.app (op ((enlargedSchemeInclusion X).obj U)) ≫
            (enlargedStructureRestriction X).hom.hom.app (op U) = 𝟙 _) ∧
        ar.unit.app Y.enlargedStructureSheaf ≫
          (enlargedDirectImage f RingCat.{u}).map e.hom = enlargedStructuralMap f := by
  sorry

/-- Every surjective étale scheme chart has a scheme overlap, in the enlarged site.
Source: Stacks, Tag 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: the scheme-test representability of the chart represents its self-fibre
product by a scheme (`etale_fibreProduct_isScheme`). Both projections and its map
to `X` are étale; their universal property supplies the asserted pullback square. -/
theorem enlargedChartOverlap_exists (X : AlgebraicSpace S)
    (T : X.EnlargedEtaleSite) (T₀ : X.EtaleSite)
    (a : (enlargedSchemeInclusion X).obj T₀ ⟶ T)
    (ha : IsEtale a.hom.left.hom.hom ∧ IsSurjective a.hom.left.hom.hom) :
    ∃ (T₁ : X.EtaleSite) (p q : T₁ ⟶ T₀),
      IsPullback ((enlargedSchemeInclusion X).map p)
        ((enlargedSchemeInclusion X).map q) a a := by
  sorry


/-- The set-sheaf comparison equivalence has literal restriction as forward functor.
Source: Stacks, Tag 03G1 (blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedSetEquivalence (X : AlgebraicSpace S) :
    Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)) ≌
      Sheaf X.etaleTopology (Type (max (u + 1) w)) :=
  @Functor.asEquivalence _ _ _ _ (enlargedRestriction X (Type (max (u + 1) w)))
    (enlargedRestriction_equivalence X).1

/-- Direct image on the small étale topoi, transported along the scheme comparisons.
Source: Stacks, Tag 03G2(3)
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model). -/
def enlargedSmallDirectImage {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Sheaf X.etaleTopology (Type (max (u + 1) w)) ⥤
      Sheaf Y.etaleTopology (Type (max (u + 1) w)) :=
  (enlargedSetEquivalence X).inverse ⋙ enlargedDirectImage f _ ⋙
    (enlargedSetEquivalence Y).functor

/-- The small étale morphism is the transport of the enlarged-site geometric morphism.
Source: Stacks, Tag 03G2(3)
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: compose the enlarged geometric morphism with the two comparison equivalences.
Their inverse functors are adjoint and preserve limits, so the composite is geometric.
Its direct image is the displayed transported evaluation-on-fibre-products functor. -/
theorem enlargedSmallDirectImage_geometric {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    ∃ g : GeometricMorphism (Sheaf X.etaleTopology (Type (max (u + 1) w)))
        (Sheaf Y.etaleTopology (Type (max (u + 1) w))),
      g.direct = enlargedSmallDirectImage f := by
  sorry


/-- Every small-site sheaf has an extension with a specified restriction isomorphism.
Source: Stacks, Tag 03H7
(blueprint: lem-trf-space-enlarged-etale-ringed-site-model).
Proof: essential surjectivity of the restriction equivalence supplies the extension.
The chosen isomorphism is retained, so `enlargedExtension_unique` applies to it. -/
theorem enlargedExtension_exists (X : AlgebraicSpace S)
    (F : Sheaf X.etaleTopology (Type (max (u + 1) w))) :
    ∃ G : Sheaf X.enlargedEtaleTopology (Type (max (u + 1) w)),
      Nonempty ((enlargedRestriction X _).obj G ≅ F) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
