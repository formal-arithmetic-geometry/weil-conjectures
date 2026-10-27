module

public import Sheaf.AlgebraicGeometry.EnlargedFaceRingedTotalModel
public import Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory
public import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.SmallEnlargedEtaleModules
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

import Sheaf.AlgebraicGeometry.FlatEtaleRingedMap
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import Sheaf.CategoryTheory.SemisimplicialEvaluationFreeAdjoint
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.CategoryTheory.Sites.GeometricInverseImageExact
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Derived sections of a flat face total site

Source: Stacks Project, spaces-simplicial.tex, Tags 0D7B--0D7F,
with the injective-order-map adaptation
(blueprint: lem-sfb-face-total-derived-sections).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Bicategory CategoryTheory.SemisimplicialRingedTotal

namespace CategoryTheory.FaceTotalDerivedSections

/-- The face omitting the indicated vertex. Source: Stacks 0D7C, face-only adaptation
(blueprint: lem-sfb-face-total-derived-sections). -/
def face (p : ℕ) (i : Fin (p + 2)) :
    op (SemiSimplexCategory.mk (p + 1)) ⟶ op (SemiSimplexCategory.mk p) :=
  (SemiSimplexCategory.homOfMono (SimplexCategory.δ i)).op

/-- Sections on an actual enlarged étale object in the explicit lifted ringed model.
Source: Stacks 03H7, 0D7F
(blueprint: lem-sfb-face-total-derived-sections). -/
def spaceSections {S : AlgebraicGeometry.Scheme.{u}}
    (X : AlgebraicGeometry.AlgebraicSpace S) (V : X.EnlargedEtaleSite) :
    (EnlargedFaceRingedTotal.site X).modules ⥤ AddCommGrpCat.{u + 1} :=
  SheafOfModules.toSheaf (EnlargedFaceRingedTotal.site X).rings ⋙
    (sheafSections (EnlargedFaceRingedTotal.site X).J AddCommGrpCat.{u + 1}).obj
      (op (show EnlargedFaceRingedTotal.Objects X from ⟨V⟩))

/-- Additivity of section evaluation on the literal enlarged-site module category.
Source: Stacks 03H7, 0D7F
(blueprint: lem-sfb-face-total-derived-sections).
Proof: the forgetful functor to abelian sheaves preserves addition, and
evaluation at the fixed enlarged object is additive sectionwise. -/
theorem spaceSections_additive {S : AlgebraicGeometry.Scheme.{u}}
    (X : AlgebraicGeometry.AlgebraicSpace S) (V : X.EnlargedEtaleSite) :
    (spaceSections X V).Additive := by
  sorry

attribute [instance] spaceSections_additive

/-- The shared fully pinned enlarged-site model; no geometry is selected existentially
for the comparison. Source: Stacks 03G0, 0D70
(blueprint: lem-sfb-face-total-derived-sections). -/
abbrev Model {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    (W : SemiSimplexCategoryᵒᵖ ⥤ Over Z) := EnlargedFaceRingedTotal.Model W

/-- Ordinary direct-image rows, pinned by the inverse-adjunct formula on every
coefficient module. Source: Stacks 0D7C--0D7D, finite-simplex adaptation
(blueprint: lem-sfb-face-total-derived-sections). -/
structure Rows {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} (G : Model W) where
  diagram : SemiSimplexCategory ⥤ ((G.rings.total G.sheaf).modules ⥤ G.base.modules)
  component : ∀ p : SemiSimplexCategory,
    diagram.obj p ≅ (G.presentation.evaluation (op p)).ordinary ⋙
      (G.augmentation.map (op p)).modules
  transpose : ∀ {p q : SemiSimplexCategory} (b : p ⟶ q)
    (M : (G.rings.total G.sheaf).modules) (H : G.base.modules)
    (t : H ⟶ (G.augmentation.map (op p)).modules.obj
      ((G.presentation.evaluation (op p)).ordinary.obj M)),
    ((G.total.components (op q)).adjunction.homEquiv _ _).symm
      (t ≫ (component p).inv.app M ≫ (diagram.map b).app M ≫ (component q).hom.app M) =
    (G.total.faceComposition b.op).ordinary.hom.app H ≫
      (G.presentation.pullback b.op).ordinary.map
        (((G.total.components (op p)).adjunction.homEquiv _ _).symm t) ≫
      (G.presentation.transition b.op).app M
  augmentation : G.total.map.modules ⟶ diagram.obj (SemiSimplexCategory.mk 0)
  augmentation_transpose : ∀ M : (G.rings.total G.sheaf).modules,
    ((G.total.components (op (SemiSimplexCategory.mk 0))).adjunction.homEquiv _ _).symm
      (augmentation.app M ≫ (component _).hom.app M) =
    (G.total.component _).inv.app (G.total.map.modules.obj M) ≫
      (G.presentation.evaluation _).ordinary.map (G.total.pullback.adjunction.counit.app M)

/-- Base evaluation on the fixed enlarged ringed site.
Source: Stacks 03H7, 0D7F (blueprint: lem-sfb-face-total-derived-sections). -/
def Model.sections {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} (G : Model W)
    (V : Z.EnlargedEtaleSite) : G.base.modules ⥤ AddCommGrpCat.{u + 1} :=
  spaceSections Z V

/-- Additivity of the base sections functor. Source: Stacks 03H7, 0D7F
(blueprint: lem-sfb-face-total-derived-sections).
Proof: this is the additive section functor on the fixed enlarged base site. -/
theorem Model.sections_additive {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} (G : Model W)
    (V : Z.EnlargedEtaleSite) : (G.sections V).Additive := by
  sorry

attribute [instance] Model.sections_additive

/-- Every section group uses the explicit model coefficient universe u+1.
Source: Stacks 05RU (blueprint: lem-sfb-face-total-derived-sections). -/
instance abelianGroupsDerived : HasDerivedCategory.{u + 2} AddCommGrpCat.{u + 1} :=
  HasDerivedCategory.standard _

/-- Localization of a nonnegative complex, with its real zero extension.
Source: Stacks 05RU, 0D7F (blueprint: lem-sfb-face-total-derived-sections). -/
def localize (K : CochainComplex AddCommGrpCat.{u + 1} ℕ) :
    DerivedCategory.{u + 2} AddCommGrpCat.{u + 1} :=
  DerivedCategory.Q.obj (K.extend ComplexShape.embeddingUpNat)

/-- Section double complex and its actual row augmentation, not just its cohomology.
Columns are identified as complexes and the horizontal differential is the signed
sum of the specified transpose maps. Source: Stacks 0D7D--0D7F
(blueprint: lem-sfb-face-total-derived-sections). -/
structure SectionModel {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} {G : Model W} (R : Rows G)
    (M : (G.rings.total G.sheaf).modules) (I : InjectiveResolution M)
    (V : Z.EnlargedEtaleSite) where
  double : HomologicalComplex₂ AddCommGrpCat.{u + 1} (.up ℕ) (.up ℕ)
  column : ∀ p : ℕ, double.X p ≅
    (((G.presentation.evaluation (op (SemiSimplexCategory.mk p))).ordinary ⋙
      (G.augmentation.map (op (SemiSimplexCategory.mk p))).modules ⋙
        G.sections V).mapHomologicalComplex (.up ℕ)).obj
        I.cocomplex
  horizontal : ∀ p q : ℕ,
    (double.d p (p + 1)).f q = (column p).hom.f q ≫
      (G.sections V).map
        ((R.component _).inv.app (I.cocomplex.X q) ≫
          (∑ i : Fin (p + 2), (-1 : ℤ) ^ i.val •
            (R.diagram.map (face p i).unop).app (I.cocomplex.X q)) ≫
          (R.component _).hom.app (I.cocomplex.X q)) ≫ (column (p + 1)).inv.f q
  row : ((G.total.map.modules ⋙ G.sections V).mapHomologicalComplex (.up ℕ)).obj
    I.cocomplex ⟶ double.total (.up ℕ)
  row_formula : ∀ q : ℕ, row.f q =
    (G.sections V).map (R.augmentation.app (I.cocomplex.X q) ≫
      (R.component _).hom.app (I.cocomplex.X q)) ≫
        (column 0).inv.f q ≫ double.ιTotal (.up ℕ) 0 q q (zero_add q)


/-- Grothendieck structure on the dependency's small site modules, from the existing
source theorem. Source: Stacks 079V (blueprint: lem-sfb-face-total-derived-sections). -/
instance siteGrothendieck (X : Site.{u + 1}) : IsGrothendieckAbelian.{u + 1} X.modules :=
  SheafOfModules.isGrothendieckAbelian X.rings

/-- The ambient K-injective right derived section functor.
Source: Stacks 0D7F, 079V (blueprint: lem-sfb-face-total-derived-sections). -/
abbrev Model.derivedSections {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} (G : Model W)
    (V : Z.EnlargedEtaleSite) := (G.sections V).rightDerivedFunctor

/-- Localization after termwise application and zero extension.
Source: Stacks 05RU (blueprint: lem-sfb-face-total-derived-sections). -/
def localizeFunctor : CochainComplex AddCommGrpCat.{u + 1} ℕ ⥤
    DerivedCategory.{u + 2} AddCommGrpCat.{u + 1} :=
  (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{u + 1}) ⋙ DerivedCategory.Q

/-- The canonical unit on a module, using the actual ordinary adjunction followed
by the ambient right-derived unit. For exact pullback this is the derived
adjunction unit on the degree-zero object. Source: Stacks 0D7D, 0158
(blueprint: lem-sfb-face-total-derived-sections). -/
def Model.unit {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} (G : Model W) (H : G.base.modules) :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor G.base.modules 0).obj H) ⟶
      G.total.map.modules.rightDerivedFunctor.obj
        (DerivedCategory.Q.obj ((CochainComplex.singleFunctor
          (G.rings.total G.sheaf).modules 0).obj (G.total.pullback.ordinary.obj H))) :=
  DerivedCategory.Q.map ((CochainComplex.singleFunctor G.base.modules 0).map
    (G.total.pullback.adjunction.unit.app H)) ≫
    DerivedCategory.Q.map
      (((HomologicalComplex.singleMapHomologicalComplex G.total.map.modules (.up ℤ) 0).inv.app
        (G.total.pullback.ordinary.obj H))) ≫
    G.total.map.modules.rightDerivedFunctorUnitQ
      ((CochainComplex.singleFunctor (G.rings.total G.sheaf).modules 0).obj
        (G.total.pullback.ordinary.obj H))


/-- The complex concentrated in degree zero, followed by localization.
Source: Stacks 05RU (blueprint: lem-sfb-face-total-derived-sections). -/
abbrev single (X : Site.{u + 1}) (M : X.modules) : X.D :=
  DerivedCategory.Q.obj ((CochainComplex.singleFunctor X.modules 0).obj M)

/-- The representative map of an injective resolution, extended by actual zero terms.
Source: Stacks 013K, 0D7F (blueprint: lem-sfb-face-total-derived-sections). -/
def resolutionMap (X : Site.{u + 1}) {M : X.modules} (I : InjectiveResolution M) :
    (CochainComplex.singleFunctor X.modules 0).obj M ⟶
      I.cocomplex.extend ComplexShape.embeddingUpNat :=
  (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl).inv ≫
      HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat

/-- Zero extension preserves the resolution quasi-isomorphism.
Source: Stacks 013K, 0D7F (blueprint: lem-sfb-face-total-derived-sections).
Proof: at nonnegative degrees use the extension homology isomorphism and I.ι;
at negative degrees both complexes vanish. -/
theorem resolutionMap_quasiIso (X : Site.{u + 1}) {M : X.modules}
    (I : InjectiveResolution M) : QuasiIso (resolutionMap X I) := by
  sorry

attribute [instance] resolutionMap_quasiIso

/-- The canonical map from the localized section resolution to the derived sections
of the right derived augmentation. Source: Stacks 0D7F
(blueprint: lem-sfb-face-total-derived-sections). -/
def Model.resolutionComparison {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} (G : Model W)
    {M : (G.rings.total G.sheaf).modules} (I : InjectiveResolution M)
    (V : Z.EnlargedEtaleSite) :
    DerivedCategory.Q.obj
      (((G.sections V).mapHomologicalComplex (.up ℤ)).obj
        ((G.total.map.modules.mapHomologicalComplex (.up ℤ)).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat))) ⟶
    (G.derivedSections V).obj
      (G.total.map.modules.rightDerivedFunctor.obj (single (G.rings.total G.sheaf) M)) :=
  (G.sections V).rightDerivedFunctorUnitQ _ ≫
    (G.derivedSections V).map (G.total.map.modules.rightDerivedFunctorUnitQ _) ≫
    (G.derivedSections V).map
      (G.total.map.modules.rightDerivedFunctor.map
        (inv (DerivedCategory.Q.map (resolutionMap _ I))))


/-- The standard finite-sum zero-extension comparison for the source of the row map.
Source: Stacks 0D7F (blueprint: lem-sfb-face-total-derived-sections). -/
def rowExtension {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} {G : Model W}
    {M : (G.rings.total G.sheaf).modules} (I : InjectiveResolution M)
    (V : Z.EnlargedEtaleSite) :
    localize (((G.total.map.modules ⋙ G.sections V).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex) ≅
    DerivedCategory.Q.obj
      (((G.sections V).mapHomologicalComplex (.up ℤ)).obj
        ((G.total.map.modules.mapHomologicalComplex (.up ℤ)).obj
          (I.cocomplex.extend ComplexShape.embeddingUpNat))) :=
  DerivedCategory.Q.mapIso (I.cocomplex.mapExtendIso ComplexShape.embeddingUpNat
    (G.total.map.modules ⋙ G.sections V)).symm

/-- Section restrictions as a natural transformation, using the actual extended sheaf.
Source: Stacks 03H7, 0D7F (blueprint: lem-sfb-face-total-derived-sections). -/
def Model.restriction {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} (G : Model W)
    {V U : Z.EnlargedEtaleSite} (b : U ⟶ V) : G.sections V ⟶ G.sections U :=
  Functor.whiskerLeft (SheafOfModules.toSheaf G.base.rings)
    ((sheafSections G.base.J AddCommGrpCat.{u + 1}).map
      (AsSmall.up.{u + 1, u + 1, u + 1}.map b).op)

/-- Whole-diagram total comparisons, with a single common internal lower bound.
Each zigzag edge is such a morphism; localization inverts backwards edges.
Source: Stacks Homology 0133, signed shift verification in the node
(blueprint: lem-sfb-face-total-derived-sections). -/
def CompatibleReplacementInvariant : Prop :=
  ∀ (K L : HomologicalComplex₂ AddCommGrpCat.{u + 1} (.up ℤ) (.up ℤ)) (c : ℤ),
    (∀ p q : ℤ, p < 0 ∨ q < c → IsZero ((K.X p).X q)) →
    (∀ p q : ℤ, p < 0 ∨ q < c → IsZero ((L.X p).X q)) →
    Nonempty (K.HasTotal (.up ℤ)) ∧ Nonempty (L.HasTotal (.up ℤ)) ∧
      ∀ [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)] (b : K ⟶ L),
        (∀ p : ℤ, QuasiIso (b.f p)) → QuasiIso (HomologicalComplex₂.total.map b (.up ℤ))

/-- All resolution, locality, naturality and augmentation clauses. The comparison is
an isomorphism in the ambient derived category of abelian groups, normalized by
both right-derived units and the row augmentation, rather than unrelated isomorphisms
of individual cohomology groups. Source: Stacks 0D7B--0D7F, face-only adaptation
(blueprint: lem-sfb-face-total-derived-sections). -/
structure Computation {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} {G : Model W} (R : Rows G) where
  model : ∀ (M : (G.rings.total G.sheaf).modules) (I : InjectiveResolution M)
    (V : Z.EnlargedEtaleSite), SectionModel R M I V
  comparison : ∀ (M : (G.rings.total G.sheaf).modules) (I : InjectiveResolution M)
    (V : Z.EnlargedEtaleSite),
    (G.derivedSections V).obj
      (G.total.map.modules.rightDerivedFunctor.obj (single (G.rings.total G.sheaf) M)) ≅
        localize ((model M I V).double.total (.up ℕ))
  normalization : ∀ (M : (G.rings.total G.sheaf).modules) (I : InjectiveResolution M)
    (V : Z.EnlargedEtaleSite),
    localizeFunctor.map (model M I V).row ≫ (comparison M I V).inv =
      (rowExtension I V).hom ≫ G.resolutionComparison I V
  columnSections : ∀ (p : ℕ) (V : Z.EnlargedEtaleSite),
    (G.augmentation.map (op (SemiSimplexCategory.mk p))).modules ⋙ G.sections V ≅
      (G.componentEquivalence _).functor ⋙
        spaceSections (W.obj (op (SemiSimplexCategory.mk p))).left
          ((AlgebraicGeometry.AlgebraicSpace.enlargedBaseChange
            (W.obj (op (SemiSimplexCategory.mk p))).hom).obj V)
  columnDerived : ∀ (M : (G.rings.total G.sheaf).modules) (I : InjectiveResolution M)
    (V : Z.EnlargedEtaleSite) (p : ℕ),
    Nonempty
      (((G.augmentation.map (op (SemiSimplexCategory.mk p))).modules ⋙
          G.sections V).rightDerivedFunctor.obj
        ((G.presentation.evaluation (op (SemiSimplexCategory.mk p))).derived.obj
          (single (G.rings.total G.sheaf) M)) ≅
        localize ((model M I V).double.X p))
  resolutionMap : ∀ {M N : (G.rings.total G.sheaf).modules}
    (I : InjectiveResolution M) (J : InjectiveResolution N) (V : Z.EnlargedEtaleSite)
    (f : M ⟶ N) (t : I.cocomplex ⟶ J.cocomplex)
    (_ht : I.ι ≫ t = (CochainComplex.single₀ _).map f ≫ J.ι),
    (model M I V).double ⟶ (model N J V).double
  resolutionMap_column : ∀ {M N : (G.rings.total G.sheaf).modules}
    (I : InjectiveResolution M) (J : InjectiveResolution N) (V : Z.EnlargedEtaleSite)
    (f : M ⟶ N) (t : I.cocomplex ⟶ J.cocomplex)
    (ht : I.ι ≫ t = (CochainComplex.single₀ _).map f ≫ J.ι) (p : ℕ),
    (resolutionMap I J V f t ht).f p ≫ ((model N J V).column p).hom =
      ((model M I V).column p).hom ≫
        (((G.presentation.evaluation (op (SemiSimplexCategory.mk p))).ordinary ⋙
          (G.augmentation.map (op (SemiSimplexCategory.mk p))).modules ⋙
            G.sections V).mapHomologicalComplex (.up ℕ)).map t
  resolution_naturality : ∀ {M N : (G.rings.total G.sheaf).modules}
    (I : InjectiveResolution M) (J : InjectiveResolution N) (V : Z.EnlargedEtaleSite)
    (f : M ⟶ N) (t : I.cocomplex ⟶ J.cocomplex)
    (ht : I.ι ≫ t = (CochainComplex.single₀ _).map f ≫ J.ι),
    (G.derivedSections V).map (G.total.map.modules.rightDerivedFunctor.map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map f))) ≫
      (comparison N J V).hom = (comparison M I V).hom ≫
        localizeFunctor.map (HomologicalComplex₂.total.map
          (resolutionMap I J V f t ht) (.up ℕ))
  restrictionMap : ∀ (M : (G.rings.total G.sheaf).modules) (I : InjectiveResolution M)
    {V U : Z.EnlargedEtaleSite} (_b : U ⟶ V),
    (model M I V).double ⟶ (model M I U).double
  restrictionMap_column : ∀ (M : (G.rings.total G.sheaf).modules)
    (I : InjectiveResolution M) {V U : Z.EnlargedEtaleSite} (b : U ⟶ V) (p : ℕ),
    (restrictionMap M I b).f p ≫ ((model M I U).column p).hom =
      ((model M I V).column p).hom ≫
        (NatTrans.mapHomologicalComplex
          (Functor.whiskerLeft
            ((G.presentation.evaluation (op (SemiSimplexCategory.mk p))).ordinary ⋙
              (G.augmentation.map (op (SemiSimplexCategory.mk p))).modules)
            (G.restriction b)) (.up ℕ)).app I.cocomplex
  restriction_naturality : ∀ (M : (G.rings.total G.sheaf).modules)
    (I : InjectiveResolution M) {V U : Z.EnlargedEtaleSite} (b : U ⟶ V),
    (Functor.rightDerivedFunctorNatTrans (G.restriction b)).app
        (G.total.map.modules.rightDerivedFunctor.obj (single (G.rings.total G.sheaf) M)) ≫
      (comparison M I U).hom = (comparison M I V).hom ≫
        localizeFunctor.map (HomologicalComplex₂.total.map (restrictionMap M I b) (.up ℕ))
  row_quasiIso : ∀ (M : (G.rings.total G.sheaf).modules) (I : InjectiveResolution M)
    (V : Z.EnlargedEtaleSite), QuasiIso (model M I V).row
  replacements : CompatibleReplacementInvariant.{u}
  detection : ∀ (K L : DerivedCategory.Plus G.base.modules) (b : K ⟶ L),
    (∀ V : Z.EnlargedEtaleSite,
      IsIso ((G.derivedSections V).map (DerivedCategory.Plus.ι.map b))) → IsIso b


/-- The base injective section comparison, normalized by the right-derived unit.
Source: Stacks 0D7F (blueprint: lem-sfb-face-total-derived-sections). -/
def Model.baseResolutionComparison {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} (G : Model W)
    {H : G.base.modules} (J : InjectiveResolution H) (V : Z.EnlargedEtaleSite) :
    localize (((G.sections V).mapHomologicalComplex (.up ℕ)).obj J.cocomplex) ⟶
      (G.derivedSections V).obj (single G.base H) :=
  (DerivedCategory.Q.mapIso
    (J.cocomplex.mapExtendIso ComplexShape.embeddingUpNat (G.sections V)).symm).hom ≫
    (G.sections V).rightDerivedFunctorUnitQ _ ≫
    (G.derivedSections V).map (inv (DerivedCategory.Q.map (resolutionMap _ J)))

/-- Localization after extension by zero inverts nonnegative quasi-isomorphisms.
Source: Stacks Homology 0133 (blueprint: lem-sfb-face-total-derived-sections).
Proof: extension by zero identifies cohomology in nonnegative degrees with the
original cohomology, and its negative cohomology vanishes. It therefore preserves
quasi-isomorphisms, which the derived-category localization inverts. -/
theorem localizeFunctor_map_isIso {K L : CochainComplex AddCommGrpCat.{u + 1} ℕ}
    (b : K ⟶ L) [QuasiIso b] : IsIso (localizeFunctor.map b) := by
  sorry

attribute [instance] localizeFunctor_map_isIso

/-- The actual derived unit is represented by augmented restriction on resolutions.
The displayed formula fixes its components in horizontal degree zero. The last
clause says the same equation holds after any compatible quasi-isomorphic
replacement of its total complex. Combined with `replacements`, this applies to
whole-diagram column quasi-isomorphisms with any common internal lower bound,
and hence to zigzags, in either direction.
Source: Stacks 0D7D--0D7F, derived.tex lemma-derived-adjoint-functors
(blueprint: lem-sfb-face-total-derived-sections). -/
structure UnitCompatibility {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    {W : SemiSimplexCategoryᵒᵖ ⥤ Over Z} {G : Model W} {R : Rows G}
    (C : Computation R) where
  augmented : ∀ (H : G.base.modules) (J : InjectiveResolution H)
    (I : InjectiveResolution (G.total.pullback.ordinary.obj H))
    (t : ((G.total.pullback.ordinary.mapHomologicalComplex (.up ℕ)).obj J.cocomplex) ⟶
      I.cocomplex)
    (_ht : G.total.pullback.ordinary.map (J.ι.f 0) ≫ t.f 0 = I.ι.f 0)
    (V : Z.EnlargedEtaleSite),
    ((G.sections V).mapHomologicalComplex (.up ℕ)).obj J.cocomplex ⟶
      (C.model _ I V).double.total (.up ℕ)
  formula : ∀ (H : G.base.modules) (J : InjectiveResolution H)
    (I : InjectiveResolution (G.total.pullback.ordinary.obj H))
    (t : ((G.total.pullback.ordinary.mapHomologicalComplex (.up ℕ)).obj J.cocomplex) ⟶
      I.cocomplex)
    (ht : G.total.pullback.ordinary.map (J.ι.f 0) ≫ t.f 0 = I.ι.f 0)
    (V : Z.EnlargedEtaleSite) (q : ℕ),
    (augmented H J I t ht V).f q =
      (G.sections V).map
        ((G.total.pullback.adjunction.homEquiv _ _ (t.f q)) ≫
          R.augmentation.app (I.cocomplex.X q) ≫
          (R.component _).hom.app (I.cocomplex.X q)) ≫
        ((C.model _ I V).column 0).inv.f q ≫
          (C.model _ I V).double.ιTotal (.up ℕ) 0 q q (zero_add q)
  unit : ∀ (H : G.base.modules) (J : InjectiveResolution H)
    (I : InjectiveResolution (G.total.pullback.ordinary.obj H))
    (t : ((G.total.pullback.ordinary.mapHomologicalComplex (.up ℕ)).obj J.cocomplex) ⟶
      I.cocomplex)
    (ht : G.total.pullback.ordinary.map (J.ι.f 0) ≫ t.f 0 = I.ι.f 0)
    (V : Z.EnlargedEtaleSite),
    localizeFunctor.map (augmented H J I t ht V) ≫ (C.comparison _ I V).inv =
      G.baseResolutionComparison J V ≫ (G.derivedSections V).map (G.unit H)
  replacement_unit : ∀ (H : G.base.modules) (J : InjectiveResolution H)
    (I : InjectiveResolution (G.total.pullback.ordinary.obj H))
    (t : ((G.total.pullback.ordinary.mapHomologicalComplex (.up ℕ)).obj J.cocomplex) ⟶
      I.cocomplex)
    (ht : G.total.pullback.ordinary.map (J.ι.f 0) ≫ t.f 0 = I.ι.f 0)
    (V : Z.EnlargedEtaleSite) (L : CochainComplex AddCommGrpCat.{u + 1} ℕ)
    (b : (C.model _ I V).double.total (.up ℕ) ⟶ L) [QuasiIso b]
    (a : ((G.sections V).mapHomologicalComplex (.up ℕ)).obj J.cocomplex ⟶ L)
    (_ha : a = augmented H J I t ht V ≫ b),
    localizeFunctor.map a ≫ inv (localizeFunctor.map b) ≫ (C.comparison _ I V).inv =
      G.baseResolutionComparison J V ≫ (G.derivedSections V).map (G.unit H)

/-- Derived sections of the flat face total site, with all comparison and unit data.

Source: Stacks Project, spaces-simplicial.tex, Tags 0D7B, 0D7C, 0D7D and 0D7F;
agent-supplied injective-order-map adaptation
(blueprint: lem-sfb-face-total-derived-sections).

Proof:
1. Construct the shared pinned Model on AsSmall of the actual enlarged étale
sites, with the literal enlarged covering families and the explicit ULift of
regular-function rings. The existing projection-preserving enlargedIdentityIso,
enlargedCompositionIso and enlargedDirectCompositionIso supply exactly its
unitor, compositor and augmentation mates. Apply
semisimplicial_ringed_total_category to obtain a model. Then fix ANY such model;
all remaining steps use its normalized data, so they apply to every model,
without selecting a new module category for the conclusion.
2. Chartwise flatness gives exactness of face and augmentation pullbacks, using
lem-sfb-space-flat-etale-ringed-comparison, def-sfb-flat-etale-ringed-map and
lem-trf-geometric-inverse-image-exact. The exact free extensions of
semisimplicial_evaluation_free_adjoint show evaluations preserve injectives.
The exact augmentation pullback shows its right adjoint preserves injectives.
3. Resolve a base module H by the labelled free extensions of its component
pullbacks. In component m this is the augmented ordered finite m-simplex. Insert
vertex 0 when absent, and use zero when present. The first face gives the identity;
all other double deletions cancel in opposite-sign pairs. This includes m=0,
augmentation degree -1 and zero terms above m, proving componentwise exactness.
4. Apply Hom(-,I) for an injective total module. The normalized free adjunction
and component pullback adjunction identify the result with Rows.transpose and
Rows.augmentation_transpose. Take H to be the free representable module E_V of
lem-trf-free-representable-module-ext-evaluation. Its Hom evaluation proves
exactness on sections over every enlarged object V, naturally in V and I.
5. Apply this to every term of any total injective resolution. The alternating
cofaces commute with its differential and square to zero. Form SectionModel with
the finite-diagonal Mathlib totalization, whose signs are d_h + (-1)^p d_v.
The horizontal-first double-complex spectral sequence has finite filtrations:
its row augmentation is an isomorphism on the first page, hence on each graded
piece, and successive short exact sequences give a total quasi-isomorphism.
6. Bounded-below injective complexes and their slice restrictions are K-injective
by lem-weil-pbc-dplus-injective-representative and lem-pur-kinjective-restrict-localized.
Thus the actual right-derived units compute both the total image and each column.
lem-sfb-ringed-sections-forget-abelian gives the same abelian section model.
The canonical comparison is normalized by these units and the row map. Naturality
of all section restrictions and resolution maps gives the two naturality squares.
7. For compatible replacements shift their common lower bound c to zero. The
horizontal-degree-p factor (-1)^(c*p) identifies the shifted signed totals.
Apply lem-sc-first-quadrant-total-column-comparison, then shift back. This proves
the entire-diagram invariant, inverting backwards arrows of a zigzag. Comparison
of total injective resolutions is unique up to homotopy by
lem-weil-pbc-kinjective-hom-derived, so this also gives resolution independence.
8. For a base resolution J and a resolution I of a*H, lift the identity of a*H
to t:a*J→I using K-injectivity. Its degreewise adjoint followed by the row map is
the augmented restriction. The derived adjunction of lem-pc-derived-adjoint-functors
is obtained from this same ordinary adjunction; hence its unit is Model.unit,
and the displayed square follows on these representatives. Compatible augmented
replacements commute before localization and are inverted there, giving the final
unit equation after replacements and zigzags.
9. Finally represent a map of bounded-below base objects by injective complexes.
If all section maps are derived isomorphisms, their section cones are acyclic.
The presheaf cone therefore has zero cohomology objectwise. Exact module
sheafification (lem-weil-pbc-ringed-site-module-sheafification-exact) identifies its
sheafified cone with the original sheaf cone and makes it acyclic. Thus the map
is a derived isomorphism. Scheme étale objects suffice and are contained in the
enlarged site. No step uses a hypercover or quasi-coherence. -/
theorem face_total_derived_sections {S : AlgebraicGeometry.Scheme.{u}}
    {Z : AlgebraicGeometry.AlgebraicSpace S}
    (W : SemiSimplexCategoryᵒᵖ ⥤ Over Z)
    (flat_faces : ∀ {p q : SemiSimplexCategoryᵒᵖ} (b : p ⟶ q),
      AlgebraicGeometry.AlgebraicSpace.MapIsFlat (W.map b).left)
    (flat_augmentation : ∀ p : SemiSimplexCategoryᵒᵖ,
      AlgebraicGeometry.AlgebraicSpace.MapIsFlat (W.obj p).hom) :
    Nonempty (Model W) ∧ ∀ G : Model W,
      ∃ (R : Rows G) (C : Computation R), Nonempty (UnitCompatibility C) := by
  sorry

end CategoryTheory.FaceTotalDerivedSections
