/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q104
-/
module

public import Sheaf.AlgebraicGeometry.TotalEtaleAugmentationAdjunction
public import Sheaf.CategoryTheory.Sites.GeometricMorphism
public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.Currying
import Sheaf.AlgebraicGeometry.TotalSimplicialEtaleSite
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.CategoryTheory.DerivedCategory.CompositionAdjunctionNormalization
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import Sheaf.CategoryTheory.KInjectiveComputes
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Homology.FirstQuadrantAugmentation
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# Canonical simplicial direct images and their augmentation spectral sequence

Source: Stacks Project, spaces-simplicial.tex, Tags 0DH0, 0DH1, 0D99 and 0D7F
(blueprint: lem-trf-simplicial-derived-image-spectral-sequence).

We use sheaves with values in `ModuleCat Λ`, the constant-coefficient module model
already used by `totalEtaleAugmentationAdjunction`. All direct images below are
specified on sections, and all derived direct images are `rightDerivedFunctorPlus`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w uA vA uB vB

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial ZeroObject

namespace AlgebraicGeometry

/-- Constant-coefficient modules on the total site, in the `ModuleCat` sheaf model.
Source: Stacks 0D72 (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
abbrev SimplicialEtaleMod (U : SimplicialObject Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] :=
  Sheaf (totalEtaleTopology U) (ModuleCat.{u + 1} Λ)

/-- Constant-coefficient modules on the small étale site.
Source: Stacks 0D72 (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
abbrev EtaleMod (X : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] :=
  Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)

/-- Component evaluation in the constant-module sheaf model.
Source: Stacks 0D72 (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
abbrev simplicialEtaleRestrict (U : SimplicialObject Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] (p : ℕ) :=
  totalEtaleRestriction U p (ModuleCat.{u + 1} Λ)

/-- Structural functor retaining both the simplicial degree and the map to the base.
Source: Stacks 0D7C (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
def simplicialEtaleDegreeToOver {X : Scheme.{u}} (U : SimplicialObject (Over X)) :
    TotalEtaleSite (U ⋙ Over.forget X) ⥤ SimplexCategoryᵒᵖ × Over X :=
  ((ObjectProperty.ι _ ⋙ Comma.snd _ _).prod' (totalEtaleToOver U))

/-- The canonical cosimplicial presheaf of component direct images. At `(p,V/X)`
its sections are `F(p,U_p ×_X V)`, with transitions induced by the total-site arrows.
The right Kan extension is taken before restricting the test objects to étale schemes.
Source: Stacks 0D7C (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
def simplicialEtaleCosimplicialPresheaf {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] :
    SimplicialEtaleMod (U ⋙ Over.forget X) Λ ⥤
      SimplexCategory ⥤ X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
  sheafToPresheaf _ _ ⋙ (simplicialEtaleDegreeToOver U).op.ran ⋙
    (Functor.whiskeringLeft _ _ _).obj
      ((Functor.prod (opOp SimplexCategory) (Scheme.Etale.forget X).op) ⋙
        (prodOpEquiv (C := SimplexCategoryᵒᵖ) (D := Over X)).inverse) ⋙
    Functor.curry

/-- The cosimplicial component direct images, sheafified degreewise. Its underlying
presheaf is identified with the preceding section formula in the theorem below.
Source: Stacks 0D7C (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
def simplicialEtaleCosimplicialDirect {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] :
    SimplicialEtaleMod (U ⋙ Over.forget X) Λ ⥤ SimplexCategory ⥤ EtaleMod X Λ :=
  simplicialEtaleCosimplicialPresheaf U Λ ⋙
    (Functor.whiskeringRight _ _ _).obj (presheafToSheaf X.smallEtaleTopology _)

/-- Additivity of component evaluation, inherited from preservation of finite products.
Source: Stacks 0D72 (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
instance simplicialEtaleRestrict_additive (U : SimplicialObject Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] (p : ℕ) :
    (simplicialEtaleRestrict U Λ p).Additive :=
  by
    dsimp [simplicialEtaleRestrict, totalEtaleRestriction]
    exact Functor.additive_of_preserves_binary_products _

/-- The structural functor for a morphism of simplicial schemes, before imposing étaleness
on target test objects. Source: Stacks 0DH0
(blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
def simplicialEtaleMorphismToComma {U V : SimplicialObject Scheme.{u}} (h : V ⟶ U) :
    TotalEtaleSite V ⥤ Comma (𝟭 Scheme.{u}) U :=
  ObjectProperty.ι _ ⋙ Comma.mapRight (𝟭 Scheme.{u}) h

/-- Direct-image sections for a simplicial morphism are compatible sections over all total
objects mapping to a target test object. Source: Stacks 0DH0
(blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
def simplicialEtaleMorphismDirectPresheaf {U V : SimplicialObject Scheme.{u}} (h : V ⟶ U)
    (Λ : Type (u + 1)) [CommRing Λ] :
    SimplicialEtaleMod V Λ ⥤ (TotalEtaleSite U)ᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
  sheafToPresheaf _ _ ⋙ (simplicialEtaleMorphismToComma h).op.ran ⋙
    (Functor.whiskeringLeft _ _ _).obj (ObjectProperty.ι _).op

/-- The canonical total direct image. The theorem asserts that the presheaf being
sheafified is already a sheaf and identifies its components with `h_p,*`.
Source: Stacks 0DH0 (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
def simplicialEtaleMorphismDirect {U V : SimplicialObject Scheme.{u}} (h : V ⟶ U)
    (Λ : Type (u + 1)) [CommRing Λ] :
    SimplicialEtaleMod V Λ ⥤ SimplicialEtaleMod U Λ :=
  simplicialEtaleMorphismDirectPresheaf h Λ ⋙ presheafToSheaf (totalEtaleTopology U) _

/-- Canonical total direct images preserve finite products, hence are additive.
Source: Stacks 0DH0 (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
instance simplicialEtaleMorphismDirect_additive {U V : SimplicialObject Scheme.{u}}
    (h : V ⟶ U) (Λ : Type (u + 1)) [CommRing Λ] :
    (simplicialEtaleMorphismDirect h Λ).Additive :=
  by
    let := ((simplicialEtaleMorphismToComma h).op.ranAdjunction
      (ModuleCat.{u + 1} Λ)).isRightAdjoint
    dsimp [simplicialEtaleMorphismDirect, simplicialEtaleMorphismDirectPresheaf]
    exact Functor.additive_of_preserves_binary_products _

/-- Component restriction is exact and preserves injectives.
Source: Stacks 0D72 and 0D75
(blueprint: lem-trf-simplicial-derived-image-spectral-sequence).
Proof: kernels are computed sectionwise. Cokernels are sheafified sectionwise cokernels;
the total topology is generated in a fixed degree, so evaluation commutes with this
sheafification. The left adjoint sends `M` in degree `p` to the sum over maps `[p] → [n]`
of the transition inverse images of `M`. These sums are finite, and the inverse images
for constant coefficients are exact. Hence this left adjoint is exact, and evaluation,
as its right adjoint, preserves injectives. -/
theorem simplicial_etale_restriction_exact (U : SimplicialObject Scheme.{u})
    (Λ : Type (u + 1)) [CommRing Λ] (p : ℕ) :
    PreservesFiniteLimits (simplicialEtaleRestrict U Λ p) ∧
    PreservesFiniteColimits (simplicialEtaleRestrict U Λ p) ∧
    (simplicialEtaleRestrict U Λ p).PreservesInjectiveObjects := by
  sorry

/-- The compatible-section total direct image has an exact inverse-image adjoint and
the expected component formulas. Source: Stacks 0DH0 and 0DH1
(blueprint: lem-trf-simplicial-derived-image-spectral-sequence).
Proof: at a total test object `(p,T/U_p)` the degree-p pullback `V_p ×_{U_p} T`
is initial in the opposite comma category computing the right Kan extension. Thus
its sections are the component direct-image sections. They satisfy the sheaf condition
because coverings are degreewise. Define inverse image componentwise using the usual
étale inverse images, with transition maps supplied by naturality of `h`; component
adjunction and the triangle identities identify compatible maps and give the total
adjunction. The inverse image is exact componentwise; its units and counits are the
component ones. This also proves the two natural component formulas. -/
theorem simplicial_etale_morphism_direct_image {U V : SimplicialObject Scheme.{u}}
    (h : V ⟶ U) (Λ : Type (u + 1)) [CommRing Λ] :
    (∀ F : SimplicialEtaleMod V Λ, Presheaf.IsSheaf (totalEtaleTopology U)
      ((simplicialEtaleMorphismDirectPresheaf h Λ).obj F)) ∧
    ∃ inverse : SimplicialEtaleMod U Λ ⥤ SimplicialEtaleMod V Λ,
    ∃ adj : inverse ⊣ simplicialEtaleMorphismDirect h Λ,
      PreservesFiniteLimits inverse ∧
      (∀ p : ℕ, Nonempty (inverse ⋙ simplicialEtaleRestrict V Λ p ≅
        simplicialEtaleRestrict U Λ p ⋙
          Etale.upperStar (ModuleCat.{u + 1} Λ) (h.app (op ⦋p⦌)))) ∧
      (∀ p : ℕ, Nonempty (simplicialEtaleMorphismDirect h Λ ⋙
        simplicialEtaleRestrict U Λ p ≅ simplicialEtaleRestrict V Λ p ⋙
          Etale.lowerStar (ModuleCat.{u + 1} Λ) (h.app (op ⦋p⦌)))) := by
  sorry

/-- Canonical derived component comparison, fixed by the underived comparison and the
units of the right-derived functors. Source: Stacks 0DH1
(blueprint: lem-trf-simplicial-derived-image-spectral-sequence).
Proof: use the preceding ordinary component formula. Restriction preserves injectives,
and the total direct image does so because its inverse image is exact. Thus both sides
on a bounded-below injective resolution are the same componentwise direct-image complex.
The comparison is the identity under these identifications; the displayed unit equation
is the universal-property characterization, so it is natural in every derived morphism.
The standard shift and cone structures on right derived functors give triangulated
exactness, without an additional assumption on `h`. -/
theorem simplicial_etale_derived_component {U V : SimplicialObject Scheme.{u}}
    (h : V ⟶ U) (Λ : Type (u + 1)) [CommRing Λ] (p : ℕ)
    [HasDerivedCategory.{w} (SimplicialEtaleMod V Λ)]
    [HasDerivedCategory.{w} (SimplicialEtaleMod U Λ)]
    [HasDerivedCategory.{w} (EtaleMod (V.obj (op ⦋p⦌)) Λ)]
    [HasDerivedCategory.{w} (EtaleMod (U.obj (op ⦋p⦌)) Λ)] :
    Functor.IsTriangulated (simplicialEtaleMorphismDirect h Λ).rightDerivedFunctorPlus ∧
    Functor.IsTriangulated
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) (h.app (op ⦋p⦌))).rightDerivedFunctorPlus ∧
    ∃ e : simplicialEtaleMorphismDirect h Λ ⋙ simplicialEtaleRestrict U Λ p ≅
        simplicialEtaleRestrict V Λ p ⋙
          Etale.lowerStar (ModuleCat.{u + 1} Λ) (h.app (op ⦋p⦌)),
    ∃ eD : (simplicialEtaleMorphismDirect h Λ).rightDerivedFunctorPlus ⋙
        (simplicialEtaleRestrict U Λ p).rightDerivedFunctorPlus ≅
      (simplicialEtaleRestrict V Λ p).rightDerivedFunctorPlus ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (h.app (op ⦋p⦌))).rightDerivedFunctorPlus,
      Functor.rightDerivedFunctorPlusCompUnit (simplicialEtaleMorphismDirect h Λ)
          (simplicialEtaleRestrict U Λ p) ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh eD.hom =
        Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus e.hom) DerivedCategory.Plus.Qh ≫
          Functor.rightDerivedFunctorPlusCompUnit (simplicialEtaleRestrict V Λ p)
            (Etale.lowerStar (ModuleCat.{u + 1} Λ) (h.app (op ⦋p⦌))) := by
  sorry

/-- The full subcategory of bounded-below derived objects with a specified lower bound.
Source: Stacks 0D7F (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
abbrev DerivedCohomologicalLower (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{w} A] (c : ℤ) :=
  ObjectProperty.FullSubcategory (fun L : DerivedCategory.Plus A ↦
    ∀ q : ℤ, q < c → IsZero ((DerivedCategory.Plus.homologyFunctor A q).obj L))

/-- Component evaluation of a scheme-over-base diagram with its displayed component
as codomain; this is the same restriction functor with the forgetful composite unfolded.
Source: Stacks 0D72 (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
abbrev simplicialEtaleRestrictOver {X : Scheme.{u}} (U : SimplicialObject (Over X))
    (Λ : Type (u + 1)) [CommRing Λ] (p : ℕ) :
    SimplicialEtaleMod (U ⋙ Over.forget X) Λ ⥤ EtaleMod (U.obj (op ⦋p⦌)).left Λ :=
  simplicialEtaleRestrict (U ⋙ Over.forget X) Λ p

/-- Additivity of the displayed component restriction is inherited from evaluation.
Source: Stacks 0D72 (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
instance simplicialEtaleRestrictOver_additive {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] (p : ℕ) :
    (simplicialEtaleRestrictOver U Λ p).Additive :=
  simplicialEtaleRestrict_additive (U ⋙ Over.forget X) Λ p

/-- The actual ordinary component direct images, before deriving.
Source: Stacks 0D7F (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
abbrev simplicialEtaleComponentDirect {X : Scheme.{u}} (U : SimplicialObject (Over X))
    (Λ : Type (u + 1)) [CommRing Λ] (p : ℕ) :=
  simplicialEtaleRestrict (U ⋙ Over.forget X) Λ p ⋙
    Etale.lowerStar (ModuleCat.{u + 1} Λ) (U.obj (op ⦋p⦌)).hom

/-- Stable pages extended by zero outside the translated first quadrant.
Source: Stacks 0D7F (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
def augmentationStableTerm {B : Type uB} [Category.{vB} B] [Abelian B]
    (E : CohomologicalSpectralSequenceNat B 1) (c p q : ℤ) : B :=
  if 0 ≤ p ∧ c ≤ q then
    (E.page (p.toNat + (q - c).toNat + 2) (by omega)).X (p.toNat, (q - c).toNat)
  else 0

/-- The map on actual stable pages, extended by the zero map outside the half-plane.
Source: Stacks 0D7F (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
def augmentationStableMap {B : Type uB} [Category.{vB} B] [Abelian B]
    {E E' : CohomologicalSpectralSequenceNat B 1} (f : E ⟶ E') (c p q : ℤ) :
    augmentationStableTerm E c p q ⟶ augmentationStableTerm E' c p q := by
  unfold augmentationStableTerm
  split_ifs
  · exact (f.hom (p.toNat + (q - c).toNat + 2) (by omega)).f (p.toNat, (q - c).toNat)
  · exact 0

/-- The face transformation on the actual component direct images, transported from
cosimplicial evaluation. Source: Stacks 0D7C
(blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
def augmentationCoface {A : Type uA} {B : Type uB}
    [Category.{vA} A] [Category.{vB} B] (component : ℕ → A ⥤ B)
    (cosimplicial : A ⥤ SimplexCategory ⥤ B)
    (e : ∀ p : ℕ, cosimplicial ⋙ (evaluation SimplexCategory B).obj ⦋p⦌ ≅ component p)
    (p : ℕ) (i : Fin (p + 2)) : component p ⟶ component (p + 1) :=
  (e p).inv ≫ Functor.whiskerLeft cosimplicial
    ((evaluation SimplexCategory B).map (SimplexCategory.δ i)) ≫ (e (p + 1)).hom

/-- An integer total complex obtained by extending the nonnegative total by zero.
Source: Stacks 0D7F (blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
abbrev augmentationIntegerTotal {B : Type uB} [Category.{vB} B] [Abelian B]
    (K : HomologicalComplex₂ B (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :=
  (K.total (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat

/-- All the spectral-sequence data, including functorial page-one identifications,
actual stable pages, the finite abutment filtration in every integer degree, and
computation on injective resolutions. These are conclusions, not supplied hypotheses.
Source: Stacks 0D7F and its proof
(blueprint: lem-trf-simplicial-derived-image-spectral-sequence). -/
structure SimplicialAugmentationSpectralSequence
    {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [EnoughInjectives A] (R : A ⥤ B) [R.Additive]
    (component : ℕ → A ⥤ B) [∀ p : ℕ, (component p).Additive]
    (cosimplicial : A ⥤ SimplexCategory ⥤ B) (c : ℤ) where
  /-- Functoriality in arbitrary derived morphisms preserving the lower bound. -/
  sequence : DerivedCohomologicalLower A c ⥤
    CohomologicalSpectralSequenceNat B 1
  /-- Natural page-one identifications, with `q` translated by the lower bound. -/
  pageOne (p q : ℕ) :
    sequence ⋙ SpectralSequence.pageFunctor _ _ 1 1 ⋙ HomologicalComplex.eval _ _ (p, q) ≅
      ObjectProperty.ι _ ⋙ (component p).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor B (c + q)
  /-- The cosimplicial section construction gives precisely the component direct images. -/
  componentIso (p : ℕ) :
    cosimplicial ⋙ (evaluation SimplexCategory B).obj ⦋p⦌ ≅ component p
  /-- Under the specified page-one identifications, d1 is the actual alternating coface sum. -/
  differential (L : DerivedCohomologicalLower A c) (p q : ℕ) :
    ((sequence.obj L).page 1 (by omega)).d (p, q) (p + 1, q) ≫
        (pageOne (p + 1) q).hom.app L =
      (pageOne p q).hom.app L ≫
        ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          (DerivedCategory.Plus.homologyFunctor B (c + q)).map
            ((Functor.rightDerivedFunctorPlusNatTrans
              (augmentationCoface component cosimplicial componentIso p i)).app L.obj)
  /-- Decreasing filtration of the actual augmentation derived image. -/
  filtration (L : DerivedCohomologicalLower A c) (n : ℤ) :
    DecreasingFiltration ((DerivedCategory.Plus.homologyFunctor B n).obj
      (R.rightDerivedFunctorPlus.obj L.obj))
  filtration_zero (L : DerivedCohomologicalLower A c) (n : ℤ) :
    (filtration L n).F 0 = ⊤
  filtration_finite (L : DerivedCohomologicalLower A c) (n : ℤ) :
    (filtration L n).F (max (n - c + 1) 0) =
      ⊥
  /-- All integer graded pieces, including negative `n-p` and the zero region. -/
  graded (L : DerivedCohomologicalLower A c) (n p : ℤ) :
    (filtration L n).gradedPiece p ≅ augmentationStableTerm (sequence.obj L) c p (n - p)
  /-- The maps of filtration steps induced by cohomology maps. -/
  filtrationMap {L M : DerivedCohomologicalLower A c} (f : L ⟶ M) (n p : ℤ) :
    ((filtration L n).F p : B) ⟶ ((filtration M n).F p : B)
  filtrationMap_comm {L M : DerivedCohomologicalLower A c} (f : L ⟶ M) (n p : ℤ) :
    filtrationMap f n p ≫ ((filtration M n).F p).arrow =
      ((filtration L n).F p).arrow ≫ (DerivedCategory.Plus.homologyFunctor B n).map
        (R.rightDerivedFunctorPlus.map f.hom)
  /-- The specified associated-graded identifications are natural on the actual stable pages. -/
  graded_natural {L M : DerivedCohomologicalLower A c} (f : L ⟶ M) (n p : ℤ) :
    ∃ g : (filtration L n).gradedPiece p ⟶ (filtration M n).gradedPiece p,
      cokernel.π (Subobject.ofLE _ _ ((filtration L n).F_succ_le p)) ≫ g =
        filtrationMap f n p ≫
          cokernel.π (Subobject.ofLE _ _ ((filtration M n).F_succ_le p)) ∧
      g ≫ (graded M n p).hom =
        (graded L n p).hom ≫ augmentationStableMap (sequence.map f) c p (n - p)
  /-- A bounded-below injective representative gives the stated alternating-face bicomplex.
The explicit equations fix both differentials; no arbitrary double complex is allowed. -/
  computation (L : DerivedCohomologicalLower A c) :
    ∃ I : CochainComplex.Plus A,
      (∀ j : ℤ, Injective (I.obj.X j)) ∧
      (∀ j : ℤ, j < c → IsZero (I.obj.X j)) ∧
      Nonempty (DerivedCategory.Plus.Q.obj I ≅ L.obj) ∧
      ∃ K : HomologicalComplex₂ B (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      ∃ t : ∀ p q : ℕ, (K.X p).X q ≅
        (cosimplicial.obj (I.obj.X (c + q))).obj ⦋p⦌,
      (∀ p q : ℕ,
        (K.d p (p + 1)).f q ≫ (t (p + 1) q).hom = (t p q).hom ≫
          ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
            (cosimplicial.obj (I.obj.X (c + q))).map
              (SimplexCategory.δ i)) ∧
      (∀ p q : ℕ,
        (K.X p).d q (q + 1) ≫ (t p (q + 1)).hom = (t p q).hom ≫
          (cosimplicial.map
            (I.obj.d (c + q) (c + (q + 1 : ℕ)))).app ⦋p⦌) ∧
      (∃ e : ∀ p q : ℕ, ((sequence.obj L).page 1 (by omega)).X (p, q) ≅ (K.X p).homology q,
        ∀ p q : ℕ, ((sequence.obj L).page 1 (by omega)).d (p, q) (p + 1, q) ≫
          (e (p + 1) q).hom = (e p q).hom ≫
            HomologicalComplex.homologyMap (K.d p (p + 1)) q) ∧
      (∀ p q : ℕ,
        K.ιTotal (ComplexShape.up ℕ) p q (p + q) rfl ≫
          (K.total (ComplexShape.up ℕ)).d (p + q) (p + q + 1) =
        (K.d p (p + 1)).f q ≫
          K.ιTotalOrZero (ComplexShape.up ℕ) (p + 1) q (p + q + 1) +
        (-1 : ℤ) ^ p • ((K.X p).d q (q + 1) ≫
          K.ιTotalOrZero (ComplexShape.up ℕ) p (q + 1) (p + q + 1))) ∧
      (∀ n : ℕ, Nonempty ((K.total (ComplexShape.up ℕ)).homology n ≅
        (DerivedCategory.Plus.homologyFunctor B (c + n)).obj
          (R.rightDerivedFunctorPlus.obj L.obj))) ∧
      ∃ F : DecreasingFiltration (augmentationIntegerTotal K),
      (∀ (p : ℤ) (n : ℕ), F.complexStep p n =
        (Finset.range (n + 1)).sup (fun i : ℕ ↦
          if p ≤ (i : ℤ) then imageSubobject
            (K.ιTotalOrZero (ComplexShape.up ℕ) i (n - i) n ≫
              ((K.total (ComplexShape.up ℕ)).extendXIso
                ComplexShape.embeddingUpNat (i := n) rfl).inv)
          else ⊥)) ∧
      (∃ D : ∀ (r : ℤ), 1 ≤ r → FilteredComplexPageDifferential (augmentationIntegerTotal K) F r,
       ∃ e : ∀ (r : ℤ) (hr : 1 ≤ r) (p q : ℕ),
          ((sequence.obj L).page r hr).X (p, q) ≅
            filteredComplexPageObject (augmentationIntegerTotal K) F r (p, q),
        ∀ (r : ℤ) (hr : 1 ≤ r) (p q p' q' : ℕ),
          ((sequence.obj L).page r hr).d (p, q) (p', q') ≫ (e r hr p' q').hom =
            (e r hr p q).hom ≫ (D r hr).d (p, q) (p', q')) ∧
      (∃ e : ∀ n : ℕ, (augmentationIntegerTotal K).homology n ≅
          (DerivedCategory.Plus.homologyFunctor B (c + n)).obj
            (R.rightDerivedFunctorPlus.obj L.obj),
        ∀ (n : ℕ) (p : ℤ), (filtration L (c + n)).F p =
          (Subobject.map (e n).hom).obj
            (imageSubobject (HomologicalComplex.homologyMap (F.F p).arrow (n : ℤ))))

/-- Derived images and the augmentation spectral sequence on the total étale site.
Source: Stacks 0D7F, 0D72 and 0D7C--0D7D
(blueprint: lem-trf-simplicial-derived-image-spectral-sequence).

Proof: evaluate total sheaves on their component sites; kernels are evaluated sectionwise,
and cokernel sheafification only uses coverings in the same degree. The exact left adjoint
to component evaluation sends a module `M` in degree `n` to the finite direct sums of its
inverse images indexed by maps `[n] → [m]`; thus restriction preserves injectives. Choose an
injective representative starting at `c`. For each resolution degree apply the cosimplicial
component direct-image functor. Its alternating-face augmented row is exact on injectives:
the free augmented simplicial module on a test module is contracted by inserting vertex zero,
and applying Hom into an injective module is exact. Consequently the row augmentation from
the augmentation direct image is a quasi-isomorphism onto the total complex. Translate the
resolution index by `c`, and use the first filtration of this first-quadrant bicomplex.
Its first page is column cohomology; exact evaluation and component injectivity identify it
with the indicated component derived image. Its first differential is induced by the
horizontal alternating sum. The total-complex signs give `d_face + (-1)^p d_resolution`.
The image filtration on total cohomology has the displayed graded pieces and finite bound.
Outside the half-plane both the stable terms and the graded pieces are zero, including
negative total degrees below `c`. Chain maps between injective resolutions exist for every
derived morphism; their homotopy uniqueness proves the natural page identifications and
filtration compatibility, with identities and composition inherited from chain maps. -/
theorem simplicial_derived_image_spectral_sequence {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{w} (SimplicialEtaleMod (U ⋙ Over.forget X) Λ)]
    [HasDerivedCategory.{w} (EtaleMod X Λ)] (c : ℤ) :
    Functor.IsTriangulated (totalEtaleAugmentationDirect U Λ).rightDerivedFunctorPlus ∧
    Nonempty (SimplicialAugmentationSpectralSequence
      (totalEtaleAugmentationDirect U Λ) (simplicialEtaleComponentDirect U Λ)
      (simplicialEtaleCosimplicialDirect U Λ) c) := by
  sorry

/-- The composite component image used in the first page is the component derived image
of the restriction, with the canonical derived-unit normalization.
Source: Stacks 0D7F (blueprint: lem-trf-simplicial-derived-image-spectral-sequence).
Proof: restriction is exact and preserves injectives, so a total injective resolution
restricts to an injective resolution on the component. Apply the component direct image
to this resolution. The right-derived universal property gives the displayed natural
isomorphism and its unit equation, characterizing it on injective representatives. -/
theorem simplicial_etale_augmentation_component {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] (p : ℕ)
    [HasDerivedCategory.{w} (SimplicialEtaleMod (U ⋙ Over.forget X) Λ)]
    [HasDerivedCategory.{w} (EtaleMod X Λ)]
    [HasDerivedCategory.{w} (EtaleMod (U.obj (op ⦋p⦌)).left Λ)] :
    ∃ e : (simplicialEtaleComponentDirect U Λ p).rightDerivedFunctorPlus ≅
      (simplicialEtaleRestrictOver U Λ p).rightDerivedFunctorPlus ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) (U.obj (op ⦋p⦌)).hom).rightDerivedFunctorPlus,
      (simplicialEtaleComponentDirect U Λ p).rightDerivedFunctorPlusUnit ≫
          Functor.whiskerLeft DerivedCategory.Plus.Qh e.hom =
        Functor.rightDerivedFunctorPlusCompUnit
          (simplicialEtaleRestrictOver U Λ p)
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) (U.obj (op ⦋p⦌)).hom) := by
  let := (simplicial_etale_restriction_exact (U ⋙ Over.forget X) Λ p).2.2
  exact ⟨Functor.rightDerivedFunctorPlusCompIso
    (simplicialEtaleRestrictOver U Λ p)
    (Etale.lowerStar (ModuleCat.{u + 1} Λ) (U.obj (op ⦋p⦌)).hom),
    Functor.rightDerivedFunctorPlusCompIso_fac
      (simplicialEtaleRestrictOver U Λ p)
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) (U.obj (op ⦋p⦌)).hom)⟩

/-- Composition of canonical total direct images and their derived functors.
Source: Stacks 0DH0, 0DH1 and 0D99
(blueprint: lem-trf-simplicial-derived-image-spectral-sequence).
Proof: on degree-p test objects the compatible-section formula is the component
pushforward. The usual component composition isomorphisms commute with transition maps
by naturality of the component adjunctions; they therefore glue to the ordinary total
composition isomorphism. The exact inverse images show that direct images preserve
injectives. On injective resolutions the comparison is the ordinary one term by term;
the right-derived universal property gives the displayed unit equation and naturality.
The next declaration identifies this normalization with the composite-adjunction mate. -/
theorem simplicial_etale_direct_image_composition
    {U V W : SimplicialObject Scheme.{u}} (h : V ⟶ U) (k : W ⟶ V)
    (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{w} (SimplicialEtaleMod U Λ)]
    [HasDerivedCategory.{w} (SimplicialEtaleMod V Λ)]
    [HasDerivedCategory.{w} (SimplicialEtaleMod W Λ)] :
    ∃ e : simplicialEtaleMorphismDirect (k ≫ h) Λ ≅
      simplicialEtaleMorphismDirect k Λ ⋙ simplicialEtaleMorphismDirect h Λ,
    ∃ eD : (simplicialEtaleMorphismDirect (k ≫ h) Λ).rightDerivedFunctorPlus ≅
      (simplicialEtaleMorphismDirect k Λ).rightDerivedFunctorPlus ⋙
        (simplicialEtaleMorphismDirect h Λ).rightDerivedFunctorPlus,
      (simplicialEtaleMorphismDirect (k ≫ h) Λ).rightDerivedFunctorPlusUnit ≫
          Functor.whiskerLeft DerivedCategory.Plus.Qh eD.hom =
        Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus e.hom)
          DerivedCategory.Plus.Qh ≫ Functor.rightDerivedFunctorPlusCompUnit
            (simplicialEtaleMorphismDirect k Λ) (simplicialEtaleMorphismDirect h Λ) := by
  sorry

/-- The composition comparison normalized by the specified inverse-image adjunctions:
it is the derived conjugate of the inverse-image comparison. This equation includes
both the unit and counit compatibility, not only an isomorphism of underlying functors.
Source: Stacks 0D99; composite inverse-image adjunction normalization
(blueprint: lem-trf-simplicial-derived-image-spectral-sequence).
Proof: the exact inverse-image adjunctions induce the standard derived adjunctions.
On bounded-below injective resolutions, both the derived conjugate and the comparison
of composite right-derived functors are represented by the ordinary conjugate.
Derived uniqueness makes these the same natural transformation. The conjugate
identities give the unit and counit equations. Associativity and identities follow
from those of the ordinary composite adjunction, so this also covers identity maps. -/
theorem simplicial_etale_composite_adjunction_normalization
    {U V W : SimplicialObject Scheme.{u}} (h : V ⟶ U) (k : W ⟶ V)
    (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{w} (SimplicialEtaleMod U Λ)]
    [HasDerivedCategory.{w} (SimplicialEtaleMod V Λ)]
    [HasDerivedCategory.{w} (SimplicialEtaleMod W Λ)]
    (iH : SimplicialEtaleMod U Λ ⥤ SimplicialEtaleMod V Λ)
    (iK : SimplicialEtaleMod V Λ ⥤ SimplicialEtaleMod W Λ)
    (iKH : SimplicialEtaleMod U Λ ⥤ SimplicialEtaleMod W Λ)
    [iH.Additive] [iK.Additive] [iKH.Additive]
    [PreservesFiniteLimits iH] [PreservesFiniteColimits iH]
    [PreservesFiniteLimits iK] [PreservesFiniteColimits iK]
    [PreservesFiniteLimits iKH] [PreservesFiniteColimits iKH]
    (adjH : iH ⊣ simplicialEtaleMorphismDirect h Λ)
    (adjK : iK ⊣ simplicialEtaleMorphismDirect k Λ)
    (adjKH : iKH ⊣ simplicialEtaleMorphismDirect (k ≫ h) Λ)
    (comparison : iH ⋙ iK ≅ iKH) :
    ∃ eD : (simplicialEtaleMorphismDirect (k ≫ h) Λ).rightDerivedFunctorPlus ≅
      (simplicialEtaleMorphismDirect k Λ).rightDerivedFunctorPlus ⋙
        (simplicialEtaleMorphismDirect h Λ).rightDerivedFunctorPlus,
      eD = conjugateIsoEquiv adjKH.derivedPlus (adjH.derivedPlus.comp adjK.derivedPlus)
        ((Functor.mapDerivedCategoryPlusCompIso iH iK).symm ≪≫
          Functor.mapDerivedCategoryPlusNatIso comparison) ∧
      (simplicialEtaleMorphismDirect (k ≫ h) Λ).rightDerivedFunctorPlusUnit ≫
          Functor.whiskerLeft DerivedCategory.Plus.Qh eD.hom =
        Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus
          (conjugateIsoEquiv adjKH (adjH.comp adjK) comparison).hom)
          DerivedCategory.Plus.Qh ≫ Functor.rightDerivedFunctorPlusCompUnit
            (simplicialEtaleMorphismDirect k Λ) (simplicialEtaleMorphismDirect h Λ) := by
  sorry

/-- Naturality for arbitrary maps of augmented diagrams, including a nonidentity base map.
The natural isomorphism on derived images is fixed by the ordinary square on every
injective representative through the explicit right-derived-unit equation.
Source: Stacks 0D99 (blueprint: lem-trf-simplicial-derived-image-spectral-sequence).
Proof: the augmentation inverse image is componentwise pullback. The commuting square
of scheme maps identifies the two composite inverse images, with the usual component
composition normalization. Its ordinary right-adjoint conjugate gives the displayed
square of direct images. All inverse images are exact, so their right adjoints preserve
injectives. Computing both composites on injective resolutions gives the derived square
and its unit equation. Taking adjunction mates yields the same square, so units and
counits commute; uniqueness of the construction gives naturality for coefficient maps,
composition of augmented diagrams and their identity diagrams. No hypercover or
properness hypothesis is used. -/
theorem simplicial_etale_augmented_diagram_comparison
    {X Y : Scheme.{u}} (U : SimplicialObject (Over X)) (V : SimplicialObject (Over Y))
    (f : Y ⟶ X) (h : V ⋙ Over.forget Y ⟶ U ⋙ Over.forget X)
    (comm : ∀ n : SimplexCategoryᵒᵖ,
      h.app n ≫ (U.obj n).hom = (V.obj n).hom ≫ f)
    (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{w} (SimplicialEtaleMod (U ⋙ Over.forget X) Λ)]
    [HasDerivedCategory.{w} (SimplicialEtaleMod (V ⋙ Over.forget Y) Λ)]
    [HasDerivedCategory.{w} (EtaleMod X Λ)]
    [HasDerivedCategory.{w} (EtaleMod Y Λ)] :
    ∃ e : simplicialEtaleMorphismDirect h Λ ⋙ totalEtaleAugmentationDirect U Λ ≅
      totalEtaleAugmentationDirect V Λ ⋙ Etale.lowerStar (ModuleCat.{u + 1} Λ) f,
    ∃ eD : (simplicialEtaleMorphismDirect h Λ).rightDerivedFunctorPlus ⋙
        (totalEtaleAugmentationDirect U Λ).rightDerivedFunctorPlus ≅
      (totalEtaleAugmentationDirect V Λ).rightDerivedFunctorPlus ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus,
      Functor.rightDerivedFunctorPlusCompUnit (simplicialEtaleMorphismDirect h Λ)
          (totalEtaleAugmentationDirect U Λ) ≫
          Functor.whiskerLeft DerivedCategory.Plus.Qh eD.hom =
        Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus e.hom) DerivedCategory.Plus.Qh ≫
          Functor.rightDerivedFunctorPlusCompUnit (totalEtaleAugmentationDirect V Λ)
            (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) := by
  sorry

/-- Adjunction normalization for the augmented-diagram comparison, with its base map.
The two right-image composites are compared by the conjugate of the specified ordinary
inverse-image square. Their derived comparison is exactly the conjugate under the
composite derived adjunctions, so both units and counits agree with composition.
Source: Stacks 0D99 (blueprint: lem-trf-simplicial-derived-image-spectral-sequence).
Proof: apply the exact inverse images to bounded-below complexes and the right adjoints
to injective resolutions. The ordinary inverse-image square gives its termwise adjoint
square on these resolutions. The derived adjunction is constructed from these very
units and counits. Its conjugate therefore has the displayed right-derived-unit
factorization. Derived uniqueness identifies it with the composition comparison.
Conjugation gives unit and counit compatibility for every coefficient morphism and
for composition and identity of augmented diagrams, including the identity base map. -/
theorem simplicial_etale_augmented_adjunction_normalization
    {X Y : Scheme.{u}} (U : SimplicialObject (Over X)) (V : SimplicialObject (Over Y))
    (f : Y ⟶ X) (h : V ⋙ Over.forget Y ⟶ U ⋙ Over.forget X)
    (Λ : Type (u + 1)) [CommRing Λ]
    [HasDerivedCategory.{w} (SimplicialEtaleMod (U ⋙ Over.forget X) Λ)]
    [HasDerivedCategory.{w} (SimplicialEtaleMod (V ⋙ Over.forget Y) Λ)]
    [HasDerivedCategory.{w} (EtaleMod X Λ)]
    [HasDerivedCategory.{w} (EtaleMod Y Λ)]
    (inverse : SimplicialEtaleMod (U ⋙ Over.forget X) Λ ⥤
      SimplicialEtaleMod (V ⋙ Over.forget Y) Λ)
    [inverse.Additive] [PreservesFiniteLimits inverse] [PreservesFiniteColimits inverse]
    (adj : inverse ⊣ simplicialEtaleMorphismDirect h Λ)
    (comparison : Etale.upperStar (ModuleCat.{u + 1} Λ) f ⋙
        totalEtaleAugmentationInverse V Λ ≅ totalEtaleAugmentationInverse U Λ ⋙ inverse) :
    ∃ eD : (simplicialEtaleMorphismDirect h Λ).rightDerivedFunctorPlus ⋙
        (totalEtaleAugmentationDirect U Λ).rightDerivedFunctorPlus ≅
      (totalEtaleAugmentationDirect V Λ).rightDerivedFunctorPlus ⋙
        (Etale.lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus,
      eD = conjugateIsoEquiv
        ((totalEtaleAugmentationAdjunction U Λ).derivedPlus.comp adj.derivedPlus)
        ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedPlus.comp
          (totalEtaleAugmentationAdjunction V Λ).derivedPlus)
        ((Functor.mapDerivedCategoryPlusCompIso
          (Etale.upperStar (ModuleCat.{u + 1} Λ) f)
          (totalEtaleAugmentationInverse V Λ)).symm ≪≫
          Functor.mapDerivedCategoryPlusNatIso comparison ≪≫
          Functor.mapDerivedCategoryPlusCompIso (totalEtaleAugmentationInverse U Λ) inverse) ∧
      Functor.rightDerivedFunctorPlusCompUnit (simplicialEtaleMorphismDirect h Λ)
          (totalEtaleAugmentationDirect U Λ) ≫
          Functor.whiskerLeft DerivedCategory.Plus.Qh eD.hom =
        Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus
          (conjugateIsoEquiv ((totalEtaleAugmentationAdjunction U Λ).comp adj)
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).comp
              (totalEtaleAugmentationAdjunction V Λ)) comparison).hom)
          DerivedCategory.Plus.Qh ≫
          Functor.rightDerivedFunctorPlusCompUnit (totalEtaleAugmentationDirect V Λ)
            (Etale.lowerStar (ModuleCat.{u + 1} Λ) f) := by
  sorry

end AlgebraicGeometry
