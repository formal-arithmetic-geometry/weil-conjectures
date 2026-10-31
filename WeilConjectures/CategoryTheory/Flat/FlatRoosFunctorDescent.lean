/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.CategoryTheory.Site.SiteDerivedTensorRestriction
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
import Mathlib.CategoryTheory.Localization.Pi
import all WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import all WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import all WeilConjectures.CategoryTheory.StrictRoosDerivation
import all WeilConjectures.CategoryTheory.StrictRoosModel
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all Mathlib.Algebra.Homology.Functor
import all Mathlib.CategoryTheory.Limits.Shapes.Countable
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.CategoryTheory.Abelian.FunctorCategory
import all WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all WeilConjectures.Algebra.Homology.RoosComplex
import all WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import all WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import all WeilConjectures.CategoryTheory.R.RGammaDerivedLimitSupplement
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.LinearAlgebra.Finsupp.LinearCombination
import all Mathlib.CategoryTheory.Adjunction.Evaluation
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import all WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import all WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import all Mathlib.Algebra.Homology.DerivedCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Descent of the normalized Roos realization from good cochain representatives

Source: Stacks Project, Tags 06YS, 06YU and 0941 (lemma-derived-limit-is-ok),
with the localization argument extracted in the DAG.
(blueprint: lem-pur-flat-roos-functor-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v r w uO vO rO wO

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory


set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048

attribute [local irreducible] roosF roosEval roosι DerivedCategory.Q

local instance (priority := 10000000) commRingSheafCompose
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := by
  infer_instance

private theorem flat_representative_localization
    {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{r})
    [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    [HasDerivedCategory.{w} (ringedSiteModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))] :
    ((ObjectProperty.ι (TensorFlatRepresentative (J := J) (R := R))) ⋙
      DerivedCategory.Q.{w}).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
        (ObjectProperty.ι (TensorFlatRepresentative (J := J) (R := R)))) := by
  let P : ObjectProperty _ := TensorFlatRepresentative (J := J) (R := R)
  let W := HomologicalComplex.quasiIso (ringedSiteModules.{r}
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)) (.up ℤ)
  let Φ : LocalizerMorphism (W.inverseImage P.ι) W := LocalizerMorphism.ofEq (F := P.ι) rfl
  obtain ⟨F, π, hπ, hF, hf⟩ := SheafOfModules.functorial_resolution R
  let T := P.lift F (fun X ↦ ⟨hF X, hf X⟩)
  have : Φ.functor.Full := by dsimp [Φ]; infer_instance
  have : Φ.functor.Faithful := by dsimp [Φ]; infer_instance
  have : Φ.IsInduced := ⟨rfl⟩
  have : Φ.IsLocalizedEquivalence :=
    Φ.isLocalizedEquivalence_of_functorial_left_resolutions
      (ρ := T) π (fun X ↦ hπ X) rfl
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization Φ DerivedCategory.Q

private theorem normalized_lift_unique
    {B D E : Type*} [Category* B] [Category* D] [Category* E]
    (q : B ⥤ D) (W : MorphismProperty B) [q.IsLocalization W]
    {F : B ⥤ E} {U V : D ⥤ E} (α : q ⋙ U ≅ F) (β : q ⋙ V ≅ F) :
    ∃! e : U ≅ V, ∀ X, e.hom.app (q.obj X) ≫ β.hom.app X = α.hom.app X := by
  let H := Localization.fullyFaithfulWhiskeringLeft q W E
  let e := H.preimageIso (α ≪≫ β.symm)
  have he (X : B) : e.hom.app (q.obj X) ≫ β.hom.app X = α.hom.app X := by
    have h := congrArg (fun t ↦ t.app X) (H.map_preimage (α ≪≫ β.symm).hom)
    change e.hom.app (q.obj X) = α.hom.app X ≫ β.inv.app X at h
    rw [h]
    simp
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Localization.natTrans_ext q W
  intro X
  apply (cancel_mono (β.hom.app X)).1
  exact (he' X).trans (he X).symm

private theorem normalized_pair_unique
    {B D E H : Type*} [Category* B] [Category* D] [Category* E] [Category* H]
    (q : B ⥤ D) (W : MorphismProperty B) [q.IsLocalization W]
    (RF : E ⥤ H) {F : B ⥤ E} {G : B ⥤ H} (θ : G ≅ F ⋙ RF)
    {U U' : D ⥤ E} {V V' : D ⥤ H}
    (α : q ⋙ U ≅ F) (β : q ⋙ V ≅ G) (rZ : V ≅ U ⋙ RF)
    (α' : q ⋙ U' ≅ F) (β' : q ⋙ V' ≅ G) (rZ' : V' ≅ U' ⋙ RF)
    (hc : ∀ p, rZ.hom.app (q.obj p) ≫ RF.map (α.hom.app p) =
      β.hom.app p ≫ θ.hom.app p)
    (hc' : ∀ p, rZ'.hom.app (q.obj p) ≫ RF.map (α'.hom.app p) =
      β'.hom.app p ≫ θ.hom.app p) :
    ∃! uv : (U ≅ U') × (V ≅ V'),
      (∀ p, uv.1.hom.app (q.obj p) ≫ α'.hom.app p = α.hom.app p) ∧
      (∀ p, uv.2.hom.app (q.obj p) ≫ β'.hom.app p = β.hom.app p) ∧
      (∀ x, rZ.hom.app x ≫ RF.map (uv.1.hom.app x) =
        uv.2.hom.app x ≫ rZ'.hom.app x) := by
  obtain ⟨u, hu, huniqU⟩ := normalized_lift_unique q W α α'
  obtain ⟨v, hv, huniqV⟩ := normalized_lift_unique q W β β'
  have hcompat : rZ.hom ≫ Functor.whiskerRight u.hom RF =
      v.hom ≫ rZ'.hom := by
    apply Localization.natTrans_ext q W
    intro p
    change rZ.hom.app (q.obj p) ≫ RF.map (u.hom.app (q.obj p)) =
      v.hom.app (q.obj p) ≫ rZ'.hom.app (q.obj p)
    apply (cancel_mono (RF.map (α'.hom.app p))).1
    rw [Category.assoc, ← RF.map_comp, hu, Category.assoc, hc',
      ← Category.assoc, hv]
    exact hc p
  refine ⟨(u, v), ⟨hu, hv, fun x ↦ congrArg (fun t ↦ t.app x) hcompat⟩, ?_⟩
  intro uv huv
  exact Prod.ext (huniqU uv.1 huv.1) (huniqV uv.2 huv.2.1)

private theorem resolution_formula
    {B E : Type*} [Category* B] [Category* E] {F G : B ⥤ E}
    (θ : F ≅ G) {X Y : B} (a : X ⟶ Y) [IsIso (G.map a)]
    {L : E} (ε : L ≅ F.obj Y) (d : L ≅ G.obj X)
    (hd : d.hom ≫ G.map a = ε.hom ≫ θ.hom.app Y) :
    θ.hom.app X = F.map a ≫ ε.inv ≫ d.hom := by
  apply (cancel_mono (G.map a)).1
  rw [Category.assoc, Category.assoc, hd]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    (θ.hom.naturality a).symm

private theorem projection_transport
    {E : Type*} [Category* E] {X Y L U V : E}
    (a : X ⟶ Y) (d : L ⟶ X) (η : L ⟶ Y) (p : X ⟶ U) (q : Y ⟶ V)
    (l : L ⟶ V) (ev : U ≅ V)
    (hd : d ≫ a = η) (hne : a ≫ q = p ≫ ev.hom) (he : η ≫ q = l) :
    d ≫ p = l ≫ ev.inv := by
  apply (cancel_mono ev.hom).1
  rw [Category.assoc, ← hne, ← Category.assoc, hd, he]
  simp

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option maxHeartbeats 800000 in
-- The normalization and product-localization proof has many dependent categorical expressions.
/-- A quasi-isomorphism-invariant functor on finitely many good cochain representatives
has derived lifts, and its normalized Roos comparison descends naturally and uniquely.
The isomorphism `theta` is the fixed representative comparison to total derived limit.
Its unit normalization, its formula for every injective-term K-injective resolution,
and the equations for `e` retain the actual total-limit projections. The compatibility
of `rZ` is equality of its whole representative component, not just its projections.
The final unique pair of isomorphisms compares any other lifts with these components;
this also compares any change of good resolutions. Naturality of all the displayed
isomorphisms is on the entire product derived category, hence includes roofs.

Source: Stacks Tags 06YS, 06YU, 0941 (lemma-derived-limit-is-ok), and the extracted
localization argument (blueprint: lem-pur-flat-roos-functor-descent).

Proof: Functorial flat-term K-flat resolutions make the good-cochain inclusion a
localized equivalence, so its composite with Q is a localization. Finite products
preserve this property. Levelwise quasi-isomorphisms of towers are quasi-isomorphisms,
so Q Z descends to Zbar. The generic strict Roos derivation proof applies to the
module category, which is Grothendieck after transport to a small equivalent site.
Uniqueness of right derived functors supplies theta with its unit equality. Set
Zhat = Zbar RF, use alpha followed by theta inverse to define beta, and take rZ
to be the identity. The unit equality and naturality give the formula for every
K-injective resolution and each actual limit projection. Fully faithful restriction
along the product localization gives the unique compatible comparison isomorphisms;
their compatibility with rZ is checked on the full representative components.
-/
theorem flatRoosFunctorDescent
    (k : ℕ) (_hk : 1 ≤ k)
    (C : Fin k → Type u) [∀ i, Category.{v} (C i)] [∀ i, EssentiallySmall.{r} (C i)]
    (J : ∀ i, GrothendieckTopology (C i)) (R : ∀ i, Sheaf (J i) CommRingCat.{r})
    [∀ i, HasSheafify (J i) AddCommGrpCat.{r}]
    [∀ i, (J i).WEqualsLocallyBijective AddCommGrpCat.{r}]
    [∀ i, HasDerivedCategory.{w} (ringedSiteModules.{r}
          ((sheafCompose (J i) (forget₂ CommRingCat.{r} RingCat.{r})).obj (R i)))]
    {D : Type uO} [Category.{vO} D] [EssentiallySmall.{rO} D]
    (K : GrothendieckTopology D) (S : Sheaf K CommRingCat.{rO})
    [HasSheafify K AddCommGrpCat.{rO}] [K.WEqualsLocallyBijective AddCommGrpCat.{rO}]
    [HasDerivedCategory.{wO} (ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S))]
    [HasDerivedCategory.{wO} (ℕᵒᵖ ⥤ ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S))]
    [HasCountableProducts (ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S))]
    [HasLimitsOfShape ℕᵒᵖ (ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S))]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S))]
    (Z : (∀ i, (ObjectProperty.FullSubcategory
      (TensorFlatRepresentative (J := J i) (R := R i)))) ⥤
      CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)) ℤ)
    (_hZ : ∀ {P P' : ∀ i, (ObjectProperty.FullSubcategory
      (TensorFlatRepresentative (J := J i) (R := R i)))}
      (f : P ⟶ P'), (∀ i, QuasiIso ((f i).hom)) → ∀ n : ℕ,
        QuasiIso ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
          (Z.map f)).app (op n)))
    (RF : DerivedCategory.{wO} (ℕᵒᵖ ⥤ ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)) ⥤
      DerivedCategory.{wO} (ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)))
    (eta : roosLimitFunctor (A := ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)) ⋙ DerivedCategory.Q.{wO} ⟶
      DerivedCategory.Q.{wO} (C := ℕᵒᵖ ⥤ ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)) ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor eta (HomologicalComplex.quasiIso
      (ℕᵒᵖ ⥤ ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)) (.up ℤ))) :
    ∃ (theta : roosF (A := ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)) ⋙ DerivedCategory.Q.{wO} ≅
      DerivedCategory.Q.{wO} (C := ℕᵒᵖ ⥤ ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)) ⋙ RF)
      (e : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)) ℤ)
        (n : ℕ), RF.obj (DerivedCategory.Q.{wO}.obj X) ⟶
          DerivedCategory.Q.{wO}.obj (X.asFunctor.obj (op n)))
      (Zbar : (∀ i, DerivedCategory.{w} (ringedSiteModules.{r}
          ((sheafCompose (J i) (forget₂ CommRingCat.{r} RingCat.{r})).obj (R i)))) ⥤
        DerivedCategory.{wO} (ℕᵒᵖ ⥤ ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)))
      (Zhat : (∀ i, DerivedCategory.{w} (ringedSiteModules.{r}
          ((sheafCompose (J i) (forget₂ CommRingCat.{r} RingCat.{r})).obj (R i)))) ⥤
        DerivedCategory.{wO} (ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)))
      (alpha : Functor.pi (fun i ↦ ((ObjectProperty.ι
        (TensorFlatRepresentative (J := J i) (R := R i))) ⋙
          DerivedCategory.Q.{w})) ⋙ Zbar ≅
        Z ⋙ DerivedCategory.Q.{wO})
      (beta : Functor.pi (fun i ↦ ((ObjectProperty.ι
        (TensorFlatRepresentative (J := J i) (R := R i))) ⋙
          DerivedCategory.Q.{w})) ⋙ Zhat ≅
        Z ⋙ roosF ⋙ DerivedCategory.Q.{wO})
      (rZ : Zhat ≅ Zbar ⋙ RF),
      (∀ (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)) ℤ)
        [I.IsKInjective] (_hinj : ∀ p : ℤ, Injective (I.X p)),
        QuasiIso (roosι I) ∧ DerivedCategory.Q.{wO}.map (roosι I) ≫ theta.hom.app I = eta.app I) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)) ℤ) (n : ℕ),
        theta.hom.app X ≫ e X n = DerivedCategory.Q.{wO}.map (roosEval X n)) ∧
      (∀ P : ∀ i, (ObjectProperty.FullSubcategory
        (TensorFlatRepresentative (J := J i) (R := R i))),
        rZ.hom.app (fun i ↦ DerivedCategory.Q.{w}.obj (P i).obj) ≫
            RF.map (alpha.hom.app P) = beta.hom.app P ≫ theta.hom.app (Z.obj P)) ∧
      (∀ (P : ∀ i, (ObjectProperty.FullSubcategory
        (TensorFlatRepresentative (J := J i) (R := R i))))
        (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)) ℤ)
        (a : Z.obj P ⟶ I) [QuasiIso a] [I.IsKInjective]
        (_hinj : ∀ p : ℤ, Injective (I.X p)),
        ∃ (eps : DerivedCategory.Q.{wO}.obj (limit I.asFunctor) ≅
            DerivedCategory.Q.{wO}.obj (roosF.obj I))
          (d : DerivedCategory.Q.{wO}.obj (limit I.asFunctor) ≅
            RF.obj (DerivedCategory.Q.{wO}.obj (Z.obj P))),
          eps.hom = DerivedCategory.Q.{wO}.map (roosι I) ∧
          d.hom ≫ RF.map (DerivedCategory.Q.{wO}.map a) = eta.app I ∧
          rZ.hom.app (fun i ↦ DerivedCategory.Q.{w}.obj (P i).obj) ≫
              RF.map (alpha.hom.app P) =
            beta.hom.app P ≫ DerivedCategory.Q.{wO}.map (roosF.map a) ≫ eps.inv ≫ d.hom ∧
          (∀ n : ℕ, ∃ ev : DerivedCategory.Q.{wO}.obj
              ((Z.obj P).asFunctor.obj (op n)) ≅
              DerivedCategory.Q.{wO}.obj (I.asFunctor.obj (op n)),
            ev.hom = DerivedCategory.Q.{wO}.map
              ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a).app (op n)) ∧
            d.hom ≫ e (Z.obj P) n =
              DerivedCategory.Q.{wO}.map (limit.π I.asFunctor (op n)) ≫ ev.inv)) ∧
      (∀ P : ∀ i, (ObjectProperty.FullSubcategory
        (TensorFlatRepresentative (J := J i) (R := R i))), ∀
        n : ℕ,
        rZ.hom.app (fun i ↦ DerivedCategory.Q.{w}.obj (P i).obj) ≫
            RF.map (alpha.hom.app P) ≫ e (Z.obj P) n =
          beta.hom.app P ≫ DerivedCategory.Q.{wO}.map (roosEval (Z.obj P) n)) ∧
      (∀ (Zbar' : (∀ i, DerivedCategory.{w} (ringedSiteModules.{r}
          ((sheafCompose (J i) (forget₂ CommRingCat.{r} RingCat.{r})).obj (R i)))) ⥤
          DerivedCategory.{wO} (ℕᵒᵖ ⥤ ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)))
        (Zhat' : (∀ i, DerivedCategory.{w} (ringedSiteModules.{r}
          ((sheafCompose (J i) (forget₂ CommRingCat.{r} RingCat.{r})).obj (R i)))) ⥤
          DerivedCategory.{wO} (ringedSiteModules.{rO}
        ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)))
        (alpha' : Functor.pi (fun i ↦ ((ObjectProperty.ι
          (TensorFlatRepresentative (J := J i) (R := R i))) ⋙
          DerivedCategory.Q.{w})) ⋙ Zbar' ≅
          Z ⋙ DerivedCategory.Q.{wO})
        (beta' : Functor.pi (fun i ↦ ((ObjectProperty.ι
          (TensorFlatRepresentative (J := J i) (R := R i))) ⋙
          DerivedCategory.Q.{w})) ⋙ Zhat' ≅
          Z ⋙ roosF ⋙ DerivedCategory.Q.{wO})
        (rZ' : Zhat' ≅ Zbar' ⋙ RF)
        (_hcomp : ∀ P : ∀ i, (ObjectProperty.FullSubcategory
          (TensorFlatRepresentative (J := J i) (R := R i))),
          rZ'.hom.app (fun i ↦ DerivedCategory.Q.{w}.obj (P i).obj) ≫
            RF.map (alpha'.hom.app P) = beta'.hom.app P ≫ theta.hom.app (Z.obj P)),
        ∃! uv : (Zbar ≅ Zbar') × (Zhat ≅ Zhat'),
          (∀ P : ∀ i, (ObjectProperty.FullSubcategory
            (TensorFlatRepresentative (J := J i) (R := R i))),
            uv.1.hom.app (fun i ↦ DerivedCategory.Q.{w}.obj (P i).obj) ≫
              alpha'.hom.app P = alpha.hom.app P) ∧
          (∀ P : ∀ i, (ObjectProperty.FullSubcategory
            (TensorFlatRepresentative (J := J i) (R := R i))),
            uv.2.hom.app (fun i ↦ DerivedCategory.Q.{w}.obj (P i).obj) ≫
              beta'.hom.app P = beta.hom.app P) ∧
          (∀ x : ∀ i, DerivedCategory.{w} (ringedSiteModules.{r}
          ((sheafCompose (J i) (forget₂ CommRingCat.{r} RingCat.{r})).obj (R i))),
            rZ.hom.app x ≫ RF.map (uv.1.hom.app x) =
              uv.2.hom.app x ≫ rZ'.hom.app x)) := by
  classical
  let A := ringedSiteModules.{rO}
    ((sheafCompose K (forget₂ CommRingCat.{rO} RingCat.{rO})).obj S)
  let : IsGrothendieckAbelian.{rO} A := moduleSheaves_grothendieck K _
  let : IsGrothendieckAbelian.{rO} (ℕᵒᵖ ⥤ A) := tower_grothendieck A
  let W := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)
  have hinv : W.IsInvertedBy (roosF ⋙ DerivedCategory.Q.{wO}) := by
    intro X Y f hf
    have : QuasiIso f := hf
    have : QuasiIso (roosF.map f) := roos_map_quasiIso f
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (roosF.map f)))
  obtain ⟨θ, hunit⟩ : ∃ (θ : roosF (A := A) ⋙
      DerivedCategory.Q.{wO} (C := A) ≅
      DerivedCategory.Q.{wO} (C := ℕᵒᵖ ⥤ A) ⋙ RF),
      ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
      DerivedCategory.Q.{wO}.map (roosι X) ≫ θ.hom.app X = eta.app X := by
    obtain ⟨CF, κ, hCF⟩ : ∃ (CF : DerivedCategory.{wO} (ℕᵒᵖ ⥤ A) ⥤
        DerivedCategory.{wO} A)
        (κ : roosF (A := A) ⋙ DerivedCategory.Q.{wO} (C := A) ≅
          DerivedCategory.Q.{wO} (C := ℕᵒᵖ ⥤ A) ⋙ CF),
        CF.IsRightDerivedFunctor (roosDerivedUnit (A := A) κ) W := by
      let CF := Localization.lift (roosF ⋙ DerivedCategory.Q.{wO}) hinv DerivedCategory.Q
      let κ := (Localization.fac (roosF ⋙ DerivedCategory.Q.{wO}) hinv
        DerivedCategory.Q).symm
      refine ⟨CF, κ, ?_⟩
      exact
        roos_universal W DerivedCategory.Q _ _ CF κ
          (Functor.whiskerRight roosInclusion DerivedCategory.Q)
          (CochainComplex.kInjectiveResolutionFunctor.{rO} (ℕᵒᵖ ⥤ A))
          (CochainComplex.toKInjectiveResolution.{rO} (ℕᵒᵖ ⥤ A))
          (fun X ↦ (CochainComplex.monoQuasiIso_toKInjectiveResolution_app _ X).2)
          (fun X ↦ by
            have := roos_inclusion_quasiIso
              ((CochainComplex.kInjectiveResolutionFunctor.{rO} (ℕᵒᵖ ⥤ A)).obj X)
            exact inferInstanceAs (IsIso (DerivedCategory.Q.map (roosι _))))
    let := _hRF
    let := hCF
    let ρ : CF ≅ RF := CF.rightDerivedUnique RF (roosDerivedUnit κ) eta W
    let θ : roosF ⋙ DerivedCategory.Q.{wO} ≅ DerivedCategory.Q.{wO} ⋙ RF :=
      κ ≪≫ Functor.isoWhiskerLeft DerivedCategory.Q ρ
    refine ⟨θ, ?_⟩
    intro X
    have h := CF.rightDerivedNatTrans_app RF (roosDerivedUnit κ) eta W (𝟙 _) X
    simp only [NatTrans.id_app, Category.id_comp] at h
    change (DerivedCategory.Q.map (roosι X) ≫ κ.hom.app X) ≫
      ρ.hom.app (DerivedCategory.Q.obj X) = eta.app X at h
    exact (Category.assoc _ _ _).symm.trans h
  let e := fun X n ↦ θ.inv.app X ≫ DerivedCategory.Q.map (roosEval X n)
  have he (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
      θ.hom.app X ≫ e X n = DerivedCategory.Q.map (roosEval X n) := by
    simp [e]
  let P := fun i ↦ (TensorFlatRepresentative (J := J i) (R := R i) : ObjectProperty _)
  let V := fun i ↦ (HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage (ObjectProperty.ι (P i))
  let q := Functor.pi (fun i ↦ (ObjectProperty.ι (P i)) ⋙ DerivedCategory.Q.{w})
  have (i : Fin k) : ((ObjectProperty.ι (P i)) ⋙ DerivedCategory.Q.{w}).IsLocalization (V i) :=
    flat_representative_localization (J i) (R i)
  have : q.IsLocalization (MorphismProperty.pi V) := inferInstance
  have hZ : (MorphismProperty.pi V).IsInvertedBy (Z ⋙ DerivedCategory.Q.{wO}) := by
    intro X Y f hf
    have hq : QuasiIso (Z.map f) :=
      (HomologicalComplex.quasiIso_iff_evaluation _).2 (fun n ↦ _hZ f hf n.unop)
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map (Z.map f)))
  obtain ⟨Zbar, ⟨α⟩⟩ : ∃ Zbar, Nonempty (q ⋙ Zbar ≅ Z ⋙ DerivedCategory.Q.{wO}) :=
    ⟨Localization.lift (Z ⋙ DerivedCategory.Q.{wO}) hZ q,
      ⟨Localization.fac (Z ⋙ DerivedCategory.Q.{wO}) hZ q⟩⟩
  let Zhat := Zbar ⋙ RF
  let β : q ⋙ Zhat ≅ Z ⋙ roosF ⋙ DerivedCategory.Q.{wO} :=
    Functor.isoWhiskerRight α RF ≪≫ Functor.isoWhiskerLeft Z θ.symm
  let rZ : Zhat ≅ Zbar ⋙ RF := Iso.refl _
  have hc (p : ∀ i, (ObjectProperty.FullSubcategory (P i))) :
      rZ.hom.app (q.obj p) ≫ RF.map (α.hom.app p) =
        β.hom.app p ≫ θ.hom.app (Z.obj p) := by
    simp [rZ, β]
  refine ⟨θ, e, Zbar, Zhat, α, β, rZ, ?_, he, hc, ?_, ?_, ?_⟩
  · intro I hI hIinj
    exact ⟨roos_inclusion_quasiIso I, hunit I⟩
  · intro p I a ha hI hIinj
    have : QuasiIso (roosι I) := roos_inclusion_quasiIso I
    have hQ : IsIso (DerivedCategory.Q.{wO}.map (roosι I)) := inferInstance
    have hθ : IsIso (θ.hom.app I) := (θ.app I).isIso_hom
    have hη : IsIso (eta.app I) := by
      have h := (asIso (DerivedCategory.Q.{wO}.map (roosι I)) ≪≫ θ.app I).isIso_hom
      change IsIso (DerivedCategory.Q.{wO}.map (roosι I) ≫ θ.hom.app I) at h
      exact (hunit I) ▸ h
    let ε := asIso (DerivedCategory.Q.{wO}.map (roosι I))
    let d := asIso (eta.app I) ≪≫ (asIso (RF.map (DerivedCategory.Q.map a))).symm
    have hd : d.hom ≫ RF.map (DerivedCategory.Q.map a) = eta.app I := by simp [d]
    have : IsIso ((DerivedCategory.Q.{wO} ⋙ RF).map a) :=
      inferInstanceAs (IsIso (RF.map (DerivedCategory.Q.{wO}.map a)))
    have hnorm : θ.hom.app (Z.obj p) =
        DerivedCategory.Q.map (roosF.map a) ≫ ε.inv ≫ d.hom :=
      resolution_formula θ a ε d (hd.trans (hunit I).symm)
    refine ⟨ε, d, rfl, hd, ?_, ?_⟩
    · exact (hc p).trans (congrArg (fun f ↦ β.hom.app p ≫ f) hnorm)
    · intro n
      let an := (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map a).app (op n)
      have han : QuasiIso an :=
        (HomologicalComplex.quasiIso_iff_evaluation a).mp ha (op n)
      let ev := asIso (DerivedCategory.Q.{wO}.map an)
      refine ⟨ev, rfl, ?_⟩
      have heI : eta.app I ≫ e I n =
          DerivedCategory.Q.map (limit.π I.asFunctor (op n)) := by
        calc
          _ = (DerivedCategory.Q.map (roosι I) ≫ θ.hom.app I) ≫ e I n :=
            congrArg (fun f ↦ f ≫ e I n) (hunit I).symm
          _ = DerivedCategory.Q.map (roosι I) ≫
              DerivedCategory.Q.map (roosEval I n) :=
            (Category.assoc _ _ _).trans
              (congrArg (fun f ↦ DerivedCategory.Q.map (roosι I) ≫ f) (he I n))
          _ = _ := (DerivedCategory.Q.map_comp _ _).symm.trans
            (congrArg DerivedCategory.Q.map (roosι_eval I n))
      have hne : RF.map (DerivedCategory.Q.map a) ≫ e I n =
          e (Z.obj p) n ≫ DerivedCategory.Q.map an := by
        have hn := θ.inv.naturality a
        dsimp only [Functor.comp_map] at hn
        calc
          _ = (θ.inv.app (Z.obj p) ≫
              DerivedCategory.Q.map (roosF.map a)) ≫
                DerivedCategory.Q.map (roosEval I n) := by
            exact (Category.assoc _ _ _).symm.trans
              (congrArg (fun f ↦ f ≫ DerivedCategory.Q.map (roosEval I n)) hn)
          _ = _ := by
            have ht : DerivedCategory.Q.map (roosF.map a) ≫
                DerivedCategory.Q.map (roosEval I n) =
                DerivedCategory.Q.map (roosEval (Z.obj p) n) ≫
                  DerivedCategory.Q.map an :=
              (DerivedCategory.Q.map_comp _ _).symm.trans
                ((congrArg DerivedCategory.Q.map (roosEval_natural a n)).trans
                  (DerivedCategory.Q.map_comp _ _))
            exact (Category.assoc _ _ _).trans
              ((congrArg (fun f ↦ θ.inv.app (Z.obj p) ≫ f) ht).trans
                (Category.assoc _ _ _).symm)
      exact projection_transport (RF.map (DerivedCategory.Q.map a)) d.hom
        (eta.app I) (e (Z.obj p) n) (e I n)
        (DerivedCategory.Q.map (limit.π I.asFunctor (op n))) ev hd hne heI
  · intro p n
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun f ↦ f ≫ e (Z.obj p) n) (hc p)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun f ↦ β.hom.app p ≫ f) (he (Z.obj p) n))))
  · intro Zbar' Zhat' α' β' rZ' hcomp
    exact normalized_pair_unique q (MorphismProperty.pi V) RF
      (F := Z ⋙ DerivedCategory.Q.{wO})
      (G := Z ⋙ roosF ⋙ DerivedCategory.Q.{wO})
      (Functor.isoWhiskerLeft Z θ) α β rZ α' β' rZ' hc hcomp

end CategoryTheory
