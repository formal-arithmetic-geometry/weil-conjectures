module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Paper.SiteDerivedTensorRestriction
import all Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison

/-! # Site derived tensor resolving data and localization counit

Source: Stacks Project, sites-cohomology.tex, Tags 06YS and 06YU, construction preceding
and surrounding definition-derived-tor (blueprint: def-pd-site-derived-tensor-resolving-data).

The resolving-pair model map is the recorded `CategoryTheory.tensorDescentPair` of
def-weil-pbc-tensor-descent-representative-comparison: the published descent witness's
chain/homotopy and resolving comparisons with the quotient factors. No new tensor, resolution
or comparison is selected. `counit` is the unique extension of its inverse to all complex pairs.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance 11000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

universe uC vC r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.SiteDerivedTensorResolvingData

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The recorded module-sheaf category. Source: Stacks, Modules on Sites, 03DA
(blueprint: def-pd-site-derived-tensor-resolving-data). -/
abbrev Modules := CategoryTheory.ringedSiteModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- Unbounded complexes. Source: Stacks, Tag 06YU
(blueprint: def-pd-site-derived-tensor-resolving-data). -/
abbrev Complexes := CochainComplex (Modules R) ℤ

variable [HasDerivedCategory.{w} (Modules R)]

attribute [local irreducible] SheafOfModules.siteDerivedTensorIndependentCoefficients

/-- Cached native structure; its data are the existing published instance.
Source: Stacks 03EK and 06YU (blueprint: def-pd-site-derived-tensor-resolving-data). -/
abbrev sheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := inferInstance

attribute [local instance 12000] sheafCompose

/-- Cached native structure; its data are the existing published instance.
Source: Stacks 03EK and 06YU (blueprint: def-pd-site-derived-tensor-resolving-data). -/
abbrev moduleAbelian : Abelian (Modules R) := inferInstance

attribute [local instance 12000] moduleAbelian

/-- Cached native structure; its data are the existing published instance.
Source: Stacks 03EK and 06YU (blueprint: def-pd-site-derived-tensor-resolving-data). -/
abbrev moduleMonoidal : MonoidalCategory (Modules R) :=
  inferInstance

attribute [local instance 12000] moduleMonoidal

/-- Cached native structure; its data are the existing published instance.
Source: Stacks 03EK and 06YU (blueprint: def-pd-site-derived-tensor-resolving-data). -/
abbrev moduleAdditive : MonoidalPreadditive (Modules R) :=
  inferInstance

attribute [local instance 12000] moduleAdditive

/-- Cached native structure; its data are the existing published instance.
Source: Stacks 03EK and 06YU (blueprint: def-pd-site-derived-tensor-resolving-data). -/
abbrev moduleSymmetric : SymmetricCategory (Modules R) :=
  inferInstance

attribute [local instance 12000] moduleSymmetric

/-- Cached native structure; its data are the existing published instance.
Source: Stacks 03EK and 06YU (blueprint: def-pd-site-derived-tensor-resolving-data). -/
abbrev moduleColimits : HasColimitsOfSize.{0, 0} (Modules R) :=
  inferInstance

attribute [local instance 12000] moduleColimits

/-- Cached native structure; its data are the existing published instance.
Source: Stacks 03EK and 06YU (blueprint: def-pd-site-derived-tensor-resolving-data). -/
abbrev complexMonoidal : MonoidalCategory (Complexes R) :=
  inferInstance

attribute [local instance 12000] complexMonoidal

/-- Cached native structure; its data are the existing published instance.
Source: Stacks 03EK and 06YU (blueprint: def-pd-site-derived-tensor-resolving-data). -/
abbrev complexMonoidalStruct :
    MonoidalCategoryStruct (Complexes R) := inferInstance

attribute [local instance 12000] complexMonoidalStruct

/-- The fixed resolving-pair comparison r: the recorded representative comparison
`tensorDescentPair` (inverse quotient comparison, inverse chain/homotopy comparison, resolving
comparison, quotient comparisons on both inputs), at the flat-term K-flat pair `P,Q`.
Source: Stacks 06YU, construction preceding definition-derived-tor
(blueprint: def-pd-site-derived-tensor-resolving-data). -/
abbrev model (P Q : Complexes R)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hpf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hqf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)) :
    DerivedCategory.Q.obj (P ⊗ Q) ≅
      (siteDerivedTensorIndependentCoefficients J R).obj
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
  CategoryTheory.tensorDescentPair (J := J) (R := R) P Q ⟨hp, hpf⟩ ⟨hq, hqf⟩


private theorem model_eq (P Q : Complexes R)
    (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
    (hpf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
    (hqf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)) :
    model R P Q hp hq hpf hqf =
      KFlatFixedTensor.representativeIso R P Q hp hq hpf hqf := by
  have h (X : Complexes R) :
      (DerivedCategory.quotientCompQhIso (Modules R)).hom.app X = 𝟙 _ := by
    with_unfolding_all rfl
  have hi (X : Complexes R) :
      (DerivedCategory.quotientCompQhIso (Modules R)).inv.app X = 𝟙 _ := by
    with_unfolding_all rfl
  apply Iso.ext
  dsimp only [model, CategoryTheory.tensorDescentPair, Iso.trans, Iso.symm,
    Iso.app, Functor.mapIso, Iso.prod]
  erw [hi, h P, h Q, ← CategoryTheory.prod_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  conv_lhs =>
    arg 2
    tactic => with_unfolding_all
      exact @Category.comp_id (DerivedCategory (Modules R)) _ _ _ _
  with_unfolding_all rfl


/-- The canonical resolution map extends the inverse model maps uniquely to all pairs.
Source: Stacks 06YS and 06YU (blueprint: def-pd-site-derived-tensor-resolving-data).
Proof: resolve both inputs by flat-term K-flat complexes using 06YS. The desired map is
inverse to the derived image of the two resolution maps, followed by the inverse model
map and the ordinary tensor of the resolution maps. Common resolving refinements show
independence of choices. Naturality follows by refining a pair of resolution diagrams.
Conversely naturality along the resolutions forces this formula, giving uniqueness.
-/
theorem counit_existsUnique :
    ∃! ε : ((DerivedCategory.Q (C := Modules R)).prod DerivedCategory.Q) ⋙
        siteDerivedTensorIndependentCoefficients J R ⟶
      tensor (Complexes R) ⋙ DerivedCategory.Q,
      ∀ (P Q : Complexes R)
        (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
        (hpf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
        (hqf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)),
        ε.app (P, Q) = (model R P Q hp hq hpf hqf).inv := by
  obtain ⟨m₀, _, hm₀⟩ := SheafOfModules.total_comparison.{uC, vC, r, w} R
  let m : ((DerivedCategory.Q (C := Modules R)).prod DerivedCategory.Q) ⋙
      siteDerivedTensorIndependentCoefficients J R ⟶
      tensor (Complexes R) ⋙ DerivedCategory.Q :=
    { app X := m₀.app X
      naturality X Y f := by
        have h := m₀.naturality f
        change ((siteDerivedTensorIndependentCoefficients J R).map
            (Prod.mkHom (DerivedCategory.Q.map f.1) (𝟙 (DerivedCategory.Q.obj X.2))) ≫
          (siteDerivedTensorIndependentCoefficients J R).map
            (Prod.mkHom (𝟙 (DerivedCategory.Q.obj Y.1)) (DerivedCategory.Q.map f.2))) ≫
            m₀.app Y =
          m₀.app X ≫ DerivedCategory.Q.map
            ((f.1 ▷ X.2) ≫ (Y.1 ◁ f.2)) at h
        change (siteDerivedTensorIndependentCoefficients J R).map
            (Prod.mkHom (DerivedCategory.Q.map f.1) (DerivedCategory.Q.map f.2)) ≫ m₀.app Y =
          m₀.app X ≫ DerivedCategory.Q.map (f.1 ⊗ₘ f.2)
        simpa only [← Functor.map_comp, CategoryTheory.prod_comp, Category.id_comp,
          Category.comp_id, MonoidalCategory.tensorHom_def] using h }
  have hm (P Q : Complexes R)
      (hp : P.IsKFlatIndependentCoefficients) (hq : Q.IsKFlatIndependentCoefficients)
      (hpf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (P.X n))
      (hqf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (Q.X n)) :
      m.app (P, Q) = (model R P Q hp hq hpf hqf).inv := by
    change m₀.app (P, Q) = _
    rw [hm₀ P Q hp hq hpf hqf, model_eq]
  refine ⟨m, hm, ?_⟩
  intro ε hε
  apply NatTrans.ext
  funext X
  obtain ⟨F, π, hπ, hk, hf⟩ := SheafOfModules.functorial_resolution.{uC, vC, r} R
  have := hπ X.1
  have := hπ X.2
  let f : (F.obj X.1, F.obj X.2) ⟶ X := (π.app X.1, π.app X.2)
  have hi : IsIso ((((DerivedCategory.Q (C := Modules R)).prod DerivedCategory.Q) ⋙
      siteDerivedTensorIndependentCoefficients J R).map f) := by
    change IsIso ((siteDerivedTensorIndependentCoefficients J R).map
      (Prod.mkHom (DerivedCategory.Q.map (π.app X.1))
        (DerivedCategory.Q.map (π.app X.2))))
    have hi₁ := (DerivedCategory.isIso_Q_map_iff_quasiIso (Modules R) (π.app X.1)).2 (hπ X.1)
    have hi₂ := (DerivedCategory.isIso_Q_map_iff_quasiIso (Modules R) (π.app X.2)).2 (hπ X.2)
    have : IsIso (Prod.mkHom (DerivedCategory.Q.map (π.app X.1))
        (DerivedCategory.Q.map (π.app X.2))) :=
      (CategoryTheory.isIso_prod_iff (DerivedCategory (Modules R))
        (DerivedCategory (Modules R))).2 ⟨hi₁, hi₂⟩
    infer_instance
  apply (cancel_epi ((((DerivedCategory.Q (C := Modules R)).prod DerivedCategory.Q) ⋙
    siteDerivedTensorIndependentCoefficients J R).map f)).1
  rw [ε.naturality f, m.naturality f,
    hε _ _ (hk X.1) (hk X.2) (hf X.1) (hf X.2),
    hm _ _ (hk X.1) (hk X.2) (hf X.1) (hf X.2)]


/-- The canonical all-complex resolution transformation, uniquely determined by model maps.
Source: Stacks 06YS and 06YU (blueprint: def-pd-site-derived-tensor-resolving-data). -/
def counit : ((DerivedCategory.Q (C := Modules R)).prod DerivedCategory.Q) ⋙
    siteDerivedTensorIndependentCoefficients J R ⟶
    tensor (Complexes R) ⋙ DerivedCategory.Q :=
  Classical.choose (counit_existsUnique R).exists


end SheafOfModules.SiteDerivedTensorResolvingData
