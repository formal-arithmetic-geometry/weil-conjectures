/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Ext


public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNormalization
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.SchemeModulesEnoughInjectives
import WeilConjectures.AlgebraicGeometry.AbelianReplacementSectionHomotopies

/-! # The standard-source abelian Ext section calculation

## References

* [Stacks Project, Tag 01FB](https://stacks.math.columbia.edu/tag/01FB)
* [Stacks Project, Tag 01F7](https://stacks.math.columbia.edu/tag/01F7)
* [Stacks Project, Tag 013P](https://stacks.math.columbia.edu/tag/013P)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 06XR](https://stacks.math.columbia.edu/tag/06XR)
-/

@[expose] public section
universe u v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution


/-- A concrete augmentation lift into a complex of injectives. First extend the
augmentation by injectivity, then descend and extend successively using exactness.
 No existence theorem supplies the data. -/
def sectionAugmentationLift {C : Type u} [Category.{v} C] [Abelian C] {G : C}
    (J : InjectiveResolution G) (K : CochainComplex C ℕ)
    (hK : ∀ n : ℕ, Injective (K.X n)) (γ : G ⟶ K.X 0)
    (hγ : γ ≫ K.d 0 1 = 0) : J.cocomplex ⟶ K := by
  let : ∀ n : ℕ, Injective (K.X n) := hK
  let g₀ : J.cocomplex.X 0 ⟶ K.X 0 := Injective.factorThru γ (J.ι.f 0)
  have hg₀ : J.ι.f 0 ≫ g₀ = γ := Injective.comp_factorThru _ _
  let g₁ := J.exact₀.descToInjective (g₀ ≫ K.d 0 1) (by
    rw [← Category.assoc, hg₀, hγ])
  have hg₁ : J.cocomplex.d 0 1 ≫ g₁ = g₀ ≫ K.d 0 1 :=
    J.exact₀.comp_descToInjective _ _
  exact CochainComplex.mkHom J.cocomplex K g₀ g₁ hg₁.symm
    (fun n ⟨g, g', w⟩ ↦
      ⟨(J.exact_succ n).descToInjective (g' ≫ K.d (n + 1) (n + 2)) (by
          rw [← Category.assoc, ← w, Category.assoc, K.d_comp_d, comp_zero]),
        ((J.exact_succ n).comp_descToInjective _ _).symm⟩)

/-- The concrete lift extends its specified augmentation. -/
theorem sectionAugmentationLift_comm {C : Type u} [Category.{v} C] [Abelian C] {G : C}
    (J : InjectiveResolution G) (K : CochainComplex C ℕ)
    (hK : ∀ n : ℕ, Injective (K.X n)) (γ : G ⟶ K.X 0)
    (hγ : γ ≫ K.d 0 1 = 0) :
    J.ι.f 0 ≫ (sectionAugmentationLift J K hK γ hγ).f 0 = γ := by
  exact Injective.comp_factorThru _ _

attribute [local instance] enoughInjectives

/-- The augmentation into an injective replacement of the pushed-forward resolution. -/
def sectionEdgeAugmentation {X Y : Scheme.{u}} (f : X ⟶ Y) {F : X.Modules}
    (I : InjectiveResolution F) (K : CochainComplex Y.Modules ℕ)
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K) :
    (pushforward f).obj F ⟶ K.X 0 :=
  (pushforward f).map (I.ι.f 0) ≫ l.f 0

/-- The augmentation is a cycle by the chain-map equation and the resolution equation. -/
theorem sectionEdgeAugmentation_cycle {X Y : Scheme.{u}} (f : X ⟶ Y) {F : X.Modules}
    (I : InjectiveResolution F) (K : CochainComplex Y.Modules ℕ)
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K) :
    sectionEdgeAugmentation f I K l ≫ K.d 0 1 = 0 := by
  dsimp only [sectionEdgeAugmentation]
  rw [Category.assoc, l.comm]
  change (pushforward f).map (I.ι.f 0) ≫
    (pushforward f).map (I.cocomplex.d 0 1) ≫ l.f 1 = 0
  rw [← Functor.map_comp_assoc, I.ι_f_zero_comp_complex_d, Functor.map_zero, zero_comp]

/-- The explicit lift with standard source resolution; neither an arbitrary source
resolution nor an arbitrary augmentation lift is an argument. -/
def standardSectionEdgeLift {X Y : Scheme.{u}} (f : X ⟶ Y) {F : X.Modules}
    (I : InjectiveResolution F) (K : CochainComplex Y.Modules ℕ)
    (hK : ∀ n : ℕ, Injective (K.X n))
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K) :
    (injectiveResolution ((pushforward f).obj F)).cocomplex ⟶ K :=
  sectionAugmentationLift _ K hK (sectionEdgeAugmentation f I K l)
    (sectionEdgeAugmentation_cycle f I K l)

/-- The map on abelian Ext cohomology induced by inverse image and the counit. -/
def standardSectionExtHom {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ) :
    AddCommGrpCat.of (H ((pushforward f).obj F) p) ⟶ AddCommGrpCat.of (H F p) :=
  AddCommGrpCat.ofHom ((Sheaf.H.map (coeff f (𝟙 ((pushforward f).obj F))) p).comp
    (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj F)) p))

/-- The standard-source calculation of the inverse-image/counit Ext map. -/
theorem standard_abelian_ext_section_diagram {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : X.Modules} (I : InjectiveResolution F) (K : CochainComplex Y.Modules ℕ)
    (hK : ∀ n : ℕ, Injective (K.X n))
    (l : ((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶ K)
    (hl : QuasiIso l)
    (a : ((moduleSections X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ≅
      ((moduleSections Y).mapHomologicalComplex (.up ℕ)).obj
        (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex))
    (ha : ∀ n : ℕ, a.inv.f n = (presheaf (I.cocomplex.X n)).map
      (eqToHom (by simp) : (⊤ : X.Opens) ⟶ f ⁻¹ᵁ (⊤ : Y.Opens)).op) (p : ℕ) :
    (abelianResolutionIso Y (injectiveResolution ((pushforward f).obj F)) p).hom ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p).map
          (((moduleSections Y).mapHomologicalComplex (.up ℕ)).map
            (standardSectionEdgeLift f I K hK l)) =
      standardSectionExtHom f F p ≫
        (abelianResolutionIso X I p).hom ≫
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p).map
          (a.hom ≫ ((moduleSections Y).mapHomologicalComplex (.up ℕ)).map l) := by
  let J := injectiveResolution ((pushforward f).obj F)
  let β := standardSectionEdgeLift f I K hK l
  let Γ := (moduleSections Y).mapHomologicalComplex (.up ℕ)
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) p
  have hβ : J.ι.f 0 ≫ β.f 0 = (pushforward f).map (I.ι.f 0) ≫ l.f 0 :=
    sectionAugmentationLift_comm _ _ _ _ _
  obtain ⟨q, hq, ⟨h₁⟩, ⟨h₂⟩⟩ :=
    abelian_replacement_section_homotopies f I J K hK l hl β hβ a ha
  have : QuasiIso q := hq
  have h₁' : H.map (Γ.map β) ≫ H.map q = H.map (counitSectionMap f F J) := by
    simpa only [H, Functor.map_comp, HomologicalComplex.homologyFunctor_map,
      HomologicalComplex.homologyMap_comp] using
      h₁.homologyMap_eq p
  have h₂' : H.map (a.hom ≫ Γ.map l) ≫ H.map q =
      H.map (((abelianSections X).mapHomologicalComplex (.up ℕ)).map
        (forgottenResolutionMap X I)) := by
    simpa only [H, Functor.map_comp, HomologicalComplex.homologyFunctor_map,
      HomologicalComplex.homologyMap_comp] using
      h₂.homologyMap_eq p
  have : IsIso (H.map q) := by
    change IsIso (HomologicalComplex.homologyMap q p)
    infer_instance
  apply (cancel_mono (H.map q)).1
  change ((abelianResolutionIso Y J p).hom ≫ H.map (Γ.map β)) ≫ H.map q =
    (standardSectionExtHom f F p ≫ (abelianResolutionIso X I p).hom ≫
      H.map (a.hom ≫ Γ.map l)) ≫ H.map q
  rw [Category.assoc, h₁', Category.assoc, Category.assoc, h₂']
  ext x
  exact abelian_counit_resolution_calculation f F J I p x

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
