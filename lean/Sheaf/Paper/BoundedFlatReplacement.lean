/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Data.ZMod.Basic
import WeilConjectures.Algebra.Homology.CyclePullbackResolution
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Homology.Refinements

/-!
# Functorial bounded-above flat replacement on the small etale site

Source: Weil conjectures blueprint, `sec-smooth-purity/sk-prop-sf-kunneth-ordinary`,
`lem-kun-bounded-flat-replacement`; Stacks Project, Tag 05T7 (1), with sectionwise
free covers and exact sheafification (Tags 00WJ and 03ET).
(blueprint: lem-kun-bounded-flat-replacement).

The full subcategory defined by `IsStrictlyLE N` retains every chain map between
complexes vanishing above `N`. A natural augmentation expresses compatibility of the
replacement maps with all these chain maps. Surjectivity means epimorphy of module
sheaves, not surjectivity on sections over every object of the site.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

section FlatCover

universe v w r
variable {C : Type w} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

open CategoryTheory.Functor MonoidalCategory SheafOfModules

set_option hygiene false in
local notation "O" => (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
set_option hygiene false in
local notation "A" => SheafOfModules.{r} O

attribute [local instance] isMonoidal_W_independentCoefficients
  monoidalCategory symmetricCategory

private theorem tensorPreadditive_boundedFlat : MonoidalPreadditive A := by
  have (M : A) : (tensorLeft M).Additive := tensorLeft_additive_independent R M
  have (M : A) : (tensorRight M).Additive :=
    Functor.additive_of_iso (F := tensorLeft M)
      (BraidedCategory.tensorLeftIsoTensorRight M)
  exact
    { whiskerLeft_zero := fun {X Y Z} ↦ (tensorLeft X).map_zero Y Z
      zero_whiskerRight := fun {X Y Z} ↦ (tensorRight X).map_zero Y Z
      whiskerLeft_add := fun {X Y Z} f g ↦ (tensorLeft X).map_add (f := f) (g := g)
      add_whiskerRight := fun {X Y Z} f g ↦ (tensorRight X).map_add (f := f) (g := g) }

-- This is the free-presheaf cover used in KFlatResolutionIndependentCoefficients.
-- Its construction needs colimit preservation of tensor, rather than a chosen internal Hom.
private noncomputable def tensorSheafificationIso_boundedFlat
    (F : PresheafOfModules.{r} (O).obj) :
    tensorRight ((PresheafOfModules.sheafification.{r} (𝟙 (O).obj)).obj F) ≅
      (SheafOfModules.forget.{r} O ⋙
        PresheafOfModules.restrictScalars (𝟙 (O).obj)) ⋙ tensorRight F ⋙
        PresheafOfModules.sheafification.{r} (𝟙 (O).obj) := by
  let a := PresheafOfModules.sheafification.{r} (𝟙 (O).obj)
  let c := asIso (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 (O).obj)).counit
  exact (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight c.symm _ ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (Functor.Monoidal.commTensorRight a F)

private theorem existsFlatCover_boundedFlat :
    ∃ (T : A ⥤ A) (π : T ⟶ 𝟭 A),
      (∀ M : A, ObjectProperty.flat (T.obj M)) ∧ (∀ M : A, Epi (π.app M)) := by
  let a := PresheafOfModules.sheafification.{r} (𝟙 (O).obj)
  let V := SheafOfModules.forget.{r} O ⋙ PresheafOfModules.restrictScalars (𝟙 (O).obj)
  let U := PresheafOfModules.toPresheaf.{r} (O).obj ⋙
    (Functor.whiskeringRight _ _ _).obj (CategoryTheory.forget Ab)
  let G := U ⋙ PresheafOfModules.free.{r} (O).obj
  let τ : G ⟶ 𝟭 _ :=
    { app := fun M ↦ PresheafOfModules.freeObjDesc (𝟙 _)
      naturality := by
        intro M M' f
        ext X : 1
        apply ModuleCat.free_hom_ext
        intro x
        change ModuleCat.freeDesc (↾fun x : M'.obj X ↦ x)
            ((ModuleCat.free ((O).obj.obj X)).map (↾fun x ↦ f.app X x)
              (ModuleCat.freeMk x)) =
          f.app X (ModuleCat.freeDesc (↾fun x : M.obj X ↦ x) (ModuleCat.freeMk x))
        rw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        rfl }
  have hτ (M : PresheafOfModules.{r} (O).obj) : Epi (τ.app M) := by
    apply PresheafOfModules.epi_of_surjective
    intro X x
    refine ⟨ModuleCat.freeMk x, ?_⟩
    exact ModuleCat.freeDesc_apply _ _
  let T := V ⋙ G ⋙ a
  let π : T ⟶ 𝟭 _ :=
    Functor.whiskerLeft V (Functor.whiskerRight τ a) ≫
      (PresheafOfModules.sheafificationAdjunction.{r} (𝟙 (O).obj)).counit
  have hT (M : A) : ObjectProperty.flat (T.obj M) := by
    have hflat : PreservesFiniteLimits (tensorRight (G.obj (V.obj M))) := by
      constructor
      intro K hK hfin
      constructor
      intro D
      constructor
      intro c hc
      have hflatX (X : Cᵒᵖ) : Module.Flat (R.obj.obj X) ((G.obj (V.obj M)).obj X) := by
        change Module.Flat (R.obj.obj X) (_ →₀ R.obj.obj X)
        infer_instance
      have hpres (X : Cᵒᵖ) : PreservesFiniteLimits
          (tensorRight
            (show ModuleCat (R.obj.obj X) from (G.obj (V.obj M)).obj X)) := by
        have := hflatX X
        infer_instance
      exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦
        isLimitOfPreserves (tensorRight
          (show ModuleCat (R.obj.obj X) from (G.obj (V.obj M)).obj X))
            (isLimitOfPreserves (PresheafOfModules.evaluation _ X) hc))⟩
    have := hflat
    have : PreservesLimitsOfSize.{0, 0} V :=
      (PresheafOfModules.sheafificationAdjunction.{r}
        (𝟙 (O).obj)).rightAdjoint_preservesLimits
    have : PreservesFiniteLimits (tensorRight (T.obj M)) :=
      preservesFiniteLimits_of_natIso (tensorSheafificationIso_boundedFlat R (G.obj (V.obj M))).symm
    have : PreservesFiniteLimits (tensorLeft (T.obj M)) :=
      preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (T.obj M)).symm
    have (X : A) : PreservesColimitsOfSize.{0, 0} (tensorLeft X) := by
      have := tensorLeft_preservesColimits_independentCoefficients R X
      exact preservesColimitsOfSize_shrink (tensorLeft X)
    have : PreservesFiniteColimits (tensorRight (T.obj M)) :=
      preservesFiniteColimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (T.obj M))
    exact ⟨(exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩,
      (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩⟩
  refine ⟨T, π, hT, ?_⟩
  intro M
  have := hτ (V.obj M)
  dsimp [π]
  infer_instance

end FlatCover

/-- At every fixed upper bound, complexes of modules over the constant ring sheaf
admit a functorial flat replacement and a termwise epimorphic quasi-isomorphism.
The output has the same upper bound; functor laws are those of `Φ`, and compatibility
with the augmentation is naturality of `ε`.
Source: blueprint `lem-kun-bounded-flat-replacement`; Stacks Project, Tag 05T7 (1).
(blueprint: lem-kun-bounded-flat-replacement).

Proof:
1. Form the canonical sectionwise free cover of the underlying presheaf of modules
   over the given sheaf of rings. Its evaluation is natural and sectionwise epic.
   Sheafification and its counit give a functorial epic cover of module sheaves.
2. Free section modules are flat. Evaluation jointly reflects limits, so their
   presheaf tensor functor preserves finite limits. The monoidal sheafification
   comparison transfers this property to the sheaf cover. Tensor preserves colimits
   by `tensorLeft_preservesColimits_independentCoefficients`, proving flatness.
   These constructions retain the distinct site and coefficient universes.
3. Zero objects are flat. Apply `exists_functorial_cyclePullback_construction`
   to this cover and categorical flatness. It produces a functor, natural
   augmentation, flat terms, the upper bound, and epic lifts of compatible pairs
   consisting of a next-degree cycle and a current-degree target element.
4. Two compatible-pair lifts prove termwise epimorphy: lift the cycle d(y) using
   (0,d(y)), then lift y together with that cycle lift. Compose the epic refinements.
5. Apply Mathlib's homology-map refinement criteria. A source cycle whose image is
   a boundary lifts through a pair in the preceding degree, proving monicity.
   A target cycle lifts through (0,y), proving epimorphy. Thus the augmentation is
   a quasi-isomorphism in every degree.
6. Restrict along the inclusion from `IsStrictlyLE N` to explicit vanishing above N.
   This changes no underlying object or map. Translate the upper bound with
   `isStrictlyLE_iff` and categorical flatness with `siteSheafTensorRightIso`.
   The functor and natural augmentation supply the required functoriality.
7. Specialize to `ULift (ZMod n.natAbs)` for the final assertion, for every integer n. -/
theorem exists_functorial_bounded_flat_replacement
    (T : Scheme.{u}) (Λ : Type (u + 1)) [CommRing Λ] (N : ℤ) :
    ∃ (Φ : ObjectProperty.FullSubcategory
        (fun K : CochainComplex (SheafOfModules.{u + 1}
          ((sheafCompose T.smallEtaleTopology
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
                (CommRingCat.of Λ)))) ℤ ↦ K.IsStrictlyLE N) ⥤
        CochainComplex (SheafOfModules.{u + 1}
          ((sheafCompose T.smallEtaleTopology
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
              ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
                (CommRingCat.of Λ)))) ℤ)
      (ε : Φ ⟶ ObjectProperty.ι _),
      ∀ F, (Φ.obj F).IsStrictlyLE N ∧
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (J := T.smallEtaleTopology)
          (R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of Λ)) ((Φ.obj F).X i)) ∧
        QuasiIso (ε.app F) ∧ (∀ i : ℤ, Epi ((ε.app F).f i)) := by
  let R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
    (CommRingCat.of Λ)
  let A := SheafOfModules.{u + 1}
    ((sheafCompose T.smallEtaleTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.symmetricCategory R
  let := tensorPreadditive_boundedFlat R
  obtain ⟨B, π, hB, hπ⟩ := existsFlatCover_boundedFlat R
  have hzero (M : A) (hM : IsZero M) : ObjectProperty.flat M :=
    ObjectProperty.flat_of_isZero hM
  obtain ⟨Q, ε, hQ⟩ := CochainComplex.exists_functorial_cyclePullback_construction
    ObjectProperty.flat hzero B π hB hπ N
  have hgood (F) :
      (∀ i : ℤ, ObjectProperty.flat ((Q.obj F).X i)) ∧
      (∀ i : ℤ, N < i → IsZero ((Q.obj F).X i)) ∧
      QuasiIso (ε.app F) ∧ (∀ i : ℤ, Epi ((ε.app F).f i)) := by
    have h := hQ F
    refine ⟨h.1, h.2.1, ?_, ?_⟩
    · rw [quasiIso_iff]
      intro i
      rw [quasiIsoAt_iff_isIso_homologyMap, isIso_iff_mono_and_epi]
      constructor
      · rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements
          (ε.app F) (i - 1) i (i + 1) (by simp) (by simp)]
        intro D x hx y hy
        have hlift := h.2.2 (i - 1)
        rw [show i - 1 + 1 = i by omega] at hlift
        obtain ⟨D', p, hp, z, _, hz⟩ := hlift D x y hx hy
        exact ⟨D', p, hp, z, hz.symm⟩
      · rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements
          (ε.app F) (i - 1) i (i + 1) (by simp) (by simp)]
        intro D y hy
        obtain ⟨D', p, hp, z, hz, hd⟩ :=
          h.2.2 i D 0 y (by simp) (by simpa using hy.symm)
        exact ⟨D', p, hp, z, by simpa using hd, 0, by simpa using hz.symm⟩
    · intro i
      rw [epi_iff_surjective_up_to_refinements]
      intro D y
      obtain ⟨D₁, p₁, hp₁, x₁, hx₁, hd₁⟩ :=
        h.2.2 (i + 1) D 0 (y ≫ F.obj.d i (i + 1)) (by simp) (by simp)
      have hx : x₁ ≫ (ε.app F).f (i + 1) =
          (p₁ ≫ y) ≫ F.obj.d i (i + 1) := by
        simpa only [Category.assoc] using hx₁
      obtain ⟨D₂, p₂, hp₂, x₂, hx₂, _⟩ :=
        h.2.2 i D₁ x₁ (p₁ ≫ y) (by simpa using hd₁) hx
      exact ⟨D₂, p₂ ≫ p₁, inferInstance, x₂, by simpa [Category.assoc] using hx₂.symm⟩
  let P : ObjectProperty (CochainComplex A ℤ) :=
    fun K ↦ ∀ i : ℤ, N < i → IsZero (K.X i)
  let P' : ObjectProperty (CochainComplex A ℤ) := fun K ↦ K.IsStrictlyLE N
  let I : P'.FullSubcategory ⥤ P.FullSubcategory :=
    ObjectProperty.ιOfLE (fun K hK ↦ (K.isStrictlyLE_iff N).1 hK)
  let Φ := I ⋙ Q
  let ε' : Φ ⟶ P'.ι :=
    { app := fun F ↦ ε.app (I.obj F)
      naturality := fun F G f ↦ ε.naturality (I.map f) }
  refine ⟨Φ, ε', ?_⟩
  intro F
  have h := hgood (I.obj F)
  refine ⟨((Φ.obj F).isStrictlyLE_iff N).2 h.2.1, ?_, h.2.2.1, h.2.2.2⟩
  intro i
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R ((Φ.obj F).X i)).symm (h.1 i).2

/-- Every bounded-above complex of Z/nZ-module sheaves has a bounded-above flat
replacement, for every integer n, including zero and negative n. The coefficient
ring is `ZMod n.natAbs`, the canonical presentation of Z/(n); `ULift` only places
this ring in the site's coefficient universe.
Source: blueprint `lem-kun-bounded-flat-replacement`, final assertion.
(blueprint: lem-kun-bounded-flat-replacement).

Proof: specialize exists_functorial_bounded_flat_replacement to the commutative
ring `ULift (ZMod n.natAbs)` and the supplied bound N, evaluate its augmentation
at F, and retain the bound, flatness and quasi-isomorphism (step 7 of the node).
There is no invertibility, finiteness or properness assumption. -/
theorem exists_bounded_flat_replacement_zmod
    (T : Scheme.{u}) (n : ℤ) (N : ℤ)
    (F : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose T.smallEtaleTopology
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1} (ZMod n.natAbs)))))) ℤ)
    [F.IsStrictlyLE N] :
    ∃ (P : CochainComplex (SheafOfModules.{u + 1}
        ((sheafCompose T.smallEtaleTopology
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
              (CommRingCat.of (ULift.{u + 1} (ZMod n.natAbs)))))) ℤ)
      (q : P ⟶ F), P.IsStrictlyLE N ∧
        (∀ i : ℤ, SheafOfModules.IsFlatOnSite
          (J := T.smallEtaleTopology)
          (R := (constantSheaf T.smallEtaleTopology CommRingCat.{u + 1}).obj
            (CommRingCat.of (ULift.{u + 1} (ZMod n.natAbs)))) (P.X i)) ∧ QuasiIso q := by
  obtain ⟨Φ, ε, hΦ⟩ := exists_functorial_bounded_flat_replacement
    T (ULift.{u + 1} (ZMod n.natAbs)) N
  let F' := ObjectProperty.FullSubcategory.mk (obj := F) (P := fun K ↦ K.IsStrictlyLE N)
    (inferInstance : F.IsStrictlyLE N)
  exact ⟨Φ.obj F', ε.app F', (hΦ F').1, (hΦ F').2.1, (hΦ F').2.2.1⟩

end AlgebraicGeometry.Scheme
