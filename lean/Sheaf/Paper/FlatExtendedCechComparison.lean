/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.Paper.ExtendedLocalizationCech
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.QuasiIso
import Sheaf.Paper.FlatLocalizationKoszulHomotopy
import Sheaf.Paper.FlatLocalizationKoszulCohomologyComparison
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # Flat comparison of extended localization Čech complexes

Source: Stacks Project, Algebraization, Tag 099H
(blueprint: lem-weil-pbc-flat-extended-cech-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace SheafOfModules

open CategoryTheory.Limits

private theorem homologyMap_natTrans_isIso
    {D E : Type*} [Category D] [Abelian D] [Category E] [Abelian E]
    (F G : D ⥤ E) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesHomology] [G.PreservesHomology]
    (η : F ⟶ G) (K : CochainComplex D ℤ) (q : ℤ)
    (hη : IsIso (η.app (K.homology q))) :
    IsIso (HomologicalComplex.homologyMap
      ((η.mapHomologicalComplex (.up ℤ)).app K) q) := by
  let S := K.sc q
  let m := ShortComplex.homologyMap (S.mapNatTrans η)
  have heq := NatTrans.app_homology η S
  have hcomp : IsIso ((S.mapHomologyIso F).inv ≫ m ≫ (S.mapHomologyIso G).hom) := by
    rw [← heq]
    exact hη
  have : IsIso (m ≫ (S.mapHomologyIso G).hom) :=
    IsIso.of_isIso_comp_left (S.mapHomologyIso F).inv _
  exact IsIso.of_isIso_comp_right m (S.mapHomologyIso G).hom

private theorem scalar_apply
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u})
    (s : (unit (LocalizationCech.rings R)).sections) (X : Cᵒᵖ) (a : R.obj.obj X) :
    (LocalizationCech.scalar R s).val.app X a = a * (show R.obj.obj X from s.val X) := by
  change ((unit (LocalizationCech.rings R)).val.unitHomEquiv.symm s).app X a = _
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_unitMap
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (s : (unit (LocalizationCech.rings R)).sections) :
    LocalizationCech.scalar R s ≫ LocalizationCech.unitMap φ =
      LocalizationCech.unitMap φ ≫
        (LocalizationCech.restriction φ).map
          (LocalizationCech.scalar B (LocalizationCech.mapSection φ s)) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change R.obj.obj X at a
  have h (Y : Cᵒᵖ) (b : R.obj.obj Y) :
      (LocalizationCech.unitMap φ).val.app Y b = (φ.hom.app Y) b :=
    (LocalizationCech.unitMap_existsUnique φ).choose_spec.1 Y b
  change (LocalizationCech.unitMap φ).val.app X
      ((LocalizationCech.scalar R s).val.app X a) =
    (LocalizationCech.scalar B (LocalizationCech.mapSection φ s)).val.app X
      ((LocalizationCech.unitMap φ).val.app X a)
  rw [scalar_apply, h, h, scalar_apply]
  exact (φ.hom.app X).hom.map_mul a (show R.obj.obj X from s.val X)

private theorem subsetScalar_unitMap
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (LocalizationCech.rings R)).sections) (s : Finset (Fin r)) :
    LocalizationCech.subsetScalar R r f s ≫ LocalizationCech.unitMap φ =
      LocalizationCech.unitMap φ ≫ (LocalizationCech.restriction φ).map
        (LocalizationCech.subsetScalar B r (LocalizationCech.mapSection φ ∘ f) s) := by
  classical
  unfold LocalizationCech.subsetScalar
  induction s.sort (· ≤ ·) with
  | nil => simp
  | cons j l ih =>
      dsimp only [List.foldr_cons]
      rw [Category.assoc, ih, ← Category.assoc, scalar_unitMap, Category.assoc,
        ← Functor.map_comp]
      rfl

set_option backward.isDefEq.respectTransparency false in
private theorem comparisonStage_transition
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (LocalizationCech.rings R)).sections) (n : ℕ) :
    LocalizationCech.transition R r f n ≫ LocalizationCech.comparisonStage φ r f (n + 1) =
      LocalizationCech.comparisonStage φ r f n ≫
        ((LocalizationCech.restriction φ).mapHomologicalComplex (.up ℤ)).map
          (LocalizationCech.transition B r (LocalizationCech.mapSection φ ∘ f) n) := by
  apply HomologicalComplex.Hom.ext
  funext q
  change LocalizationCech.transitionTerm R r f q ≫
      LocalizationCech.comparisonTerm φ r q =
    LocalizationCech.comparisonTerm φ r q ≫ (LocalizationCech.restriction φ).map
      (LocalizationCech.transitionTerm B r (LocalizationCech.mapSection φ ∘ f) q)
  apply Sigma.hom_ext
  intro s
  simp only [LocalizationCech.transitionTerm, LocalizationCech.comparisonTerm,
    Sigma.ι_desc_assoc, Category.assoc, ← Functor.map_comp]
  rw [Sigma.ι_desc, Functor.map_comp, ← Category.assoc, subsetScalar_unitMap]
  rw [Category.assoc]
  congr 1
  conv_rhs => rw [← Functor.map_comp, Sigma.ι_desc]
  exact (Functor.map_comp _ _ _).symm

private theorem restriction_preservesColimits
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    PreservesColimitsOfSize.{u, u} (LocalizationCech.restriction φ) := by
  have h (D : Sheaf J RingCat.{u}) : PreservesColimitsOfSize.{u, u} (toSheaf.{u} D) := by
    constructor
    intro K _
    exact ((moduleSheaves_colimits_forgetful D).2.2.2.2.2 K).2.1
  have := h (LocalizationCech.rings R)
  have := h (LocalizationCech.rings B)
  have : ReflectsColimitsOfSize.{u, u} (toSheaf.{u} (LocalizationCech.rings R)) :=
    reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{u, u}
      (LocalizationCech.restriction φ ⋙ toSheaf.{u} (LocalizationCech.rings R)) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u} (toSheaf.{u} (LocalizationCech.rings B)))
  exact preservesColimits_of_reflects_of_preserves _ (toSheaf.{u} (LocalizationCech.rings R))

private theorem comparisonStage_isIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (LocalizationCech.rings R)).sections) (n : ℕ)
    [IsIso (LocalizationCech.unitMap φ)] :
    IsIso (LocalizationCech.comparisonStage φ r f n) := by
  have := restriction_preservesColimits φ
  have : PreservesColimitsOfSize.{0, 0} (LocalizationCech.restriction φ) :=
    preservesSmallestColimits_of_preservesColimits _
  have h (q : ℤ) : IsIso (LocalizationCech.comparisonTerm φ r q) := by
    have heq : LocalizationCech.comparisonTerm φ r q =
        Limits.Sigma.map (fun _ : LocalizationCech.Indices r q ↦ LocalizationCech.unitMap φ) ≫
          (PreservesCoproduct.iso (LocalizationCech.restriction φ)
            (fun _ : LocalizationCech.Indices r q ↦ unit (LocalizationCech.rings B))).inv := by
      apply Sigma.hom_ext
      intro s
      simp [LocalizationCech.comparisonTerm]
    rw [heq]
    infer_instance
  have (q : ℤ) : IsIso ((LocalizationCech.comparisonStage φ r f n).f q) := h q
  exact HomologicalComplex.Hom.isIso_of_components _

private theorem comparison_quasiIso_of_stages
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (LocalizationCech.rings R)).sections)
    (hstage : ∀ n, QuasiIso (LocalizationCech.comparisonStage φ r f n)) :
    QuasiIso (LocalizationCech.comparison φ r f) := by
  let A := CategoryTheory.ringedSiteModules.{u} (LocalizationCech.rings R)
  let T := (LocalizationCech.restriction φ).mapHomologicalComplex (.up ℤ)
  let D := LocalizationCech.diagram R r f
  let E := LocalizationCech.diagram B r (LocalizationCech.mapSection φ ∘ f)
  have : AB5OfSize.{0, 0} (Sheaf J AddCommGrpCat.{u}) :=
    AB5OfSize_shrink.{0, 0, u, u} _
  have : HasExactColimitsOfShape ℕ A :=
    HasExactColimitsOfShape.domain_of_functor ℕ (toSheaf.{u} (LocalizationCech.rings R))
  have := restriction_preservesColimits φ
  have : PreservesColimitsOfSize.{0, 0} (LocalizationCech.restriction φ) :=
    preservesSmallestColimits_of_preservesColimits _
  let α : D ⟶ E ⋙ T := NatTrans.ofSequence
    (LocalizationCech.comparisonStage φ r f) (fun n ↦ by
      simpa only [D, E, T, LocalizationCech.diagram, Functor.comp_map,
        Functor.ofSequence_map_homOfLE_succ] using comparisonStage_transition φ r f n)
  apply MorphismProperty.colimitsOfShape_le (W := HomologicalComplex.quasiIso A (.up ℤ))
    (J := ℕ) _
  exact
    (MorphismProperty.colimitsOfShape.mk' (W := HomologicalComplex.quasiIso A (.up ℤ))
      _ _ _ _ (colimit.isColimit D)
      (isColimitOfPreserves T (colimit.isColimit E)) α (fun n ↦ hstage n)
      (LocalizationCech.comparison φ r f) (fun n ↦ by
        change colimit.ι D n ≫ colimit.desc D (LocalizationCech.comparisonCocone φ r f) = _
        rw [colimit.ι_desc]
        rfl))

private theorem unitMap_isIso_of_empty_quotient
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)
    (f : Fin 0 → (unit (LocalizationCech.rings R)).sections)
    (hquot : IsIso (LocalizationCech.quotientComparison φ 0 f)) :
    IsIso (LocalizationCech.unitMap φ) := by
  have hrow (D : Sheaf J CommRingCat.{u})
      (g : Fin 0 → (unit (LocalizationCech.rings D)).sections) :
      LocalizationCech.idealRow D 0 g = 0 := by
    apply Sigma.hom_ext
    intro i
    exact Fin.elim0 i
  have hpiR : IsIso (cokernel.π (LocalizationCech.idealRow R 0 f)) := by
    rw [hrow]
    infer_instance
  have hpiB : IsIso (cokernel.π
      (LocalizationCech.idealRow B 0 (LocalizationCech.mapSection φ ∘ f))) := by
    rw [hrow]
    infer_instance
  have heq : cokernel.π (LocalizationCech.idealRow R 0 f) ≫
      LocalizationCech.quotientComparison φ 0 f =
    LocalizationCech.unitMap φ ≫ (LocalizationCech.restriction φ).map
      (cokernel.π (LocalizationCech.idealRow B 0 (LocalizationCech.mapSection φ ∘ f))) :=
    cokernel.π_desc _ _ _
  have : IsIso (LocalizationCech.unitMap φ ≫ (LocalizationCech.restriction φ).map
      (cokernel.π (LocalizationCech.idealRow B 0 (LocalizationCech.mapSection φ ∘ f)))) := by
    rw [← heq]
    infer_instance
  exact IsIso.of_isIso_comp_right (LocalizationCech.unitMap φ)
    ((LocalizationCech.restriction φ).map
      (cokernel.π (LocalizationCech.idealRow B 0 (LocalizationCech.mapSection φ ∘ f))))

private theorem term_isZero_of_not_range
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (r : ℕ) (q : ℤ)
    (hq : ¬ (0 ≤ q ∧ q ≤ (r : ℤ))) : IsZero (LocalizationCech.term R r q) := by
  classical
  apply (IsZero.iff_id_eq_zero _).2
  apply Sigma.hom_ext
  intro s
  have hs := s.property
  have hc : s.val.card ≤ r := by
    simpa using Finset.card_le_card (Finset.subset_univ s.val)
  exfalso
  apply hq
  omega

private theorem comparisonStage_homology_isIso_of_not_range
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (LocalizationCech.rings R)).sections) (n : ℕ) (q : ℤ)
    (hq : ¬ (0 ≤ q ∧ q ≤ (r : ℤ))) :
    IsIso (HomologicalComplex.homologyMap (LocalizationCech.comparisonStage φ r f n) q) := by
  have hs : IsZero ((LocalizationCech.koszul R r f n).sc q).X₂ :=
    term_isZero_of_not_range R r q hq
  have ht : IsZero ((((LocalizationCech.restriction φ).mapHomologicalComplex (.up ℤ)).obj
      (LocalizationCech.koszul B r (LocalizationCech.mapSection φ ∘ f) n)).sc q).X₂ := by
    exact (LocalizationCech.restriction φ).map_isZero
      (term_isZero_of_not_range B r q hq)
  exact (ShortComplex.isZero_homology_of_isZero_X₂ _ hs).isIso
    (ShortComplex.isZero_homology_of_isZero_X₂ _ ht) _

/-- A flat coefficient extension unchanged modulo the generated ideal identifies
the extended alternating localization complexes by the canonical termwise map.
Source: Stacks Project, Tag 099H
(blueprint: lem-weil-pbc-flat-extended-cech-comparison).

Proof:
1. Localization commutes with scalar extension: a/g^k tensor b maps to
φ(a)b/φ(g)^k, with inverse b/φ(g)^k mapping to (1/g^k) tensor b. Sheafify
these formulas; they commute with localization maps and the degree-zero augmentation.
2. Use the explicit positive-power cochain Koszul complexes of Tag 0913:
in degree q the basis is the q-element subsets I, and insertion of j has
coefficient (-1)^a(j,I) f_j^(n+1). Paired insertions prove d squared is zero.
Multiplication by the subset product defines the transition to the next exponent.
3. The fraction cocone a e_I maps to a/(product_I f_i)^(n+1). Every fraction
occurs and equality of fractions is eventual equality in this sequential system.
Consequently its colimit is exactly the extended alternating localization complex;
these identifications commute with the coefficient comparison and augmentations.
4. Remove j from I with sign (-1)^a(j,I), or send the basis vector to zero
when j is absent. This homotopy satisfies d h_j + h_j d = f_j^(n+1) id.
Hence every cohomology sheaf is killed by each f_j^(n+1), and by the ideal
power r*n+1 for r positive. When r=0 the zero ideal itself suffices.
5. If the ideal kills a module sheaf, tensoring factors through the quotient
ring sheaf, so the quotient isomorphism identifies its canonical scalar-extension
map with the identity. Induct on a positive annihilating ideal power, using the
short exact sequence with submodule I^k F and quotient F/I^k F and exact tensoring.
The outer comparison maps are isomorphisms, hence so is the middle one.
6. Flatness and the exact-functor cohomology comparison identify the cohomology
of each scalar-extended Koszul complex with the scalar extension of its cohomology.
The comparison is the canonical map from step 5, hence an isomorphism in every degree.
7. The exact faithful forgetful functor to abelian sheaves preserves filtered
colimits, which are exact on any small site. Thus filtered colimits of module
sheaves are exact and commute with cohomology. Taking the colimit of the stage
quasi-isomorphisms gives the asserted quasi-isomorphism. For r=0 the quotient
hypothesis is precisely that φ is an isomorphism and the complexes are O[0] and B[0]. -/
theorem flat_extendedLocalizationCech_comparison_quasiIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R B : Sheaf J CommRingCat.{u}) (φ : R ⟶ B) (r : ℕ)
    (f : Fin r → (unit (LocalizationCech.rings R)).sections)
    (hflat : IsFlat ((LocalizationCech.restriction φ).obj
      (unit (LocalizationCech.rings B))))
    (hquot : IsIso (LocalizationCech.quotientComparison φ r f)) :
    QuasiIso (LocalizationCech.comparison φ r f) := by
  by_cases hr : r = 0
  · subst r
    have := unitMap_isIso_of_empty_quotient φ f hquot
    apply comparison_quasiIso_of_stages φ 0 f
    intro n
    have := comparisonStage_isIso φ 0 f n
    infer_instance
  · apply comparison_quasiIso_of_stages φ r f
    intro n
    rw [quasiIso_iff]
    intro q
    rw [quasiIsoAt_iff_isIso_homologyMap]
    by_cases hq : 0 ≤ q ∧ q ≤ (r : ℤ)
    · let := monoidalCategory R
      let A := CategoryTheory.ringedSiteModules.{u} (LocalizationCech.rings R)
      let P := (LocalizationCech.restriction φ).obj (unit (LocalizationCech.rings B))
      let F := tensorRight P
      let η : 𝟭 A ⟶ F :=
        (rightUnitorNatIso A).inv ≫ (tensoringRight A).map (LocalizationCech.unitMap φ)
      have : PreservesFiniteLimits F := hflat.1
      have : PreservesFiniteColimits F := hflat.2
      obtain ⟨hη, e, he⟩ := LocalizationCech.flat_koszul_tensor_comparison_data
        R B φ r f n q (Nat.pos_of_ne_zero hr) hq hflat hquot
        (LocalizationCech.koszul_ideal_power_annihilates_homology R r f n q)
      have : IsIso (HomologicalComplex.homologyMap
          ((η.mapHomologicalComplex (.up ℤ)).app (LocalizationCech.koszul R r f n)) q) :=
        homologyMap_natTrans_isIso (𝟭 A) F η (LocalizationCech.koszul R r f n) q hη
      rw [he, HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp]
      infer_instance
    · exact comparisonStage_homology_isIso_of_not_range φ r f n q hq

end SheafOfModules
