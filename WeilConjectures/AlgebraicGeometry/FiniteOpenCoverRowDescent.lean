/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteOpenCoverRowComparison
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Descent at the start of the ordered relative-image Čech row

Source: Stacks Project, Tag 03AZ, row calculation; Tags 03FB and 03FC for
injective module presheaves, and Tags 01FJ–01FM for the ordered comparison.
(blueprint: new-finite-cover-row-descent)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

variable {X Y : Scheme.{u}} (B : Type (u + 1)) [CommRing B]

/-- The section augmentation is monic for an arbitrary coefficient sheaf.
Source: Stacks Project, Tag 03AN. Project equality of augmentations onto the
singleton corresponding to each cover member. Transport its intersection to
the member itself. The proved covering family and sheaf separatedness then
identify the two maps into the section module of the total test object.
(blueprint: new-finite-cover-row-descent) -/
theorem finiteCoverSectionAugmentation_mono
    (f : X ⟶ Y) {m : ℕ} (U : Fin m → X.Opens) (hU : iSup U = ⊤)
    (T : Y.Etale) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    Mono (finiteCoverSectionAugmentation B f T M U) := by
  let F := finiteCoverSectionPresheaf B f T M
  constructor
  intro E s t h
  apply M.property.hom_ext_ofArrows
    (fun i ↦ finiteCoverTestObjectHom f T (le_top : U i ≤ ⊤))
    (finiteCoverTestObject_cover f T U hU)
  intro i
  let a : Fin 1 ↪o Fin m := OrderEmbedding.ofStrictMono (fun _ ↦ i) (by
    intro j k hjk
    have hjk' : j = k := Subsingleton.elim _ _
    subst k
    exact False.elim (lt_irrefl _ hjk))
  have ha : (⨅ k, U (a k)) = U i := by simp [finiteCoverIntersection, a]
  have he := h =≫ biproduct.π (fun b : Fin 1 ↪o Fin m ↦
    F.obj (op ((⨅ k, U (b k))))) a
  dsimp only [finiteCoverSectionAugmentation, finiteCoverIntersection, F] at he
  simp only [Category.assoc, biproduct.lift_π] at he
  have he' := he =≫ F.map (homOfLE (le_of_eq ha.symm)).op
  change s ≫ F.map (homOfLE (le_top : U i ≤ ⊤)).op =
    t ≫ F.map (homOfLE (le_top : U i ≤ ⊤)).op
  dsimp only [F] at he' ⊢
  simpa only [Category.assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp] using he'

private def finiteCoverSingleton {m : ℕ} (i : Fin m) : Fin 1 ↪o Fin m :=
  OrderEmbedding.ofStrictMono (fun _ ↦ i) (by
    intro j k hjk
    have hjk' : j = k := Subsingleton.elim _ _
    subst k
    exact False.elim (lt_irrefl _ hjk))

private def finiteCoverPair {m : ℕ} (i j : Fin m) (hij : i < j) : Fin 2 ↪o Fin m :=
  OrderEmbedding.ofStrictMono ![i, j] (by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all)

private def finiteCoverRankOne {A : ModuleCat.{u + 1} B} (x : A) :
    ModuleCat.of B B ⟶ A :=
  ModuleCat.ofHom
    { toFun := fun b ↦ b • x
      map_add' := fun b c ↦ add_smul b c x
      map_smul' := fun b c ↦ (smul_smul b c x).symm }

private theorem finiteCoverBiproduct_element_ext {I : Type} (A : I → ModuleCat.{u + 1} B)
    [HasBiproduct A] (x y : (⨁ A : ModuleCat.{u + 1} B))
    (h : ∀ i, biproduct.π A i x = biproduct.π A i y) :
    x = y := by
  have he : finiteCoverRankOne B x = finiteCoverRankOne B y := by
    apply biproduct.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change biproduct.π A i (b • x) = biproduct.π A i (b • y)
    simpa only [map_smul] using congrArg (fun z ↦ b • z) (h i)
  have he' := ConcreteCategory.congr_hom he (1 : B)
  change (1 : B) • x = (1 : B) • y at he'
  simpa only [one_smul] using he'

private theorem finiteCoverMap_comp_apply
    (F : X.Opensᵒᵖ ⥤ ModuleCat.{u + 1} B) {V W Z : X.Opens}
    (hVW : V ≤ W) (hWZ : W ≤ Z) (x : F.obj (op Z)) :
    F.map (homOfLE hVW).op (F.map (homOfLE hWZ).op x) =
      F.map (homOfLE (hVW.trans hWZ)).op x := by
  have he := ConcreteCategory.congr_hom
    (F.map_comp (homOfLE hWZ).op (homOfLE hVW).op) x
  simpa only [← op_comp, homOfLE_comp, ModuleCat.comp_apply] using he.symm

/-- Degree-zero descent for the actual ordered section complex.

Source: Stacks Project, Tag 03AN, applied to the inverse-image open cover;
Cohomology of Sheaves, Tags 01FJ and 01FK for the ordered coordinates.
(blueprint: new-finite-cover-row-descent)

Proof: Fix T and M. The objects T times_Y U_i cover T times_Y X, by
base change of the open cover. Sections on the singleton intersection are
identified with sections on T times_Y U_i by the unique equality of the
underlying singleton open intersection with U_i. In degree one the named
alternating differential has two terms. Project a zero cocycle onto the
increasing pair (i,j): the equation says that the sections on U_i and U_j
have equal restrictions to T times_Y (U_i intersect U_j). For equal indices
this equality is automatic; reversing a pair reverses the same equality.
The universal property of the pullback intersection then implies
compatibility along every pair of etale arrows with the same composite
into T times_Y X. The sheaf gluing axiom gives a section on the total
object restricting to the given family. Projection onto each singleton
coordinate proves that its augmentation is the original zero cocycle.
Uniqueness in the same sheaf condition makes the augmentation injective.
The elementwise exactness and monomorphism criteria for ModuleCat give
the two assertions. The top-open presentation of the total object causes
only transport along its canonical isomorphism with X times_Y T.
No injectivity of M is used. For a one-member cover the pair term is zero
and gluing is an isomorphism. Empty intersections have zero sections, and
on the empty scheme all the section modules are zero. -/
theorem finite_open_cover_section_descent
    (f : X ⟶ Y) (m : ℕ) (hm : 1 ≤ m) (U : Fin m → X.Opens) (hU : iSup U = ⊤)
    (T : Y.Etale) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
    (ShortComplex.mk (finiteCoverSectionAugmentation B f T M U)
      (finiteCoverSectionDifferential B f T M U 0)
      (finiteCoverSectionAugmentation_d B f T M U)).Exact := by
  classical
  let F := finiteCoverSectionPresheaf B f T M
  let A := fun a : Fin 1 ↪o Fin m ↦ F.obj (op ((⨅ k, U (a k))))
  have hsingle (i : Fin m) : (⨅ k, U (finiteCoverSingleton i k)) = U i := by
    simp [finiteCoverIntersection, finiteCoverSingleton]
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change (⨁ A : ModuleCat.{u + 1} B) at x
  change finiteCoverSectionDifferential B f T M U 0 x = 0 at hx
  let s (i : Fin m) : F.obj (op (U i)) :=
    F.map (homOfLE (le_of_eq (hsingle i).symm)).op
      (biproduct.π A (finiteCoverSingleton i) x)
  have hordered (a : Fin 2 ↪o Fin m) :
      F.map (homOfLE (iInf_le (fun k ↦ U (a k)) 0)).op (s (a 0)) =
        F.map (homOfLE (iInf_le (fun k ↦ U (a k)) 1)).op (s (a 1)) := by
    have he := congrArg (fun z ↦ biproduct.π
      (fun b : Fin 2 ↪o Fin m ↦
        (finiteCoverSectionPresheaf B f T M).obj (op ((⨅ k, U (b k))))) a z) hx
    rw [finiteCoverSectionDifferential_π_apply, map_zero] at he
    let v (j : Fin 2) : F.obj (op (⨅ k, U (a k))) :=
      F.map (homOfLE (le_iInf fun k ↦
        iInf_le (fun l ↦ U (a l)) (j.succAbove k))).op
        (biproduct.π A (j.succAboveOrderEmb.trans a) x)
    have he' : (∑ j : Fin 2, (-1 : ℤ) ^ (j : ℕ) • v j) = 0 := he
    have hh : v 1 = v 0 := by
      have ht : v 0 - v 1 = 0 := by
        simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
          one_zsmul, neg_one_zsmul, sub_eq_add_neg] using he'
      exact (sub_eq_zero.mp ht).symm
    have h0 : (0 : Fin 2).succAboveOrderEmb.trans a = finiteCoverSingleton (a 1) := by
      ext k
      fin_cases k
      rfl
    have h1 : (1 : Fin 2).succAboveOrderEmb.trans a = finiteCoverSingleton (a 0) := by
      ext k
      fin_cases k
      rfl
    let r (b : Fin 1 ↪o Fin m) : F.obj (op (⨅ k, U (a k))) :=
      if h : (⨅ k, U (a k)) ≤ (⨅ k, U (b k)) then
        F.map (homOfLE h).op (biproduct.π A b x) else 0
    have hr (j : Fin 2) : r (j.succAboveOrderEmb.trans a) = v j := by
      exact dif_pos (le_iInf fun k ↦ iInf_le (fun l ↦ U (a l)) (j.succAbove k))
    have hh' : r ((1 : Fin 2).succAboveOrderEmb.trans a) =
        r ((0 : Fin 2).succAboveOrderEmb.trans a) :=
      (hr 1).trans (hh.trans (hr 0).symm)
    rw [h1, h0] at hh'
    have hsub (i : Fin 2) : (⨅ k, U (a k)) ≤
        (⨅ k, U (finiteCoverSingleton (a i) k)) :=
      (iInf_le (fun k ↦ U (a k)) i).trans (le_of_eq (hsingle (a i)).symm)
    simp only [r, dif_pos (hsub 0), dif_pos (hsub 1)] at hh'
    dsimp only [s]
    simp only [finiteCoverMap_comp_apply B F]
    exact hh'

  have hs (i j : Fin m) :
      F.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (s i) =
        F.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (s j) := by
    have hl (i j : Fin m) (hij : i < j) :
        F.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (s i) =
          F.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (s j) := by
      let a := finiteCoverPair i j hij
      have ha : (⨅ k, U (a k)) = U i ⊓ U j := by
        apply le_antisymm
        · exact le_inf (iInf_le (fun k ↦ U (a k)) 0)
            (iInf_le (fun k ↦ U (a k)) 1)
        · apply le_iInf
          intro k
          fin_cases k
          · exact inf_le_left
          · exact inf_le_right
      have he := congrArg (fun z ↦ F.map (homOfLE (le_of_eq ha.symm)).op z) (hordered a)
      simpa only [finiteCoverMap_comp_apply B F, a, finiteCoverPair,
        OrderEmbedding.coe_ofStrictMono, Matrix.cons_val_zero, Matrix.cons_val_one]
        using he
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact hl i j hij
    · congr 2 <;> exact Subsingleton.elim _ _
    · have he := congrArg (fun z ↦
          F.map (homOfLE (le_of_eq (inf_comm (U i) (U j)))).op z) (hl j i hji).symm
      simpa only [finiteCoverMap_comp_apply B F] using he
  obtain ⟨t, ht⟩ := finiteCoverSection_glue B f T U hU M s hs
  refine ⟨t, ?_⟩
  apply finiteCoverBiproduct_element_ext B A
  intro a
  have ha : finiteCoverSingleton (a 0) = a := by
    ext k
    fin_cases k
    rfl
  let t' : F.obj (op ⊤) := t
  have ht' : F.map (homOfLE (le_top : U (a 0) ≤ ⊤)).op t' = s (a 0) := ht (a 0)
  have he := congrArg (fun z ↦ F.map
    (homOfLE (le_of_eq (hsingle (a 0)))).op z) ht'
  simp only [s, finiteCoverMap_comp_apply B F] at he
  have hid : homOfLE (le_of_eq (hsingle (a 0))) ≫
      homOfLE (le_of_eq (hsingle (a 0)).symm) = 𝟙 _ := Subsingleton.elim _ _
  simp only [homOfLE_comp] at hid
  rw [congrArg Quiver.Hom.op hid, op_id, F.map_id, ModuleCat.id_apply] at he
  let Φ (b : Fin 1 ↪o Fin m) : Prop :=
    F.map (homOfLE (le_top : (⨅ k, U (b k)) ≤ ⊤)).op t' = biproduct.π A b x
  have he' : Φ a := Eq.mp (congrArg Φ ha) he
  change biproduct.π A a (finiteCoverSectionAugmentation B f T M U t) =
    biproduct.π A a x
  have hp := ConcreteCategory.congr_hom (biproduct.lift_π
    (fun b : Fin 1 ↪o Fin m ↦ F.map
      (homOfLE (le_top : (⨅ k, U (b k)) ≤ ⊤)).op) a) t
  exact hp.trans he'

/-- Descent of section rows implies descent of the named sheaf-valued row.
Source: Stacks Project, Tag 03AZ. The proved comparison of short complexes
transfers monicity and exactness on sections. The inclusion of sheaves into
presheaves reflects monomorphisms. Exact sheafification transfers pointwise
exactness to sheaf exactness, and evaluations detect exactness and monicity of
natural transformations. No choice of comparison data remains.
(blueprint: new-finite-cover-row-descent) -/
theorem finite_open_cover_row_descent
    (f : X ⟶ Y) (m : ℕ) (hm : 1 ≤ m) (U : Fin m → X.Opens) (hU : iSup U = ⊤)
    (J : CochainComplex
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B) ⥤
        Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) ℕ)
    (data : finiteOpenCoverOrderedData B f m U J) :
    (∀ q, Mono ((finiteOpenCoverRowAugmentation B f m U J data.hB data.hId
      data.hComp data.hComm data.hSq data.hAug).f q)) ∧
    (∀ q, (ShortComplex.mk
      ((finiteOpenCoverRowAugmentation B f m U J data.hB data.hId data.hComp
        data.hComm data.hSq data.hAug).f q)
      (((finiteOpenCoverResolutionDoubleComplex B f m U J data.hB data.hComm data.hSq).d
        0 1).f q)
      (by rw [← HomologicalComplex.comp_f, data.hEps, HomologicalComplex.zero_f])).Exact) := by
  have h (q : ℕ) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
      (T : Y.Etale) :
      ((finiteCoverAugmentedRow B f U J data q).map
        (finiteCoverRowEvaluation B T M)).Exact ∧
      Mono (((finiteCoverAugmentedRow B f U J data q).map
        (finiteCoverRowEvaluation B T M)).f) := by
    have hmono := finiteCoverSectionAugmentation_mono B f U hU T ((J.X q).obj M)
    have he := finite_open_cover_section_descent B f m hm U hU T ((J.X q).obj M)
    exact (ShortComplex.exact_and_mono_f_iff_of_iso
      (finiteCoverAugmentedRowSectionsIso B f U J data T M q)).2 ⟨he, hmono⟩
  constructor
  · intro q
    let α := (finiteOpenCoverRowAugmentation B f m U J data.hB data.hId
      data.hComp data.hComm data.hSq data.hAug).f q
    change Mono α
    haveI : ∀ M, Mono (α.app M) := by
      intro M
      apply (sheafToPresheaf Y.smallEtaleTopology
        (ModuleCat.{u + 1} B)).mono_of_mono_map
      haveI : ∀ T, Mono (((sheafToPresheaf Y.smallEtaleTopology
          (ModuleCat.{u + 1} B)).map (α.app M)).app T) :=
        fun T ↦ (h q M T.unop).2
      exact NatTrans.mono_of_mono_app _
    exact NatTrans.mono_of_mono_app _
  · intro q
    change (finiteCoverAugmentedRow B f U J data q).Exact
    rw [ShortComplex.exact_iff_evaluation]
    intro M
    apply finiteCoverSheafExact_of_sections
    intro T
    exact (h q M T).1

end AlgebraicGeometry.Etale
