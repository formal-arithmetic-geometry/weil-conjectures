/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.Algebra.Homology.ModuleCohomologyBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.Paper.DerivedSplittingUnique
import Sheaf.RingTheory.FiniteSourceProjectiveCokernelLocalization
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Affine perfect-complex cut in degree zero

Source: Stacks Project, More on Algebra, Tag 0A1U, Lemma better-cut-complex-in-two
(blueprint: lem-pc-affine-perfect-cut-degree-zero).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace DerivedCategory

private theorem extend_map_epi {R B : Type v} [CommRing R] [CommRing B]
    (α : R →+* B) {M N : ModuleCat.{v} R} (φ : M ⟶ N) [Epi φ] :
    Epi ((ModuleCat.extendScalars α).map φ) := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  dsimp only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
    ConcreteCategory.hom_ofHom]
  let : Algebra R B := ((algebraMap B B).comp α).toAlgebra
  exact LinearMap.baseChange_surjective B ((ModuleCat.epi_iff_surjective _).mp inferInstance)

private theorem map_homologyπ {A B : Type v} [CommRing A] [CommRing B]
    (T : ShortComplex (ModuleCat.{v} B)) (G : ModuleCat.{v} B ⥤ ModuleCat.{v} A)
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G] :
    (T.map G).homologyπ ≫ (T.mapHomologyIso G).hom =
      (T.mapCyclesIso G).hom ≫ G.map T.homologyπ := by
  let h := ShortComplex.LeftHomologyData.canonical T
  rw [h.mapHomologyIso_eq G, h.mapCyclesIso_eq G]
  simp
  simpa only [← G.map_comp] using congrArg G.map h.π_comp_homologyIso_inv

private theorem cycles_epi_of_cohomologyBaseChange_epi
    {R B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hsurj : Epi (ModuleCat.cohomologyBaseChange (B := B) K 0)) :
    ∃ j : (ModuleCat.extendScalars (algebraMap R B)).obj ((K.sc 0).cycles) ⟶
        (((K.sc 0).map (ModuleCat.extendScalars (algebraMap R B))).cycles),
      Epi j ∧ j ≫ ((K.sc 0).map (ModuleCat.extendScalars (algebraMap R B))).iCycles =
        (ModuleCat.extendScalars (algebraMap R B)).map (K.sc 0).iCycles := by
  let F := ModuleCat.extendScalars (algebraMap R B)
  let G := ModuleCat.restrictScalars (algebraMap R B)
  let adj := ModuleCat.extendRestrictScalarsAdj (algebraMap R B)
  let S := K.sc 0
  let T := S.map F
  let φ := S.mapNatTrans adj.unit
  let c : S.cycles ⟶ G.obj T.cycles :=
    ShortComplex.cyclesMap φ ≫ (T.mapCyclesIso G).hom
  let j : F.obj S.cycles ⟶ T.cycles := (adj.homEquiv _ _).symm c
  have hj : j ≫ T.iCycles = F.map S.iCycles := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_right, Equiv.apply_symm_apply]
    dsimp only [c]
    rw [Category.assoc, ShortComplex.mapCyclesIso_hom_iCycles]
    erw [ShortComplex.cyclesMap_i]
    change S.iCycles ≫ adj.unit.app S.X₂ = _
    exact (adj.unit.naturality S.iCycles).symm
  have hπ : F.map S.homologyπ ≫ ModuleCat.cohomologyBaseChange (B := B) K 0 =
      j ≫ T.homologyπ := by
    apply (adj.homEquiv _ _).injective
    rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right,
      Equiv.apply_symm_apply]
    dsimp only [ModuleCat.cohomologyBaseChange]
    erw [Equiv.apply_symm_apply]
    change S.homologyπ ≫ (ShortComplex.homologyMap φ ≫ (T.mapHomologyIso G).hom) =
      c ≫ G.map T.homologyπ
    have hnat : S.homologyπ ≫ ShortComplex.homologyMap φ =
        ShortComplex.cyclesMap φ ≫ (T.map G).homologyπ := by
      simpa only [T, F, G, ShortComplex.map, Functor.comp_map, Functor.comp_obj,
        Functor.id_obj, Functor.id_map] using
        ShortComplex.homologyπ_naturality φ
    calc
      _ = (S.homologyπ ≫ ShortComplex.homologyMap φ) ≫ (T.mapHomologyIso G).hom :=
        (Category.assoc _ _ _).symm
      _ = (ShortComplex.cyclesMap φ ≫ (T.map G).homologyπ) ≫
          (T.mapHomologyIso G).hom := congrArg (fun x ↦ x ≫ _) hnat
      _ = _ := by rw [Category.assoc, map_homologyπ]; rfl
  have hto : F.map S.toCycles ≫ j = T.toCycles := by
    rw [← cancel_mono T.iCycles, Category.assoc, hj, ← F.map_comp,
      ShortComplex.toCycles_i]
    exact T.toCycles_i.symm
  let U := (ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ).map F
  let V := ShortComplex.mk T.toCycles T.homologyπ T.toCycles_comp_homologyπ
  let ψ : U ⟶ V :=
    { τ₁ := 𝟙 _
      τ₂ := j
      τ₃ := ModuleCat.cohomologyBaseChange (B := B) K 0
      comm₁₂ := by dsimp [U, V]; simpa using hto.symm
      comm₂₃ := hπ.symm }
  have he : V.Exact := V.exact_of_g_is_cokernel T.homologyIsCokernel
  have : Epi U.g := by
    change Epi (F.map S.homologyπ)
    exact extend_map_epi (algebraMap R B) S.homologyπ
  have : Epi V.g := inferInstanceAs (Epi T.homologyπ)
  have : Epi ψ.τ₁ := inferInstanceAs (Epi (𝟙 (F.obj S.X₁)))
  have : Epi ψ.τ₃ := hsurj
  have : Epi j := ShortComplex.epi_τ₂_of_exact_of_epi ψ he
  exact ⟨j, inferInstance, hj⟩

private theorem range_subtype_mono_of_cohomologyBaseChange_epi
    {R B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hsurj : Epi (ModuleCat.cohomologyBaseChange (B := B) K 0)) :
    Mono ((ModuleCat.extendScalars (algebraMap R B)).map
      (ModuleCat.ofHom (K.sc 0).g.hom.range.subtype)) := by
  let F := ModuleCat.extendScalars (algebraMap R B)
  let S := K.sc 0
  let T := S.map F
  obtain ⟨j, hjepi, hj⟩ := cycles_epi_of_cohomologyBaseChange_epi K hsurj
  let I := ModuleCat.of R S.g.hom.range
  let q : S.X₂ ⟶ I := ModuleCat.ofHom S.g.hom.rangeRestrict
  let ι : I ⟶ S.X₃ := ModuleCat.ofHom S.g.hom.range.subtype
  have hqι : q ≫ ι = S.g := rfl
  have hiq : S.iCycles ≫ q = 0 := by
    rw [← cancel_mono ι, Category.assoc, hqι, zero_comp]
    exact S.iCycles_g
  let U := (ShortComplex.mk S.iCycles q hiq).map F
  let V := ShortComplex.mk T.iCycles T.g T.iCycles_g
  let ψ : U ⟶ V :=
    { τ₁ := j
      τ₂ := 𝟙 _
      τ₃ := F.map ι
      comm₁₂ := by change j ≫ T.iCycles = F.map S.iCycles ≫ 𝟙 _; simpa using hj
      comm₂₃ := by
        change 𝟙 _ ≫ F.map S.g = F.map q ≫ F.map ι
        simpa only [Category.id_comp, ← F.map_comp] using (F.congr_map hqι).symm }
  have he : V.Exact := V.exact_of_f_is_kernel T.cyclesIsKernel
  have hq : Epi q := (ModuleCat.epi_iff_surjective _).mpr S.g.hom.surjective_rangeRestrict
  have hU : Epi U.g := by
    change Epi (F.map q)
    exact extend_map_epi (algebraMap R B) q
  have h₁ : Epi ψ.τ₁ := hjepi
  have h₂ : Mono ψ.τ₂ := inferInstanceAs (Mono (𝟙 (F.obj S.X₂)))
  exact ShortComplex.mono_of_epi_of_epi_of_mono ψ he hU h₁ h₂

private theorem tensor_baseChange_naturality
    {R B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    {M N : ModuleCat.{v} R} (φ : M ⟶ N) :
    (ModuleCat.tensorEquivExtendScalars R B N).toLinearMap.comp (φ.hom.baseChange B) =
      (((ModuleCat.extendScalars (algebraMap R B)).map φ).hom).comp
        (ModuleCat.tensorEquivExtendScalars R B M).toLinearMap := by
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, LinearMap.comp_apply] at *; rw [hx, hy]
  | tmul b m =>
    change ModuleCat.tensorEquivExtendScalars R B N
        (φ.hom.baseChange B (TensorProduct.tmul R b m)) =
      (((ModuleCat.extendScalars (algebraMap R B)).map φ).hom)
        (ModuleCat.tensorEquivExtendScalars R B M (TensorProduct.tmul R b m))
    rw [LinearMap.baseChange_tmul]
    exact (ModuleCat.ExtendScalars.map_tmul (algebraMap R B) φ b m).symm

private theorem baseChange_injective_of_mono_map
    {R B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    {M N : ModuleCat.{v} R} (φ : M ⟶ N)
    (hφ : Mono ((ModuleCat.extendScalars (algebraMap R B)).map φ)) :
    Function.Injective (φ.hom.baseChange B) := by
  let eM := ModuleCat.tensorEquivExtendScalars R B M
  let eN := ModuleCat.tensorEquivExtendScalars R B N
  have hc := tensor_baseChange_naturality (B := B) φ
  intro x y h
  apply eM.injective
  apply (ModuleCat.mono_iff_injective _).mp hφ
  change (((ModuleCat.extendScalars (algebraMap R B)).map φ).hom) (eM x) =
    (((ModuleCat.extendScalars (algebraMap R B)).map φ).hom) (eM y)
  exact (LinearMap.congr_fun hc x).symm.trans
    ((congrArg eN h).trans (LinearMap.congr_fun hc y))

private theorem projective_cokernel_extend
    {R B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    {M N : ModuleCat.{v} R} (φ : M ⟶ N)
    (hp : Module.Projective B
      (TensorProduct R B N ⧸ LinearMap.range (φ.hom.baseChange B))) :
    Module.Projective B
      (cokernel (C := ModuleCat.{v} B) ((ModuleCat.extendScalars (algebraMap R B)).map φ)) := by
  let eN := ModuleCat.tensorEquivExtendScalars R B N
  have hc := tensor_baseChange_naturality (B := B) φ
  have hr : (LinearMap.range (φ.hom.baseChange B)).map eN.toLinearMap =
      LinearMap.range (((ModuleCat.extendScalars (algebraMap R B)).map φ).hom) := by
    rw [← LinearMap.range_comp, hc, LinearMap.range_comp_of_range_eq_top _
      (ModuleCat.tensorEquivExtendScalars R B M).range]
  let e := Submodule.Quotient.equiv _ _ eN hr
  exact Module.Projective.of_equiv
    (e.trans (ModuleCat.cokernelIsoRangeQuotient _).toLinearEquiv.symm)

/-- A bounded-above finite free complex splits at zero after shrinking around a prime
where its degree-zero cohomology base-change map is surjective.
Source: Stacks Project, More on Algebra, Tag 0A1U
(blueprint: lem-pc-affine-perfect-cut-degree-zero).

Proof: The epimorphism on cohomology makes the comparison from extended cycles to
cycles of the extended complex epic, by the three lemma on boundaries, cycles and
cohomology. The four lemma on cycles, the degree-zero term and the image of its
differential then makes the image inclusion injective after residue-field extension.
The finite-source form of `lem-pc-finite-projective-cokernel-localization` makes its
cokernel projective after shrinking. This is the degree-one opcycles module, hence
the positive truncation itself is bounded finite projective in degrees `[1,b]`.
Its flat terms give the tensor bound. Apply `lem-pc-derived-splitting-unique` with
`a = 1` to the standard truncation triangle to obtain the direct-sum isomorphism. -/
theorem affine_perfect_cut_degree_zero {R : Type v} [CommRing R]
    [∀ f : R, HasDerivedCategory.{v} (ModuleCat.{v} (Localization.Away f))]
    (p : Ideal R) [p.IsPrime] (K : CochainComplex (ModuleCat.{v} R) ℤ)
    (hbounded : ∃ b : ℤ, K.IsStrictlyLE b)
    (hfree : ∀ i : ℤ, Module.Free R (K.X i) ∧ Module.Finite R (K.X i))
    (hsurj : Epi (ModuleCat.cohomologyBaseChange (B := p.ResidueField) K 0)) :
    ∃ f : R, f ∉ p ∧
      Nonempty (Q.obj ((RingTensorCohomology.extend R (Localization.Away f)).obj K) ≅
        Q.obj (((RingTensorCohomology.extend R (Localization.Away f)).obj K).truncLE 0) ⊞
        Q.obj (((RingTensorCohomology.extend R (Localization.Away f)).obj K).truncGE 1)) ∧
      (∃ (P : CochainComplex (ModuleCat.{v} (Localization.Away f)) ℤ) (b : ℤ),
        P.IsStrictlyGE 1 ∧ P.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Projective (Localization.Away f) (P.X i) ∧
          Module.Finite (Localization.Away f) (P.X i)) ∧
        Nonempty (Q.obj
          (((RingTensorCohomology.extend R (Localization.Away f)).obj K).truncGE 1) ≅
          Q.obj P)) ∧
      (Q.obj (((RingTensorCohomology.extend R (Localization.Away f)).obj K).truncGE 1)).IsPerfect ∧
      ∀ N : ModuleCat.{v} (Localization.Away f),
        (Q.obj (((RingTensorCohomology.extend R (Localization.Away f)).obj K).truncGE 1) ⊗
          (singleFunctor (ModuleCat.{v} (Localization.Away f)) 0).obj N).IsGE 1 := by
  have hlocal : ∃ f : R, f ∉ p ∧ Module.Projective (Localization.Away f)
      (((RingTensorCohomology.extend R (Localization.Away f)).obj K).opcycles 1) := by
    let d := (K.d 0 1).hom
    let I := ModuleCat.of R d.range
    let ι : I ⟶ K.X 1 := ModuleCat.ofHom d.range.subtype
    have hmono := range_subtype_mono_of_cohomologyBaseChange_epi K hsurj
    have hinj : Function.Injective (d.range.subtype.baseChange p.ResidueField) :=
      baseChange_injective_of_mono_map ι (by
        let C (i : ℤ) : Prop := Mono
          ((ModuleCat.extendScalars (algebraMap R p.ResidueField)).map
            (ModuleCat.ofHom (K.d 0 i).hom.range.subtype))
        have hm : C ((ComplexShape.up ℤ).next 0) := hmono
        have hn : (ComplexShape.up ℤ).next 0 = 1 := by simp
        exact (congrArg C hn).mp hm)
    have : Module.Finite R (K.X 0) := (hfree 0).2
    have : Module.Finite R (K.X 1) := (hfree 1).2
    have : Module.Free R (K.X 1) := (hfree 1).1
    have : Module.Finite R I := Module.Finite.range d
    have : Module.Projective R (K.X 1) := Module.Projective.of_free
    obtain ⟨f, hf, -, -, hp⟩ :=
      (Module.finiteProjectiveCokernel_residue_localization_of_finite d.range.subtype p).1 hinj
    let A := Localization.Away f
    let F := ModuleCat.extendScalars (algebraMap R A)
    let L := (RingTensorCohomology.extend R A).obj K
    have hp' : Module.Projective A (cokernel (C := ModuleCat.{v} A) (F.map ι)) :=
      projective_cokernel_extend ι hp
    let q : K.X 0 ⟶ I := ModuleCat.ofHom d.rangeRestrict
    have : Epi q := (ModuleCat.epi_iff_surjective _).mpr d.surjective_rangeRestrict
    have : Epi (F.map q) := extend_map_epi (algebraMap R A) q
    let e₁ : L.opcycles 1 ≅ cokernel (L.d 0 1) :=
      L.opcyclesIsoSc' 0 1 2 (by simp) (by simp) ≪≫ (L.sc' 0 1 2).opcyclesIsoCokernel
    let e₂ : cokernel (L.d 0 1) ≅ cokernel (F.map q ≫ F.map ι) :=
      eqToIso (by congr 1; rw [← F.map_comp]; rfl)
    let e₃ := cokernelEpiComp (F.map q) (F.map ι)
    exact ⟨f, hf, Module.Projective.of_equiv (e₁ ≪≫ e₂ ≪≫ e₃).toLinearEquiv.symm⟩
  obtain ⟨f, hf, hp⟩ := hlocal
  let L := (RingTensorCohomology.extend R (Localization.Away f)).obj K
  obtain ⟨c, hc⟩ := hbounded
  have hfreeL (i : ℤ) : Module.Free (Localization.Away f) (L.X i) ∧
      Module.Finite (Localization.Away f) (L.X i) := by
    have := (hfree i).1
    have := (hfree i).2
    let e := ModuleCat.tensorEquivExtendScalars R (Localization.Away f) (K.X i)
    exact ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩
  have hL : L.IsStrictlyLE c := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (ModuleCat.extendScalars (algebraMap R (Localization.Away f))).map_isZero
      (K.isZero_of_isStrictlyLE c i hi)
  let P := L.truncGE 1
  let b := max c 1
  have hge : P.IsStrictlyGE 1 := inferInstance
  have hle : P.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (L.isZero_of_isStrictlyLE c i (by omega)).of_iso (L.truncGEXIso 1 i (by omega))
  have hproj (i : ℤ) : Module.Projective (Localization.Away f) (P.X i) ∧
      Module.Finite (Localization.Away f) (P.X i) := by
    rcases lt_trichotomy i 1 with hi | rfl | hi
    · have := ModuleCat.isZero_iff_subsingleton.mp
        (P.isZero_of_isStrictlyGE 1 i hi)
      exact ⟨inferInstance, inferInstance⟩
    · have hfin : Module.Finite (Localization.Away f) (L.opcycles 1) := by
        have := (hfreeL 1).2
        exact Module.Finite.of_surjective (L.pOpcycles 1).hom
          ((ModuleCat.epi_iff_surjective _).mp inferInstance)
      exact ⟨Module.Projective.of_equiv (L.truncGEXIsoOpcycles 1).toLinearEquiv.symm,
        Module.Finite.equiv (L.truncGEXIsoOpcycles 1).toLinearEquiv.symm⟩
    · have := (hfreeL i).1
      have := (hfreeL i).2
      exact ⟨Module.Projective.of_equiv (L.truncGEXIso 1 i hi).toLinearEquiv.symm,
        Module.Finite.equiv (L.truncGEXIso 1 i hi).toLinearEquiv.symm⟩
  have hP : ∃ (P' : CochainComplex (ModuleCat.{v} (Localization.Away f)) ℤ) (b' : ℤ),
      P'.IsStrictlyGE 1 ∧ P'.IsStrictlyLE b' ∧
      (∀ i : ℤ, Module.Projective (Localization.Away f) (P'.X i) ∧
        Module.Finite (Localization.Away f) (P'.X i)) ∧
      Nonempty (Q.obj (L.truncGE 1) ≅ Q.obj P') :=
    ⟨P, b, hge, hle, hproj, ⟨Iso.refl _⟩⟩
  have hperf : (Q.obj (L.truncGE 1)).IsPerfect :=
    ⟨P, 1, b, hge, hle, hproj, ⟨Iso.refl _⟩⟩
  have htor : ∀ N : ModuleCat.{v} (Localization.Away f),
      (Q.obj (L.truncGE 1) ⊗ (singleFunctor _ 0).obj N).IsGE 1 := by
    intro N
    have hflat (i : ℤ) : ObjectProperty.flat (P.X i) := by
      have := (hproj i).1
      exact (ModuleCat.flat_iff_flat _).mpr inferInstance
    exact (torAmplitudeIn_Q_obj_of_flat P 1 b hflat N).1
  refine ⟨f, hf, ?_, hP, hperf, htor⟩
  let eP : Q.obj (L.truncGE 1) ≅ Q.obj P := Iso.refl _
  let hS := L.shortComplexTruncLE_shortExact 0
  let T := triangleOfSES hS
  let eC : T.obj₃ ≅ Q.obj (L.truncGE 1) :=
    asIso (Q.map (L.shortComplexTruncLEX₃ToTruncGE 0 1 (by omega)))
  have hrep : ∃ P : CochainComplex (ModuleCat.{v} (Localization.Away f)) ℤ,
      (∀ i : ℤ, Projective (P.X i)) ∧
        (∀ i : ℤ, i < 1 ∨ b < i → IsZero (P.X i)) ∧
        Nonempty (T.obj₃ ≅ Q.obj P) := by
    refine ⟨P, fun i ↦ ?_, ?_, ⟨eC ≪≫ eP⟩⟩
    · have := (hproj i).1
      infer_instance
    · intro i hi
      rcases hi with hi | hi
      · exact P.isZero_of_isStrictlyGE 1 i hi
      · exact P.isZero_of_isStrictlyLE b i hi
  have hvan : ∀ i : ℤ, 1 + 1 ≤ i →
      IsZero ((homologyFunctor (ModuleCat.{v} (Localization.Away f)) i).obj T.obj₁) := by
    intro i hi
    exact (Q.obj (L.truncLE 0)).isZero_of_isLE 0 i (by omega)
  obtain ⟨e, -, -⟩ := (derivedSplittingUnique 1 b T.obj₁ T.obj₃ hrep).2.1
    hvan T.obj₂ T rfl rfl rfl (triangleOfSES_distinguished hS)
  exact ⟨e ≪≫ biprod.mapIso (Iso.refl _) eC⟩

end DerivedCategory
