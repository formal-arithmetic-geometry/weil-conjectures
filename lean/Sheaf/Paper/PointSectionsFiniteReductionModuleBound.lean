module
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

@[expose] public section
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.longLine false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace DerivedCategory

/-- Upper boundedness of the selected second-factor derived tensor on bounded objects.
(blueprint: lem-trf-point-sections-finite-reduction-module-bound) -/
theorem isLE_derivedTensor_second_factor_obj
    {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (hC : C.IsStrictlyLE 0)
    (N : DerivedCategory (ModuleCat.{u} R))
    (hN : ∃ b : ℤ, N.IsLE b) :
    ∃ b : ℤ,
      (((Classical.choose
        (exists_derivedTensor_second_factor_functor f).2).obj C).obj N).IsLE b := by
  obtain ⟨b, hb⟩ := hN
  letI : N.IsLE b := hb
  obtain ⟨K, hK, ⟨eN⟩⟩ := N.exists_iso_Q_obj_of_isLE b
  letI : K.IsStrictlyLE b := hK
  letI := ModuleCat.hasFunctorialFlatResolution R
  obtain ⟨P, hP, π, hπ, hPflat⟩ :=
    CochainComplex.exists_quasiIso_flat_of_isStrictlyLE K b
  letI : P.IsStrictlyLE b := hP
  let B := (ModuleCat.mixedTensor f).flip.map₂CochainComplex
  obtain ⟨hfirst, hrest⟩ := exists_derivedTensor_second_factor_functor f
  let T := Classical.choose hrest
  let hrest' := Classical.choose_spec hrest
  let ε := Classical.choose hrest'
  obtain ⟨hderived, htri, hcomp, huniq, hassoc, hnat, hid, hmapcomp, hquasi⟩ :=
    Classical.choose_spec hrest'
  have hKflat : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat P b hPflat
  have hcompiso := hcomp C P hKflat
  let eT : (T.obj C).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((B.obj P).obj C) :=
    (asIso ((T.obj C).map (DerivedCategory.Q.map π))).symm ≪≫
      asIso ((ε C).app P)
  letI : C.IsStrictlyLE 0 := hC
  have hBP : (B.obj P).obj C |>.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [IsZero.iff_id_eq_zero]
    refine HomologicalComplex.mapBifunctor.hom_ext (fun p q hpq ↦ ?_)
    have hpq' : p + q = i := hpq
    by_cases hp : b < p
    · apply IsZero.eq_of_src
      exact ((ModuleCat.mixedTensor f).flip.map_isZero
        (CochainComplex.isZero_of_isStrictlyLE P b p hp)).obj (C.X q)
    · have hq : 0 < q := by omega
      apply IsZero.eq_of_src
      exact ((ModuleCat.mixedTensor f).flip.obj (P.X p)).map_isZero
        (CochainComplex.isZero_of_isStrictlyLE C 0 q hq)
  have hB' : ((B.obj P).obj C).IsLE b :=
    (CochainComplex.isLE_iff _ b).2 (fun i hi ↦
      HomologicalComplex.ExactAt.of_isZero
        ((CochainComplex.isStrictlyLE_iff _ b).1 hBP i hi))
  have hQ : (DerivedCategory.Q.obj ((B.obj P).obj C)).IsLE b := by
    rw [DerivedCategory.isLE_Q_obj_iff]
    exact hB'
  have hT : (T.obj C).obj N |>.IsLE b := by
    letI : (DerivedCategory.Q.obj ((B.obj P).obj C)).IsLE b := hQ
    exact DerivedCategory.TStructure.t.isLE_of_iso
      ((T.obj C).mapIso eN ≪≫ eT).symm b
  have heq :
      (Classical.choose (exists_derivedTensor_second_factor_functor f).2).obj C = T.obj C := by
    simp [T]
  exact ⟨b, heq ▸ hT⟩
end DerivedCategory
