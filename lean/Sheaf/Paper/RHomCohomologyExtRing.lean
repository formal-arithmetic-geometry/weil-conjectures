/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Sheaf.Algebra.Homology.KFlatTensorQuasiIso
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import WeilConjectures.Algebra.Homology.NormalizedHomComplexGlobalCochains
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt

/-! # Ring-valued cohomology of derived internal Hom

Source: Stacks Project, More on Algebra, Tag 0A64, equation equation-h0-RHom.
(blueprint: lem-sc-rhom-cohomology-ext-ring)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u w

open CategoryTheory Opposite

namespace CategoryTheory

private abbrev ring (A : Type u) [CommRing A] :=
  (sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
    (CochainComplex.onePointRingSheaf A)

private abbrev Mod (A : Type u) [CommRing A] := SheafOfModules.{u} (ring A)

private noncomputable abbrev ev (A : Type u) [CommRing A] : Mod A ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation (ring A) (op (Discrete.mk PUnit.unit))

private instance (A : Type u) [CommRing A] : (ev A).Additive where
  map_add := by intros; rfl

private noncomputable def const (A : Type u) [CommRing A] : ModuleCat.{u} A ⥤ Mod A where
  obj M := ⟨(PresheafOfModules.constFunctor {pt := RingCat.of A, ι := 𝟙 _}).obj M,
    Presheaf.isSheaf_bot _⟩
  map f := ⟨(PresheafOfModules.constFunctor {pt := RingCat.of A, ι := 𝟙 _}).map f⟩

private noncomputable def component (A : Type u) [CommRing A]
    (M : Mod A) (U : (Discrete PUnit.{u + 1})ᵒᵖ) :
    M.val.obj U ≅ (((ev A) ⋙ const A).obj M).val.obj U := by
  rcases U with ⟨⟨⟨⟩⟩⟩
  exact Iso.refl _

set_option backward.isDefEq.respectTransparency false in
private noncomputable def unitIso (A : Type u) [CommRing A] :
    𝟭 (Mod A) ≅ ev A ⋙ const A := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let i := PresheafOfModules.isoMk (component A M) (by
      intro U V f
      rcases U with ⟨⟨⟨⟩⟩⟩
      rcases V with ⟨⟨⟨⟩⟩⟩
      rw [show f = 𝟙 _ from Subsingleton.elim _ _]
      ext x
      simp)
    exact
      { hom := ⟨i.hom⟩
        inv := ⟨i.inv⟩
        hom_inv_id := SheafOfModules.hom_ext i.hom_inv_id
        inv_hom_id := SheafOfModules.hom_ext i.inv_hom_id }
  · intro M N f
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    rcases U with ⟨⟨⟨⟩⟩⟩
    rfl

private noncomputable def pointEquivalence (A : Type u) [CommRing A] :
    Mod A ≌ ModuleCat.{u} A where
  functor := ev A
  inverse := const A
  unitIso := unitIso A
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  functor_unitIso_comp M := by
    change ((unitIso A).hom.app M).val.app _ ≫ 𝟙 _ = 𝟙 _
    rfl

private instance (A : Type u) [CommRing A] : (ev A).IsEquivalence :=
  (pointEquivalence A).isEquivalence_functor

private noncomputable def sectionEquiv (A : Type u) [CommRing A] (M : Mod A) :
    (ev A).obj M ≃ M.sections where
  toFun x := M.val.sectionsMk (fun U ↦ by
    rcases U with ⟨⟨⟨⟩⟩⟩
    exact x) (by
      intro U V f
      rcases U with ⟨⟨⟨⟩⟩⟩
      rcases V with ⟨⟨⟨⟩⟩⟩
      rw [show f = 𝟙 _ from Subsingleton.elim _ _]
      simp)
  invFun s := s.val (op (Discrete.mk PUnit.unit))
  left_inv _ := rfl
  right_inv s := by
    apply Subtype.ext
    funext U
    rcases U with ⟨⟨⟨⟩⟩⟩
    rfl

private noncomputable def unitEquiv (A : Type u) [CommRing A] (M : Mod A) :
    (SheafOfModules.unit (ring A) ⟶ M) ≃+ (ev A).obj M where
  toEquiv := M.unitHomEquiv.trans (sectionEquiv A M).symm
  map_add' _ _ := rfl

private noncomputable def homEquiv (A : Type u) [CommRing A] (M N : Mod A) :
    (M ⟶ N) ≃+ ((ev A).obj M ⟶ (ev A).obj N) where
  toEquiv := Equiv.ofBijective (ev A).map
    ⟨Functor.map_injective _, Functor.map_surjective _⟩
  map_add' _ _ := rfl

private theorem homEquiv_apply (A : Type u) [CommRing A] {M N : Mod A} (f : M ⟶ N) :
    homEquiv A M N f = (ev A).map f := rfl

private noncomputable instance pointLinear (A : Type u) [CommRing A] : Linear A (Mod A) where
  homModule M N := (homEquiv A M N).module A
  smul_comp M N P r f g := by
    apply (homEquiv A M P).injective
    simp only [homEquiv_apply, Functor.map_comp]
    change ((homEquiv A M N) ((homEquiv A M N).symm (r • (ev A).map f))) ≫
      (ev A).map g = (homEquiv A M P) ((homEquiv A M P).symm
        (r • ((ev A).map f ≫ (ev A).map g)))
    simp
  comp_smul M N P f r g := by
    apply (homEquiv A M P).injective
    simp only [homEquiv_apply, Functor.map_comp]
    change (ev A).map f ≫
      ((homEquiv A N P) ((homEquiv A N P).symm (r • (ev A).map g))) =
      (homEquiv A M P) ((homEquiv A M P).symm
        (r • ((ev A).map f ≫ (ev A).map g)))
    simp

private instance pointEvaluationLinear (A : Type u) [CommRing A] : (ev A).Linear A where
  map_smul := by
    intro M N r f
    exact (homEquiv A M N).apply_symm_apply _

private theorem unitEquiv_smul (A : Type u) [CommRing A] (M : Mod A)
    (r : A) (f : SheafOfModules.unit (ring A) ⟶ M) :
    unitEquiv A M (r • f) = r • unitEquiv A M f := by
  change (ev A).map (r • f) (1 : A) = r • (ev A).map f (1 : A)
  rw [Functor.map_smul]
  rfl

private theorem factor_smul (A : Type u) [CommRing A] (M N : Mod A)
    (r : A) (f : SheafOfModules.unit (ring A) ⟶ SheafOfModules.homObj
      (R := CochainComplex.onePointRingSheaf A) M N) :
    normalizedHomFactorEquiv M N (r • f) = r • normalizedHomFactorEquiv M N f := by
  apply (homEquiv A M N).injective
  simp only [homEquiv_apply, Functor.map_smul]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((((ev A).map (r • f)) (1 : A)).app (op (Over.mk (𝟙 _)))) x =
    r • ((((ev A).map f (1 : A)).app (op (Over.mk (𝟙 _)))) x)
  rw [Functor.map_smul]
  rfl

set_option maxHeartbeats 600000 in
-- Scalar compatibility compares the chosen product projections with the transferred action.
open CochainComplex HomComplex in
private noncomputable def globalCochains (A : Type u) [CommRing A]
    (K L : CochainComplex (Mod A) ℤ) (n : ℤ) :
    (ev A).obj ((homComplex (R := CochainComplex.onePointRingSheaf A) K L).X n) ≃ₗ[A]
      Cochain K L n where
  __ := (unitEquiv A _).symm.trans
    (normalizedHomGlobalCochains (CochainComplex.onePointRingSheaf A) K L n)
  map_smul' r x := by
    have hu : (unitEquiv A _).symm (r • x) = r • (unitEquiv A _).symm x := by
      apply (unitEquiv A _).injective
      rw [AddEquiv.apply_symm_apply, unitEquiv_smul, AddEquiv.apply_symm_apply]
    change normalizedHomGlobalCochains (CochainComplex.onePointRingSheaf A) K L n
      ((unitEquiv A _).symm (r • x)) = _
    rw [hu]
    apply Cochain.ext
    intro p q hpq
    simp only [normalizedHomGlobalCochains_v]
    change normalizedHomFactorEquiv (K.X p) (L.X q)
      ((r • (unitEquiv A _).symm x) ≫ normalizedHomProjection K L n p q hpq) =
        r • normalizedHomFactorEquiv (K.X p) (L.X q)
          ((unitEquiv A _).symm x ≫ normalizedHomProjection K L n p q hpq)
    rw [Linear.smul_comp, factor_smul]

open CochainComplex HomComplex Limits in
private noncomputable def linearHomComplex
    {D : Type (u + 1)} [Category.{u} D] [Preadditive D]
    (A : Type u) [CommRing A] [Linear A D] (K L : CochainComplex D ℤ) :
    CochainComplex (ModuleCat.{u} A) ℤ where
  X n := ModuleCat.of A (Cochain K L n)
  d n m := ModuleCat.ofHom (δ_hom A K L n m)
  shape n m h := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext (δ_shape n m h)
  d_comp_d' n m k _ _ := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext (δ_δ n m k)

open CochainComplex HomComplex in
private theorem cocycleHom_smul
    {D : Type (u + 1)} [Category.{u} D] [Preadditive D]
    (A : Type u) [CommRing A] [Linear A D]
    {K L : CochainComplex D ℤ} {n : ℤ} (r : A) (z : Cocycle K L n) :
    Cocycle.equivHomShift.symm (r • z) = r • Cocycle.equivHomShift.symm z := by
  ext p
  simp [Cocycle.equivHomShift_symm_apply, Cocycle.homOf, Cocycle.rightShift,
    Cochain.rightShift_smul, Cochain.smul_v]

open CochainComplex HomComplex in
private noncomputable def cocyclesToExt
    {D : Type (u + 1)} [Category.{u} D] [Abelian D] [HasExt.{u} D]
    (A : Type u) [CommRing A] [Linear A D]
    (M N : D) (I : InjectiveResolution N) (n : ℕ) :
    Cocycle ((singleFunctor D 0).obj M) I.cochainComplex n →ₗ[A] Abelian.Ext M N n where
  toFun z := I.extEquivCohomologyClass.symm (CohomologyClass.mk z)
  map_add' z t := by simp
  map_smul' r z := by
    let := HasDerivedCategory.standard D
    apply Abelian.Ext.ext
    rw [Abelian.Ext.smul_hom,
      I.extEquivCohomologyClass_symm_mk_hom,
      I.extEquivCohomologyClass_symm_mk_hom, cocycleHom_smul A]
    simp [ShiftedHom.map, ShiftedHom.comp, ShiftedHom.mk₀, Functor.map_smul]

open CochainComplex HomComplex Limits in
private noncomputable def linearHomologyData
    {D : Type (u + 1)} [Category.{u} D] [Abelian D] [HasExt.{u} D]
    (A : Type u) [CommRing A] [Linear A D]
    (M N : D) (I : InjectiveResolution N) (n : ℕ) :
    ShortComplex.LeftHomologyData
      ((linearHomComplex A ((singleFunctor D 0).obj M) I.cochainComplex).sc (n : ℤ)) := by
  let K := (singleFunctor D 0).obj M
  let L := I.cochainComplex
  let C := linearHomComplex A K L
  let i : ModuleCat.of A (Cocycle K L n) ⟶ C.X n := ModuleCat.ofHom
    { toFun := fun z ↦ z.1
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hi : IsLimit (KernelFork.ofι (f := (C.sc (n : ℤ)).g) i (by
      ext z
      exact z.δ_eq_zero _)) := by
    apply ModuleCat.isLimitKernelFork
    · intro z
      change δ (n : ℤ) ((ComplexShape.up ℤ).next n) z = 0 ↔ _
      constructor
      · intro hz
        exact ⟨⟨z, by
          rw [Cocycle.mem_iff (n : ℤ) ((ComplexShape.up ℤ).next n) (by simp)]
          exact hz⟩, rfl⟩
      · rintro ⟨z, rfl⟩
        exact z.δ_eq_zero _
    · intro z t h
      exact Subtype.ext h
  let π := ModuleCat.ofHom (cocyclesToExt A M N I n)
  have hexact : Function.Exact
      (hi.lift (KernelFork.ofι (C.sc (n : ℤ)).f (C.sc (n : ℤ)).zero)).hom π.hom := by
    intro z
    change I.extEquivCohomologyClass.symm (CohomologyClass.mk z) = 0 ↔ _
    rw [← I.extEquivCohomologyClass_symm_zero, Equiv.symm_apply_eq,
      Equiv.apply_symm_apply, CohomologyClass.mk_eq_zero_iff]
    rw [mem_coboundaries_iff z ((ComplexShape.up ℤ).prev n) (by simp)]
    constructor
    · rintro ⟨b, hb⟩
      refine ⟨b, ?_⟩
      apply Subtype.ext
      have hf := ConcreteCategory.congr_hom
        (Fork.IsLimit.lift_ι hi (t := KernelFork.ofι (C.sc (n : ℤ)).f
          (C.sc (n : ℤ)).zero)) b
      exact hf.trans hb
    · rintro ⟨b, hb⟩
      have hf := ConcreteCategory.congr_hom
        (Fork.IsLimit.lift_ι hi (t := KernelFork.ofι (C.sc (n : ℤ)).f
          (C.sc (n : ℤ)).zero)) b
      exact ⟨b, hf.symm.trans (congrArg Subtype.val hb)⟩
  exact
    { K := ModuleCat.of A (Cocycle K L n)
      H := ModuleCat.of A (Abelian.Ext M N n)
      i := i
      π := π
      wi := by ext z; exact z.δ_eq_zero _
      hi := hi
      wπ := by ext z; exact hexact.apply_apply_eq_zero z
      hπ := ModuleCat.isColimitCokernelCofork _ _ hexact (by
        intro e
        obtain ⟨z, hz⟩ := CohomologyClass.mk_surjective (I.extEquivCohomologyClass e)
        exact ⟨z, by change I.extEquivCohomologyClass.symm _ = e; rw [hz]; simp⟩) }

open CochainComplex HomComplex in
private noncomputable def evaluatedHomIso (A : Type u) [CommRing A]
    (K L : CochainComplex (Mod A) ℤ) :
    ((ev A).mapHomologicalComplex (.up ℤ)).obj
      (homComplex (R := CochainComplex.onePointRingSheaf A) K L) ≅
        linearHomComplex A K L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (globalCochains A K L n).toModuleIso) (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hu : (unitEquiv A _).symm ((ev A).map
          ((homComplex (R := CochainComplex.onePointRingSheaf A) K L).d i j) x) =
          (unitEquiv A _).symm x ≫
            (homComplex (R := CochainComplex.onePointRingSheaf A) K L).d i j := by
        apply (unitEquiv A _).injective
        change _ = (ev A).map ((unitEquiv A _).symm x ≫
          (homComplex (R := CochainComplex.onePointRingSheaf A) K L).d i j) (1 : A)
        rw [Functor.map_comp]
        change _ = (ev A).map _ (unitEquiv A _ ((unitEquiv A _).symm x))
        simp only [AddEquiv.apply_symm_apply]
      change δ i j (normalizedHomGlobalCochains (CochainComplex.onePointRingSheaf A)
        K L i ((unitEquiv A _).symm x)) = _
      change _ = normalizedHomGlobalCochains (CochainComplex.onePointRingSheaf A)
        K L j ((unitEquiv A _).symm ((ev A).map _ x))
      rw [hu]
      exact (normalizedHomGlobalCochains_comm
        (CochainComplex.onePointRingSheaf A) K L i j _).symm)

/-- Evaluation of derived internal Hom on the one-point ringed site computes ordinary Ext.

Source: Stacks Project, More on Algebra, Tag 0A64, equation equation-h0-RHom.
(blueprint: lem-sc-rhom-cohomology-ext-ring)

Proof: Evaluation at the unique object is an exact equivalence between sheaves of modules
on the bottom-topology one-point site and modules over A. Its inverse is the constant
module sheaf. Choose an injective resolution I of the constant sheaf associated to N.
The derived internal Hom is represented by the sheaf Hom complex from M[0] to I.
Maps from the rank-one free sheaf identify its evaluated terms with ordinary cochains;
the normalized-Hom differential formula makes this an isomorphism of complexes.
Transfer the A-linear structure along evaluation. The cocycles-to-Ext map for I is
A-linear, surjective, and has precisely the coboundaries as kernel, so it identifies
cohomology with Ext in the sheaf category. Finally evaluation induces a linear
bijection on Ext because it is an exact equivalence. Compose these identifications.
The construction also covers n = 0 and the zero ring or zero modules. -/
theorem nonempty_rhom_cohomology_ext_ring
    (A : Type u) [CommRing A]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (CochainComplex.onePointRingSheaf A)))]
    (M N : ModuleCat.{u} A) (n : ℕ) :
    Nonempty
      ((SheafOfModules.evaluation
        ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
          (CochainComplex.onePointRingSheaf A))
        (op (Discrete.mk PUnit.unit))).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u}
            ((sheafCompose ⊥ (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (CochainComplex.onePointRingSheaf A))) (n : ℤ)).obj
          ((derivedInternalHom ⊥ (CochainComplex.onePointRingSheaf A)).obj
            (op ((DerivedCategory.singleFunctor _ 0).obj
              ⟨(PresheafOfModules.constFunctor
                  {pt := RingCat.of A, ι := 𝟙 _}).obj M,
               Presheaf.isSheaf_bot _⟩),
             (DerivedCategory.singleFunctor _ 0).obj
              ⟨(PresheafOfModules.constFunctor
                  {pt := RingCat.of A, ι := 𝟙 _}).obj N,
               Presheaf.isSheaf_bot _⟩))) ≃ₗ[A]
        Abelian.Ext M N n) := by
  classical
  let C := Mod A
  let : IsGrothendieckAbelian.{u} C := SheafOfModules.isGrothendieckAbelian (ring A)
  let : HasExt.{u} C := hasExt_of_enoughInjectives C
  let M' := (const A).obj M
  let N' := (const A).obj N
  let I := injectiveResolution N'
  let K := (CochainComplex.singleFunctor C 0).obj M'
  let eM : DerivedCategory.Q.obj K ≅ (DerivedCategory.singleFunctor C 0).obj M' :=
    ((DerivedCategory.singleFunctorIsoCompQ C 0).app M').symm
  let eN : DerivedCategory.Q.obj I.cochainComplex ≅
      (DerivedCategory.singleFunctor C 0).obj N' :=
    (asIso (DerivedCategory.Q.map I.ι')).symm ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app N').symm
  obtain ⟨h⟩ := derivedInternalHom_obj_iso ⊥ (CochainComplex.onePointRingSheaf A)
    _ _ K I.cochainComplex eM eN
  let H := DerivedCategory.homologyFunctor C (n : ℤ)
  let T := homComplex (R := CochainComplex.onePointRingSheaf A) K I.cochainComplex
  let c := (ev A).mapIso (H.mapIso h ≪≫
    (DerivedCategory.homologyFunctorFactors C (n : ℤ)).app T)
  let d := ((T.sc (n : ℤ)).mapHomologyIso (ev A)).symm
  let e := (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) (n : ℤ)).mapIso
    (evaluatedHomIso A K I.cochainComplex)
  let f := (linearHomologyData A M' N' I n).homologyIso
  let g := LinearEquiv.ofBijective ((ev A).mapExtLinearMap A M' N' n)
    ((ev A).mapExt_bijective_of_preservesInjectiveObjects M' N' n)
  exact ⟨(c ≪≫ d ≪≫ e ≪≫ f).toLinearEquiv.trans g⟩

end CategoryTheory
