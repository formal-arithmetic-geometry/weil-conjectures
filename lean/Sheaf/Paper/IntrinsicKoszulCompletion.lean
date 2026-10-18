/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.Paper.CompleteCoefficientDatum
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-! # Intrinsic Koszul completion

Source: blueprint, proper base change, order 1257
(blueprint: def-weil-pbc-intrinsic-koszul-completion).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{t}) (Λ : Type t) [CommRing Λ]

/-- Constant commutative ring sheafification unit, forgetting commutativity.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulConstantUnit :
    (Functor.const X.ProEtᵒᵖ).obj (RingCat.of (ULift.{t + 1} Λ)) ⟶
      (adicModuleRing X Λ).obj :=
  Functor.whiskerRight
    (toSheafify (ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} Λ))))
    (forget₂ CommRingCat RingCat)

set_option backward.isDefEq.respectTransparency false in
/-- Local bijectivity of the constant ring sheafification unit.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion).
Proof: forgetting commutativity preserves the underlying sections and local equalities;
the original sheafification unit is locally bijective. -/
theorem koszulConstantUnit_local :
    Presheaf.IsLocallyInjective (ProEt.topology X) (koszulConstantUnit X Λ) ∧
    Presheaf.IsLocallySurjective (ProEt.topology X) (koszulConstantUnit X Λ) := by
  constructor
  · rw [← Presheaf.isLocallyInjective_forget_iff]
    change Presheaf.IsLocallyInjective (ProEt.topology X)
      (Functor.whiskerRight
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} Λ))))
        (CategoryTheory.forget CommRingCat))
    infer_instance
  · rw [Presheaf.isLocallySurjective_iff_whisker_forget]
    change Presheaf.IsLocallySurjective (ProEt.topology X)
      (Functor.whiskerRight
        (toSheafify (ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{t + 1} Λ))))
        (CategoryTheory.forget CommRingCat))
    infer_instance

/-- Constant module sheaves, obtained by actual module sheafification.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulConstantFunctor :
    ModuleCat.{t + 1} (ULift.{t + 1} Λ) ⥤
      SheafOfModules.{t + 1} (adicModuleRing X Λ) :=
  haveI := (koszulConstantUnit_local X Λ).1
  haveI := (koszulConstantUnit_local X Λ).2
  siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ) ⋙
    PresheafOfModules.sheafification (koszulConstantUnit X Λ)

/-- Constants preserve zero morphisms.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion).
Proof: the constant presheaf construction and module sheafification are additive. -/
theorem koszulConstantFunctor_preservesZero :
    (koszulConstantFunctor X Λ).PreservesZeroMorphisms := by
  constructor
  intro M N
  apply (SheafOfModules.toSheaf.{t + 1} (adicModuleRing X Λ)).map_injective
  change (presheafToSheaf (ProEt.topology X) AddCommGrpCat.{t + 1}).map
    ((PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ)).map
        (0 : M ⟶ N))) = 0
  have h : (PresheafOfModules.toPresheaf _).map
      ((siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ)).map
        (0 : M ⟶ N)) = 0 := by rfl
  rw [h, Functor.map_zero]

attribute [local instance] koszulConstantFunctor_preservesZero

/-- The cohomologically reindexed Koszul complex of the positive power m+1.
The lift changes only the carrier universe, not the coefficient ring.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulPower (r : ℕ) (f : Fin r → Λ) (m : ℕ) :
    CochainComplex (ModuleCat.{t + 1} (ULift.{t + 1} Λ)) ℤ :=
  (ExteriorAlgebra.koszulComplex (ULift.{t + 1} Λ) r
    (fun j ↦ ULift.up (f j ^ (m + 1)))).extend ComplexShape.embeddingDownNat

/-- The constant Koszul sheaf complex.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulPowerSheaf (r : ℕ) (f : Fin r → Λ) (m : ℕ) :=
  ((koszulConstantFunctor X Λ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (koszulPower Λ r f m)

/-- Exterior map on the free generators, e_j ↦ f_j e_j.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulPowerGenerator (r : ℕ) (f : Fin r → Λ) :
    (Fin r →₀ ULift.{t + 1} Λ) →ₗ[ULift.{t + 1} Λ] (Fin r →₀ ULift.{t + 1} Λ) :=
  Finsupp.linearCombination (ULift.{t + 1} Λ) (fun j ↦ Finsupp.single j (ULift.up (f j)))

private theorem koszulExteriorMap_coe (R : Type t) [CommRing R] (r n : ℕ)
    (g : (Fin r →₀ R) →ₗ[R] (Fin r →₀ R)) (x : ⋀[R]^n (Fin r →₀ R)) :
    (exteriorPower.map n g x : ExteriorAlgebra R (Fin r →₀ R)) =
      ExteriorAlgebra.map g (x : ExteriorAlgebra R (Fin r →₀ R)) := by
  have h : (⋀[R]^n (Fin r →₀ R)).subtype.comp (exteriorPower.map n g) =
      (ExteriorAlgebra.map g).toLinearMap.comp (⋀[R]^n (Fin r →₀ R)).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      Submodule.subtype_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.ιMulti_apply_coe, AlgHom.toLinearMap_apply,
      ExteriorAlgebra.map_apply_ιMulti]
  exact LinearMap.congr_fun h x

private theorem koszulContract_natural (R : Type t) [CommRing R] (r : ℕ)
    (g : (Fin r →₀ R) →ₗ[R] (Fin r →₀ R))
    (φ ψ : (Fin r →₀ R) →ₗ[R] R) (h : ψ.comp g = φ)
    (x : ExteriorAlgebra R (Fin r →₀ R)) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin r →₀ R))) ψ
        (ExteriorAlgebra.map g x) =
      ExteriorAlgebra.map g
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin r →₀ R))) φ x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap c => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    have hv : ψ (g v) = φ v := LinearMap.congr_fun h v
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      hv, hx, map_sub, map_smul]

/-- The power transition commutes with Koszul contraction.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion).
Proof: on each exterior generator, contraction on the target multiplies the removed
factor by f_j^(m+1), while the exterior map supplies f_j. This is f_j^(m+2),
which is the source contraction. Multilinearity extends the equality. -/
theorem koszulPowerTransition_comm (r : ℕ) (f : Fin r → Λ) (m i j : ℕ) :
    ModuleCat.ofHom (exteriorPower.map i (koszulPowerGenerator Λ r f)) ≫
      (ExteriorAlgebra.koszulComplex (ULift.{t + 1} Λ) r
        (fun k ↦ ULift.up (f k ^ (m + 1)))).d i j =
    (ExteriorAlgebra.koszulComplex (ULift.{t + 1} Λ) r
      (fun k ↦ ULift.up (f k ^ (m + 2)))).d i j ≫
        ModuleCat.ofHom (exteriorPower.map j (koszulPowerGenerator Λ r f)) := by
  by_cases hij : i = j + 1
  · subst i
    dsimp only [ExteriorAlgebra.koszulComplex]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (ExteriorAlgebra.koszulBoundary (ULift.{t + 1} Λ) r
        (fun k ↦ ULift.up (f k ^ (m + 1))) j
        (exteriorPower.map (j + 1) (koszulPowerGenerator Λ r f) x) :
          ExteriorAlgebra (ULift.{t + 1} Λ) (Fin r →₀ ULift.{t + 1} Λ)) =
      (exteriorPower.map j (koszulPowerGenerator Λ r f)
        (ExteriorAlgebra.koszulBoundary (ULift.{t + 1} Λ) r
          (fun k ↦ ULift.up (f k ^ (m + 2))) j x) :
            ExteriorAlgebra (ULift.{t + 1} Λ) (Fin r →₀ ULift.{t + 1} Λ))
    simp only [koszulExteriorMap_coe, ExteriorAlgebra.koszulBoundary,
      LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    apply koszulContract_natural
    apply Finsupp.lhom_ext
    intro k c
    simp only [LinearMap.comp_apply, koszulPowerGenerator,
      Finsupp.linearCombination_single, map_smul, smul_eq_mul]
    congr 1
    exact congrArg ULift.up (by simpa [Nat.add_assoc, mul_comm] using
      (pow_succ (f k) (m + 1)).symm)
  · have hn : ¬ (ComplexShape.down ℕ).Rel i j := by
      simpa only [ComplexShape.down_Rel, eq_comm] using hij
    rw [HomologicalComplex.shape _ i j hn, HomologicalComplex.shape _ i j hn,
      zero_comp, comp_zero]

/-- The specified exterior-algebra transition, followed by cohomological reindexing.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulPowerTransition (r : ℕ) (f : Fin r → Λ) (m : ℕ) :
    koszulPower Λ r f (m + 1) ⟶ koszulPower Λ r f m :=
  HomologicalComplex.extendMap
    { f := fun i ↦ ModuleCat.ofHom (exteriorPower.map i (koszulPowerGenerator Λ r f))
      comm' := fun i j _ ↦ koszulPowerTransition_comm Λ r f m i j }
    ComplexShape.embeddingDownNat

/-- The canonical section 1 identifies the constant coefficient module with the unit.
The equation at every site object determines the map, not merely its isomorphism class.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion).
Proof: send 1 to the image of 1 under module sheafification. This gives a compatible
section, hence a module map from the unit. A map from the unit is determined by 1. -/
theorem koszulConstantOne_exists :
    ∃! u : SheafOfModules.unit (adicModuleRing X Λ) ⟶
        (koszulConstantFunctor X Λ).obj (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ)),
      ∀ U : X.ProEtᵒᵖ,
        u.val.app U (1 : (adicModuleRing X Λ).obj.obj U) =
          (toSheafify (ProEt.topology X)
            ((siteConstantModulePresheafGeneral (C := X.ProEt)
              (ULift.{t + 1} Λ)).obj
              (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ))).presheaf).app U
                (1 : ULift.{t + 1} Λ) := by
  let P := (siteConstantModulePresheafGeneral (C := X.ProEt) (ULift.{t + 1} Λ)).obj
    (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ))
  let M := (koszulConstantFunctor X Λ).obj
    (ModuleCat.of (ULift.{t + 1} Λ) (ULift.{t + 1} Λ))
  let η := toSheafify (ProEt.topology X) P.presheaf
  let s : M.sections := PresheafOfModules.sectionsMk (fun U ↦ η.app U (1 : ULift.{t + 1} Λ)) (by
    intro U V g
    exact (NatTrans.naturality_apply η g (1 : ULift.{t + 1} Λ)).symm)
  refine ⟨M.unitHomEquiv.symm s, ?_, ?_⟩
  · intro U
    exact congrArg (fun z : M.sections ↦ z.val U) (M.unitHomEquiv.apply_symm_apply s)
  · intro u hu
    apply M.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    exact (hu U).trans
      (congrArg (fun z : M.sections ↦ z.val U) (M.unitHomEquiv.apply_symm_apply s)).symm


/-- The canonical constant unit map selected by its unique section formula.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulConstantOne := (koszulConstantOne_exists X Λ).exists.choose

/-- Degree zero of the Koszul complex contains the identity coefficient unit.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulSheafUnitZero (r : ℕ) (f : Fin r → Λ) (m : ℕ) :
    SheafOfModules.unit (adicModuleRing X Λ) ⟶ (koszulPowerSheaf X Λ r f m).X 0 :=
  koszulConstantOne X Λ ≫ (koszulConstantFunctor X Λ).map
    (ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} Λ)
      (Fin r →₀ ULift.{t + 1} Λ)).symm.toLinearMap) ≫
    (koszulConstantFunctor X Λ).map
      ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} Λ) r
        (fun k ↦ ULift.up (f k ^ (m + 1)))).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv

/-- The degree-zero unit is closed.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion).
Proof: the Koszul cochain complex has no positive terms, so the differential out of
zero is zero. -/
theorem koszulSheafUnitZero_closed (r : ℕ) (f : Fin r → Λ) (m : ℕ)
    (j : ℤ) (hj : (ComplexShape.up ℤ).Rel 0 j) :
    koszulSheafUnitZero X Λ r f m ≫ (koszulPowerSheaf X Λ r f m).d 0 j = 0 := by
  have _ := hj
  have hd : (koszulPower Λ r f m).d 0 j = 0 := by
    exact HomologicalComplex.extend_d_from_eq_zero _ ComplexShape.embeddingDownNat
      0 j 0 rfl (by simp [ComplexShape.down_Rel])
  change _ ≫ (koszulConstantFunctor X Λ).map ((koszulPower Λ r f m).d 0 j) = 0
  rw [hd, Functor.map_zero, comp_zero]

/-- The complex unit into each constant Koszul complex.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulSheafUnit (r : ℕ) (f : Fin r → Λ) (m : ℕ) :
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit (adicModuleRing X Λ)) ⟶ koszulPowerSheaf X Λ r f m :=
  HomologicalComplex.mkHomFromSingle (koszulSheafUnitZero X Λ r f m)
    (koszulSheafUnitZero_closed X Λ r f m)

/-- Total tensor complex of the fixed representative and the constant Koszul complex.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulTensor (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) (m : ℕ) :=
  letI := SheafOfModules.monoidalCategory (adicConstantRing X Λ)
  CochainComplex.mapBifunctor C (koszulPowerSheaf X Λ r f m) (curriedTensor _)

/-- The transition 1_C tensor t_m.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulTensorTransition (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) (m : ℕ) :
    koszulTensor X Λ r f C (m + 1) ⟶ koszulTensor X Λ r f C m :=
  letI := SheafOfModules.monoidalCategory (adicConstantRing X Λ)
  HomologicalComplex.mapBifunctorMap (𝟙 C)
    (((koszulConstantFunctor X Λ).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (koszulPowerTransition Λ r f m)) (curriedTensor _) (ComplexShape.up ℤ)

/-- The component c ↦ c tensor 1, included in the total tensor summand (p,0).
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulTensorUnitComponent (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) (m : ℕ) (p : ℤ) :
    C.X p ⟶ (koszulTensor X Λ r f C m).X p :=
  letI := SheafOfModules.monoidalCategory (adicConstantRing X Λ)
  (ρ_ (C.X p)).inv ≫ (C.X p ◁ koszulSheafUnitZero X Λ r f m) ≫
    HomologicalComplex.ιMapBifunctor C (koszulPowerSheaf X Λ r f m) (curriedTensor _)
      (ComplexShape.up ℤ) p 0 p (add_zero p)

private theorem tensorClosedUnit_comm
    {A : Type*} [Category* A] [Preadditive A] [MonoidalCategory A]
    [(curriedTensor A).PreservesZeroMorphisms]
    [∀ Z, ((curriedTensor A).obj Z).PreservesZeroMorphisms]
    (C D : CochainComplex A ℤ)
    [HomologicalComplex.HasMapBifunctor C D (curriedTensor A) (ComplexShape.up ℤ)]
    (u : 𝟙_ A ⟶ D.X 0) (hu : u ≫ D.d 0 1 = 0)
    (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel p q) :
    ((ρ_ (C.X p)).inv ≫ (C.X p ◁ u) ≫
      HomologicalComplex.ιMapBifunctor C D (curriedTensor A)
        (ComplexShape.up ℤ) p 0 p (add_zero p)) ≫
      (HomologicalComplex.mapBifunctor C D (curriedTensor A) (ComplexShape.up ℤ)).d p q =
    C.d p q ≫ (ρ_ (C.X q)).inv ≫ (C.X q ◁ u) ≫
      HomologicalComplex.ιMapBifunctor C D (curriedTensor A)
        (ComplexShape.up ℤ) q 0 q (add_zero q) := by
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.d_eq,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hpq 0 q (add_zero q),
    HomologicalComplex.mapBifunctor.d₂_eq' _ _ _ _ p
      (show (ComplexShape.up ℤ).Rel 0 1 by rfl) q]
  dsimp only [curriedTensor_map_app, curriedTensor_obj_map]
  have hs : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, 0) = 1 := rfl
  rw [hs, one_smul]
  have hzero : C.X p ◁ (0 : 𝟙_ A ⟶ D.X 1) = 0 :=
    Functor.map_zero ((curriedTensor A).obj (C.X p)) _ _
  rw [Linear.comp_units_smul, ← whiskerLeft_comp_assoc, hu,
    hzero, zero_comp, smul_zero, comp_zero, add_zero]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]

/-- Tensoring with the closed degree-zero unit commutes with the total differential.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion).
Proof: on the summand (p,0), the first differential is d_C tensor 1. The second is
(-1)^p times c tensor d(1), which is zero. Naturality of the right unitor gives the claim. -/
theorem koszulTensorUnitComponent_comm (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) (m : ℕ)
    (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel p q) :
    koszulTensorUnitComponent X Λ r f C m p ≫ (koszulTensor X Λ r f C m).d p q =
      C.d p q ≫ koszulTensorUnitComponent X Λ r f C m q := by
  have : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{t + 1} := inferInstance
  have : HasWeakSheafify (ProEt.topology X) AddCommGrpCat.{t + 1} := inferInstance
  let := SheafOfModules.isMonoidal_W_separateHomUniverse.{t + 1, t}
    (adicConstantRing X Λ)
  let : MonoidalCategory (SheafOfModules.{t + 1} (adicModuleRing X Λ)) :=
    SheafOfModules.monoidalCategory.{t, t + 1, t + 1} (adicConstantRing X Λ)
  exact tensorClosedUnit_comm (A := SheafOfModules.{t + 1} (adicModuleRing X Λ))
    C (koszulPowerSheaf X Λ r f m) (koszulSheafUnitZero X Λ r f m)
    (koszulSheafUnitZero_closed X Λ r f m 1 (by rfl)) p q hpq

/-- The tensor unit gives c ↦ c tensor 1 in each level.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulTensorUnit (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) (m : ℕ) :
    C ⟶ koszulTensor X Λ r f C m where
  f := koszulTensorUnitComponent X Λ r f C m
  comm' := koszulTensorUnitComponent_comm X Λ r f C m

/-- The termwise product of the positive-power tensor tower (index n means m=n+1).
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulProduct (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) :=
  ∏ᶜ (koszulTensor X Λ r f C)

/-- One minus the transition shift, specified by its actual product components.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulOneSubShift (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) :
    koszulProduct X Λ r f C ⟶ koszulProduct X Λ r f C :=
  𝟙 _ - Pi.lift (fun n ↦ Pi.π (koszulTensor X Λ r f C) (n + 1) ≫
    koszulTensorTransition X Λ r f C n)

/-- The specified shifted cone complex, rather than a choice of a Roos triangle.
Mathlib orders its degree-a summands as P^a ⊞ P^(a-1); interchanging them gives
exactly (-d y -(1-s)x, d x) in the node's order (y,x).
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulCompletionComplex (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) :
    CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ :=
  (CochainComplex.mappingCone (koszulOneSubShift X Λ r f C))⟦(-1 : ℤ)⟧

/-- The compatible family of tensor units, as a map into the actual product complex.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulProductUnit (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) :
    C ⟶ koszulProduct X Λ r f C :=
  Pi.lift (koszulTensorUnit X Λ r f C)

set_option backward.isDefEq.respectTransparency false in
private theorem koszulPowerUnit_transition (r : ℕ) (f : Fin r → Λ) (m : ℕ) :
    ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} Λ)
        (Fin r →₀ ULift.{t + 1} Λ)).symm.toLinearMap ≫
      ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} Λ) r
        (fun k ↦ ULift.up (f k ^ (m + 1 + 1)))).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv ≫
      (koszulPowerTransition Λ r f m).f 0 =
    ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} Λ)
        (Fin r →₀ ULift.{t + 1} Λ)).symm.toLinearMap ≫
      ((ExteriorAlgebra.koszulComplex (ULift.{t + 1} Λ) r
        (fun k ↦ ULift.up (f k ^ (m + 1)))).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv := by
  have hz : ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} Λ)
        (Fin r →₀ ULift.{t + 1} Λ)).symm.toLinearMap ≫
      ModuleCat.ofHom (exteriorPower.map 0 (koszulPowerGenerator Λ r f)) =
      ModuleCat.ofHom (exteriorPower.zeroEquiv (ULift.{t + 1} Λ)
        (Fin r →₀ ULift.{t + 1} Λ)).symm.toLinearMap := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (exteriorPower.zeroEquiv (ULift.{t + 1} Λ)
      (Fin r →₀ ULift.{t + 1} Λ)).injective
    exact LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality
      (koszulPowerGenerator Λ r f)) _
  dsimp only [koszulPowerTransition]
  rw [HomologicalComplex.extendMap_f _ ComplexShape.embeddingDownNat
    (i := 0) (i' := 0) rfl, Iso.inv_hom_id_assoc, ← Category.assoc, hz]

set_option backward.isDefEq.respectTransparency false in
private theorem koszulSheafUnitZero_transition (r : ℕ) (f : Fin r → Λ) (m : ℕ) :
    koszulSheafUnitZero X Λ r f (m + 1) ≫
      (((koszulConstantFunctor X Λ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (koszulPowerTransition Λ r f m)).f 0 = koszulSheafUnitZero X Λ r f m := by
  dsimp only [koszulSheafUnitZero]
  change (koszulConstantOne X Λ ≫ _ ≫ _) ≫
    (koszulConstantFunctor X Λ).map ((koszulPowerTransition Λ r f m).f 0) = _
  simp only [Category.assoc, ← Functor.map_comp, koszulPowerUnit_transition]

set_option backward.isDefEq.respectTransparency false in
private theorem koszulTensorUnit_transition (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) (m : ℕ) :
    koszulTensorUnit X Λ r f C (m + 1) ≫ koszulTensorTransition X Λ r f C m =
      koszulTensorUnit X Λ r f C m := by
  let : MonoidalCategory (SheafOfModules.{t + 1} (adicModuleRing X Λ)) :=
    SheafOfModules.monoidalCategory.{t, t + 1, t + 1} (adicConstantRing X Λ)
  apply HomologicalComplex.hom_ext
  intro p
  dsimp only [HomologicalComplex.comp_f, koszulTensorUnit, koszulTensorTransition,
    koszulTensorUnitComponent, koszulPowerSheaf, koszulTensor]
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
    id_whiskerRight]
  erw [Category.id_comp]
  rw [← whiskerLeft_comp_assoc, koszulSheafUnitZero_transition]

set_option backward.isDefEq.respectTransparency false in
private theorem koszulProductUnit_oneSubShift (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) :
    koszulProductUnit X Λ r f C ≫ koszulOneSubShift X Λ r f C = 0 := by
  dsimp only [koszulOneSubShift, koszulProduct, koszulProductUnit]
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero]
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.lift_π, Pi.lift_π_assoc, koszulTensorUnit_transition]

set_option backward.isDefEq.respectTransparency false in
private theorem shiftedConeUnit_comm {A : Type*} [Category* A] [Preadditive A]
    (C P : CochainComplex A ℤ) (a : C ⟶ P) (φ : P ⟶ P)
    [HomologicalComplex.HasHomotopyCofiber φ] (hz : a ≫ φ = 0)
    (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel p q) :
    (a.f p ≫ HomologicalComplex.homotopyCofiber.inlX φ
      p (p + (-1)) (by change p + (-1) + 1 = p; omega)) ≫
        ((CochainComplex.mappingCone φ)⟦(-1 : ℤ)⟧).d p q =
    C.d p q ≫ a.f q ≫ HomologicalComplex.homotopyCofiber.inlX φ
      q (q + (-1)) (by change q + (-1) + 1 = q; omega) := by
  have hp : p = q + (-1) := by
    change p + 1 = q at hpq
    omega
  subst p
  change (a.f (q + (-1)) ≫ _) ≫ ((-1 : ℤ).negOnePow •
    HomologicalComplex.homotopyCofiber.d φ (q + (-1) + (-1)) (q + (-1))) = _
  rw [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul,
    Preadditive.comp_neg, Category.assoc,
    HomologicalComplex.homotopyCofiber.inlX_d φ (q + (-1) + (-1)) (q + (-1)) q
      (by change q + (-1) + (-1) + 1 = q + (-1); omega)
      (by change q + (-1) + 1 = q; omega)]
  simp only [Preadditive.comp_add, Preadditive.comp_neg, neg_add_rev, neg_neg]
  have hz' := congrArg (fun u ↦ u.f (q + (-1))) hz
  change a.f (q + (-1)) ≫ φ.f (q + (-1)) = 0 at hz'
  rw [← Category.assoc, hz', zero_comp, neg_zero, zero_add]
  rw [← a.comm_assoc (q + (-1)) q]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The unit components define a chain map into the shifted cone.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion).
Proof: t_m sends 1 to 1, so a followed by 1-s is zero. The shifted cone differential
on (0,a(c)) is (0,a(dc)), using that each tensor unit is a chain map. -/
theorem koszulCompletionUnit_comm (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ)
    (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel p q) :
    ((koszulProductUnit X Λ r f C).f p ≫
      HomologicalComplex.homotopyCofiber.inlX (koszulOneSubShift X Λ r f C)
        p (p + (-1)) (by change p + (-1) + 1 = p; omega)) ≫
        (koszulCompletionComplex X Λ r f C).d p q =
    C.d p q ≫ (koszulProductUnit X Λ r f C).f q ≫
      HomologicalComplex.homotopyCofiber.inlX (koszulOneSubShift X Λ r f C)
        q (q + (-1)) (by change q + (-1) + 1 = q; omega) := by
  exact shiftedConeUnit_comm C (koszulProduct X Λ r f C)
    (koszulProductUnit X Λ r f C) (koszulOneSubShift X Λ r f C)
    (koszulProductUnit_oneSubShift X Λ r f C) p q hpq

/-- The actual chain map c ↦ (0,a(c)), with Mathlib's cone summands interchanged.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def koszulCompletionUnitComplex (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) :
    C ⟶ koszulCompletionComplex X Λ r f C where
  f p := (koszulProductUnit X Λ r f C).f p ≫
    HomologicalComplex.homotopyCofiber.inlX (koszulOneSubShift X Λ r f C)
      p (p + (-1)) (by change p + (-1) + 1 = p; omega)
  comm' := koszulCompletionUnit_comm X Λ r f C

/-- Intrinsic Koszul completion under exactly the coefficient hypotheses of order 1255.
The generators may be empty; no regular-sequence or boundedness hypothesis is imposed.
C is the fixed K-flat representative, with its identification with the given K.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def intrinsicKoszulCompletion (_d : CompleteCoefficientDatum Λ) (r : ℕ) (f : Fin r → Λ)
    (_hf : Ideal.span (Set.range f) = _d.ideal) (K : proEtaleDerivedCategory X Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ)
    (_hC : CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X Λ) C)
    (_e : (adicLocalization X Λ).obj C ≅ K) : proEtaleDerivedCategory X Λ :=
  (adicLocalization X Λ).obj (koszulCompletionComplex X Λ r f C)

/-- The derived completion unit, transported from the fixed K-flat representative.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def intrinsicKoszulCompletionUnit (d : CompleteCoefficientDatum Λ) (r : ℕ) (f : Fin r → Λ)
    (hf : Ideal.span (Set.range f) = d.ideal) (K : proEtaleDerivedCategory X Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X Λ) C)
    (e : (adicLocalization X Λ).obj C ≅ K) :
    K ⟶ intrinsicKoszulCompletion X Λ d r f hf K C hC e :=
  e.inv ≫ (adicLocalization X Λ).map (koszulCompletionUnitComplex X Λ r f C)

/-- Intrinsic derived I-completeness: precisely invertibility of the specified unit.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion). -/
def IsIntrinsicallyDerivedComplete (d : CompleteCoefficientDatum Λ) (r : ℕ) (f : Fin r → Λ)
    (hf : Ideal.span (Set.range f) = d.ideal) (K : proEtaleDerivedCategory X Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ)
    (hC : CochainComplex.IsAcyclicTensorKFlat (R := adicConstantRing X Λ) C)
    (e : (adicLocalization X Λ).obj C ≅ K) : Prop :=
  IsIso (intrinsicKoszulCompletionUnit X Λ d r f hf K C hC e)

end AlgebraicGeometry.Scheme
