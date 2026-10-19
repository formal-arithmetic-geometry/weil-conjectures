/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups ND and Q22
-/
module

public import Sheaf.Paper.CompletedConstantFiniteComplexRealization
public import Sheaf.Paper.AdicCoefficientDatumCompleted
public import Sheaf.Paper.SequentialDerivedInverseLimitCompleted
public import Sheaf.Paper.KoszulComplex
public import Sheaf.Paper.KoszulDifferential
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Sheaf.Paper.CompletedConstantSheafReduction
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts

import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Intrinsic completion over the completed coefficient sheaf

Source: blueprint, proper base change, order 1247; Stacks Tags 099M and 091Z
(blueprint: def-weil-pbc-intrinsic-completion).

The ring and tensor product are those of Mod(A_T), with site object universe t+1
and morphism universe t. The mapping cocone of minus (1-shift) has differential
(dx, (1-shift)x-dy) after listing its degree-i terms as (x,y).

## Main definitions

* `completedKoszulPowerSheaf`: the completed-coefficient Koszul complex.
* `completedKoszulFiber`: the explicit completion complex.
* `completedIntrinsicCompletionMap`: its specified unit.
* `IsCompletedIntrinsicallyDerivedComplete`: invertibility of that unit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{t}) {A : Type (t + 1)} [CommRing A]
variable (d : ProEtaleAdicCoefficientDatum A)

/-- Constant A-modules extended to the actual completed coefficient sheaf.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulConstant : ModuleCat.{t + 1} A ⥤ adicDatumModules X d :=
  adicLisseConstantModules X A ⋙ completedConstantExtension X (adicDatumScalar X d)

/-- Constant module sheafification and scalar extension are additive.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion).
Proof: addition and zero hold on the constant presheaves, then on their sheafification;
scalar extension is additive by its specified tensor/restriction adjunction. -/
theorem completedKoszulConstant_additive : (completedKoszulConstant X d).Additive := by
  let := CompletedConstantReduction.constant_additive X A
  exact Functor.Additive.mk (by
    intro M N f g
    dsimp [completedKoszulConstant]
    rw [Functor.map_add, Functor.map_add])
attribute [instance] completedKoszulConstant_additive

/-- The cohomologically reindexed Koszul complex of the positive power m+1.
The module carrier has the same universe as the original coefficient ring.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulPower (r : ℕ) (f : Fin r → A) (m : ℕ) :
    CochainComplex (ModuleCat.{t + 1} (A)) ℤ :=
  (ExteriorAlgebra.koszulComplex (A) r
    (fun j ↦ f j ^ (m + 1))).extend ComplexShape.embeddingDownNat

/-- The constant Koszul sheaf complex.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulPowerSheaf (r : ℕ) (f : Fin r → A) (m : ℕ) :=
  ((completedKoszulConstant X d).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (completedKoszulPower (A := A) r f m)

/-- Exterior map on the free generators, e_j ↦ f_j e_j.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulGenerator (r : ℕ) (f : Fin r → A) :
    (Fin r →₀ A) →ₗ[A] (Fin r →₀ A) :=
  Finsupp.linearCombination (A) (fun j ↦ Finsupp.single j (f j))

private theorem completedKoszulExteriorMap_coe (R : Type*) [CommRing R] (r n : ℕ)
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

private theorem completedKoszulContract_natural (R : Type*) [CommRing R] (r : ℕ)
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
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion).
Proof: on each exterior generator, contraction on the target multiplies the removed
factor by f_j^(m+1), while the exterior map supplies f_j. This is f_j^(m+2),
which is the source contraction. Multilinearity extends the equality. -/
theorem completedKoszulTransition_comm (r : ℕ) (f : Fin r → A) (m i j : ℕ) :
    ModuleCat.ofHom (exteriorPower.map i (completedKoszulGenerator (A := A) r f)) ≫
      (ExteriorAlgebra.koszulComplex (A) r
        (fun k ↦ f k ^ (m + 1))).d i j =
    (ExteriorAlgebra.koszulComplex (A) r
      (fun k ↦ f k ^ (m + 2))).d i j ≫
        ModuleCat.ofHom (exteriorPower.map j (completedKoszulGenerator (A := A) r f)) := by
  by_cases hij : i = j + 1
  · subst i
    dsimp only [ExteriorAlgebra.koszulComplex]
    rw [ChainComplex.of_d, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (ExteriorAlgebra.koszulBoundary A r
        (fun k ↦ f k ^ (m + 1)) j
        (exteriorPower.map (j + 1) (completedKoszulGenerator (A := A) r f) x) :
          ExteriorAlgebra A (Fin r →₀ A)) =
      (exteriorPower.map j (completedKoszulGenerator (A := A) r f)
        (ExteriorAlgebra.koszulBoundary A r
          (fun k ↦ f k ^ (m + 2)) j x) : ExteriorAlgebra A (Fin r →₀ A))
    simp only [completedKoszulExteriorMap_coe, ExteriorAlgebra.koszulBoundary,
      LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    apply completedKoszulContract_natural
    apply Finsupp.lhom_ext
    intro k c
    simp only [LinearMap.comp_apply, completedKoszulGenerator,
      Finsupp.linearCombination_single, map_smul, smul_eq_mul]
    congr 1
    simpa [Nat.add_assoc, mul_comm] using (pow_succ (f k) (m + 1)).symm
  · have hn : ¬ (ComplexShape.down ℕ).Rel i j := by
      simpa only [ComplexShape.down_Rel, eq_comm] using hij
    rw [HomologicalComplex.shape _ i j hn, HomologicalComplex.shape _ i j hn,
      zero_comp, comp_zero]

/-- The specified exterior-algebra transition, followed by cohomological reindexing.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulTransition (r : ℕ) (f : Fin r → A) (m : ℕ) :
    completedKoszulPower (A := A) r f (m + 1) ⟶ completedKoszulPower (A := A) r f m :=
  HomologicalComplex.extendMap
    { f := fun i ↦ ModuleCat.ofHom (exteriorPower.map i (completedKoszulGenerator (A := A) r f))
      comm' := fun i j _ ↦ completedKoszulTransition_comm (A := A) r f m i j }
    ComplexShape.embeddingDownNat

/-- The completed unit is the image of 1 tensor 1 in the extended constant module.
The section formula uniquely determines it, including over the empty scheme.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion).
Proof: maps from the regular module correspond to global sections. The compatible
section 1 tensor 1 gives the map and determines it uniquely by linearity. -/
theorem completedKoszulOne_exists :
    ∃! u : SheafOfModules.unit ((adicLisseForget X).obj (adicDatumRing X d)) ⟶
        (completedKoszulConstant X d).obj (ModuleCat.of A A),
      ∀ U : X.ProEtᵒᵖ, u.val.app U (1 : (adicDatumRing X d).obj.obj U) =
        adicDatumTensorSection X (adicDatumScalar X d)
          ((adicLisseConstantModules X A).obj (ModuleCat.of A A)) U 1
          (completedConstantGenerator X A (ModuleCat.of A A) U 1) := by
  let M := (completedKoszulConstant X d).obj (ModuleCat.of A A)
  let s : M.sections := PresheafOfModules.sectionsMk
    (fun U ↦ adicDatumTensorSection X (adicDatumScalar X d)
      ((adicLisseConstantModules X A).obj (ModuleCat.of A A)) U 1
      (completedConstantGenerator X A (ModuleCat.of A A) U 1)) (by
        intro U V g
        let N := (adicLisseConstantModules X A).obj (ModuleCat.of A A)
        let u := adicDatumOrdinaryUnit X (adicDatumScalar X d) N
        have hu := (adicDatumOrdinaryUnit_exists X (adicDatumScalar X d) N).exists.choose_spec
        rw [← hu U, ← hu V]
        have hn := u.val.naturality g
        have hg : N.val.map g (completedConstantGenerator X A (ModuleCat.of A A) U 1) =
            completedConstantGenerator X A (ModuleCat.of A A) V 1 := by
          exact (ConcreteCategory.congr_hom
            ((toSheafify (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).naturality g) (1 : A)).symm
        change M.val.map g (u.val.app U _) = u.val.app V _
        exact (ConcreteCategory.congr_hom hn _).symm.trans (congrArg (u.val.app V) hg))
  refine ⟨M.unitHomEquiv.symm s, ?_, ?_⟩
  · intro U
    exact congrArg (fun z : M.sections ↦ z.val U)
      (M.unitHomEquiv.apply_symm_apply s)
  · intro u hu
    apply M.unitHomEquiv.injective
    apply PresheafOfModules.sections_ext
    intro U
    exact (hu U).trans
      (congrArg (fun z : M.sections ↦ z.val U)
        (M.unitHomEquiv.apply_symm_apply s)).symm

/-- The canonical degree-zero unit of the extended Koszul complex.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulOne := (completedKoszulOne_exists X d).exists.choose

/-- Degree zero of the Koszul complex contains the identity coefficient unit.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulSheafUnitZero (r : ℕ) (f : Fin r → A) (m : ℕ) :
    SheafOfModules.unit ((adicLisseForget X).obj (adicDatumRing X d)) ⟶
      (completedKoszulPowerSheaf X d r f m).X 0 :=
  completedKoszulOne X d ≫ (completedKoszulConstant X d).map
    (ModuleCat.ofHom (exteriorPower.zeroEquiv (A)
      (Fin r →₀ A)).symm.toLinearMap) ≫
    (completedKoszulConstant X d).map
      ((ExteriorAlgebra.koszulComplex (A) r
        (fun k ↦ f k ^ (m + 1))).extendXIso
          ComplexShape.embeddingDownNat (i := 0) rfl).inv

/-- The degree-zero unit is closed.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion).
Proof: the Koszul cochain complex has no positive terms, so the differential out of
zero is zero. -/
theorem completedKoszulSheafUnitZero_closed (r : ℕ) (f : Fin r → A) (m : ℕ)
    (j : ℤ) (hj : (ComplexShape.up ℤ).Rel 0 j) :
    completedKoszulSheafUnitZero X d r f m ≫ (completedKoszulPowerSheaf X d r f m).d 0 j = 0 := by
  have _hj := hj
  have hd : (completedKoszulPower (A := A) r f m).d 0 j = 0 := by
    apply HomologicalComplex.extend_d_from_eq_zero _ ComplexShape.embeddingDownNat
      0 j 0 rfl
    simp [ComplexShape.down_Rel]
  change _ ≫ (completedKoszulConstant X d).map
    ((completedKoszulPower (A := A) r f m).d 0 j) = 0
  rw [hd, Functor.map_zero, comp_zero]

/-- The complex unit into each constant Koszul complex.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulSheafUnit (r : ℕ) (f : Fin r → A) (m : ℕ) :
    (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (SheafOfModules.unit ((adicLisseForget X).obj (adicDatumRing X d))) ⟶
        completedKoszulPowerSheaf X d r f m :=
  HomologicalComplex.mkHomFromSingle (completedKoszulSheafUnitZero X d r f m)
    (completedKoszulSheafUnitZero_closed X d r f m)

/-- Total tensor complex of the fixed representative and the constant Koszul complex.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulTensor (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) (m : ℕ) :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  letI := SheafOfModules.monoidalCategory (adicDatumRing X d)
  CochainComplex.mapBifunctor C (completedKoszulPowerSheaf X d r f m) (curriedTensor _)

/-- The transition 1_C tensor t_m.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulTensorTransition (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) (m : ℕ) :
    completedKoszulTensor X d r f C (m + 1) ⟶ completedKoszulTensor X d r f C m :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  letI := SheafOfModules.monoidalCategory (adicDatumRing X d)
  HomologicalComplex.mapBifunctorMap (𝟙 C)
    (((completedKoszulConstant X d).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (completedKoszulTransition (A := A) r f m)) (curriedTensor _) (ComplexShape.up ℤ)

/-- The component c ↦ c tensor 1, included in the total tensor summand (p,0).
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulTensorUnitComponent (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) (m : ℕ) (p : ℤ) :
    C.X p ⟶ (completedKoszulTensor X d r f C m).X p :=
  letI := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  letI := SheafOfModules.monoidalCategory (adicDatumRing X d)
  (ρ_ (C.X p)).inv ≫ (C.X p ◁ completedKoszulSheafUnitZero X d r f m) ≫
    HomologicalComplex.ιMapBifunctor C (completedKoszulPowerSheaf X d r f m) (curriedTensor _)
      (ComplexShape.up ℤ) p 0 p (add_zero p)

/-- Tensoring with the closed degree-zero unit commutes with the total differential.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion).
Proof: on the summand (p,0), the first differential is d_C tensor 1. The second is
(-1)^p times c tensor d(1), which is zero. Naturality of the right unitor gives the claim. -/
theorem completedKoszulTensorUnitComponent_comm (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) (m : ℕ)
    (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel p q) :
    completedKoszulTensorUnitComponent X d r f C m p ≫ (completedKoszulTensor X d r f C m).d p q =
      C.d p q ≫ completedKoszulTensorUnitComponent X d r f C m q := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients (adicDatumRing X d)
  let := SheafOfModules.monoidalCategory (adicDatumRing X d)
  dsimp only [completedKoszulTensorUnitComponent, completedKoszulTensor]
  rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add]
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hpq 0 q (add_zero q),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ p (show
      (ComplexShape.up ℤ).Rel 0 1 from rfl) q (by
        change p + 1 = q
        exact hpq)]
  have hε : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (p, 0) = 1 := rfl
  rw [hε, one_smul]
  simp only [curriedTensor_obj_map, curriedTensor_map_app]
  have hz : C.X p ◁ completedKoszulSheafUnitZero X d r f m ≫
      C.X p ◁ (completedKoszulPowerSheaf X d r f m).d 0 1 = 0 := by
    rw [← whiskerLeft_comp, completedKoszulSheafUnitZero_closed X d r f m 1 rfl]
    exact Functor.map_zero ((curriedTensor _).obj (C.X p)) _ _
  simp only [Linear.comp_units_smul]
  rw [← Category.assoc (C.X p ◁ completedKoszulSheafUnitZero X d r f m)
      (C.X p ◁ (completedKoszulPowerSheaf X d r f m).d 0 1), hz,
    zero_comp, comp_zero, smul_zero, add_zero]
  rw [whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc]

/-- The tensor unit gives c ↦ c tensor 1 in each level.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulTensorUnit (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) (m : ℕ) :
    C ⟶ completedKoszulTensor X d r f C m where
  f := completedKoszulTensorUnitComponent X d r f C m
  comm' := completedKoszulTensorUnitComponent_comm X d r f C m

/-- The termwise product of the positive-power tensor tower (index n means m=n+1).
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulProduct (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) :=
  ∏ᶜ (completedKoszulTensor X d r f C)

/-- One minus the transition shift, specified by its actual product components.
Source: blueprint order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulOneSubShift (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) :
    completedKoszulProduct X d r f C ⟶ completedKoszulProduct X d r f C :=
  𝟙 _ - Pi.lift (fun n ↦ Pi.π (completedKoszulTensor X d r f C) (n + 1) ≫
    completedKoszulTensorTransition X d r f C n)

/-- Explicit mapping fiber with differential (dx,(1-s)x-dy), in the node's order.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulFiber (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) :=
  CochainComplex.mappingCocone (- completedKoszulOneSubShift X d r f C)

/-- The compatible units C to C tensor Q_m give the actual product augmentation.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulProductUnit (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) :=
  Pi.lift (completedKoszulTensorUnit X d r f C)

/-- The unit has zero homotopy component in the mapping fiber.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion).
Proof: every transition sends the Koszul degree-zero unit to itself. Consequently
(1-shift) composed with the product of units is zero. The zero cochain has zero
differential, giving precisely the relation required by the mapping-fiber lift. -/
theorem completedKoszulLift_relation (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) :
    CochainComplex.HomComplex.δ (-1) 0
      (0 : CochainComplex.HomComplex.Cochain C (completedKoszulProduct X d r f C) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (completedKoszulProductUnit X d r f C ≫
          (- completedKoszulOneSubShift X d r f C)) = 0 := by
  sorry

/-- The completion chain map c maps to (u(c),0) in the specified fiber coordinates.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedKoszulUnitComplex (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) :
    C ⟶ completedKoszulFiber X d r f C :=
  CochainComplex.mappingCocone.lift _ (completedKoszulProductUnit X d r f C) 0
    (completedKoszulLift_relation X d r f C)

/-- The intrinsic completion of any representative, localized in D(Mod(A_T)).
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedIntrinsicCompletion (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) : adicDatumDerived X d :=
  (completedConstantQ _).obj (completedKoszulFiber X d r f C)

/-- The intrinsic completion map, transported through a specified realization of C.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def completedIntrinsicCompletionMap (r : ℕ) (f : Fin r → A)
    (C : CochainComplex (adicDatumModules X d) ℤ) {K : adicDatumDerived X d}
    (e : (completedConstantQ _).obj C ≅ K) :
    K ⟶ completedIntrinsicCompletion X d r f C :=
  e.inv ≫ (completedConstantQ _).map (completedKoszulUnitComplex X d r f C)

/-- Derived I-completeness is invertibility of the specified Koszul completion map.
The finite generator tuple is explicitly required to generate I; it may be empty.
Source: order 1247 (blueprint: def-weil-pbc-intrinsic-completion). -/
def IsCompletedIntrinsicallyDerivedComplete (r : ℕ) (f : Fin r → A)
    (_hf : Ideal.span (Set.range f) = d.ideal)
    (C : CochainComplex (adicDatumModules X d) ℤ) {K : adicDatumDerived X d}
    (e : (completedConstantQ _).obj C ≅ K) : Prop :=
  IsIso (completedIntrinsicCompletionMap X d r f C e)

/-- The explicit Koszul fiber and its unit descend through quasi-isomorphisms.
No arbitrary representative is chosen to define the data of the fiber complex.
Source: order 1247; Tags 07KC and 05RU (blueprint: def-weil-pbc-intrinsic-completion).
Proof: tensor with a bounded finite-free Koszul complex preserves quasi-isomorphisms.
Exact countable products preserve them, and the mapping-fiber triangle then preserves
them. Apply the localization universal property to the fiber functor and its
natural zero-homotopy unit. The displayed identification is the localization
comparison and carries the descended unit to the stated chain map. -/
theorem completedIntrinsicCompletion_descends (r : ℕ) (f : Fin r → A) :
    ∃ (F : adicDatumDerived X d ⥤ adicDatumDerived X d) (η : 𝟭 _ ⟶ F),
      ∀ C : CochainComplex (adicDatumModules X d) ℤ,
        ∃ e : F.obj ((completedConstantQ _).obj C) ≅
            completedIntrinsicCompletion X d r f C,
          η.app ((completedConstantQ _).obj C) ≫ e.hom =
            (completedConstantQ _).map (completedKoszulUnitComplex X d r f C) := by
  sorry

end AlgebraicGeometry.Scheme
