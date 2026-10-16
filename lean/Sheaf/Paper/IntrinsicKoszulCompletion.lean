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
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Sheaf.Algebra.Homology.KFlatResolutionGeneral
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts

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

/-- Local bijectivity of the constant ring sheafification unit.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion).
Proof: forgetting commutativity preserves the underlying sections and local equalities;
the original sheafification unit is locally bijective. -/
theorem koszulConstantUnit_local :
    Presheaf.IsLocallyInjective (ProEt.topology X) (koszulConstantUnit X Λ) ∧
    Presheaf.IsLocallySurjective (ProEt.topology X) (koszulConstantUnit X Λ) := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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

/-- Tensoring with the closed degree-zero unit commutes with the total differential.
Source: blueprint order 1257 (blueprint: def-weil-pbc-intrinsic-koszul-completion).
Proof: on the summand (p,0), the first differential is d_C tensor 1. The second is
(-1)^p times c tensor d(1), which is zero. Naturality of the right unitor gives the claim. -/
theorem koszulTensorUnitComponent_comm (r : ℕ) (f : Fin r → Λ)
    (C : CochainComplex (SheafOfModules.{t + 1} (adicModuleRing X Λ)) ℤ) (m : ℕ)
    (p q : ℤ) (hpq : (ComplexShape.up ℤ).Rel p q) :
    koszulTensorUnitComponent X Λ r f C m p ≫ (koszulTensor X Λ r f C m).d p q =
      C.d p q ≫ koszulTensorUnitComponent X Λ r f C m q := by
  sorry

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
  sorry

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
