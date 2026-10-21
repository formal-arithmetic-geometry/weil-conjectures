/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Sheaf.Paper.ExactScalarPeriodicResolution
public import Sheaf.Algebra.Homology.RingedKFlatSingleTensorComparison
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # The zero-differential normal form of a periodic tensor

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples"; Stacks Tags 03EK, 06YU.
(blueprint: lem-sfb-periodic-tensor-normal-form)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

/-- The prescribed normal form has M in every nonpositive degree and zero differential.
Source: blueprint, "The examples" (blueprint: lem-sfb-periodic-tensor-normal-form). -/
def periodicTensorZeroComplex (M : Modules R) : CochainComplex (Modules R) ℤ where
  X := CochainComplex.scalarPeriodicX M
  d := fun _ _ ↦ 0

/-- The nonpositive term of the normal form is M itself.
Source: blueprint, "The examples" (blueprint: lem-sfb-periodic-tensor-normal-form). -/
def periodicTensorZeroXIso (M : Modules R) (i : ℤ) (hi : i ≤ 0) :
    (periodicTensorZeroComplex R M).X i ≅ M := eqToIso (if_pos hi)

/-- The induced normal-form map is f in nonpositive degrees and zero above zero.
Source: blueprint, "The examples" (blueprint: lem-sfb-periodic-tensor-normal-form). -/
def periodicTensorZeroMap {M N : Modules R} (f : M ⟶ N) :
    periodicTensorZeroComplex R M ⟶ periodicTensorZeroComplex R N where
  f i := if hi : i ≤ 0 then
    (periodicTensorZeroXIso R M i hi).hom ≫ f ≫
      (periodicTensorZeroXIso R N i hi).inv else 0
  comm' _ _ _ := comp_zero.trans zero_comp.symm

/-- Tensoring the prescribed periodic scalar complex with a module killed by the scalar
has its canonical zero-differential normal form. The formulas specify both directions
using the degree-zero total-tensor projection and the unit tensor isomorphism; locally
these are a tensor m mapped to a*m, and m mapped to 1 tensor m. Naturality is a chain-map
identity. No exactness of scalar multiplication on R and no nonvanishing are assumed.

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-def-localizing-closure-ctf-equals-bc.proof.md, "The examples"; Stacks 03EK and 06YU
(blueprint: lem-sfb-periodic-tensor-normal-form).

Proof (the node's seven steps):
1. The existing exactScalarPeriodicComplex uses scalar multiplication in negative
   degrees. Its square is zero by t squared = 0; the cutoff handles the other degrees.
2. The sectionwise balanced maps a tensor m to a*m and m to 1 tensor m are inverse
   and commute with restrictions. Sheafification (def-weil-presheaf-modules-sheafification)
   gives the unit tensor iso of def-pur-sheaf-tensor-product, including tensor with zero.
3. In total degree n all summands except (n,0) vanish. The coproduct projection and
   injection give mapBifunctorSingle₂Iso, followed in nonpositive degrees by the unit iso.
4. The second signed differential is zero. The first becomes t*a*m = a*(t*m) = 0.
   At degree zero its target vanishes; above zero its source vanishes. The graded
   inverse maps therefore commute with differentials and are inverse chain maps.
5. Linearity gives a*f(m) = f(a*m) and f(1 tensor m) = 1 tensor f(m).
   Sheafification uniqueness proves naturality; positive-degree squares are zero.
6. Kernels in the zero-differential complex are whole terms, and images are zero.
   Transport cohomology along the iso: every H^(-q) is M, including q=0, and positive
   cohomology vanishes. The same computation on the one-point site is ordinary tensor.
7. Given a K-flat resolution epsilon, lem-sf-ringed-kflat-single-tensor-comparison
   identifies the derived tensor with the localized termwise tensor. Its degree-zero
   comparison and the iso above identify this with Q(Z_M). Invert Q(epsilon) in the
   first factor. This uses the specified resolution without boundedness or flatness of M.
-/
theorem periodic_tensor_normal_form
    (t : (unit ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)).sections)
    (ht : ∀ U : Cᵒᵖ, (@id (R.obj.obj U) (t.val U)) * (@id (R.obj.obj U) (t.val U)) = 0)
    [HasDerivedCategory.{w} (Modules R)] :
    ∃ phi : ∀ (M : Modules R)
        (_ : ∀ (U : Cᵒᵖ) (m : M.val.obj U), (@id (R.obj.obj U) (t.val U)) • m = 0),
      CochainComplex.mapBifunctor (exactScalarPeriodicComplex R t ht)
          ((HomologicalComplex.single _ (.up ℤ) 0).obj M) (ordinaryTensor R) ≅
        periodicTensorZeroComplex R M,
      (∀ (M : Modules R)
          (hM : ∀ (U : Cᵒᵖ) (m : M.val.obj U), (@id (R.obj.obj U) (t.val U)) • m = 0)
          (i : ℤ) (hi : i ≤ 0),
        (phi M hM).hom.f i ≫ (periodicTensorZeroXIso R M i hi).hom =
          (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) M
            (exactScalarPeriodicComplex R t ht)).hom.f i ≫
          ((ordinaryTensor R).map (CochainComplex.scalarPeriodicXIso
            (exactScalarMultiplication R t) (exactScalarMultiplication_sq R t ht) i hi).hom
            ).app M ≫ (λ_ M).hom) ∧
      (∀ (M : Modules R)
          (hM : ∀ (U : Cᵒᵖ) (m : M.val.obj U), (@id (R.obj.obj U) (t.val U)) • m = 0)
          (i : ℤ) (hi : i ≤ 0),
        (phi M hM).inv.f i = (periodicTensorZeroXIso R M i hi).hom ≫ (λ_ M).inv ≫
          ((ordinaryTensor R).map (CochainComplex.scalarPeriodicXIso
            (exactScalarMultiplication R t) (exactScalarMultiplication_sq R t ht) i hi).inv
            ).app M ≫
          (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) M
            (exactScalarPeriodicComplex R t ht)).inv.f i) ∧
      (∀ (M N : Modules R)
          (hM : ∀ (U : Cᵒᵖ) (m : M.val.obj U), (@id (R.obj.obj U) (t.val U)) • m = 0)
          (hN : ∀ (U : Cᵒᵖ) (n : N.val.obj U), (@id (R.obj.obj U) (t.val U)) • n = 0)
          (f : M ⟶ N),
        ((totalTensor R).obj (exactScalarPeriodicComplex R t ht)).map
            ((HomologicalComplex.single _ (.up ℤ) 0).map f) ≫ (phi N hN).hom =
          (phi M hM).hom ≫ periodicTensorZeroMap R f) ∧
      (∀ (M : Modules R)
          (hM : ∀ (U : Cᵒᵖ) (m : M.val.obj U), (@id (R.obj.obj U) (t.val U)) • m = 0),
        (∀ q : ℕ, Nonempty ((CochainComplex.mapBifunctor (exactScalarPeriodicComplex R t ht)
          ((HomologicalComplex.single _ (.up ℤ) 0).obj M) (ordinaryTensor R)).homology
            (-(q : ℤ)) ≅ M)) ∧
        (∀ i : ℤ, 0 < i → IsZero ((CochainComplex.mapBifunctor
          (exactScalarPeriodicComplex R t ht)
          ((HomologicalComplex.single _ (.up ℤ) 0).obj M) (ordinaryTensor R)).homology i)) ∧
        (∀ (E : Modules R)
            (epsilon : exactScalarPeriodicComplex R t ht ⟶
              (HomologicalComplex.single _ (.up ℤ) 0).obj E)
            (hepsilon : CochainComplex.IsKFlatResolutionIndependentCoefficients epsilon),
          ∃ e : ((derivedTensor R).obj
            (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj E))).obj
              (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≅
            DerivedCategory.Q.obj (periodicTensorZeroComplex R M),
            ((derivedTensor R).map (DerivedCategory.Q.map epsilon)).app _ ≫ e.hom =
              ((ringed_kFlat_single_tensor_comparison R).choose
                (exactScalarPeriodicComplex R t ht) hepsilon.2 M).hom ≫
              DerivedCategory.Q.map
                ((CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) M
                  (exactScalarPeriodicComplex R t ht)).inv ≫ (phi M hM).hom))) := by
  sorry

end SheafOfModules
