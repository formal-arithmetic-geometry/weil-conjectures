/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FlatProjectiveHilbertPolynomialLocality
public import WeilConjectures.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistTensor
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
import WeilConjectures.AlgebraicGeometry.ProjectiveClosedSubschemeHomogeneousIdeal
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Modules.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelSum
import WeilConjectures.AlgebraicGeometry.FreeQuotientKernelRegularityBound
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.MRegularConsequences
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.PicardPn
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.NagataAffineProjScalarExtension
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Uniform regularity and vanishing for projective closed subschemes

Source: Stacks Project, varieties.tex, Tags 08AG, 08A6, 08AE; coherent.tex, Tag 01XT
(blueprint: lem-sfb-uniform-projective-fibre-vanishing).

The polynomial arrows below are normalized on each standard chart. In particular the
right arrow is restriction of homogeneous polynomials, with no arbitrary choice of map.
Cohomology is the right derived functor in module sheaves.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.UniformProjectiveFibreVanishing

noncomputable section

/-- Module cohomology with scalars restricted along the specified field structure map.
Source: Stacks, Tag 01DZ (blueprint: lem-sfb-uniform-projective-fibre-vanishing). -/
def cohomology (k : Type u) [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    (F : X.Modules) (j : ℕ) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom).obj
    ((RingedSpace.moduleCohomology X.toRingedSpace j).obj F)

/-- The canonical degree-zero cohomology-to-sections identification. Its underlying
function is used to specify the chart values of the polynomial arrows.
Source: Stacks, Tag 01DZ (blueprint: lem-sfb-uniform-projective-fibre-vanishing). -/
def zeroSections {X : Scheme.{u}} (F : X.Modules) :
    (RingedSpace.moduleCohomology X.toRingedSpace 0).obj F ≅
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj F :=
  letI : PreservesFiniteLimits (RingedSpace.globalSectionsFunctor X.toRingedSpace) :=
    inferInstanceAs (PreservesFiniteLimits
      (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op ⊤)))
  (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedZeroIsoSelf.app F

/-- A uniform positive bound on ideal regularity, both higher-cohomology vanishings,
and the canonical exact finite-dimensional polynomial restriction sequence.

Source: Stacks, Tags 08AG, 08A6, 08AE and 01XT
(blueprint: lem-sfb-uniform-projective-fibre-vanishing).

Proof (the five DAG steps, for stage 3):
1. Identify the base-change projective space with Proj(k[x]) using
   lem-nagata-affine-proj-scalar-extension and lem-weil-pbc-polynomial-scalar-extension.
   The chart fractions and twists agree. The homogeneous-ideal presentation
   lem-sfb-projective-closed-subscheme-homogeneous-ideal identifies the actual coordinate
   ideal. The field coordinate--Euler comparison
   lem-sfb-projective-field-coordinate-euler-polynomial gives properness, Noetherianity,
   coherence and P(t)=chi(Z,O_Z(t)) for every integer t. Closed-immersion coherent
   cohomology and coherent-kernel closure give coherence of the actual ideal J and the
   exact sequence 0 -> J -> O -> i_*O_Z -> 0.
2. Closed-immersion projection and cohomology identify chi(i_*O_Z(t)) with P(t).
   Apply lem-sfb-free-quotient-kernel-regularity-bound at rank one and set m=max(1,a).
   The upward clause of lem-sfb-m-regular-coherent-sheaf-consequences makes J m-regular.
3. Tensor the ideal sequence by O(d); this preserves exactness since each twist has its
   specified free rank-one basis on every standard chart. The projection isomorphism
   identifies the last term with i_*O_Z(d), and the map is restriction of functions.
4. For d>=m, regularity consequences kill all positive cohomology of J(d). The projective
   twist computation sk-thm-picard-pn kills all positive cohomology of O(d). Its canonical
   polynomial section map is injective by dehomogenization on U_0 and bijective by the
   monomial dimension count. The long exact sequence of
   lem-sfb-closed-immersion-cokernel-cohomology kills positive cohomology on Z and gives
   the stated exact sequence. Its arrows have exactly the chart values specified below.
5. The middle space has its finite monomial basis; its subspace and quotient are finite
   dimensional. Positive-degree vanishing reduces the Euler characteristic to degree
   zero, hence its dimension is P(d). In dimension zero the regularity range is empty.
   For empty Z, J=O and P=0, so the sequence is the monomial identification. Unrealizable
   polynomials give a vacuous assertion. All bounds depend only on n and P. -/
theorem exists_uniform_projective_fibre_vanishing (n : ℕ) (P : Polynomial ℚ)
    (hP : ∃ N : ℕ, ∀ d : ℕ, N ≤ d → ∃ z : ℤ, P.eval (d : ℚ) = (z : ℚ)) :
    ∃ m : ℤ, 1 ≤ m ∧ ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (Z : Scheme.{u}) (i : Z ⟶ ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))),
      IsClosedImmersion i → ProjectiveHilbertPolynomial.IsCoordinatePolynomial k n i P →
      RingedSpace.IsCoherent
        ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace i.ker.toModules ∧
      (∀ j : ℕ, 1 ≤ j → j ≤ n →
        Subsingleton ((RingedSpace.moduleCohomology
          ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace j).obj
          (i.ker.toModules ⊗ₘ ProjectiveSpace.twist
            (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (m - (j : ℤ))))) ∧
      ∀ d : ℤ, m ≤ d →
        (∀ j : ℕ, 0 < j →
          Subsingleton ((RingedSpace.moduleCohomology
            ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace j).obj
            (i.ker.toModules ⊗ₘ ProjectiveSpace.twist
              (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)) ∧
          Subsingleton ((RingedSpace.moduleCohomology Z.toRingedSpace j).obj
            ((Scheme.Modules.tensorPullback i).obj (ProjectiveSpace.twist
              (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)))) ∧
        Module.Finite k (cohomology k
          (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k))
          (i.ker.toModules ⊗ₘ ProjectiveSpace.twist
            (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d) 0) ∧
        Module.Finite k
          (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k d.toNat) ∧
        Module.Finite k (cohomology k
          (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)))
          ((Scheme.Modules.tensorPullback i).obj (ProjectiveSpace.twist
            (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)) 0) ∧
        (Module.finrank k (cohomology k
          (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)))
          ((Scheme.Modules.tensorPullback i).obj (ProjectiveSpace.twist
            (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)) 0) : ℚ) = P.eval (d : ℚ) ∧
        ∃ σ : ModuleCat.of k
            (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k d.toNat) ≅
            cohomology k (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k))
              (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d) 0,
          (∀ F : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k d.toNat,
            ∀ a : ULift.{u} (Fin (n + 1)),
              (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d).presheaf.map
                (homOfLE le_top).op
                ((zeroSections (ProjectiveSpace.twist
                  (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)).hom (σ.hom F)) =
              ProjectiveSpace.chartRingEquiv _ k a (MvPolynomial.dehomogenizeX k a F.val) •
                ProjectiveSpace.twistGenerator _ (Spec (.of k)) d a) ∧
          ∃ β : ModuleCat.of k
              (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k d.toNat) ⟶
              cohomology k
                (i ≫ (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)))
                ((Scheme.Modules.tensorPullback i).obj (ProjectiveSpace.twist
                  (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)) 0,
            (∀ F : MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k d.toNat,
              ∀ a : ULift.{u} (Fin (n + 1)),
                ((Scheme.Modules.tensorPullback i).obj (ProjectiveSpace.twist
                  (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)).presheaf.map
                    (homOfLE le_top).op
                    ((zeroSections ((Scheme.Modules.tensorPullback i).obj
                      (ProjectiveSpace.twist
                        (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d))).hom (β F)) =
                Scheme.Modules.tensorPullbackSection i
                  (ProjectiveSpace.twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)
                  (ProjectiveSpace.standardOpen _ (Spec (.of k)) a)
                  (ProjectiveSpace.chartRingEquiv _ k a
                    (MvPolynomial.dehomogenizeX k a F.val) •
                      ProjectiveSpace.twistGenerator _ (Spec (.of k)) d a)) ∧
            Function.Injective
              (((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
                  (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)).appTop).hom).map
                ((RingedSpace.moduleCohomology
                  ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace 0).map
                    (i.ker.toModulesι ▷ ProjectiveSpace.twist
                      (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d ≫
                    (λ_ (ProjectiveSpace.twist
                      (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)).hom))) ≫ σ.inv) ∧
            Function.Exact
              (((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫
                  (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)).appTop).hom).map
                ((RingedSpace.moduleCohomology
                  ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace 0).map
                    (i.ker.toModulesι ▷ ProjectiveSpace.twist
                      (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d ≫
                    (λ_ (ProjectiveSpace.twist
                      (ULift.{u} (Fin (n + 1))) (Spec (.of k)) d)).hom))) ≫ σ.inv) β ∧
            Function.Surjective β := by
  sorry

end

end AlgebraicGeometry.UniformProjectiveFibreVanishing
