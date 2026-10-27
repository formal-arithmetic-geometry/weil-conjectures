/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
public import Sheaf.AlgebraicGeometry.SmoothTensorDuality
public import Sheaf.Paper.NoetherianEtaleSectionSpecialization
public import Sheaf.AlgebraicGeometry.EtaleSupportMapCompatibility
public import Sheaf.AlgebraicGeometry.VectorBundleIntegration
public import Sheaf.Targets.VectorBundlePurity
public import Sheaf.Paper.FiniteSmoothGammaConstructions
import Sheaf.Paper.FiniteSmoothDiagonalNormalization
import Sheaf.Paper.FiniteSmoothDeformationNormalization
import Sheaf.Paper.FiniteSmoothTensorNormalization

/-! # Normalization of the three-factor orientation in dimension zero -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

noncomputable section

namespace AlgebraicGeometry.Etale

/-- Every factor of the geometric orientation is the identity in the specified
adjunction-preserving coordinates. Gamma is rho inverse, and its adjunct is precisely
the sum/evaluation counit transported by the graph-normalized comparison.
Source: sk-thm-smooth-purity, three-factor formula at d=0
(blueprint: lem-pur-finite-smooth-gamma-normalization).

Proof:
1. Use quasifiniteCompactSupportExact and etaleSupportMapCompatibility to identify R e_!
   with exact sum extension by graph extension and the total-derived unit. Transport the
   sum adjunction and apply the Hom bijections to its counit. Adjoint uniqueness gives rho
   and the counit equation, including omega_e = A_V in these coordinates.
2. The etale diagonal is a clopen section of p_1. Its ideal is zero on its image and the
   unit ideal on its complement V_0. It is regular of codimension zero, and the actual
   normal projection is an isomorphism with zero section its inverse.
3. The specified compact-support exchange becomes the sum exchange. The latter's
   unit--exchange--counit formula and both triangle identities identify the exceptional
   mate with the pullback compositor. Restrict by Delta: the first coordinate equation.
4. Compute the actual Rees algebra on both clopen pieces: O_X[t] and O_{V_0}[t,t^-1].
   Thus D = A1_X disjoint union (V_0 times Gm), preserving parameter and section. The
   fibres are (W,Delta) at one and (X,id) at zero.
5. These spaces and maps are Noetherian, separated, etale and finite type. Open-subscheme
   and base-change permanence give these assertions on the punctured second component;
   Nagata supplies compactifiability, including that required by the deformation family.
6. In the coordinates of Step 1 the family and both specified fibre mates are constant
   identities. Uniqueness of kappa normalized at one therefore makes its zero reading
   the identity: the second coordinate equation.
7. Rank-zero integration is the identity trace and its purity adjunct is the identity.
   Transport through the actual normal projection and zero section gives the third
   coordinate equation. The composite orientation is consequently rho at the unit.
8. The specified projection map becomes the sum projection, on a generator sending
   (s,m) tensor k to (s,m tensor s^*k). Its inverse uses the natural signed symmetry;
   on the coefficient unit in degree zero that sign is one. Sum extension preserves
   flat and K-flat complexes, so the calculation descends for all unbounded K.
9. Under rho, the transpose of the canonical tensor map is tensoring with evaluation
   and then evaluating. Insert alpha inverse: on every summand the result is precisely
   evaluation. Adjunction bijectivity gives gamma = rho inverse, and its displayed
   adjunct is the actual sum counit, with the exact/left-derived inverse-image transport.
-/
theorem finite_smooth_gamma_normalization
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : ∀ x : X, IsUnit (ell : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (f : X ⟶ Y) [Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (N : FiniteSmoothCompactSupportComparisons (NoetherianSectionSpecialization.Coeff ell n))
    (hN : FiniteSmoothComparisonNormalized (NoetherianSectionSpecialization.Coeff ell n) N) :
    ∃ (G : FiniteSmoothGammaData (NoetherianSectionSpecialization.Coeff ell n) f)
      (α : dualizingComplex (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) f ≅
        MonoidalCategoryStruct.tensorUnit
          (DerivedCategoryModule (NoetherianSectionSpecialization.Coeff ell n) X)),
      α.hom = finiteSmoothDiagonalFactor _ f ≫ finiteSmoothDeformationFactor _ f G ≫
        finiteSmoothRankZeroFactor _ f G ∧
      finiteSmoothDiagonalFactor _ f ≫
          (finiteSmoothSectionCoordinates _ N (pullback.fst f f) (pullback.diagonal f)).hom =
        (finiteSmoothOmegaCoordinates _ N f).hom ∧
      finiteSmoothDeformationFactor _ f G ≫ (finiteSmoothNormalCoordinates _ N f G).hom =
        (finiteSmoothSectionCoordinates _ N (pullback.fst f f) (pullback.diagonal f)).hom ∧
      finiteSmoothRankZeroFactor _ f G = (finiteSmoothNormalCoordinates _ N f G).hom ∧
      α = finiteSmoothOmegaCoordinates _ N f ∧
      ∀ K : DerivedCategoryModule (NoetherianSectionSpecialization.Coeff ell n) Y,
        finiteSmoothGammaMap _ f α K = (finiteSmoothAdjointCoordinates _ N f).inv.app K ∧
        ((rightDerivedUpperShriekAdjunction
          (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) f).homEquiv _ K).symm
            (finiteSmoothGammaMap _ f α K) =
          (finiteSmoothSumComparison _ N f).hom.app _ ≫
            (etaleLowerShriek
              (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) f
              inferInstance).mapDerivedCategory.map
                ((leftDerivedUpperStarIsoMapDerivedCategory
                  (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) f).hom.app K) ≫
            ((etaleLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) f
              inferInstance).mapDerivedCategoryAdjunction).counit.app K := by
  obtain ⟨G, hdeformation, hrank⟩ :=
    finiteSmoothDeformation_coordinates ell n hn hX hY f N hN
  have hdiagonal := finiteSmoothDiagonal_coordinates ell n hn hX hY f N hN
  refine ⟨G, finiteSmoothOmegaCoordinates _ N f, ?_, hdiagonal,
    hdeformation, hrank, rfl, ?_⟩
  · rw [hrank, hdeformation, hdiagonal]
  · intro K
    have htensor := finiteSmoothTensor_coordinates ell n hn hX hY f N hN K
    refine ⟨htensor, ?_⟩
    rw [htensor]
    let adj := rightDerivedUpperShriekAdjunction
      (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) f
    let sumAdj := (etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) f
      inferInstance).mapDerivedCategoryAdjunction
    let c := finiteSmoothSumComparison _ N f
    let i := leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{u + 1} (NoetherianSectionSpecialization.Coeff ell n)) f
    let adj' := sumAdj.ofNatIsoLeft c.symm
    have hc := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app adj' adj K
    rw [← Adjunction.rightAdjointUniq_inv_app] at hc
    change (adj.homEquiv _ K).symm
      (i.hom.app K ≫ (adj.rightAdjointUniq adj').inv.app K) = _
    rw [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
    rw [← Adjunction.homEquiv_symm_apply, hc]
    change _ ≫ (c.hom.app _ ≫ sumAdj.counit.app K) = _
    rw [← Category.assoc, c.hom.naturality, Category.assoc]

end AlgebraicGeometry.Etale
