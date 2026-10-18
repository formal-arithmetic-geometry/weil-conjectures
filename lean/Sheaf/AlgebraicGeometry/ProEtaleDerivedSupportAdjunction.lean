/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q103
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleSupportedKernelComplex
public import Sheaf.AlgebraicGeometry.ProEtaleOpenUnitEvaluation
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Sheaf.CategoryTheory.KInjectiveTotalDerived
import Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.RingedSiteModules

/-!
# The supported-kernel adjunction and its unbounded derived counit

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
lem-exc-proetale-support-triangle, first and last sentences of the proof;
Stacks Project, Tags 08BJ, 070I, 070K, 070Y, 079P, 079Q and 015F
(blueprint: lem-exc-proetale-derived-adjunction-triangle).

The existing finiteSupportedKernel and finiteSupportedH constructions are reused.
All coefficients are left modules over the actual continuous-function ring sheaves,
including noncommutative finite rings. The open restriction hypothesis spells out
coefficient compatibility, naturality, and the normalization of the actual unit.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Closed pushforward is left adjoint to H = i* ker(1 → j*j*), with the specified
supported-kernel counit, and its termwise descent is left adjoint to the total right
derived H. The comparison beta computes RH on every K-injective complex. The final
isomorphism c is fixed by the exact-pushforward comparison and beta, and identifies
the derived counit with Q of the actual termwise sheaf counit.

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sf-localization,
lem-exc-proetale-support-triangle, first and last sentences of its proof;
Stacks Project, Tags 08BJ, 070I, 070K, 070Y, 079P, 079Q and 015F
(blueprint: lem-exc-proetale-derived-adjunction-triangle).

Proof:
1. Kernels are sectionwise by def-weil-sheaf-of-modules-category. The restriction
   hypothesis makes the open unit the identity on an object over U, using the
   base-change formula of def-weil-proetale-inverse-image. Thus j*F(N) = 0.
   The supported-unit assumption gives the natural isomorphism theta, whose
   components are exactly the closed units. Kernel maps and i* are additive by
   prop-weil-pbc-proetale-constant-exact, as in the existing F and H constructions.
2. For h:i*M → N, naturality of the open unit and j*i*M = 0 factor h uniquely
   through F(N). Full faithfulness of i* then gives the unique map M → H(N).
   Conversely compose i* of such a map with theta inverse and the kernel inclusion.
   Kernel uniqueness and full faithfulness show the two natural maps are inverse.
   The transpose of the identity is the asserted sheaf counit.
3. Lift the additive adjunction to complexes and homotopy categories by
   lem-weil-pbc-termwise-adjunction-homotopy. Its counit is the termwise chain map.
   Exactness of the left adjoint gives K-injectivity of H(I) by
   lem-weil-pbc-right-adjoint-preserves-kinjective, without boundedness assumptions.
4. Apply lem-weil-pbc-ring-sheaves-grothendieck on the small site models and
   lem-weil-pbc-kinjective-functorial-existence. Both module categories have enough
   K-injectives, also for noncommutative rings, by transport back to the original sites.
5. Additivity preserves the cone block differential, the inclusion, the negative
   projection, and the shifted differential. Hence the homotopy functor followed by Q
   is exact, by def-weil-abstract-derived-category, lem-pur-homotopy-category-triangulated
   and def-weil-triangulated-category. Apply lem-weil-pbc-kinjective-total-derived:
   RH exists with beta invertible on every K-injective I.
6. By lem-sf-exact-functor-derived-triangulated, exact i* has its termwise descent L
   and factorization a. For a complex M and K-injective I, identify Hom(L QM,QI)
   with Hom_K(i*M,I), then Hom_K(M,H(I)), then Hom_D(QM,QH(I)), using
   lem-weil-pbc-kinjective-hom-derived and the termwise homotopy adjunction.
   Postcomposition with beta_I gives Hom_D(QM,RH(QI)).
7. Naturality holds for chain maps and their homotopy classes. Every morphism
   between K-injectives is a unique such class. In the source variable, localization
   extends naturality to inverse quasi-isomorphisms. Every target has a K-injective
   representative, and transport is independent of that representative by naturality.
   Thus these are bifunctorial Hom bijections on the full derived categories.
8. The termwise counit transposes to the identity of H(I). Under the derived
   bijection its localized map, preceded by a, transposes to beta_I. Hence the
   derived counit is its composite with L(beta_I inverse). The inverse comparison
   a inverse followed by L(beta_I) is precisely c and gives the final two formulas.
   Step 2 identifies its degreewise arrows with the claimed kernel inclusions. -/
theorem finiteSupportedH_derivedAdjunction
    {T Z U : Scheme.{u}} (i : Z ⟶ T) (j : U ⟶ T)
    [IsLocallyNoetherian T] [CompactSpace T]
    [IsClosedImmersion i] [IsOpenImmersion j] [QuasiCompact j]
    (hU : Set.range j = (Set.range i)ᶜ)
    (A : Type (u + 1)) [Ring A] [Finite A]
    [TopologicalSpace A] [DiscreteTopology A]
    [PreservesFiniteLimits (finiteModulePushforward i A)]
    [PreservesFiniteColimits (finiteModulePushforward i A)]
    [(finiteModulePushforward i A).Full] [(finiteModulePushforward i A).Faithful]
    (hRestriction : ∃ d : (finiteCoefficientRingSheaf U A).obj ≅
        (Scheme.proEtaleOpenComposition j).op ⋙ (finiteCoefficientRingSheaf T A).obj,
      (∀ (W : U.ProEt) (a : A),
        (d.hom.app (op W)) ((finiteCoefficientScalarMap U A).app (op W) a) =
          (finiteCoefficientScalarMap T A).app
            (op ((Scheme.proEtaleOpenComposition j).obj W)) a) ∧
      ∃ rho : ∀ (N : FiniteCoefficientModules T A) (W : U.ProEt),
          ((finiteCoefficientModulePullback j A).obj N).val.obj (op W) ≃+
            N.val.obj (op ((Scheme.proEtaleOpenComposition j).obj W)),
        (∀ (N : FiniteCoefficientModules T A) (W : U.ProEt)
          (r : (finiteCoefficientRingSheaf U A).obj.obj (op W))
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N W (r • m) = (d.hom.app (op W) r) • rho N W m) ∧
        (∀ (N : FiniteCoefficientModules T A) (W W' : U.ProEt) (b : W' ⟶ W)
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N W' (((finiteCoefficientModulePullback j A).obj N).val.map b.op m) =
            N.val.map ((Scheme.proEtaleOpenComposition j).map b).op (rho N W m)) ∧
        (∀ (N N' : FiniteCoefficientModules T A) (h : N ⟶ N') (W : U.ProEt)
          (m : ((finiteCoefficientModulePullback j A).obj N).val.obj (op W)),
          rho N' W (((finiteCoefficientModulePullback j A).map h).val.app (op W) m) =
            h.val.app (op ((Scheme.proEtaleOpenComposition j).obj W)) (rho N W m)) ∧
        (∀ (N : FiniteCoefficientModules T A) (V : T.ProEt) (m : N.val.obj (op V)),
          rho N ((Scheme.proEtaleBaseChange j).obj V)
              (((finiteModuleAdjunction j A).unit.app N).val.app (op V) m) =
            N.val.map (Scheme.proEtaleOpenSectionProjection j V).op m))
    (hVanishing : ∀ M : FiniteCoefficientModules Z A,
      IsZero ((finiteCoefficientModulePullback j A).obj
        ((finiteModulePushforward i A).obj M)))
    (hSupported : ∀ N : FiniteCoefficientModules T A,
      IsZero ((finiteCoefficientModulePullback j A).obj N) →
        IsIso ((finiteModuleAdjunction i A).unit.app N)) :
    ∃ theta : finiteSupportedKernel j A ≅ finiteSupportedH i j A ⋙ finiteModulePushforward i A,
      (∀ N : FiniteCoefficientModules T A,
        theta.hom.app N =
          (finiteModuleAdjunction i A).unit.app ((finiteSupportedKernel j A).obj N)) ∧
      ∃ adj : finiteModulePushforward i A ⊣ finiteSupportedH i j A,
        (∀ N : FiniteCoefficientModules T A,
          adj.counit.app N = theta.inv.app N ≫
            kernel.ι ((finiteModuleAdjunction j A).unit.app N)) ∧
        ∃ (RH : FiniteCoefficientDerivedCategory T A ⥤ FiniteCoefficientDerivedCategory Z A)
          (beta : (finiteSupportedH i j A).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
            DerivedCategory.Q ⋙ RH),
          RH.IsRightDerivedFunctor beta
              (HomologicalComplex.quasiIso (FiniteCoefficientModules T A) (.up ℤ)) ∧
          ∃ derivedAdj : (finiteModulePushforward i A).mapDerivedCategory ⊣ RH,
            ∀ (I : CochainComplex (FiniteCoefficientModules T A) ℤ) [I.IsKInjective],
              CochainComplex.IsKInjective
                  (((finiteSupportedH i j A).mapHomologicalComplex (.up ℤ)).obj I) ∧
              IsIso (beta.app I) ∧
              ∃ c : DerivedCategory.Q.obj
                    (((finiteModulePushforward i A).mapHomologicalComplex (.up ℤ)).obj
                      (((finiteSupportedH i j A).mapHomologicalComplex (.up ℤ)).obj I)) ≅
                  (finiteModulePushforward i A).mapDerivedCategory.obj
                    (RH.obj (DerivedCategory.Q.obj I)),
                c.hom = (finiteModulePushforward i A).mapDerivedCategoryFactors.inv.app
                    (((finiteSupportedH i j A).mapHomologicalComplex (.up ℤ)).obj I) ≫
                  (finiteModulePushforward i A).mapDerivedCategory.map (beta.app I) ∧
                c.hom ≫ derivedAdj.counit.app (DerivedCategory.Q.obj I) =
                  DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app I) := by
  sorry

end AlgebraicGeometry.ProEtale
