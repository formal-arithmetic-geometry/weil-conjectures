/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Sheaf.AlgebraicGeometry.EtaleDerivedTensorSymmetry
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.InvertibleFactorHomCancellation
public import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.KFlatTelescopeClosure
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! # Transport of evaluation biduality across an invertible twist

Source: Weil conjectures blueprint, sec-six-functors/sk-prop-sf-biduality-general,
proof paragraph 4, returned step 7
(blueprint: lem-sf-etale-twisted-bidual-transport).

The internal Hom is the existing closed derived internal Hom on ordinary constant-coefficient
etale sheaves. The braiding is the actual descended Koszul braiding. The two isomorphisms
in the conclusion are specified by evaluation equations, which uniquely determine them:
the first equation specifies alpha via t, and the second is the uncurrying of s gamma = u.

## Main definitions

- `CategoryTheory.TwistedBidualHomEvaluation`: the beta evaluation equation.
- `CategoryTheory.TwistedBidualTransportConclusion`: the three exact conclusion equations.
- `twistedBidualPullback`: a transparent abbreviation for existing derived inverse image.

## Main statement

- `etale_twisted_bidual_transport`: the ordinary-etale evaluation-bidual transport.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

/-- Evaluation normalization of the canonical internal-Hom comparison.
The tensor and Hom functors are explicit, so specialization retains their frozen
upstream instances instead of reducing alternative presentations of derived tensor.
Source: blueprint proof paragraph 4, returned step 7
(blueprint: lem-sf-etale-twisted-bidual-transport). -/
def TwistedBidualHomEvaluation {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    (TC : C ⥤ C ⥤ C) (HC : Cᵒᵖ ⥤ C ⥤ C)
    (TD : D ⥤ D ⥤ D) (HD : Dᵒᵖ ⥤ D ⥤ D)
    (adjC : ∀ X : C, TC.obj X ⊣ HC.obj (op X))
    (adjD : ∀ X : D, TD.obj X ⊣ HD.obj (op X)) (F : C ⥤ D)
    (μ : ∀ X Y : C, F.obj ((TC.obj X).obj Y) ≅ (TD.obj (F.obj X)).obj (F.obj Y))
    (B Ω : C) (b : F.obj ((HC.obj (op B)).obj Ω) ≅
      (HD.obj (op (F.obj B))).obj (F.obj Ω)) : Prop :=
  (μ B ((HC.obj (op B)).obj Ω)).hom ≫ (TD.obj (F.obj B)).map b.hom ≫
    (adjD (F.obj B)).counit.app (F.obj Ω) = F.map ((adjC B).counit.app Ω)

/-- The full three-equation conclusion, using the given tensor-Hom adjunctions.
The first two equations characterize alpha and gamma by uncurrying the canonical
invertible-factor maps t and s. They introduce no new comparison-map assumption.
Source: blueprint proof paragraph 4, returned step 7
(blueprint: lem-sf-etale-twisted-bidual-transport). -/
def TwistedBidualTransportConclusion {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    (TC : C ⥤ C ⥤ C) (HC : Cᵒᵖ ⥤ C ⥤ C)
    (TD : D ⥤ D ⥤ D) (HD : Dᵒᵖ ⥤ D ⥤ D)
    (adjC : ∀ X : C, TC.obj X ⊣ HC.obj (op X))
    (adjD : ∀ X : D, TD.obj X ⊣ HD.obj (op X))
    (σC : TC ≅ TC.flip) (σD : TD ≅ TD.flip)
    (aD : ∀ X Y Z : D, (TD.obj ((TD.obj X).obj Y)).obj Z ≅
      (TD.obj X).obj ((TD.obj Y).obj Z))
    (F : C ⥤ D) (K Ω : C) (W J : D) (θ : F.obj Ω ≅ (TD.obj W).obj J)
    (βK : F.obj ((HC.obj (op K)).obj Ω) ≅ (HD.obj (op (F.obj K))).obj (F.obj Ω))
    (βDK : F.obj ((HC.obj (op ((HC.obj (op K)).obj Ω))).obj Ω) ≅
      (HD.obj (op (F.obj ((HC.obj (op K)).obj Ω)))).obj (F.obj Ω)) : Prop :=
  ∃ α : F.obj ((HC.obj (op K)).obj Ω) ≅ (TD.obj ((HD.obj (op (F.obj K))).obj W)).obj J,
    ∃ γ : F.obj ((HC.obj (op ((HC.obj (op K)).obj Ω))).obj Ω) ≅
        (HD.obj (op ((HD.obj (op (F.obj K))).obj W))).obj W,
      (((adjD (F.obj K)).homEquiv _ _).symm
          (βK.hom ≫ (HD.obj (op (F.obj K))).map θ.hom) =
        (TD.obj (F.obj K)).map α.hom ≫
          (aD (F.obj K) ((HD.obj (op (F.obj K))).obj W) J).inv ≫
          (TD.map ((adjD (F.obj K)).counit.app W)).app J) ∧
      (((adjD ((TD.obj ((HD.obj (op (F.obj K))).obj W)).obj J)).homEquiv _ _).symm
          (βDK.hom ≫ (HD.map α.inv.op).app (F.obj Ω) ≫
            (HD.obj (op ((TD.obj ((HD.obj (op (F.obj K))).obj W)).obj J))).map θ.hom) =
        (TD.obj ((TD.obj ((HD.obj (op (F.obj K))).obj W)).obj J)).map γ.hom ≫
          (aD ((HD.obj (op (F.obj K))).obj W) J
            ((HD.obj (op ((HD.obj (op (F.obj K))).obj W))).obj W)).hom ≫
          (TD.obj ((HD.obj (op (F.obj K))).obj W)).map
            (((σD.app J).app ((HD.obj (op ((HD.obj (op (F.obj K))).obj W))).obj W)).hom) ≫
          (aD ((HD.obj (op (F.obj K))).obj W)
            ((HD.obj (op ((HD.obj (op (F.obj K))).obj W))).obj W) J).inv ≫
          (TD.map ((adjD ((HD.obj (op (F.obj K))).obj W)).counit.app W)).app J) ∧
      F.map ((adjC ((HC.obj (op K)).obj Ω)).homEquiv K Ω
        (((σC.app ((HC.obj (op K)).obj Ω)).app K).hom ≫ (adjC K).counit.app Ω)) ≫
          γ.hom =
        (adjD ((HD.obj (op (F.obj K))).obj W)).homEquiv (F.obj K) W
          (((σD.app ((HD.obj (op (F.obj K))).obj W)).app (F.obj K)).hom ≫
            (adjD (F.obj K)).counit.app W)

end CategoryTheory

namespace AlgebraicGeometry.Etale

variable (A : Type (u + 1)) [CommRing A]

/-- A transparent abbreviation for the existing derived inverse image, with no new choice.
Source: blueprint proof paragraph 4, returned step 7
(blueprint: lem-sf-etale-twisted-bidual-transport). -/
abbrev twistedBidualPullback {T V : Scheme.{u}} (g : T ⟶ V) :=
  (upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor

/-- Evaluation biduality commutes with inverse image and cancellation of a shifted line.
The cover is a trivialization as A-module sheaves, including the module action. The two
sheaf tensor inverses and arbitrary integer shift are retained. Exactness and strong
monoidality of ordinary inverse image are supplied by the imported upstream API; its
specified tensor comparison is used in both beta normalization hypotheses.

The tensor, Hom, adjunction and symmetry are the existing upstream functors and maps.
The associator witness is identified by heterogeneous equality with the canonical descended
associator. It is a conclusion, not an assumption or a freely chosen structural map.
The witnesses alpha and gamma are the specified canonical composites, not arbitrary
isomorphisms: the first equation uncurries alpha followed by t = beta followed by Hom(P,theta).
The second equation is uncurry(s gamma)=uncurry([alpha^{-1},theta] beta). Thus it uniquely
specifies gamma, since uncurry is bijective and s is invertible by tensor cancellation.

Source: blueprint proof paragraph 4, returned step 7
(blueprint: lem-sf-etale-twisted-bidual-transport).

Proof:
1. Trivialize Q on its etale cover. Its given sheaf inverse is trivial there too, so both
   sheaves are flat. Bounded-flat K-flatness (lem-pc-kflat-closure) computes the tensor of
   their one-term shifted complexes. Thus Qinv[-m] is a two-sided inverse of J=Q[m].
2. Apply lem-sf-ringed-derived-closed-symmetric-monoidal and the canonical factor maps of
   lem-sf-invertible-factor-hom-cancellation. Put P=F K, H=[P,W], b=[P,theta] betaK.
   Define alpha=t^{-1} b; this gives the first normalization in the conclusion.
3. Set u=[alpha^{-1},theta] betaDK and gamma=s^{-1} u. Uncurrying the equation s gamma=u
   gives the second normalization below, with associators and the Koszul braiding explicit.
4. Evaluation naturality, the two beta hypotheses, and the normalizations of t and s give
   theta F(e_K)=(e_P tensor 1_J)(1_H tensor sigma_{J,P})(alpha tensor 1_P), and
   theta F(e_DK)=(e_H tensor 1_J)(gamma tensor alpha), with associators inserted.
5. Apply F to the defining transpose equation for delta_K. Postcompose with theta and
   precompose with 1_P tensor alpha^{-1}. With f=gamma F(delta_K), the equations in step 4
   identify e_H(f tensor 1_H) tensor 1_J with
   (e_P tensor 1_J)(1_H tensor sigma_{J,P}) sigma_{P,H tensor J}.
   The hexagon and sigma_{J,P} sigma_{P,J}=1 make this
   (e_P sigma_{P,H}) tensor 1_J, including the signs for odd m.
6. Tensor with the inverse of J to cancel the common factor. The resulting equation says
   that f and delta'_P have identical uncurrying. The injectivity in
   lem-pod-closed-uncurry-laws gives the last equality. No bidual isomorphism is used.
-/
theorem etale_twisted_bidual_transport {T V : Scheme.{u}} (g : T ⟶ V)
    (W : DerivedCategoryModule A T) (Ω K : DerivedCategoryModule A V)
    (Q Qinv : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (_hline : ∃ cover : Scheme.Cover.{u} Scheme.etalePrecoverage T, ∀ i : cover.I₀,
      Nonempty ((upperStar (ModuleCat.{u + 1} A) (cover.f i)).obj Q ≅ 𝟙_ _))
    (_a : Q ⊗ Qinv ≅ 𝟙_ _) (_b : Qinv ⊗ Q ≅ 𝟙_ _)
    (m : ℤ) (J : DerivedCategoryModule A T)
    (_j : J ≅ ((_root_.DerivedCategory.singleFunctor _ 0).obj Q)⟦m⟧)
    (θ : (twistedBidualPullback A g).obj Ω ≅
      ((derivedTensor (ModuleCat.{u + 1} A) T).obj W).obj J)
    (βK : (twistedBidualPullback A g).obj
        (((derivedHom (ModuleCat.{u + 1} A) V).obj (op K)).obj Ω) ≅
      ((derivedHom (ModuleCat.{u + 1} A) T).obj
        (op ((twistedBidualPullback A g).obj K))).obj ((twistedBidualPullback A g).obj Ω))
    (βDK : (twistedBidualPullback A g).obj
        (((derivedHom (ModuleCat.{u + 1} A) V).obj
          (op (((derivedHom (ModuleCat.{u + 1} A) V).obj (op K)).obj Ω))).obj Ω) ≅
      ((derivedHom (ModuleCat.{u + 1} A) T).obj
        (op ((twistedBidualPullback A g).obj
          (((derivedHom (ModuleCat.{u + 1} A) V).obj (op K)).obj Ω)))).obj
            ((twistedBidualPullback A g).obj Ω))
    (_hβK : TwistedBidualHomEvaluation
      (derivedTensor (ModuleCat.{u + 1} A) V) (derivedHom (ModuleCat.{u + 1} A) V)
      (derivedTensor (ModuleCat.{u + 1} A) T) (derivedHom (ModuleCat.{u + 1} A) T)
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} A))
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} A)) (twistedBidualPullback A g)
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g) K Ω βK)
    (_hβDK : TwistedBidualHomEvaluation
      (derivedTensor (ModuleCat.{u + 1} A) V) (derivedHom (ModuleCat.{u + 1} A) V)
      (derivedTensor (ModuleCat.{u + 1} A) T) (derivedHom (ModuleCat.{u + 1} A) T)
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} A))
      (derivedTensorHomAdjunction (ModuleCat.{u + 1} A)) (twistedBidualPullback A g)
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) g)
      (((derivedHom (ModuleCat.{u + 1} A) V).obj (op K)).obj Ω) Ω βDK) :
    ∃ aT : ∀ X Y Z : DerivedCategoryModule A T,
        ((derivedTensor (ModuleCat.{u + 1} A) T).obj
          (((derivedTensor (ModuleCat.{u + 1} A) T).obj X).obj Y)).obj Z ≅
        ((derivedTensor (ModuleCat.{u + 1} A) T).obj X).obj
          (((derivedTensor (ModuleCat.{u + 1} A) T).obj Y).obj Z),
      (∀ X Y Z : DerivedCategoryModule A T,
        HEq (aT X Y Z)
          ((((DerivedMonoidal.associator DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (ComplexShape.up ℤ))).app
                X).app Y).app Z)) ∧
      TwistedBidualTransportConclusion
        (derivedTensor (ModuleCat.{u + 1} A) V) (derivedHom (ModuleCat.{u + 1} A) V)
        (derivedTensor (ModuleCat.{u + 1} A) T) (derivedHom (ModuleCat.{u + 1} A) T)
        (derivedTensorHomAdjunction (ModuleCat.{u + 1} A))
        (derivedTensorHomAdjunction (ModuleCat.{u + 1} A))
        (derivedTensorSymmetry (ModuleCat.{u + 1} A) V)
        (derivedTensorSymmetry (ModuleCat.{u + 1} A) T)
        aT (twistedBidualPullback A g) K Ω W J θ βK βDK := by
  sorry

end AlgebraicGeometry.Etale
