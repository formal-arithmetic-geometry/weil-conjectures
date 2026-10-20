/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
public import Sheaf.Paper.ModuleCupResolutionData
import Sheaf.AlgebraicGeometry.ScalarCupModuleCupCompatibility
import Sheaf.AlgebraicGeometry.ScalarModuleCohomologyPullbackComparison

/-! # Scalar and module external cup comparison

Source: Stacks Project, Cohomology, Tags 01F7 and 0FKV; Varieties, Tag 0BED.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules

/-- The scalar Ext external cup is the signed module cup of the two pullbacks.
Source: Stacks Project, Cohomology, Tags 01F7 and 0FKV; Varieties, Tag 0BED.
(blueprint: lem-sc-scalar-external-cup-module-comparison).

Proof: Choose computing acyclic resolutions with a sectionwise tensor pairing for
both pulled-back coefficients and their tensor product. Represent the two module
cohomology classes by injective-resolution global cocycles. The normalization of
moduleExtEquiv identifies these classes with morphisms from the structure module,
evaluated at 1. The module pullback map is induced by the tensor-pullback adjunction
unit. Under exact restriction of scalars, this is the same morphism as the scalar
pullback coefficient, whose adjoint is that unit on every open. Thus scalar and
module pullback give the same underlying cohomology classes. On the computing
pairing, tensoring the two unit morphisms and composing with scalarTensorCoefficient
evaluates to the tensor of their sections: its pure-tensor formula is tmulSection.
The signed total tensor differential is the same in both constructions. Hence the
scalar Ext cup gives (-1)^(p*q) times the paired cocycle class. IsModuleCupProduct identifies
this class with cup of the module pullback classes. Resolution comparison and
homotopy independence remove the choices. This argument is valid in all natural
degrees; zero coefficients or an empty scheme give zero classes, and in degree
zero both sides tensor the pulled-back sections. No Cech cover is used. The cup
hypothesis below is the defining formula of
IsModuleCupProduct, expanded to avoid importing its unrelated existence proof. -/
theorem scalarExternalCup_moduleComparison
    {k : Type w} [Field k] {X Y : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (g : Y ⟶ Spec (CommRingCat.of k))
    (F : X.Modules) (G : Y.Modules) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace p).obj
        ((tensorPullback (pullback.fst f g)).obj F) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace q).obj
        ((tensorPullback (pullback.snd f g)).obj G) →ₗ[Γ(Limits.pullback f g, ⊤)]
      (RingedSpace.moduleCohomology (Limits.pullback f g).toRingedSpace (p + q)).obj
        (externalCupCoefficients f g F G))
    (hcup :
      ∀ (D : CupResolutionPairing
            ((tensorPullback (pullback.fst f g)).obj F)
            ((tensorPullback (pullback.snd f g)).obj G))
        (a : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor
          (Limits.pullback f g).toRingedSpace).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c)
    (x : scalarCohomology f F p) (y : scalarCohomology g G q) :
    externalCup f g F G p q x y =
      (-1 : ℤ) ^ (p * q) •
        cup (moduleCohomologyPullback (pullback.fst f g) F p x)
          (moduleCohomologyPullback (pullback.snd f g) G q y) := by
  have hx := scalar_moduleCohomologyPullback_comparison f (pullback.fst f g ≫ f)
    (pullback.fst f g) rfl F p x
  have hy := scalar_moduleCohomologyPullback_comparison g (pullback.fst f g ≫ f)
    (pullback.snd f g) pullback.condition.symm G q y
  unfold externalCup
  exact (scalarCup_moduleCup_compatibility (pullback.fst f g ≫ f) _ _
    p q cup hcup _ _).trans (congrArg (fun z ↦ (-1 : ℤ) ^ (p * q) • z)
      (congrArg₂ (fun a b ↦ cup a b) hx hy))

end AlgebraicGeometry.Scheme.Modules
