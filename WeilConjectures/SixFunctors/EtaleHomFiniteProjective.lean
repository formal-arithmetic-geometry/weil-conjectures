/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.FiniteProjective
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.TensorHom
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions

/-!
# Internal Hom with a finite projective etale module

The dual is ordinary sheaf Hom. Its evaluation is placed in degree zero and
transposed under the ambient derived tensor--Hom adjunction.
Source: latest blueprint, lem-sf-hom-finite-projective and companion proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.Etale


/-- The ordinary sheaf dual of a module sheaf. Source: def-pur-sheaf-hom
(blueprint: lem-sf-hom-finite-projective). -/
noncomputable def finiteProjectiveOrdinaryDual
    {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    (P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (ihom P).obj (𝟙_ _)

/-- The canonical tensor comparison for degree-zero etale sheaves. Source: the
ambient derived tensor construction (blueprint: lem-sf-hom-finite-projective). -/
noncomputable def finiteProjectiveSingleTensor
    {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    (P Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (DerivedCategory.singleFunctor _ 0).obj P ⊗
        (DerivedCategory.singleFunctor _ 0).obj Q ⟶
      (DerivedCategory.singleFunctor _ 0).obj (P ⊗ Q) :=
  (tensorIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app P)
    ((DerivedCategory.singleFunctorIsoCompQ _ 0).app Q)).hom ≫
  Functor.LaxMonoidal.μ DerivedCategory.Q
    ((CochainComplex.singleFunctor _ 0).obj P)
    ((CochainComplex.singleFunctor _ 0).obj Q) ≫
  DerivedCategory.Q.map
    ((CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) Q
      ((CochainComplex.singleFunctor _ 0).obj P)).hom ≫
      (HomologicalComplex.singleMapHomologicalComplex (tensorRight Q) (.up ℤ) 0).hom.app P) ≫
  (DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app (P ⊗ Q)

/-- Ordinary evaluation placed in the ambient derived category. Source: def-pur-sheaf-hom
(blueprint: lem-sf-hom-finite-projective). -/
noncomputable def finiteProjectiveDerivedEvaluation
    {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    (P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (DerivedCategory.singleFunctor _ 0).obj P ⊗
        (DerivedCategory.singleFunctor _ 0).obj (finiteProjectiveOrdinaryDual P) ⟶
      𝟙_ (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :=
  finiteProjectiveSingleTensor P (finiteProjectiveOrdinaryDual P) ≫
    (DerivedCategory.singleFunctor _ 0).map ((ihom.ev P).app (𝟙_ _)) ≫
    (DerivedCategory.singleFunctorObjUnitIso _).hom

/-- The evaluation-induced canonical map from the ordinary dual tensor to derived internal Hom.
Source: def-weil-derived-pullback-tensor-hom
(blueprint: lem-sf-hom-finite-projective). -/
noncomputable def finiteProjectiveTensorHomMap
    {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}
    (P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (N : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      ((DerivedCategory.singleFunctor _ 0).obj (finiteProjectiveOrdinaryDual P))).obj N ⟶
      ((derivedHom (ModuleCat.{u + 1} Λ) X).obj
        (op ((DerivedCategory.singleFunctor _ 0).obj P))).obj N :=
  MonoidalClosed.curry ((α_ ((DerivedCategory.singleFunctor _ 0).obj P)
      ((DerivedCategory.singleFunctor _ 0).obj (finiteProjectiveOrdinaryDual P)) N).inv ≫
    finiteProjectiveDerivedEvaluation P ▷ N ≫ (λ_ N).hom)

/-- Internal Hom with a locally finite projective module, including ordinary
biduality and naturality of the canonical comparison.
Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-sf-rf-shriek-preservation/lem-sf-hom-finite-projective.md and companion proof
(blueprint: lem-sf-hom-finite-projective).

Proof: Restrict to splitting covers; exact restriction detects derived isomorphisms.
For a finite free module the inverse sends h to the sum of dual basis vectors tensored
with their images under h, including the empty sum for rank zero. For a retract with
maps i and p, transport the inverse by dual(i) and Hom(p,-); the inverse equations
reduce to i followed by p being the identity. The same argument inverts ordinary
bidual evaluation. Tensor and Hom out of the module are locally retracts of finite
power functors, hence exact. Apply this to a K-flat model of N and its K-injective
resolution. The chain-level evaluation is an isomorphism and descends to precisely
finiteProjectiveTensorHomMap. Local inverses glue by uniqueness. The evaluation
formulas commute with maps of P and N and give both displayed naturality equations. -/
theorem hom_finite_projective
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
    (k : Type u) [Field k] {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) [HasInvertibleExponent Λ X]
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX]
    [HasCompactification aX]
    (P : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (_hP : IsFiniteProjectiveSheaf P)
    (N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (_hN : DerivedCategory.boundedConstructibleFiniteTor Λ X N) :
    IsIso (finiteProjectiveTensorHomMap P N) ∧
      IsIso (MonoidalClosed.toIhomIhomUnit P) ∧
      (∀ (P' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsFiniteProjectiveSheaf P' → ∀ (f : P ⟶ P'),
          (DerivedCategory.singleFunctor _ 0).map ((pre f).app (𝟙_ _)) ▷ N ≫
              finiteProjectiveTensorHomMap P N =
            finiteProjectiveTensorHomMap P' N ≫
              (pre ((DerivedCategory.singleFunctor _ 0).map f)).app N) ∧
      (∀ (N' : _root_.DerivedCategory
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))),
        DerivedCategory.boundedConstructibleFiniteTor Λ X N' → ∀ (g : N ⟶ N'),
          (DerivedCategory.singleFunctor _ 0).obj (finiteProjectiveOrdinaryDual P) ◁ g ≫
              finiteProjectiveTensorHomMap P N' =
            finiteProjectiveTensorHomMap P N ≫
              (ihom ((DerivedCategory.singleFunctor _ 0).obj P)).map g) := by
  sorry

end AlgebraicGeometry.Etale
