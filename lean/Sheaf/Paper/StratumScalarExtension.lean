/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
public import Sheaf.Paper.ProEtaleLocallyConstantSheaf
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Sheaf.Algebra.Homology.ChangeOfRingsComplex
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses
import Sheaf.Paper.SfCommonStageWeilCohomology

/-!
# Stratum pullback and scalar-extension comparison

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
  sk-def-sp-scalar-extension/sk-def-sp-scalar-extension-functor.proof.md,
  proof paragraph (2), expanded constant-module pullback and stratum tensor comparison
(blueprint: lem-sp-stratum-scalar-extension).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme

/-- The map of constant coefficient rings induced by a unital map of rings.
Source: the coefficient comparison in the scalar-extension proof (blueprint:
`lem-sp-stratum-scalar-extension`). -/
noncomputable def proEtaleConstantRingMap {T : Scheme.{u}} {A B : Type u}
    [CommRing A] [CommRing B] (α : A →+* B) :
    proEtaleConstantRing T A ⟶ proEtaleConstantRing T B :=
  (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
    (CommRingCat.ofHom (RingHom.ulift α))

/-- The constant section represented by an element of the module, using the actual
simultaneous module sheafification unit.
Source: scalar-extension proof paragraph (2), constant module operations
(blueprint: lem-sp-stratum-scalar-extension). -/
noncomputable def stratumConstantModuleSection (T : Scheme.{u}) (A : Type u) [CommRing A]
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (U : T.ProEtᵒᵖ) (m : M) :
    (proEtaleConstantModuleSheaf T A M).val.obj U :=
  (CategoryTheory.toSheafify (ProEt.topology T)
    (proEtaleConstantModulePresheaf T.ProEt A M).presheaf).app U m

/-- The local unit `m ↦ 1 ⊗ m` of scalar extension, followed by sheafification.
Source: scalar-extension proof paragraph (2), termwise tensor comparison
(blueprint: lem-sp-stratum-scalar-extension). -/
noncomputable def stratumScalarExtensionUnitSection {T : Scheme.{u}} {A B : Type u}
    [CommRing A] [CommRing B] (α : A →+* B)
    (N : proEtaleRingModules T (proEtaleConstantRing T A)) (U : T.ProEtᵒᵖ)
    (m : N.val.obj U) :
    (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
      (proEtaleConstantRingMap (T := T) α) N).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T B))
      (𝟙 _)).unit.app
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := T) α) N)).app U)
          ((1 : (proEtaleConstantRing T B).obj.obj U) ⊗ₜ[_,
            ((proEtaleConstantRingMap (T := T) α).hom.app U).hom] m)

/-- Pullback of a finite constant module, scalar extension, K-flatness and cohomology
commute with an immersed stratum.  The proof follows the six steps in the blueprint
proof. First identify the coefficient ring via the constant-section comparison and
use exactness of coefficient pullback. Second, the constant-sheaf/global-sections
adjunction and uniqueness of left adjoints identify inverse image of constant sets,
with adjunct sending each constant section to itself. Third, naturality at addition,
negation, zero and the action, together with finite-product preservation, makes this
an isomorphism of module sheaves; the displayed adjunct equation fixes this canonical
isomorphism. Fourth, ringed-topos module tensor pullback, followed by the constant-B
comparison, gives the B-linear family β. On units it sends the pullback of `1 ⊗ m` to
`1 ⊗` the pullback unit of m, as displayed. Naturality in a module map gives the stated
square; apply it to every differential to get the displayed family of complex
isomorphisms with components β. Applied to each component of any cochain map the same square gives
naturality of this complex comparison. Fifth, ringed-topos K-flat pullback preserves
K-flatness and flat terms under the two hypotheses. Sixth, exact functor cohomology
identifies every cohomology object with pullback of the original cohomology object.
The cited dependency nodes provide the inverse-image, locally constant,
K-flat, flatness, tensor, and cohomology notions used here.
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
  sk-def-sp-scalar-extension/sk-def-sp-scalar-extension-functor.proof.md,
  proof paragraph (2) (blueprint: lem-sp-stratum-scalar-extension). -/
theorem stratumScalarExtension
    {T S : Scheme.{u}} (i : S ⟶ T) [IsImmersion i]
    (hi : Topology.IsConstructible (Set.range i)) (A B : Type u)
    [CommRing A] [CommRing B] [Finite A] [Finite B]
    (α : A →+* B)
    (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) [Finite M]
    (P : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
    (hP : CochainComplex.IsAcyclicTensorKFlat P)
    (hflat : ∀ n : ℤ,
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology T)
        (R := proEtaleConstantRing T A) (P.X n))
    (K : DerivedCategory (proEtaleRingModules T (proEtaleConstantRing T A)))
    (hK : ∀ q : ℤ,
      IsLocallyConstantProEtaleModuleSheaf S A
        (proEtaleConstantModulePullback i A
          ((DerivedCategory.homologyFunctor
            (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K)) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (y : Spec (.of Ω) ⟶ S),
        Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing S A)
          (proEtaleConstantModulePullback i A
            ((DerivedCategory.homologyFunctor
              (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K))))) :
    IsIso (proEtaleCoefficientInverseImageMap i A) ∧
    (∃ e : proEtaleConstantModulePullback i A
        (proEtaleConstantModuleSheaf T A M) ≅ proEtaleConstantModuleSheaf S A M,
      ∀ (U : T.ProEtᵒᵖ) (m : M),
        (((proEtaleConstantRingAdjunction A i).homEquiv _ _ e.hom).val.app U)
          (stratumConstantModuleSection T A M U m) =
        stratumConstantModuleSection S A M ((proEtaleBaseChange i).op.obj U) m) ∧
    CochainComplex.IsAcyclicTensorKFlat
      (((proEtaleConstantRingPullback A i).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) ∧
    (∀ n : ℤ,
      SheafOfModules.IsFlatOnSite.{u + 1, u, u + 1, u + 1} (J := ProEt.topology S)
        (R := proEtaleConstantRing S A)
        (HomologicalComplex.X (((proEtaleConstantRingPullback A i).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj P) n)) ∧
    (∃ β : ∀ N : proEtaleRingModules T (proEtaleConstantRing T A),
        proEtaleConstantModulePullback i B
          (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
            (proEtaleConstantRingMap (T := T) α) N) ≅
        SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := S) α) (proEtaleConstantModulePullback i A N),
      (∀ (N N' : proEtaleRingModules T (proEtaleConstantRing T A)) (f : N ⟶ N'),
        proEtaleConstantModulePullbackMap i B
            (SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
              (proEtaleConstantRingMap (T := T) α) N f) ≫
          (β N').hom =
        (β N).hom ≫ SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1}
          (proEtaleConstantRingMap (T := S) α) _ (proEtaleConstantModulePullbackMap i A f)) ∧
      (∀ (N : proEtaleRingModules T (proEtaleConstantRing T A))
          (U : T.ProEtᵒᵖ) (m : N.val.obj U),
        (((proEtaleConstantRingAdjunction B i).homEquiv _ _ (β N).hom).val.app U)
            (stratumScalarExtensionUnitSection α N U m) =
          stratumScalarExtensionUnitSection α (proEtaleConstantModulePullback i A N)
            ((proEtaleBaseChange i).op.obj U)
            (((proEtaleConstantRingAdjunction A i).unit.app N).val.app U m)) ∧
      (∃ e : ∀ Q : CochainComplex
          (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ,
          ((proEtaleConstantRingPullback B i).mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (SheafOfModules.changeOfRingsComplex.{u + 1, u}
              (proEtaleConstantRingMap (T := T) α) Q) ≅
          SheafOfModules.changeOfRingsComplex.{u + 1, u} (proEtaleConstantRingMap (T := S) α)
            (((proEtaleConstantRingPullback A i).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj Q),
        ∀ (Q : CochainComplex (proEtaleRingModules T (proEtaleConstantRing T A)) ℤ)
          (n : ℤ), (e Q).hom.f n = (β (Q.X n)).hom)) ∧
    (∀ q : ℤ, Nonempty (
      (DerivedCategory.homologyFunctor
        (proEtaleRingModules S (proEtaleConstantRing S A)) q).obj
        ((proEtaleConstantRingDerivedPullback A i).obj K) ≅
      (proEtaleConstantRingPullback A i).obj
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules T (proEtaleConstantRing T A)) q).obj K))) := by
  sorry

end AlgebraicGeometry.Scheme
