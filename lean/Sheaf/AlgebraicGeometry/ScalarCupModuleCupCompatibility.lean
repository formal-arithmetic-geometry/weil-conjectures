/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Sheaf.Paper.ModuleCupResolutionData
import Sheaf.Paper.ModuleCupPairingExists
import Sheaf.AlgebraicGeometry.ScalarCupResolutionClassCompatibility

/-! # Scalar and module cup compatibility

Source: Stacks Project, Cohomology, section-cup-product and Tag 0FKV.
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

private theorem cupCycleClass_surjective_local {R : Type w} [Ring R]
    (K : CochainComplex (ModuleCat.{w} R) ℕ) (n : ℕ) :
    Function.Surjective (cupCycleClass K n) := by
  exact (ModuleCat.epi_iff_surjective
    ((K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ)).mp inferInstance

private theorem cupPair_exists_cycle_local {X : Scheme.{w}} {F G : X.Modules}
    (D : CupResolutionPairing F G) (p q : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
    (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K) :
    ∃ c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K,
      c.val = D.pair p q ⊤ a.val b.val := by
  have ha := a.property
  have hb := b.property
  change (D.left.K.d p ((ComplexShape.up ℕ).next p)).val.app (op ⊤) a.val = 0 at ha
  change (D.right.K.d q ((ComplexShape.up ℕ).next q)).val.app (op ⊤) b.val = 0 at hb
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel p (p + 1))] at ha
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel q (q + 1))] at hb
  refine ⟨⟨D.pair p q ⊤ a.val b.val, ?_⟩, rfl⟩
  change (D.target.K.d (p + q) ((ComplexShape.up ℕ).next (p + q))).val.app (op ⊤)
    (D.pair p q ⊤ a.val b.val) = 0
  rw [ComplexShape.next_eq' (ComplexShape.up ℕ) (by simp :
    (ComplexShape.up ℕ).Rel (p + q) (p + q + 1))]
  rw [D.leibniz, ha, hb]
  simp

private theorem cupResolutionClass_surjective_local {X : Scheme.{w}} {F : X.Modules}
    (D : CupAcyclicResolution F) (n : ℕ) : Function.Surjective (D.class n) := by
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let T := (RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
    (ComplexShape.up ℕ)
  have : IsIso (HomologicalComplex.homologyMap (T.map D.comparison) n) := D.computes n
  exact ((ModuleCat.epi_iff_surjective
    (D.I.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) n).inv).mp
      inferInstance).comp
    (((ModuleCat.epi_iff_surjective
      (HomologicalComplex.homologyMap (T.map D.comparison) n)).mp inferInstance).comp
        (cupCycleClass_surjective_local (T.obj D.K) n))


/-- The scalar Ext cup is `(-1)^(p*q)` times the cup computed by acyclic resolutions.
Source: Stacks Project, Cohomology, section-cup-product and Tag 0FKV.
(blueprint: lem-sc-scalar-cup-module-cup-compatibility).

Proof: Choose acyclic resolutions with a sectionwise tensor pairing extending the
augmentation tensor map. Represent the two module cohomology classes by cycles in
these resolutions. Evaluation at 1 identifies the module Hom complex from the unit
with its sections complex. Exact restriction to k and precomposition by the scalar
unit identify these cycles with the classes under scalarCohomologyExtEquiv. The
Yoneda tensor pairing is represented by the signed total tensor of the two cycles.
Its augmentation coefficient is scalarTensorCoefficient, which sends pure tensors
of sections to tmulSection. Thus this pairing is exactly the module resolution
pairing, with the additional factor `(-1)^(p*q)` from extracting the left shift
before the right shift. Apply IsModuleCupProduct to the paired cycle. Its signed
target class is the scalar cup by the preceding identification. The
resolution comparison maps and homotopy independence ensure that this conclusion
is independent of all chosen resolutions and representatives. No pullback is used.
In degree zero this is the pure tensor of sections; empty schemes and zero
coefficients have zero classes and the same identities. The cup hypothesis below
is the defining formula of IsModuleCupProduct, expanded to avoid importing its
unrelated existence proof. -/
theorem scalarCup_moduleCup_compatibility
    {k : Type w} [Field k] {X : Scheme.{w}}
    (f : X ⟶ Spec (CommRingCat.of k)) (F G : X.Modules) (p q : ℕ)
    (cup : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace q).obj G →ₗ[Γ(X, ⊤)]
      (RingedSpace.moduleCohomology X.toRingedSpace (p + q)).obj
        (@id X.Modules (F ⊗ G)))
    (hcup :
      ∀ (D : CupResolutionPairing F G)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc p).moduleCatLeftHomologyData.K)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc q).moduleCatLeftHomologyData.K)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc (p + q)).moduleCatLeftHomologyData.K),
        c.val = D.pair p q ⊤ a.val b.val →
          cup (D.left.class p a) (D.right.class q b) = D.target.class (p + q) c)
    (a : scalarCohomology f F p) (b : scalarCohomology f G q) :
    scalarCohomologyCup f F G p q a b =
      (-1 : ℤ) ^ (p * q) • cup a b := by
  obtain ⟨D⟩ := exists_moduleCupResolutionPairing F G
  obtain ⟨a', ha⟩ := cupResolutionClass_surjective_local D.left p a
  obtain ⟨b', hb⟩ := cupResolutionClass_surjective_local D.right q b
  rw [← ha, ← hb]
  obtain ⟨c', hc'⟩ := cupPair_exists_cycle_local D p q a' b'
  have hcup' := hcup D a' b' c' hc'
  rw [hcup']
  exact scalarCup_resolution_class_compatibility f F G p q D a' b' c' hc'



end AlgebraicGeometry.Scheme.Modules
