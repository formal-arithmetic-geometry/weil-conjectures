/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KummerLine.KummerLineGeometry
public import WeilConjectures.AlgebraicGeometry.KummerLine.KummerRootLineComputation

/-!
# Kummer computations with arbitrary finite ring coefficients

Source: blueprint thm-pur-kummer-affine-line, with the arbitrary-ring correction
of expert message 1385, answers 5–6 (2026-11-01).

The coefficient sheaf and insertions are the published Kummer module coefficient
functor. Multiplication on the coefficient ring gives its canonical ring action
on cohomology. Scalar extension uses `ModuleCat.extendScalars`, so no algebra
structure or flatness assumption is imposed on an arbitrary ring homomorphism.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.KummerLine

/-- The canonical homomorphism from the lifted residue ring to an annihilated ring.
Source: the coefficient convention in thm-pur-kummer-affine-line
(blueprint: thm-pur-kummer-affine-line). -/
def ringCoefficientScalar (m : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (m : A) = 0) : ULift.{u + 1} (ZMod m) →+* A :=
  (Scheme.finiteEtaleTwistScalar m A hA).comp ULift.ringEquiv.toRingHom

/-- A coefficient ring regarded as its canonical residue module, with no freeness assumption.
Source: def-pur-kummer-module-coefficients and the arbitrary-ring convention
(blueprint: thm-pur-kummer-affine-line). -/
def ringCoefficientModule (m : ℕ) (A : Type (u + 1)) [CommRing A]
    (hA : (m : A) = 0) : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)) :=
  (ModuleCat.restrictScalars (ringCoefficientScalar m A hA)).obj (ModuleCat.of A A)

/-- The existing abelian cohomology equipped with its canonical coefficient-ring action.
The action is induced by multiplication endomorphisms of the coefficient module.
Source: functoriality of cohomology in thm-pur-kummer-affine-line
(blueprint: thm-pur-kummer-affine-line). -/
def coefficientScalarAction (k : Type u) [Field k] (b : Bool)
    (m : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) (q : ℕ)
    (a : A) : CategoryTheory.End
      ((ModuleCat.restrictScalars (ringCoefficientScalar m A hA) ⋙
        Scheme.kummerAbelianTwist (curve k b) m ⋙
        Sheaf.functorH (curve k b).smallEtaleTopology q).obj (ModuleCat.of A A)) :=
  End.of ((ModuleCat.restrictScalars (ringCoefficientScalar m A hA) ⋙
    Scheme.kummerAbelianTwist (curve k b) m ⋙
    Sheaf.functorH (curve k b).smallEtaleTopology q).map
      (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) a)))

/-- The scalar action laws for the canonical multiplication endomorphisms.
The maps are the actual multiplication maps; the laws are the coefficient-functor
naturality needed to package them as a ring homomorphism.
Source: the `A`-module structure of `H^q(C, A(1))` in thm-pur-kummer-affine-line and the
coefficient functoriality of def-pur-kummer-module-coefficients
(blueprint: thm-pur-kummer-affine-line).

Proof: `a ↦ H^q(1 ⊗ (a·))` sends `1` to the identity and products to composites because
the composite coefficient functor preserves identities and composition; it is additive
because restriction of scalars, the sheafified tensor `μ_m ⊗ -`, the forgetful functor and
`H^q` are additive functors. -/
theorem coefficientScalarRingHom_exists (k : Type u) [Field k] (b : Bool)
    (m : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) (q : ℕ) :
    ∃ h : A →+* CategoryTheory.End
      ((ModuleCat.restrictScalars (ringCoefficientScalar m A hA) ⋙
        Scheme.kummerAbelianTwist (curve k b) m ⋙
        Sheaf.functorH (curve k b).smallEtaleTopology q).obj (ModuleCat.of A A)),
      ∀ a : A, h a = coefficientScalarAction k b m A hA q a := by
  let F := ModuleCat.restrictScalars (ringCoefficientScalar m A hA) ⋙
    Scheme.kummerAbelianTwist (curve k b) m ⋙
    Sheaf.functorH (curve k b).smallEtaleTopology q
  have : (Scheme.kummerAbelianTwist (curve k b) m).Additive := by
    unfold Scheme.kummerAbelianTwist Scheme.kummerModuleTwist
    infer_instance
  refine ⟨{ toFun := coefficientScalarAction k b m A hA q
            map_one' := ?_
            map_mul' := ?_
            map_zero' := ?_
            map_add' := ?_ }, fun _ => rfl⟩
  · apply End.ext
    change F.map (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) 1)) = 𝟙 _
    convert F.map_id (ModuleCat.of A A) using 1
    congr 1
    ext
    simp [LinearMap.lsmul_apply]
  · intro a c
    apply End.ext
    change F.map (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) (a * c))) =
      F.map (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) c)) ≫
        F.map (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) a))
    rw [← F.map_comp]
    congr 1
    ext
    simp [LinearMap.lsmul_apply]
  · apply End.ext
    change F.map (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) 0)) = 0
    convert F.map_zero (ModuleCat.of A A) (ModuleCat.of A A) using 1
    congr 1
    ext
    simp
  · intro a c
    apply End.ext
    change F.map (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) (a + c))) =
      F.map (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) a)) +
        F.map (ModuleCat.ofHom (LinearMap.lsmul A (ModuleCat.of A A) c))
    rw [← F.map_add]
    congr 1
    ext
    simp [LinearMap.lsmul_apply]

/-- The existing abelian cohomology equipped with its canonical coefficient-ring action.
Source: functoriality of cohomology in thm-pur-kummer-affine-line
(blueprint: thm-pur-kummer-affine-line). -/
noncomputable def ringCoefficientCohomology (k : Type u) [Field k] (b : Bool)
    (m : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) (q : ℕ) :
    ModuleCat.{u + 1} A :=
  ModuleCat.mkOfSMul (Classical.choose
    (coefficientScalarRingHom_exists k b m A hA q))

/-- The ordinary residue-cohomology tensor coefficient ring, viewed as an `A`-module.
The tensor factors appear in the order `A ⊗_R H`; symmetry gives the paper's `H ⊗_R A`.
Source: the coefficient comparison in thm-pur-kummer-affine-line
(blueprint: thm-pur-kummer-affine-line). -/
def ringCoefficientTensor (k : Type u) [Field k] (b : Bool)
    (m : ℕ) (A : Type (u + 1)) [CommRing A] (hA : (m : A) = 0) (q : ℕ) :
    ModuleCat.{u + 1} A :=
  (ModuleCat.extendScalars (ringCoefficientScalar m A hA)).obj
    (ModuleCat.of (ULift.{u + 1} (ZMod m))
      (Sheaf.H ((curve k b).rootsOfUnitySheaf m) q))

end AlgebraicGeometry.KummerLine
