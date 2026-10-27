/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q109
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.AlgebraicGeometry.FittingIdealSheaf
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage

/-! # Bounded generators and the Fitting relation ideal under pullback

Source: Stacks Project, More on Algebra, Tag 07ZD; Divisors, Tags 0C3G and 0C3D
(blueprint: lem-sfb-bounded-generators-fitting-pullback-criterion).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The specified base-changed presentation for a ring map, with codomain the actual
extension-of-scalars module. It is the existing `LinearMap.baseChangePresentation`, using
this ring map as the algebra structure, so it sends a basis vector to `1 ⊗ π(eᵢ)`.
Source: Stacks Project, More on Algebra, Tags 07ZA(3), 07ZD; Divisors, Tag 0C3D
(blueprint: lem-sfb-bounded-generators-fitting-pullback-criterion). -/
noncomputable def fittingPullbackPresentation {R B : Type u} [CommRing R] [CommRing B]
    {M : Type u} [AddCommGroup M] [Module R M] {r : ℕ}
    (φ : R →+* B) (π : (Fin r → R) →ₗ[R] M) :
    (Fin r → B) →ₗ[B] (ModuleCat.extendScalars φ).obj (ModuleCat.of R M) :=
  letI := φ.toAlgebra
  π.baseChangePresentation B

/-- The bounded-generator Fitting criterion, including its affine relation-coordinate
calculation and the specified presentation after arbitrary pullback. Families with exactly
`r` entries encode at most `r` generators by padding with zeros. The ideal `J` is fixed by
its displayed equality, including the separate rank-zero convention.
Source: Stacks Project, More on Algebra, Tag 07ZD; Divisors, Tags 0C3G and 0C3D
(blueprint: lem-sfb-bounded-generators-fitting-pullback-criterion).

Proof plan:
1. If r = 0, local generation by the empty family and the sheaf axiom give E = 0.
   Tensor pullback of zero is zero, so it is free of rank zero and the zero ideal maps to zero.
2. Otherwise pad local generators with zeros and refine to affine opens. The tilde-Gamma
   adjunction (lem-weil-pbc-affine-tilde-gamma-adjunction), the finite-free tilde comparison
   (lem-weil-pbc-spec-tilde-free-module), and affine exactness
   (lem-weil-pbc-quasi-coherent-module-cokernel-image) give the section surjections π.
3. The affine-sections formula (lem-trf-fitting-ideal-sheaf-affine-sections) computes
   Fit_(r-1) by size-one minors, exactly the coordinates of kernel vectors. Independence
   (lem-trf-fitting-ideal-independence-base-change) removes the choice of π.
4. On every affine V mapping into U, tensor pullback identifies the restriction with
   the tilde of B tensor M (lem-trf-fitting-sheaf-arbitrary-pullback). The same presentation
   base-change theorem identifies the kernel-coordinate ideal with J(U)B. The ideal-sheaf
   pullback formula (lem-trf-fitting-ideal-sheaf-pullback) identifies these affine ideals
   with the image of the canonical map from h*J to O_T. No flatness is used.
5. If this ideal vanishes, every coordinate of every kernel vector vanishes. The specified
   base-changed surjection is therefore bijective, giving the free rank-r trivializations.
6. Conversely refine to affine opens trivializing h*E. Compute with the identity
   presentation of a free rank-r module: its kernel is zero. Presentation independence
   gives vanishing for the specified presentation. Vanishing glues by the sheaf axiom.
-/
theorem boundedGenerators_fitting_pullback_criterion (W : Scheme.{u}) (E : W.Modules)
    [E.IsFiniteType] [E.IsQuasicoherent] (r : ℕ)
    (hgen : ∀ x : W, ∃ U : W.Opens, x ∈ U ∧
      ∃ s : ULift.{u} (Fin r) → (E.over U).sections,
        Epi ((E.over U).freeHomEquiv.symm s)) :
    ∃ J : W.IdealSheafData,
      J = (if r = 0 then ⊥ else fittingIdealSheaf E (r - 1)) ∧
      J.toModules.IsQuasicoherent ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ W),
        ((tensorPullback h).obj E).IsFiniteLocallyFreeOfRank r ↔
          (tensorPullback h).map J.toModulesι ≫ tensorPullbackObjUnitToUnit h = 0) ∧
      (r = 0 → IsZero E ∧ ∀ (T : Scheme.{u}) (h : T ⟶ W),
        ((tensorPullback h).obj E).IsFiniteLocallyFreeOfRank 0 ∧
          (tensorPullback h).map J.toModulesι ≫ tensorPullbackObjUnitToUnit h = 0) ∧
      (0 < r →
        (∀ x : W, ∃ U : W.affineOpens, x ∈ U.1 ∧
          ∃ π : (Fin r → Γ(W, U.1)) →ₗ[Γ(W, U.1)] Γ(E, U.1),
            Function.Surjective π) ∧
        ∀ (U : W.affineOpens)
          (π : (Fin r → Γ(W, U.1)) →ₗ[Γ(W, U.1)] Γ(E, U.1)),
          Function.Surjective π →
          Nonempty (E.restrict U.2.fromSpec ≅
            tilde (ModuleCat.of Γ(W, U.1) Γ(E, U.1))) ∧
          J.ideal U = Ideal.span {a | ∃ z : Fin r → Γ(W, U.1),
            π z = 0 ∧ ∃ i : Fin r, z i = a} ∧
          J.ideal U = π.presentationFittingIdeal (r - 1) ∧
          ∀ (T : Scheme.{u}) (h : T ⟶ W) (V : T.affineOpens)
            (hVU : V.1 ≤ h ⁻¹ᵁ U.1),
            Nonempty (((tensorPullback h).obj E).restrict V.2.fromSpec ≅
              tilde ((ModuleCat.extendScalars (h.appLE U.1 V.1 hVU).hom).obj
                (ModuleCat.of Γ(W, U.1) Γ(E, U.1)))) ∧
            Function.Surjective (fittingPullbackPresentation (h.appLE U.1 V.1 hVU).hom π) ∧
            Ideal.span {b | ∃ z : Fin r → Γ(T, V.1),
              fittingPullbackPresentation (h.appLE U.1 V.1 hVU).hom π z = 0 ∧
                ∃ i : Fin r, z i = b} =
              Ideal.map (h.appLE U.1 V.1 hVU).hom (J.ideal U) ∧
            (fittingPullbackPresentation (h.appLE U.1 V.1 hVU).hom π).presentationFittingIdeal
                (r - 1) = Ideal.map (h.appLE U.1 V.1 hVU).hom (J.ideal U) ∧
            (Ideal.map (h.appLE U.1 V.1 hVU).hom (J.ideal U) = ⊥ →
              Function.Bijective (fittingPullbackPresentation (h.appLE U.1 V.1 hVU).hom π)) ∧
            (((tensorPullback h).obj E).IsFiniteLocallyFreeOfRank r →
              ∀ t : T, t ∈ V.1 → ∃ (V' : T.affineOpens) (hV'V : V'.1 ≤ V.1),
                t ∈ V'.1 ∧
                Nonempty (((tensorPullback h).obj E).restrict V'.1.ι ≅
                  SheafOfModules.free (R := V'.1.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) ∧
                Ideal.map (h.appLE U.1 V'.1 (hV'V.trans hVU)).hom (J.ideal U) = ⊥)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
