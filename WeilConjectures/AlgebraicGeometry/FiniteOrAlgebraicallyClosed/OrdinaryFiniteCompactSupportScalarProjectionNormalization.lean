/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteExceptionalTensor.FiniteExceptionalCoefficientTensor

/-! # Ordinary finite-coefficient compact-support scalar normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.FiniteExceptionalTensor
open scoped CategoryTheory.Functor

attribute [local instance 2000] CommRing.toRing isNoetherian_of_finite
attribute [local instance 10000] finiteProjection_groupW finiteProjection_groupSheafify
  finiteProjection_moduleSheafify finiteProjection_sheafGroth finiteProjection_functorLimits
  finiteProjection_functorColimits finiteProjection_inverseAdditive finiteProjection_inverseLimits
  finiteProjection_inverseColimits finiteProjection_moduleGroth finiteProjection_modulePreadditive
  finiteProjection_moduleFlat finiteProjection_upperFlat


namespace AlgebraicGeometry.ProEtale.FiniteOrAlgebraicallyClosed

/-- Invertibility of b on the two required inputs and compatibility with the
coefficient-first proper/open projection, before conjugation by tensor symmetry.

Source: latest blueprint, det-sp-reduction-compatibilities, Proof (3), Tensor map;
det-sp-reduction-direct-image and lem-fix-condensed-scalar-projection-coherence.
(blueprint: lem-sp-ordinary-finite-compact-support-scalar-projection-normalization).

Proof: Finite ordinary coefficient realization identifies the intrinsic Dctf
predicate with bounded constructibility and the same Tor intervals. Pullback and
tensor preserve that predicate, so both M and f_A^*K tensor M are admissible inputs.
The finite or algebraically closed field has finite ell-cohomological dimension.
Apply the finite-coefficient direct-image scalar comparison to the fixed proper/open
compactification at both inputs. Normalize the realization comparison by its ordinary
restriction square: on the proper factor the adjunct is scalar extension of the
geometric counit, and on the open factor it is the unit-normalized balancing map.
Uniqueness of adjunction transposes identifies their composite with exactly
compactComparison, for the supplied scalar adjunctions. This proves the two
isomorphism assertions without assuming coefficient flatness.
For the equation, use the same normalization of the tensor and pullback comparisons.
The scalar/projection coherence theorem for the proper factor is the mate identity
for its counit and the tensor comparison. For the open factor, transpose under
extension-by-zero adjoint to restriction and apply the identical unit equation.
Naturality pastes these two squares. The normalized pullback comparison respects
the compositor Li^* Lp^* = Lf^*, so appending the final compactification compositor
gives the displayed coefficient-first equation. Every factor is the specified
ordinary map, and no invertibility is used to identify these morphisms.
-/
theorem ordinaryFiniteCompactSupport_scalar_projection_normalization
    (k : Type u) [Field k] (p : ℕ) (hp : p.Prime) (hpk : ringChar k = p)
    (hscope : Finite k ∨ IsAlgClosed k) (ell : ℕ) (hell : ell.Prime) (hEll : ell ≠ p)
    (A B : Type u) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (hA : ∃ n : ℕ, 1 ≤ n ∧ ∀ a : A, (ell ^ n) • a = 0)
    (hB : ∃ n : ℕ, 1 ≤ n ∧ ∀ b : B, (ell ^ n) • b = 0)
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (c : Compactification f) [c.Z.Over (Spec (.of k))]
    [IsSeparated (c.Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (c.Z ↘ Spec (.of k))]
    [QuasiCompact (c.Z ↘ Spec (.of k))]
    [c.i.IsOver (Spec (.of k))] [c.g.IsOver (Spec (.of k))]
    (K : D A Y) (M : D A X) (hK : ctf A Y K) (hM : ctf A X M) (aX : scalar φ X ⊣ restrict φ X)
    (aY : scalar φ Y ⊣ restrict φ Y) :
    IsIso (compactComparison φ c aX aY M) ∧
      IsIso (compactComparison φ c aX aY ((pull A f).obj K ⊗ M)) ∧
      ((scalar φ Y).map
          (((projectionMapOfCompactification
            (ModuleCat.{u + 1} (ULift.{u + 1} A)) c).app M).app K) ≫
        compactComparison φ c aX aY (M ⊗ (pull A f).obj K) ≫
        (support B c).map (scalarTensor φ X aX M ((pull A f).obj K)) ≫
        (support B c).map (𝟙 ((scalar φ X).obj M) ⊗ₘ scalarPull φ f aX aY K) =
      scalarTensor φ Y aY ((support A c).obj M) K ≫
        (compactComparison φ c aX aY M ⊗ₘ 𝟙 ((scalar φ Y).obj K)) ≫
        (((projectionMapOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1} B)) c).app
            ((scalar φ X).obj M)).app ((scalar φ Y).obj K))) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteOrAlgebraicallyClosed
