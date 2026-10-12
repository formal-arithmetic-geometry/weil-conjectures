/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism
import Sheaf.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Sheaf.AlgebraicGeometry.ThickeningIntegral

/-!
# Scheme components from a split reduced tensor algebra

Source: smooth purity blueprint, finite-algebra calculation in
`lem-weil-pbc-finite-pushforward-generic-constructible`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme

/-- Convert a specified reduced tensor product decomposition into open scheme components.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`, finite-algebra calculation.
(blueprint: lem-weil-pbc-split-tensor-algebra-scheme-components).

Proof: Identify the affine schemes with spectra of their global sections, compatibly
with g. Identify the principal open with Spec of the localization away from c, and
use the specified finite étale surjective algebra to construct its cover Spec A'.
The affine tensor product formula identifies the pullback source with Spec of the
specified tensor algebra. The given algebra isomorphism identifies its reduction
with the spectrum of the finite product. The factor spectra are open and closed,
pairwise disjoint, and cover that spectrum, including when r = 0. Reduction is a
surjective closed immersion and a homeomorphism, so these opens lift uniquely to
opens of the original source. Each reduced component maps universally
homeomorphically to Spec A' by hD. The lifted component does also: the reduction
immersion is surjective. Integrality descends across this source thickening with
identity thickening on T. Surjectivity follows from that of the composite with
reduction. After any base change, reduction is still surjective: lift two points
with the same image to the reduced component and use its injectivity to identify
them. This proves universal injectivity. Transport through the affine identifications. -/
theorem finite_scheme_components_of_split_tensor_algebra
    (S : Scheme.{u}) [IsAffine S] {Z : Scheme.{u}} [IsAffine Z] (g : Z ⟶ S)
    (c : Γ(S, ⊤)) (A' : Type u) [CommRing A']
    [Algebra (Localization.Away c) A'] [Algebra Γ(S, ⊤) A']
    [IsScalarTower Γ(S, ⊤) (Localization.Away c) A']
    [Module.Finite (Localization.Away c) A']
    [Algebra.Etale (Localization.Away c) A']
    (hSurj : Surjective
      (Spec.map (CommRingCat.ofHom (algebraMap (Localization.Away c) A'))))
    (r : ℕ) (D : Fin r → Type u) [∀ j, CommRing (D j)] [∀ j, Algebra A' (D j)]
    (hD : ∀ j, IsUniversalHomeomorphism
      (Spec.map (CommRingCat.ofHom (algebraMap A' (D j)))))
    (he : letI := g.appTop.hom.toAlgebra
      letI := Algebra.TensorProduct.rightAlgebra (R := Γ(S, ⊤)) (A := Γ(Z, ⊤)) (B := A')
      Nonempty (((Γ(Z, ⊤) ⊗[Γ(S, ⊤)] A') ⧸ _root_.nilradical (Γ(Z, ⊤) ⊗[Γ(S, ⊤)] A'))
        ≃ₐ[A'] (∀ j, D j))) :
    ∃ (T : Scheme.{u}) (p : T ⟶ (S.basicOpen c).toScheme),
      IsFinite p ∧ Etale p ∧ Surjective p ∧
      ∃ (W : Fin r → (pullback g (p ≫ (S.basicOpen c).ι)).Opens),
        (⨆ i, W i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (W i) (W j)) ∧
        ∀ i, IsUniversalHomeomorphism
          ((W i).ι ≫ pullback.snd g (p ≫ (S.basicOpen c).ι)) := by sorry

end AlgebraicGeometry.Scheme
