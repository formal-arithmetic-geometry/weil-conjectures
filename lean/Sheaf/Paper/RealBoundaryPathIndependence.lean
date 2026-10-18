/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.Paper.RealBoundaryDecompositionLanding
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentation
public import Mathlib.RepresentationTheory.Invariants
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.LinearAlgebra
import Sheaf.FieldTheory.FiniteFieldAbsoluteGalois

/-!
# Path independence of the inertia invariants of a Weil sheaf

Source: blueprint main-20261015, sec-purity-real-sheaves/sk-d-real-boundary,
d-real-boundary.proof.md, complete proof (blueprint: lem-real-boundary-path-independence).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.PreGaloisCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.FiniteEtale

namespace RealSheaves

/-- The full path-independence assertion, with the ordinary open-curve structure supplied
from the chapter curve convention before elaborating the existing Weil-representation API.
This predicate binds the sheaf, its actual fundamental representation and the two specified
local path maps; its body is the linear isomorphism and Frobenius intertwining assertion.
The instance binding is in this reducible definition, so downstream proofs can unfold it;
there is no additional IsCurve hypothesis or statement-level let binder.
Source: blueprint main-20261015, d-real-boundary.proof.md, complete proof.
(blueprint: lem-real-boundary-path-independence) -/
def BoundaryInertiaPathIndependence
    (D : Setup.{u, v}) (C₀ : Scheme.{u}) [C₀.Over (Spec (.of D.k₀))]
    (hC : D.IsCurve C₀)
    (U₀ : C₀.Opens) (hU : Nonempty U₀) (_hS : (U₀ : Set C₀)ᶜ.Finite)
    (s : C₀) (_hs : s ∉ U₀)
    (H : Type u) [CommRing H] [HenselianLocalRing H] [IsDomain H]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal (C₀.presheaf.stalk s))) H]
    [Algebra (C₀.presheaf.stalk s) H]
    [IsScalarTower (C₀.presheaf.stalk s)
      (Localization.AtPrime (IsLocalRing.maximalIdeal (C₀.presheaf.stalk s))) H]
    (_hH : Algebra.IsHenselizationAtPrime' (C₀.presheaf.stalk s)
      (IsLocalRing.maximalIdeal (C₀.presheaf.stalk s)) H)
    (K : Type u) [Field K] [Algebra H K] [IsFractionRing H K]
    [Algebra (C₀.presheaf.stalk s) K] [IsScalarTower (C₀.presheaf.stalk s) H K]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [Algebra H Ω] [IsScalarTower H K Ω]
    [IsLocalRing (integralClosure H Ω)]
    [IsLocalHom (algebraMap H (integralClosure H Ω))]
    [IsAlgClosure (IsLocalRing.ResidueField H)
      (IsLocalRing.ResidueField (integralClosure H Ω))]
    (a : (Ω ≃ₐ[K] Ω) →* (integralClosure H Ω ≃ₐ[H] integralClosure H Ω))
    (_ha : ∀ (σ : Ω ≃ₐ[K] Ω) (b : integralClosure H Ω), (a σ b : Ω) = σ (b : Ω))
    (Ωr : Type w) [Field Ωr] [Algebra (IsLocalRing.ResidueField H) Ωr]
    [IsAlgClosure (IsLocalRing.ResidueField H) Ωr]
    (e : IsLocalRing.ResidueField (integralClosure H Ω) ≃ₐ[IsLocalRing.ResidueField H] Ωr)
    (r : (Ω ≃ₐ[K] Ω) →* (Ωr ≃ₐ[IsLocalRing.ResidueField H] Ωr))
    (_hr : ∀ (σ : Ω ≃ₐ[K] Ω) (b : integralClosure H Ω),
      r σ (e (IsLocalRing.residue (integralClosure H Ω) b)) =
        e (IsLocalRing.residue (integralClosure H Ω) (a σ b)))
    (Φ : Ωr ≃ₐ[IsLocalRing.ResidueField H] Ωr)
    (_hΦ : ∀ x : Ωr,
      Φ.symm x = x ^ Nat.card (C₀.residueField s))
    (ξ : Spec (.of K) ⟶ U₀.toScheme)
    (_hξ : ξ ≫ U₀.ι =
      Spec.map (CommRingCat.ofHom (algebraMap (C₀.presheaf.stalk s) K)) ≫
        C₀.fromSpecStalk s)
    : Prop :=
  letI := D.openIsCurve C₀ hC U₀ hU
  ∀ (W : AlgebraicGeometry.WeilGroup (U₀.toScheme ↘ Spec (.of D.k₀)))
    (B : AlgebraicGeometry.WeilGroup.BasePointData W)
    (M : AlgebraicGeometry.ProEtale.LisseMonodromy D.l
      (U₀.toScheme ↘ Spec (.of D.k₀)).geometricFiber D.k₀)
    (DM : AlgebraicGeometry.WeilGroup.WeilMonodromyData B)
    (F : WeilSheaf D.k₀ D.l U₀.toScheme) (hF : F.IsLisse)
    (γ₁ γ₂ : fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ ξ) ≅
      fiber W.basePoint)
    (θ₁ θ₂ : (Ω ≃ₐ[K] Ω) →* W.fundamentalGroup)
    (_hθ₁ : ∀ (σ : Ω ≃ₐ[K] Ω) (P : U₀.toScheme.FiniteEtale)
        (z : (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ ξ)).obj P),
      (γ₁.inv.app P (θ₁ σ • γ₁.hom.app P z)).left =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.left)
    (_hθ₂ : ∀ (σ : Ω ≃ₐ[K] Ω) (P : U₀.toScheme.FiniteEtale)
        (z : (fiber (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ ξ)).obj P),
      (γ₂.inv.app P (θ₂ σ • γ₂.hom.app P z)).left =
        Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ z.left)
    (τ₁ τ₂ : (Subgroup.zpowers Φ).comap r →* W.carrier)
    (_hτ₁ : ∀ σ : (Subgroup.zpowers Φ).comap r,
      W.toFundamentalGroup (τ₁ σ) = θ₁ σ.val)
    (_hτ₂ : ∀ σ : (Subgroup.zpowers Φ).comap r,
      W.toFundamentalGroup (τ₂ σ) = θ₂ σ.val)
    (α₁ α₂ : Representation (PadicAlgCl D.l) ((Subgroup.zpowers Φ).comap r)
      (AlgebraicGeometry.ProEtale.LisseMonodromy.StalkSpace B.t (F.toLisse hF)))
    (_hα₁ : α₁ = (AlgebraicGeometry.WeilGroup.fundamentalRep M DM F hF).comp τ₁)
    (_hα₂ : α₂ = (AlgebraicGeometry.WeilGroup.fundamentalRep M DM F hF).comp τ₂)
    (φ : (Subgroup.zpowers Φ).comap r) (_hφ : r φ.val = Φ),
    ∃ A : Representation.invariants
        (α₁.comp (r.ker.comap ((Subgroup.zpowers Φ).comap r).subtype).subtype)
        ≃ₗ[PadicAlgCl D.l]
          Representation.invariants
            (α₂.comp (r.ker.comap ((Subgroup.zpowers Φ).comap r).subtype).subtype),
      ∀ x, A (α₁.toInvariants (r.ker.comap ((Subgroup.zpowers Φ).comap r).subtype) φ x) =
        α₂.toInvariants (r.ker.comap ((Subgroup.zpowers Φ).comap r).subtype) φ (A x)

/-- Changing the local etale path identifies inertia invariants with their Frobenius action.
Source: blueprint main-20261015, d-real-boundary.proof.md, complete proof.
(blueprint: lem-real-boundary-path-independence)

The local fields, residue action and local generic point use exactly the models and
characterizing equations of `exists_boundary_decomposition_landing`. The two paths have the
same source. The equations htheta characterize their decomposition homomorphisms on every
finite etale fibre. The maps tau are their restrictions to the local Weil group, identified
with the global Weil group by W.toFundamentalGroup. The representations alpha are names for
the pullbacks of the actual fundamental representation of F, not arbitrary actions.
In the unfolded BoundaryInertiaPathIndependence predicate, the normal subgroup in each
invariant space is the kernel of r restricted to the local
Weil group. Mathlib's toInvariants supplies the restriction of the Frobenius operator;
quotientToInvariants shows that it is independent of the chosen lift.
The ordinary IsCurve instance on the open is supplied by Setup.openIsCurve from hC and hU,
without an additional hypothesis. W, B, M and DM are the recorded presentation data of
the fundamental representation.
The arithmetic base point W.basePoint is identified with the geometric point B.t by B.path;
composing both displayed paths with B.path.symm gives paths to that same geometric point.

Proof (the five steps of the DAG node):
1. Write g = gamma2 gamma1^{-1}. Evaluation of the two path formulas gives
   theta2(sigma) = g theta1(sigma) g^{-1} in the arithmetic fundamental group.
2. By lem-real-boundary-local-constants the residue extension has positive finite degree,
   the residue map is onto, and the constant-field projection of the decomposition group
   is Gal(k/k_s). FiniteFieldAbsoluteGalois identifies the finite quotient Gal(k_s/k_0)
   as cyclic generated by Frobenius. Choose n matching the image of g there, and delta
   with arithmetic image F^{-n}p(g). Then w = g theta1(delta)^{-1} is in the Weil group.
   This uses only the Weil representation at w, never at g or theta1(delta).
3. The kernel of the residue map is normal. Conjugation by delta permutes inertia,
   giving theta2(I_s) = w theta1(I_s) w^{-1}.
4. The restrictions of rho(w) and rho(w^{-1}) are inverse linear maps between the two
   invariant spaces; use the fundamental representation's homomorphism law.
5. The residue Galois group is abelian (finite-field absolute Galois theorem). Therefore
   delta Phi delta^{-1} and Phi differ by inertia. The quotient action on invariants
   (Representation.quotientToInvariants, lem-real-boundary-frobenius-invariants) identifies
   their operators. Substitution into the path-conjugacy formula gives T2 A = A T1.
-/
theorem boundary_inertia_invariants_path_independent
    (D : Setup.{u, v}) (C₀ : Scheme.{u}) [C₀.Over (Spec (.of D.k₀))]
    (hC : D.IsCurve C₀)
    (U₀ : C₀.Opens) (hU : Nonempty U₀) (hS : (U₀ : Set C₀)ᶜ.Finite)
    (s : C₀) (hs : s ∉ U₀)
    (H : Type u) [CommRing H] [HenselianLocalRing H] [IsDomain H]
    [Algebra (Localization.AtPrime (IsLocalRing.maximalIdeal (C₀.presheaf.stalk s))) H]
    [Algebra (C₀.presheaf.stalk s) H]
    [IsScalarTower (C₀.presheaf.stalk s)
      (Localization.AtPrime (IsLocalRing.maximalIdeal (C₀.presheaf.stalk s))) H]
    (hH : Algebra.IsHenselizationAtPrime' (C₀.presheaf.stalk s)
      (IsLocalRing.maximalIdeal (C₀.presheaf.stalk s)) H)
    (K : Type u) [Field K] [Algebra H K] [IsFractionRing H K]
    [Algebra (C₀.presheaf.stalk s) K] [IsScalarTower (C₀.presheaf.stalk s) H K]
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    [Algebra H Ω] [IsScalarTower H K Ω]
    [IsLocalRing (integralClosure H Ω)]
    [IsLocalHom (algebraMap H (integralClosure H Ω))]
    [IsAlgClosure (IsLocalRing.ResidueField H)
      (IsLocalRing.ResidueField (integralClosure H Ω))]
    (a : (Ω ≃ₐ[K] Ω) →* (integralClosure H Ω ≃ₐ[H] integralClosure H Ω))
    (ha : ∀ (σ : Ω ≃ₐ[K] Ω) (b : integralClosure H Ω), (a σ b : Ω) = σ (b : Ω))
    (Ωr : Type w) [Field Ωr] [Algebra (IsLocalRing.ResidueField H) Ωr]
    [IsAlgClosure (IsLocalRing.ResidueField H) Ωr]
    (e : IsLocalRing.ResidueField (integralClosure H Ω) ≃ₐ[IsLocalRing.ResidueField H] Ωr)
    (r : (Ω ≃ₐ[K] Ω) →* (Ωr ≃ₐ[IsLocalRing.ResidueField H] Ωr))
    (hr : ∀ (σ : Ω ≃ₐ[K] Ω) (b : integralClosure H Ω),
      r σ (e (IsLocalRing.residue (integralClosure H Ω) b)) =
        e (IsLocalRing.residue (integralClosure H Ω) (a σ b)))
    (Φ : Ωr ≃ₐ[IsLocalRing.ResidueField H] Ωr)
    (hΦ : ∀ x : Ωr,
      Φ.symm x = x ^ Nat.card (C₀.residueField s))
    (ξ : Spec (.of K) ⟶ U₀.toScheme)
    (hξ : ξ ≫ U₀.ι =
      Spec.map (CommRingCat.ofHom (algebraMap (C₀.presheaf.stalk s) K)) ≫
        C₀.fromSpecStalk s)
    : BoundaryInertiaPathIndependence D C₀ hC U₀ hU hS s hs H hH K Ω a ha Ωr e r hr
        Φ hΦ ξ hξ := by
  sorry

end RealSheaves
