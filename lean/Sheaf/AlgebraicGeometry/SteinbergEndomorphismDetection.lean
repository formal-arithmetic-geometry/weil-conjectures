/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.GroupScheme.Semisimple
public import Sheaf.AlgebraicGeometry.RationalRepresentationGZero
import Sheaf.AlgebraicGeometry.RhoSectionModules

/-! # Steinberg endomorphisms detect nonzero invariant vectors

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Section 9.7, Lemmas 9.7.2 and 9.7.4, Remark 9.7.3 and Theorem 9.7.5.
(blueprint: lem-sfb-steinberg-endomorphism-detection)

Equivariance into the conjugation representation is expressed by equivariance of the
bilinear evaluation map U tensor E to E. Conjugation-fixed endomorphisms are precisely
endomorphisms commuting with the coaction of E. Both conditions are coordinate-coaction
identities, so they retain the action over every commutative scalar extension.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry

/-- The precise detection property, using the actual finite rational coordinate comodules.
Equivariance is the tensor-coefficient identity for evaluation, and the fixed-endomorphism
condition uses the existing comodule-map predicate.
Source: Alper, Theorem 9.7.5, endomorphism construction
(blueprint: lem-sfb-steinberg-endomorphism-detection). -/
def HasSteinbergEndomorphismDetection {F : Type u} [Field F]
    (S : Over (Spec (.of F))) [GrpObj S] [IsAffine S.left] : Prop :=
  ∀ (U : EquivariantCoherent.Representation F S) (x : U.space),
    x ≠ 0 → U.coaction x = x ⊗ₜ[F] (1 : Γ(S.left, ⊤)) →
    ∃ (E : EquivariantCoherent.Representation F S),
      Nontrivial E.space ∧ ∃ φ : U.space →ₗ[F] Module.End F E.space,
        φ x ≠ 0 ∧
        (∀ (v : U.space) (e : E.space),
          (TensorProduct.lift φ).rTensor Γ(S.left, ⊤)
              (HopfAction.tensorCoefficients F Γ(S.left, ⊤) F U.space E.space
                (U.coaction v ⊗ₜ[F] E.coaction e)) = E.coaction (φ v e)) ∧
        ∀ a : Module.End F E.space,
          EquivariantCoherent.IsRepresentationMap E E a ↔
            ∃ c : F, a = c • LinearMap.id

/-- A nonzero invariant vector is detected in an endomorphism representation whose
conjugation-fixed subspace is the scalar identity line.
Source: Alper, Section 9.7, Lemmas 9.7.2 and 9.7.4, Remark 9.7.3 and Theorem 9.7.5
(blueprint: lem-sfb-steinberg-endomorphism-detection).

The tensor-coefficient equation says that evaluation (u,e) maps to phi(u)(e)
is equivariant. Since the action on E is invertible, this is exactly equivariance
of phi into End(E) with conjugation action. Likewise IsRepresentationMap E E a
is exactly the condition that a is fixed by conjugation. These are coaction identities,
not tests on rational points alone. The affine instance is supplied by hS itself.

Proof plan:
1. Apply lem-sfb-rho-section-modules to choose a split maximal torus and Borel,
   its half-sum character rho and actual nonzero finite-dimensional section modules W_m.
2. Apply lem-sfb-rho-tensor-square-eventual-detection to U and x, obtaining M >= 1
   and equivariant a_m : U to W_m tensor W_m with a_m(x) nonzero for every m >= M.
3. In characteristic zero choose m=M. In characteristic p choose nu >= 1 with
   p^nu-1 >= M. By lem-sfb-rho-section-self-duality the same E=W_m admits an
   equivariant isomorphism d : E to its dual. Thus the chosen a=a_m detects x.
4. Define Theta(u tensor v)(w)=d(v)(w)u. For a basis e_i with dual e_i*, its inverse
   sends A to sum_i A(e_i) tensor d^{-1}(e_i*). The dual-basis identities prove both
   inverse equations. Equivariance of d gives d(sv)(w)=d(v)(s^{-1}w), hence Theta
   intertwines the diagonal and conjugation actions over every test algebra.
   Put phi=Theta composed with a; injectivity of Theta gives phi(x) nonzero.
5. By lem-sfb-rho-tensor-square-invariant-line the invariant tensor square has
   dimension one. Theta and its inverse identify it with the conjugation invariants
   in End(E). The identity is invariant and nonzero because E is nonzero, so it spans
   this one-dimensional space. This gives exactly the scalar-endomorphism equivalence.
-/
theorem exists_steinberg_endomorphism_detection {F : Type u} [Field F] [IsAlgClosed F]
    (S : Over (Spec (.of F))) [GrpObj S] (hS : IsSemisimpleGroupScheme S)
    (hsc : ∀ (S' : Over (Spec (.of F))) [GrpObj S'],
      IsSemisimpleGroupScheme S' → ∀ (f : S' ⟶ S) [IsMonHom f],
      Surjective f.left → IsFinite (GrpObj.ker f).hom →
      (∀ (A : Type u) [CommRing A] [Algebra F A]
        (x : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F A))) ⟶ GrpObj.ker f)
        (s : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap F A))) ⟶ S'),
        (x ≫ GrpObj.kerι f) * s = s * (x ≫ GrpObj.kerι f)) → IsIso f)
    : @HasSteinbergEndomorphismDetection F _ S _ hS.2.2.1 := by
  sorry

end AlgebraicGeometry
