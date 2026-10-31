/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.LocallyFreeCharpoly
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteType
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.InvariantBasisNumber
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.TensorPullbackOpenRestriction

/-! # Determinant norm from a principal free cover

Source: Stacks Project, Exercises, Tags 02DU (1), 02DV (1), (3), and More on Algebra,
Tag 09XI, proof of (3) implies (1), characteristic-polynomial gluing paragraph
(blueprint: lem-a1-principal-free-algebra-determinant-norm).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

/-- Multiplication by `u/1` on the localized module, transported through the canonical
localization-tensor equivalence. On `d/a^q` it sends the fraction to `ud/a^q`.
Source: Stacks, Tags 02DU (1), 02DV (1), (3)
(blueprint: lem-a1-principal-free-algebra-determinant-norm). -/
noncomputable def localizedMul {R : Type u} {D : Type v}
    [CommRing R] [CommRing D] [Algebra R D] (a : R) (u : D) :
    LocalizedModule.Away a D →ₗ[Localization.Away a] LocalizedModule.Away a D :=
  (LocalizedModule.isBaseChange (Submonoid.powers a) D).equiv.conj
    ((LinearMap.mul R D u).baseChange (Localization.Away a))

/-- The norm is the signed constant coefficient of the uniquely characterized locally
free characteristic polynomial of multiplication. No global basis is chosen.
Source: Stacks, Tags 02DU (1), 02DV (1); Tag 09XI, characteristic-polynomial paragraph
(blueprint: lem-a1-principal-free-algebra-determinant-norm). -/
noncomputable def principalFreeNorm {R : Type u} {D : Type v}
    [CommRing R] [CommRing D] [Algebra R D] {r m : ℕ} (f : Fin m → R)
    (hgen : Ideal.span (Set.range f) = ⊤)
    (hfree : ∀ i : Fin m, ∃ _e : Module.Basis (Fin r) (Localization.Away (f i))
      (LocalizedModule.Away (f i) D), True) (u : D) : R :=
  (-1) ^ r * (locallyFreeCharpoly f hgen hfree (LinearMap.mul R D u)).eval 0

/-- Local determinant characterization, uniqueness, and arbitrary free scalar extension.
Source: Stacks, Tags 02DU (1), 02DV (1), (3); Tag 09XI, gluing paragraph
(blueprint: lem-a1-principal-free-algebra-determinant-norm).
Proof: (1) Multiplication is R-linear. Use lem-weil-pbc-charpoly-locally-free-existence
and the existing locallyFreeCharpoly to define the signed constant coefficient.
(2) In a rank-r scalar-extension basis its characteristic polynomial is det(ZI-M).
Evaluation at zero gives det(-M)=(-1)^r det(M), by the permutation formula of
 def-weil-pbc-matrix-determinant. Multiplying by (-1)^r cancels the sign.
(3) For any finite basis of size k, localize the target at the images of the f_i.
The images still generate the unit ideal. Transitive base change and the
localization-tensor equivalence transport both the rank-r and rank-k bases.
On a nonzero localization invariant basis number gives k=r; on a zero localization
the equality is automatic. Determinants commute with ring maps by their permutation
formula, so lem-weil-pbc-standard-covering-glue (i) descends the equality.
(4) The canonical localization-tensor equivalence carries scalar-extended multiplication
to multiplication by u/1. This gives the displayed formula for every a and finite basis.
Any other function satisfies the same formula at every f_i. Their difference has zero
image throughout the generating cover, so the same gluing injectivity proves uniqueness.
This characterization has no chosen cover or basis. Zero rings and empty matrices are
allowed: rank zero gives characteristic polynomial 1 and determinant 1; an empty
unit-ideal generating cover forces R and D to be zero. -/
theorem principalFreeNorm_spec {R : Type u} {D : Type v}
    [CommRing R] [CommRing D] [Algebra R D] {r m : ℕ} (f : Fin m → R)
    (hgen : Ideal.span (Set.range f) = ⊤)
    (hfree : ∀ i : Fin m, ∃ _e : Module.Basis (Fin r) (Localization.Away (f i))
      (LocalizedModule.Away (f i) D), True) :
    (∀ (a : R) (k : ℕ)
      (e : Module.Basis (Fin k) (Localization.Away a) (LocalizedModule.Away a D))
      (u : D), algebraMap R (Localization.Away a) (principalFreeNorm f hgen hfree u) =
        (LinearMap.toMatrix e e (localizedMul a u)).det) ∧
    (∀ N : D → R,
      (∀ (a : R) (k : ℕ)
        (e : Module.Basis (Fin k) (Localization.Away a) (LocalizedModule.Away a D))
        (u : D), algebraMap R (Localization.Away a) (N u) =
          (LinearMap.toMatrix e e (localizedMul a u)).det) →
      N = principalFreeNorm f hgen hfree) ∧
    (∀ (S : Type (max u w)) [CommRing S] [Algebra R S]
      (e : Module.Basis (Fin r) S (S ⊗[R] D)) (u : D),
      algebraMap R S (principalFreeNorm f hgen hfree u) =
        (LinearMap.toMatrix e e ((LinearMap.mul R D u).baseChange S)).det) := by
  sorry

end Algebra

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry

/-- The affine-open clause of the determinant norm: the basis lives in the actual sections
of the direct image of the structure module, whose value on V is O(p⁻¹V).
The matrix entries are the coordinates of multiplication by the restricted u.
Source: Stacks, Tags 02DU (1), 02DV (1), (3)
(blueprint: lem-a1-principal-free-algebra-determinant-norm).
Proof: (5) Set F=p_*O and A=O(V). Apply
lem-weil-pbc-module-pullback-affine-sections to V→Spec R and F. The unit-compatible
comparison of lem-weil-pbc-open-immersion-module-pullback-restriction identifies
pullback with restriction. Together with Γ(Spec D,O)=D it gives the A-linear
isomorphism A⊗_R D→F(V), sending a⊗d to a(d|p⁻¹V). On pure tensors this identifies
scalar-extended multiplication with multiplication by the restricted u, since
u(ad)=a(ud); pure tensors generate. Transport the given finite basis through the
inverse isomorphism and use the arbitrary-finite-basis argument in step (3) of
principalFreeNorm_spec. The multiplication matrices agree entry by entry.
(6) Empty opens, zero section rings and rank zero are included, with empty determinant 1. -/
theorem principalFreeNorm_affineOpen {R D : Type u}
    [CommRing R] [CommRing D] [Algebra R D] {r m : ℕ} (f : Fin m → R)
    (hgen : Ideal.span (Set.range f) = ⊤)
    (hfree : ∀ i : Fin m, ∃ _e : Module.Basis (Fin r) (Localization.Away (f i))
      (LocalizedModule.Away (f i) D), True)
    (_hqc : ((Scheme.Modules.pushforward
      (Spec.map (CommRingCat.ofHom (algebraMap R D)))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of D)).ringCatSheaf)).IsQuasicoherent)
    (V : (Spec (CommRingCat.of R)).affineOpens) (k : ℕ)
    (e : Module.Basis (Fin k) Γ(Spec (CommRingCat.of R), V.1)
      Γ(((Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom (algebraMap R D)))).obj
        (SheafOfModules.unit (Spec (CommRingCat.of D)).ringCatSheaf)), V.1))
    (u : D) :
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec (CommRingCat.of R)).presheaf.map (homOfLE (le_top : V.1 ≤ ⊤)).op).hom
        (Algebra.principalFreeNorm f hgen hfree u)) =
      Matrix.det (fun i j ↦ e.repr
        ((((Scheme.ΓSpecIso (CommRingCat.of D)).inv ≫
          (Spec (CommRingCat.of D)).presheaf.map (homOfLE
            (le_top : (Spec.map (CommRingCat.ofHom (algebraMap R D))) ⁻¹ᵁ V.1 ≤ ⊤)).op).hom u) *
          (@id Γ(Spec (CommRingCat.of D),
            (Spec.map (CommRingCat.ofHom (algebraMap R D))) ⁻¹ᵁ V.1) (e j))) i) := by
  sorry

end AlgebraicGeometry
