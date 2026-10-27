/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecTraceFormula.TwoTermKernelNormalization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover

/-!
# Locality and equivariance of kernel normalization

Source: Stacks Project, More on Algebra, Tags 0FJC, 0FJI and 0FJK
(blueprint: lem-trf-two-term-normalization-locality-equivariance).

Localized models are specified by `IsLocalizedModule` and the commuting differential
and chain-map squares. This allows any model of the actual fraction localization,
without imposing equal coefficient and module universes. Exterior inclusions, dual
evaluations and pure-tensor formulas pin all determinant comparisons.

## Main statements

- `maps_eq_of_prime_localizations`: equality detection for arbitrary module maps.
- `determinant_line_localization`: canonical localization of every two-term determinant.
- `normalization_localization`: localization of kernels and all normalization data.
- `normalization_equivariance`: the four chain-isomorphism equivariance identities.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory
open scoped TensorProduct

namespace Module.TwoTerm

/-- The two kernel-first maps and the assembly, element and inverse already characterized
by the recorded kernel-normalization predicate. Source: Stacks Project, Tags 0FJB and 0FJI
(blueprint: lem-trf-two-term-normalization-locality-equivariance). -/
structure Normalization {R : Type u} [CommRing R]
    {P Q : Arrow (ModuleCat.{v} R)} (a : P ⟶ Q) where
  gammaNeg : (determinantModule R (LinearMap.ker a.left.hom) ⊗[R]
    determinantModule R (Q.left : Type v)) ≃ₗ[R] determinantModule R (P.left : Type v)
  gammaZero : (determinantModule R (LinearMap.ker a.right.hom) ⊗[R]
    determinantModule R (Q.right : Type v)) ≃ₗ[R] determinantModule R (P.right : Type v)
  gammaNeg_spec : IsDeterminantExactSequenceMap (Submodule.subtype _) a.left.hom gammaNeg
  gammaZero_spec : IsDeterminantExactSequenceMap (Submodule.subtype _) a.right.hom gammaZero
  assembly : determinant Q ⊗[R] kernelDeterminant a ≃ₗ[R] determinant P
  element : kernelDeterminant a
  inverse : determinant P ≃ₗ[R] determinant Q
  canonical : IsKernelNormalizedAssembly a assembly element inverse

/-- Exterior and dual localization of a determinant line. Evaluation on localized
vectors specifies the dual map, with fraction formula lambda(x)/(st).
Source: Stacks Project, Tags 0FJA and 0FJI
(blueprint: lem-trf-two-term-normalization-locality-equivariance). -/
structure DeterminantLocalization {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] (S : Submonoid R)
    {M : Type v} [AddCommGroup M] [Module R M]
    {M' : Type z} [AddCommGroup M'] [Module A M'] [Module R M']
    [IsScalarTower R A M'] (f : M →ₗ[R] M') where
  map : determinantModule R M →ₗ[R] determinantModule A M'
  exterior : ∀ x, (map x).val = ExteriorAlgebra.scalarExtensionMap f x.val
  localized : IsLocalizedModule S map
  dual : Dual R (determinantModule R M) →ₗ[R] Dual A (determinantModule A M')
  evaluation : ∀ phi x, dual phi (map x) = algebraMap R A (phi x)
  dual_localized : IsLocalizedModule S dual

/-- Localization of the two-term determinant, fixed on pure tensors by exterior and
dual localization. Source: Stacks Project, Tag 0FJI
(blueprint: lem-trf-two-term-normalization-locality-equivariance). -/
structure LineLocalization {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] (S : Submonoid R)
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {M' N' : Type z} [AddCommGroup M'] [Module A M'] [Module R M']
    [IsScalarTower R A M'] [AddCommGroup N'] [Module A N'] [Module R N']
    [IsScalarTower R A N'] (f : M →ₗ[R] M') (g : N →ₗ[R] N') where
  neg : DeterminantLocalization (A := A) S f
  zero : DeterminantLocalization (A := A) S g
  map : determinantModule R N ⊗[R] Dual R (determinantModule R M) →ₗ[R]
    determinantModule A N' ⊗[A] Dual A (determinantModule A M')
  pure : ∀ y phi, map (y ⊗ₜ[R] phi) = zero.map y ⊗ₜ[A] neg.dual phi
  localized : IsLocalizedModule S map

/-- The determinant of a module isomorphism, specified by its exterior inclusion.
Source: Stacks Project, Tag 0FJC
(blueprint: lem-trf-two-term-normalization-locality-equivariance). -/
structure DeterminantIso {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] (f : M ≃ₗ[R] N) where
  map : determinantModule R M ≃ₗ[R] determinantModule R N
  exterior : ∀ x, (map x).val = ExteriorAlgebra.map f.toLinearMap x.val

/-- D(w) is the tensor product of the positive determinant map with the dual of the
inverse negative determinant map. Source: Stacks Project, Tag 0FJI
(blueprint: lem-trf-two-term-normalization-locality-equivariance). -/
noncomputable def lineIso {R : Type u} [CommRing R]
    {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {M' N' : Type w} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
    {f : M ≃ₗ[R] M'} {g : N ≃ₗ[R] N'} (dneg : DeterminantIso f)
    (dzero : DeterminantIso g) :
    determinantModule R N ⊗[R] Dual R (determinantModule R M) ≃ₗ[R]
      determinantModule R N' ⊗[R] Dual R (determinantModule R M') :=
  TensorProduct.congr dzero.map dneg.map.symm.dualMap

/-- Equality of arbitrary module maps is detected at every prime, including when R is
zero and its spectrum is empty. Source: Stacks Project, More on Algebra, Tag 0FJK,
final paragraph; Algebra, Tag 00HN
(blueprint: lem-trf-two-term-normalization-locality-equivariance).

Proof, step 1: the annihilator of f(x)-g(x) meets the complement of every prime by
the fraction criterion. Its basic opens cover Spec R, so it is the unit ideal by the
basic-open criterion. Thus f(x)-g(x)=0. Extensionality finishes. Over the zero ring
all unital modules are subsingleton. Mathlib's maximal-localization criterion also applies. -/
theorem maps_eq_of_prime_localizations {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N] (f g : M →ₗ[R] N)
    (h : ∀ (p : Ideal R) [p.IsPrime], LocalizedModule.map p.primeCompl f =
      LocalizedModule.map p.primeCompl g) : f = g := by
  sorry

/-- Every finite-projective two-term complex has its canonical localized determinant
line, using any localized models of its terms. Source: Stacks Project, Tag 0FJI
(blueprint: lem-trf-two-term-normalization-locality-equivariance).

Proof, step 4: use determinant exterior localization on both terms. A finite dual
frame gives the inverse of the localized evaluation map. Tensor localization sends
(x tensor y)/s to (x/s) tensor (y/1); its inverse multiplies denominators. These
formulas prove the pure-tensor characterization and the localization universal property. -/
theorem determinant_line_localization {R : Type u} [CommRing R]
    (E : Arrow (ModuleCat.{v} R))
    [Module.Finite R E.left] [Module.Projective R E.left]
    [Module.Finite R E.right] [Module.Projective R E.right]
    (p : Ideal R) [p.IsPrime]
    {A : Type z} [CommRing A] [Algebra R A] [IsLocalization p.primeCompl A]
    {M N : Type w} [AddCommGroup M] [Module A M]
    [Module R M] [IsScalarTower R A M]
    [AddCommGroup N] [Module A N]
    [Module R N] [IsScalarTower R A N]
    (f : (E.left : Type v) →ₗ[R] M) (g : (E.right : Type v) →ₗ[R] N)
    [IsLocalizedModule p.primeCompl f] [IsLocalizedModule p.primeCompl g] :
    Nonempty (LineLocalization (A := A) p.primeCompl f g) := by
  sorry

/-- Kernel normalization commutes with prime localization, on arbitrary actual localized
models. The commuting squares mean that ap is precisely the localization of a; the
localized-module hypotheses specify the universal fraction construction, not extra
assumptions on the original complexes.
Source: Stacks Project, More on Algebra, Tags 0FJI and 0FJK
(blueprint: lem-trf-two-term-normalization-locality-equivariance).

Proof, steps 2--5: localize the kernel inclusions. A fraction in the localized kernel
has a numerator whose image is killed by a denominator, so clearing that denominator
produces a fraction of an original kernel element. This proves the kernel comparison.
Localizing sections and the inverse kernel differential gives the localized surjection
and quasi-isomorphism, also by a direct two-term cycle chase. Finite standard free
covers give finite free terms and kernels over the local ring. Exterior determinant
localization and dual localization by a finite dual frame give lP, lQ and lN. The
exact-sequence determinant localization identity gives both gamma squares. The
pure-tensor assembly formula then gives the Gamma square. Contraction with determinant
vectors identifies the differential element. Localize the two inverse equations and
use uniqueness of inverse to identify T. Empty wedges include zero ranks. -/
theorem normalization_localization {R : Type u} [CommRing R]
    {P Q : Arrow (ModuleCat.{v} R)} (a : P ⟶ Q)
    [Module.Finite R P.left] [Module.Projective R P.left]
    [Module.Finite R P.right] [Module.Projective R P.right]
    [Module.Finite R Q.left] [Module.Projective R Q.left]
    [Module.Finite R Q.right] [Module.Projective R Q.right]
    (ha : DegreewiseSurjective a) (hqa : QuasiIso a) (n : Normalization a)
    (p : Ideal R) [p.IsPrime]
    {A : Type z} [CommRing A] [Algebra R A] [IsLocalization p.primeCompl A]
    {Pp Qp : Arrow (ModuleCat.{w} A)}
    [Module R Pp.left] [IsScalarTower R A Pp.left]
    [Module R Pp.right] [IsScalarTower R A Pp.right]
    [Module R Qp.left] [IsScalarTower R A Qp.left]
    [Module R Qp.right] [IsScalarTower R A Qp.right]
    (ap : Pp ⟶ Qp)
    (fPn : (P.left : Type v) →ₗ[R] (Pp.left : Type w))
    (fPz : (P.right : Type v) →ₗ[R] (Pp.right : Type w))
    (fQn : (Q.left : Type v) →ₗ[R] (Qp.left : Type w))
    (fQz : (Q.right : Type v) →ₗ[R] (Qp.right : Type w))
    [IsLocalizedModule p.primeCompl fPn] [IsLocalizedModule p.primeCompl fPz]
    [IsLocalizedModule p.primeCompl fQn] [IsLocalizedModule p.primeCompl fQz]
    (hP : ∀ x, Pp.hom.hom (fPn x) = fPz (P.hom.hom x))
    (hQ : ∀ x, Qp.hom.hom (fQn x) = fQz (Q.hom.hom x))
    (hn : ∀ x, ap.left.hom (fPn x) = fQn (a.left.hom x))
    (hz : ∀ x, ap.right.hom (fPz x) = fQz (a.right.hom x)) :
    DegreewiseSurjective ap ∧ QuasiIso ap ∧
    Module.Finite A Pp.left ∧
    Module.Free A Pp.left ∧
    Module.Finite A Pp.right ∧
    Module.Free A Pp.right ∧
    Module.Finite A Qp.left ∧
    Module.Free A Qp.left ∧
    Module.Finite A Qp.right ∧
    Module.Free A Qp.right ∧
    Module.Finite A (LinearMap.ker ap.left.hom) ∧
    Module.Free A (LinearMap.ker ap.left.hom) ∧
    Module.Finite A (LinearMap.ker ap.right.hom) ∧
    Module.Free A (LinearMap.ker ap.right.hom) ∧
    ∃ (kneg : LinearMap.ker a.left.hom →ₗ[R] LinearMap.ker ap.left.hom)
      (kzero : LinearMap.ker a.right.hom →ₗ[R] LinearMap.ker ap.right.hom),
      (∀ x, (kneg x).val = fPn x.val) ∧ (∀ x, (kzero x).val = fPz x.val) ∧
      IsLocalizedModule p.primeCompl kneg ∧ IsLocalizedModule p.primeCompl kzero ∧
      (∀ x, kernelDifferential ap (kneg x) = kzero (kernelDifferential a x)) ∧
      ∃ (lP : LineLocalization (A := A) p.primeCompl fPn fPz)
        (lQ : LineLocalization (A := A) p.primeCompl fQn fQz)
        (lN : LineLocalization (R := R) (A := A) p.primeCompl
          (M := LinearMap.ker a.left.hom) (N := LinearMap.ker a.right.hom)
          (M' := LinearMap.ker ap.left.hom) (N' := LinearMap.ker ap.right.hom) kneg kzero)
        (np : Normalization ap),
        (∀ (x : determinantModule R (LinearMap.ker a.left.hom))
          (y : determinantModule R (Q.left : Type v)),
          lP.neg.map (n.gammaNeg (x ⊗ₜ[R] y)) =
          np.gammaNeg (lN.neg.map x ⊗ₜ[A] lQ.neg.map y)) ∧
        (∀ (x : determinantModule R (LinearMap.ker a.right.hom))
          (y : determinantModule R (Q.right : Type v)),
          lP.zero.map (n.gammaZero (x ⊗ₜ[R] y)) =
          np.gammaZero (lN.zero.map x ⊗ₜ[A] lQ.zero.map y)) ∧
        (∀ (x : determinant Q) (y : kernelDeterminant a),
          lP.map (n.assembly (x ⊗ₜ[R] y)) =
          np.assembly (lQ.map x ⊗ₜ[A] lN.map y)) ∧
        lN.map n.element = np.element ∧
        (∀ x, lQ.map (n.inverse x) = np.inverse (lP.map x)) := by
  sorry

/-- The four normalization identities for a square of chain isomorphisms. Kernel
isomorphisms are pinned as restrictions of u and determinant maps by exterior inclusion.
Source: Stacks Project, More on Algebra, Tags 0FJC, 0FJI and 0FJK, first paragraph
(blueprint: lem-trf-two-term-normalization-locality-equivariance).

Proof, steps 6--8: restrict u and its inverse to the kernels. On a finite free chart,
choose kernel-first bases and quotient lifts. Both gamma composites give the same
ordered wedge, so local equality detection proves the two gamma squares. The kernel
chain equation and the Hom interpretation of D give preservation of delta. Tensor
the degree-zero square with the inverse dual of the negative square and reorder the
factors by ordinary symmetry to get the Gamma square. Insert delta into this square
and cancel the two inverse normalization maps to get the T square. This includes
empty wedges, characteristic two and the zero ring. -/
theorem normalization_equivariance {R : Type u} [CommRing R]
    {P Q P' Q' : Arrow (ModuleCat.{v} R)} (a : P ⟶ Q) (a' : P' ⟶ Q')
    [Module.Finite R P.left] [Module.Projective R P.left]
    [Module.Finite R P.right] [Module.Projective R P.right]
    [Module.Finite R Q.left] [Module.Projective R Q.left]
    [Module.Finite R Q.right] [Module.Projective R Q.right]
    [Module.Finite R P'.left] [Module.Projective R P'.left]
    [Module.Finite R P'.right] [Module.Projective R P'.right]
    [Module.Finite R Q'.left] [Module.Projective R Q'.left]
    [Module.Finite R Q'.right] [Module.Projective R Q'.right]
    (ha : DegreewiseSurjective a) (hqa : QuasiIso a)
    (ha' : DegreewiseSurjective a') (hqa' : QuasiIso a')
    (n : Normalization a) (n' : Normalization a')
    (uIso : P' ≅ P) (vIso : Q' ≅ Q)
    (h : uIso.hom ≫ a = a' ≫ vIso.hom) :
    ∃ (cneg : LinearMap.ker a'.left.hom ≃ₗ[R] LinearMap.ker a.left.hom)
      (czero : LinearMap.ker a'.right.hom ≃ₗ[R] LinearMap.ker a.right.hom),
      (∀ x, (cneg x).val = uIso.hom.left.hom x.val) ∧
      (∀ x, (czero x).val = uIso.hom.right.hom x.val) ∧
      (∀ x, kernelDifferential a (cneg x) = czero (kernelDifferential a' x)) ∧
      ∃ (dUn : DeterminantIso ((Arrow.leftFunc.mapIso uIso).toLinearEquiv))
        (dUz : DeterminantIso ((Arrow.rightFunc.mapIso uIso).toLinearEquiv))
        (dVn : DeterminantIso ((Arrow.leftFunc.mapIso vIso).toLinearEquiv))
        (dVz : DeterminantIso ((Arrow.rightFunc.mapIso vIso).toLinearEquiv))
        (dCn : DeterminantIso cneg) (dCz : DeterminantIso czero),
        (∀ x y, dUn.map (n'.gammaNeg (x ⊗ₜ[R] y)) =
          n.gammaNeg (dCn.map x ⊗ₜ[R] dVn.map y)) ∧
        (∀ x y, dUz.map (n'.gammaZero (x ⊗ₜ[R] y)) =
          n.gammaZero (dCz.map x ⊗ₜ[R] dVz.map y)) ∧
        lineIso dCn dCz n'.element = n.element ∧
        (∀ x y, lineIso dUn dUz (n'.assembly (x ⊗ₜ[R] y)) =
          n.assembly (lineIso dVn dVz x ⊗ₜ[R] lineIso dCn dCz y)) ∧
        (∀ x, n.inverse (lineIso dUn dUz x) = lineIso dVn dVz (n'.inverse x)) := by
  sorry

end Module.TwoTerm

end
