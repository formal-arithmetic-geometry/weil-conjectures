/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Sheaf.AlgebraicGeometry.FlatLCICanonicalAdjunction
public import Sheaf.AlgebraicGeometry.PureDimension
public import WeilConjectures.RingTheory.CompleteIntersectionOverField
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.LinearAlgebra.TensorProduct.Tower

import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import Sheaf.TraceFormula.CompletedJacobianDifferentials
import Sheaf.RingTheory.FormalJacobianCoordinateChainRule

/-!
# The formal plane adjunction lattice

Source: Stacks Project, Duality for Schemes, Tag 0E9Z and its preceding determinant formula;
Curves, Tags 0C4B and 0C4D. This is the completion-compatible auxiliary formulation specified
in the DAG, rather than a verbatim assertion of 0E9Z
(blueprint: lem-trf-formal-plane-adjunction-lattice).

The coefficient of `dt` identifies the ambient rational differential module with
`LaurentSeries k`. Tensor products put the scalar ring first. Thus the completed branch span
is written `k[[t]] ⊗[S] Γ(K, ⊤)`, canonically the iterated extension from the stalk at `m`.
The generic comparison below is normalized by the recorded smooth-locus determinant map;
it cannot be replaced by an arbitrary isomorphism of one-dimensional vector spaces.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Global sections of the canonical adjunction line on the affine curve. Localizing this
module at `m` gives precisely its stalk `K_A`.
Source: Stacks, Tag 0E9Z (blueprint: lem-trf-formal-plane-adjunction-lattice). -/
noncomputable abbrev formalPlaneAdjunctionSections
    {k S : Type u} [Field k] [CommRing S] [Algebra k S]
    (J : FlatLCIAdjunctionSystem (Spec.map (CommRingCat.ofHom (algebraMap k S))) 1) :=
  (moduleSpecΓFunctor (R := CommRingCat.of S)).obj
    (J.line (FlatLCIBaseChange.identity (Spec.map (CommRingCat.ofHom (algebraMap k S)))))

/-- Evaluate a regular function on an open chart at the specified branch generic point.
Source: Stacks, Tag 0E9Z (blueprint: lem-trf-formal-plane-adjunction-lattice). -/
noncomputable def formalPlaneGenericValue {F : Type u} [Field F] {U : Scheme.{u}}
    (h : Spec (CommRingCat.of F) ⟶ U) : Γ(U, ⊤) →+* F :=
  (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.comp h.appTop.hom

/-- The prescribed generic comparison, expressed on a smooth affine neighbourhood of the
branch generic point. The additive map `ρ` is fixed on all scalar multiples of all universal
differentials (written as one-fold wedges). These generate the differential module on the
affine chart, so this condition fixes the map, including its scalar normalization.
Source: Stacks, Tag 0E9Z, preceding determinant formula and smooth restriction
(blueprint: lem-trf-formal-plane-adjunction-lattice). -/
def IsFormalPlaneGenericComparison
    {k S F : Type u} [Field k] [CommRing S] [Algebra k S]
    [Field F] [Algebra k F] [Algebra S F]
    (J : FlatLCIAdjunctionSystem (Spec.map (CommRingCat.ofHom (algebraMap k S))) 1)
    (q : formalPlaneAdjunctionSections J → KaehlerDifferential k F) : Prop :=
  ∃ (U : (Spec (CommRingCat.of S)).Opens),
    IsAffine U.toScheme ∧
    Nonempty (FlatLCIPresentation (Spec.map (CommRingCat.ofHom (algebraMap k S))) 1 U) ∧
    Smooth (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S))) ∧
    ∃ (h : Spec (CommRingCat.of F) ⟶ U.toScheme),
      h ≫ U.ι = Spec.map (CommRingCat.ofHom (algebraMap S F)) ∧
      ∃ (e : (Scheme.Modules.tensorPullback U.ι).obj
          (J.line (FlatLCIBaseChange.identity
            (Spec.map (CommRingCat.ofHom (algebraMap k S))))) ≅
          Scheme.Modules.exteriorSheaf
            (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S))).relativeDifferentials 1),
        J.IsSmoothComparison (FlatLCIBaseChange.identity
          (Spec.map (CommRingCat.ofHom (algebraMap k S)))) U e ∧
        ∃ ρ : Γ(Scheme.Modules.exteriorSheaf
            (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S))).relativeDifferentials 1,
            ⊤) →+ KaehlerDifferential k F,
          (∀ a b : Γ(U.toScheme, ⊤),
            ρ (a • Scheme.Modules.exteriorSheafSection
              (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S))).relativeDifferentials
              1 ⊤ (fun _ ↦
                (Scheme.Hom.relativeDifferentialsDerivation
                  (U.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap k S)))).d (X := op ⊤) b)) =
              formalPlaneGenericValue h a •
                KaehlerDifferential.D k F (formalPlaneGenericValue h b)) ∧
          ∀ s : formalPlaneAdjunctionSections J,
            q s = ρ (e.hom.app ⊤ (Scheme.Modules.tensorPullbackSection U.ι
              (J.line (FlatLCIBaseChange.identity
                (Spec.map (CommRingCat.ofHom (algebraMap k S))))) ⊤ s))

/-- The coefficient of `dx/f_y` after the formal branch substitution.
Source: Stacks, Tag 0E9Z, determinant calculation
(blueprint: lem-trf-formal-plane-adjunction-lattice). -/
noncomputable def formalPlaneResidueY {k : Type u} [Field k]
    (π : MvPowerSeries (Fin 2) k →ₐ[k] PowerSeries k) (f : MvPowerSeries (Fin 2) k) :
    LaurentSeries k :=
  algebraMap (PowerSeries k) (LaurentSeries k)
      (PowerSeries.derivative k (π (MvPowerSeries.X 0))) /
    algebraMap (PowerSeries k) (LaurentSeries k) (π (MvPowerSeries.pderiv k 1 f))

/-- The coefficient of `-dy/f_x` after the formal branch substitution.
Source: Stacks, Tag 0E9Z, determinant calculation
(blueprint: lem-trf-formal-plane-adjunction-lattice). -/
noncomputable def formalPlaneResidueX {k : Type u} [Field k]
    (π : MvPowerSeries (Fin 2) k →ₐ[k] PowerSeries k) (f : MvPowerSeries (Fin 2) k) :
    LaurentSeries k :=
  -(algebraMap (PowerSeries k) (LaurentSeries k)
      (PowerSeries.derivative k (π (MvPowerSeries.X 1))) /
    algebraMap (PowerSeries k) (LaurentSeries k) (π (MvPowerSeries.pderiv k 0 f)))

/-- Change coefficients of a differential under `t ↦ σ(t)`: substitute by `τ` and multiply
by `σ(t)'`, the coefficient of `dt` in the new parameter.
Source: Stacks, Curves, Tag 0C4B, chain rule
(blueprint: lem-trf-formal-plane-adjunction-lattice). -/
noncomputable def formalPlaneParameterTransport {k : Type u} [Field k]
    (σ : PowerSeries k ≃ₐ[k] PowerSeries k)
    (τ : LaurentSeries k ≃ₐ[k] LaurentSeries k) (z : LaurentSeries k) : LaurentSeries k :=
  algebraMap (PowerSeries k) (LaurentSeries k) (PowerSeries.derivative k (σ PowerSeries.X)) *
    τ z

/-- The formal plane calculation with its intrinsic generic normalization.
Source: Stacks, Tag 0E9Z and its determinant formula, with the completion-compatible
auxiliary formulation of this node (blueprint: lem-trf-formal-plane-adjunction-lattice).

Proof:
1. By lem-weil-pbc-power-series-domain the power series ring is a domain. The nonzero
   equation is a nonzerodivisor, and membership in the variable ideal makes it a regular
   sequence of length one (def-weil-pbc-regular-sequence). Apply
   lem-trf-completed-conormal-determinant-comparison with n=2,c=d=1. Its normalization
   identifies the completed algebraic adjunction line with the formal conormal determinant
   through the specified generic smooth comparison, rather than through an arbitrary scalar.
2. Write a=f_x and b=f_y on the branch. The determinant map sends dx to bε and dy to -aε
   for ε=-f∨⊗(dx∧dy). Its inverse sends ε to dx/b or -dy/a, respectively.
3. Apply lem-trf-completed-jacobian-differentials to the smooth branch with one variable
   and no equation. This identifies its completed regular differentials with k[[t]]dt.
   The extension of the universal derivation is coefficientwise differentiation; the
   quotient rule identifies its rational extension with the stated Laurent derivative.
4. Apply the same lemma to the plane presentation. Continuity and agreement on the dense
   algebraic local ring imply dx maps to x'(t)dt and dy maps to y'(t)dt. Tensor associativity
   identifies the completed D-span with the tensor product in the conclusion. The generic
   comparison and step 3 show that the residue generator is nonzero, hence a free basis.
5. The conormal relation gives ax'+by'=0. Dividing by ab proves agreement when both are nonzero.
6. The canonical generic comparison and its pure-tensor characterization are independent
   of algebraic and formal presentations. Under a parameter change, apply
   lem-trf-formal-jacobian-coordinate-chain-rule in one variable: dt goes to t'(s)ds,
   an invertible change of the regular differential module. The same intrinsic tensor
   module and its uniquely characterized map therefore compare all the calculated lattices.
-/
theorem formalPlaneAdjunctionLattice
    (k S A Q D F : Type u) [Field k] [IsAlgClosed k]
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S] [_root_.IsReduced S]
    (_hpure : (Spec (CommRingCat.of S)).IsPureDimension 1)
    (_hlci : Algebra.IsLocalCompleteIntersection k S)
    (m : Ideal S) [m.IsMaximal] (_hm : Nonempty ((S ⧸ m) ≃ₐ[k] k))
    [CommRing A] [Algebra S A] [IsLocalization.AtPrime A m] [IsLocalRing A]
    [Algebra k A] [IsScalarTower k S A]
    [CommRing Q] [Algebra A Q] [IsLocalization (nonZeroDivisors A) Q]
    (n : Ideal (integralClosure A Q)) [n.IsMaximal]
    (_hn : Ideal.comap (algebraMap A (integralClosure A Q)) n = IsLocalRing.maximalIdeal A)
    [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [Algebra (integralClosure A Q) D] [IsLocalization.AtPrime D n]
    [Algebra A D] [IsScalarTower A (integralClosure A Q) D]
    [Algebra k D] [IsScalarTower k A D] [Algebra.EssFiniteType k D]
    (_hresidue : Nonempty ((IsLocalRing.ResidueField D) ≃ₐ[k] k))
    (_hcurve : ∃ (C : Scheme.{u}) (p : C ⟶ Spec (CommRingCat.of k)),
      IsCurve p ∧ Smooth p ∧ ∃ (z : C) (e : D ≃+* C.presheaf.stalk z),
        ∀ c : k, e (algebraMap k D c) =
          C.presheaf.germ ⊤ z (by trivial)
            (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)))
    [Field F] [Algebra D F] [IsFractionRing D F]
    [Algebra k F] [IsScalarTower k D F]
    [Algebra S F]
    (_hSF : ∀ s : S, algebraMap S F s =
      algebraMap D F (algebraMap A D (algebraMap S A s)))
    (J : FlatLCIAdjunctionSystem (Spec.map (CommRingCat.ofHom (algebraMap k S))) 1)
    (_hJ : J.IsNormalized)
    (q : formalPlaneAdjunctionSections J → KaehlerDifferential k F)
    (_hq : IsFormalPlaneGenericComparison J q)
    (f : MvPowerSeries (Fin 2) k) (_hf : f ≠ 0)
    (_hforigin : f ∈ Ideal.span (Set.range
      (fun i : Fin 2 ↦ (MvPowerSeries.X i : MvPowerSeries (Fin 2) k))))
    (_hreduced : _root_.IsReduced (MvPowerSeries (Fin 2) k ⧸ Ideal.span {f}))
    (α : (MvPowerSeries (Fin 2) k ⧸ Ideal.span {f}) ≃ₐ[k]
      AdicCompletion (IsLocalRing.maximalIdeal A) A)
    (θ : AdicCompletion (IsLocalRing.maximalIdeal D) D ≃ₐ[k] PowerSeries k)
    (ψ : AdicCompletion (IsLocalRing.maximalIdeal A) A →ₐ[k] PowerSeries k)
    (_hψ : ∀ a : A,
      ψ (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A) a) =
        θ (algebraMap D (AdicCompletion (IsLocalRing.maximalIdeal D) D) (algebraMap A D a)))
    (π : MvPowerSeries (Fin 2) k →ₐ[k] PowerSeries k)
    (_hπ : ∀ g : MvPowerSeries (Fin 2) k, π g = ψ (α (Ideal.Quotient.mk _ g)))
    (_hπcontinuous : ∀ r : ℕ, ∃ N : ℕ, ∀ g : MvPowerSeries (Fin 2) k,
      g ∈ (Ideal.span (Set.range
        (fun i : Fin 2 ↦ (MvPowerSeries.X i : MvPowerSeries (Fin 2) k)))) ^ N →
      π g ∈ (Ideal.span {(PowerSeries.X : PowerSeries k)}) ^ r)
    [Algebra D (PowerSeries k)]
    (_hDP : ∀ d : D, algebraMap D (PowerSeries k) d =
      θ (algebraMap D (AdicCompletion (IsLocalRing.maximalIdeal D) D) d))
    [Algebra S (PowerSeries k)]
    (_hSP : ∀ s : S, algebraMap S (PowerSeries k) s =
      θ (algebraMap D (AdicCompletion (IsLocalRing.maximalIdeal D) D)
        (algebraMap A D (algebraMap S A s))))
    [Algebra F (LaurentSeries k)]
    (_hFL : ∀ d : D, algebraMap F (LaurentSeries k) (algebraMap D F d) =
      algebraMap (PowerSeries k) (LaurentSeries k)
        (θ (algebraMap D (AdicCompletion (IsLocalRing.maximalIdeal D) D) d)))
    (δ : KaehlerDifferential k F →ₗ[F] LaurentSeries k)
    (_hδ : ∀ z : F, δ (KaehlerDifferential.D k F z) =
      LaurentSeries.derivative k (algebraMap F (LaurentSeries k) z))
    (_hpartials : π (MvPowerSeries.pderiv k 0 f) ≠ 0 ∨
      π (MvPowerSeries.pderiv k 1 f) ≠ 0) :
    ∃ Φ : PowerSeries k ⊗[S] formalPlaneAdjunctionSections J →ₗ[PowerSeries k] LaurentSeries k,
      (∀ (c : PowerSeries k) (s : formalPlaneAdjunctionSections J),
        Φ (c ⊗ₜ[S] s) = c • δ (q s)) ∧
      Function.Injective Φ ∧
      (∃ G : (F ⊗[S] formalPlaneAdjunctionSections J) ≃ₗ[F] KaehlerDifferential k F,
        ∀ s : formalPlaneAdjunctionSections J, G ((1 : F) ⊗ₜ[S] s) = q s) ∧
      (∀ Ψ : PowerSeries k ⊗[S] formalPlaneAdjunctionSections J →ₗ[PowerSeries k]
          LaurentSeries k,
        (∀ (c : PowerSeries k) (s : formalPlaneAdjunctionSections J),
          Ψ (c ⊗ₜ[S] s) = c • δ (q s)) → Ψ = Φ) ∧
      (∀ _hb : π (MvPowerSeries.pderiv k 1 f) ≠ 0,
        LinearMap.range Φ = Submodule.span (PowerSeries k) {formalPlaneResidueY π f} ∧
        formalPlaneResidueY π f ≠ 0) ∧
      (∀ _ha : π (MvPowerSeries.pderiv k 0 f) ≠ 0,
        LinearMap.range Φ = Submodule.span (PowerSeries k) {formalPlaneResidueX π f} ∧
        formalPlaneResidueX π f ≠ 0) ∧
      (π (MvPowerSeries.pderiv k 0 f) ≠ 0 → π (MvPowerSeries.pderiv k 1 f) ≠ 0 →
        formalPlaneResidueY π f = formalPlaneResidueX π f) ∧
      (∀ σ : PowerSeries k ≃ₐ[k] PowerSeries k,
        ∃ τ : LaurentSeries k ≃ₐ[k] LaurentSeries k,
          (∀ c : PowerSeries k,
            τ (algebraMap (PowerSeries k) (LaurentSeries k) c) =
              algebraMap (PowerSeries k) (LaurentSeries k) (σ c)) ∧
          IsUnit (PowerSeries.derivative k (σ PowerSeries.X)) ∧
          (∀ _hb : π (MvPowerSeries.pderiv k 1 f) ≠ 0,
            (formalPlaneParameterTransport σ τ) '' (LinearMap.range Φ : Set (LaurentSeries k)) =
              (Submodule.span (PowerSeries k)
                {formalPlaneResidueY (σ.toAlgHom.comp π) f} : Set (LaurentSeries k))) ∧
          (∀ _ha : π (MvPowerSeries.pderiv k 0 f) ≠ 0,
            (formalPlaneParameterTransport σ τ) '' (LinearMap.range Φ : Set (LaurentSeries k)) =
              (Submodule.span (PowerSeries k)
                {formalPlaneResidueX (σ.toAlgHom.comp π) f} : Set (LaurentSeries k)))) ∧
      ∃ E : (PowerSeries k ⊗[D] KaehlerDifferential k D) ≃ₗ[PowerSeries k] PowerSeries k,
        ∀ (c : PowerSeries k) (d : D),
          E (c ⊗ₜ[D] KaehlerDifferential.D k D d) =
            c * PowerSeries.derivative k
              (θ (algebraMap D (AdicCompletion (IsLocalRing.maximalIdeal D) D) d)) := by
  sorry

end AlgebraicGeometry
