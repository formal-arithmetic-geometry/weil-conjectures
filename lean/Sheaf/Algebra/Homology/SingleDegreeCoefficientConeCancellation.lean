/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.DerivedBaseChange
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs

import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.RingTheory.RingPseudoCoherent
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.Algebra.Homology.RingedTensorCohomologicalBounds
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import WeilConjectures.AlgebraicGeometry.AffineDerivedPushforwardTExact
import WeilConjectures.AlgebraicGeometry.DerivedAdjoint

/-! # Cancellation of a finite top coefficient-cone obstruction

Source: agent-formulated affine prerequisite for the Kiehl paragraph after Stacks
Tag 0CSD, perfect.tex, lemma-flat-proper-pseudo-coherent-direct-image-general.
That paragraph does not itself assert this lemma; the Kiehl primary proof is WANTED.
(blueprint: lem-sfb-single-degree-coefficient-cone-cancellation).

We use the canonical tensor presentation Q_D tensor_D A of Q_A, identified with
A[x_1,...,x_s] by tensor symmetry and MvPolynomial.algebraTensorAlgEquiv.
Universal arrows IsDerivedBaseChange specify derived tensor and its unit, rather
than an arbitrary map. Their transpose equation specifies extension followed by
its actual scalar-action counit. In the conclusion the bound is tested after
forgetting the retained S'-action to A: exact faithful forgetful functors detect
cohomology vanishing, so this is the same bound on the stipulated S'-linear cone.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped TensorProduct

namespace ModuleCat

/-- Canonical identity-on-elements restriction transport around a commutative ring square.
Source: Stacks Tag 05G3, restriction of scalars and composition; Mathlib
restrictScalarsCongr and the existing derivedRestrictScalarsCompIso.
(blueprint: lem-sfb-single-degree-coefficient-cone-cancellation). -/
noncomputable def coefficientConeRestrictionSquareIso
    {R₀ R₁ R₂ R₃ : Type u}
    [CommRing R₀] [CommRing R₁] [CommRing R₂] [CommRing R₃]
    (f : R₀ →+* R₁) (g : R₁ →+* R₃)
    (h : R₀ →+* R₂) (k : R₂ →+* R₃) (w : g.comp f = k.comp h) :
    derivedRestrictScalars g ⋙ derivedRestrictScalars f ≅
      derivedRestrictScalars k ⋙ derivedRestrictScalars h :=
  derivedRestrictScalarsCompIso rfl ≪≫
    Functor.mapDerivedCategoryNatIso (restrictScalarsCongr w) ≪≫
    (derivedRestrictScalarsCompIso rfl).symm

/-- A finite top obstruction to the coefficient action map can be cancelled in one degree.
Source: agent-formulated prerequisite for the unnumbered Kiehl paragraph following
Stacks Tag 0CSD, perfect.tex; supporting Tags 066E, 0145, 0152 and 05RS.
(blueprint: lem-sfb-single-degree-coefficient-cone-cancellation).

Proof plan, with the node's ten steps:
1. Transfer L, K and gamma to Spec S and use def-sfb-dg-coefficient-realization,
lem-pc-affine-qcoh-derived-equivalence and lem-sfb-dg-coefficient-realization-comparison.
Their normalized comparison identifies the polynomial restriction of the dg cone
with C_Q, including the actual action counit.
2. Finite type over Noetherian D makes S Noetherian. By
lem-weil-pbc-noetherian-pseudocoherent-cohomology-criterion and
def-pc-ring-pseudo-coherent-complex choose a bounded-above finite-free model F of L.
Its brutal tail E in degrees at least n is bounded finite free. The quotient N is
zero above n-1, and lem-weil-pbc-complex-ses-triangle gives E -> L -> N.
3. The dg functor T is exact, computes A tensor_D^L with the S-action, and sends N
to degrees at most n-1 by lem-weil-pbc-ringed-tensor-cohomological-bounds and
lem-pc-affine-derived-pullback-tensor-tilde. Its image of E is perfect by its finite
free filtration, using the dg comparison and realization definitions.
4. TR4 gives T(N) -> C_E -> C_Q. The long exact sequence
lem-sf-derived-homology-long-exact identifies H^i(C_E) with H^i(C_Q) for i >= n,
Q_A-linearly. Pick finitely many generators z_j of H^n(C_E); its action factors
through S_A, so they also generate over S_A.
5. Lift z_j to cycles of an affine complex, obtaining S^r[-n] -> U(C_E).
Transpose by T adjoint to U to obtain q : B^r[-n] -> C_E. Its H^n is onto since
H^0(B)=S_A and its higher cohomology is zero; use the affine equivalence and dg
comparison, including the actual multiplication action.
6. Put V=Cone(q). Its cohomology vanishes in degrees >= n. TR4, equivalently the
homotopy pullback of K-hat -> C_E along q, gives a perfect H and u:H -> K-hat
whose cone is V. Thus H^i(u) is an isomorphism above n and onto at n.
7. Apply lem-sfb-perfect-coefficient-arrow-finite-realization on Spec S with m=n.
The given presentation makes this scheme separated and finite type. It gives D',
a bounded coherent G, gamma', and sigma:H -> Phi_D'(G) with nu(gamma') sigma=u
and H^i(sigma) onto for i >= n.
8. At n the composite implies H^n(nu(gamma')) is onto. Above n an onto first
factor with invertible composite is invertible, as is the second factor.
The long exact sequence gives cone cohomology zero for every i >= n.
9. Identify the affine base change with Spec(S tensor_D D') and take its affine
module L'. Finite-type Noetherian permanence and coherent=quasi-coherent finite
type give bounded finite cohomology. Use pqf-lem-coherent-ft-locnoeth,
lem-weil-pbc-quasi-coherent-finite-type-affine and the affine derived equivalence.
The normalized dg comparison, affine pullback/tensor formula and
lem-pc-ringed-spaces-derived-adjoint identify gamma' and the action arrow with
those here: both transposes apply gamma' followed by the given A-action.
lem-sc-affine-derived-pushforward-t-exact detects the cone bound after forgetting.
10. The same construction permits r=0, E=0, K=0, s=0, zero rings and all integers n.
Only upper tensor bounds are used; negative Tor is retained. There is no required
map from L to L', no pseudo-coherence assumption on K and no lower-degree claim. -/
theorem singleDegreeCoefficientConeCancellation
    (D A S : Type u) [CommRing D] [CommRing A] [CommRing S]
    [IsNoetherianRing D] [Algebra D A] [Algebra D S] [Algebra.FiniteType D S]
    (s : ℕ) (q : MvPolynomial (Fin s) D →ₐ[D] S) (hq : Function.Surjective q)
    (K : DerivedCategory (ModuleCat.{u} (S ⊗[D] A)))
    (L : DerivedCategory (ModuleCat.{u} S))
    (hL : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj L))
    (hLfinite : ∀ i : ℤ,
      Module.Finite S ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj L))
    (γ : L ⟶ (derivedRestrictScalars
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[D] A)).obj K)
    (T_Q : DerivedCategory (ModuleCat.{u} (MvPolynomial (Fin s) D ⊗[D] A)))
    (η_Q : (derivedRestrictScalars q.toRingHom).obj L ⟶
      (derivedRestrictScalars (Algebra.TensorProduct.includeLeftRingHom :
        MvPolynomial (Fin s) D →+* MvPolynomial (Fin s) D ⊗[D] A)).obj T_Q)
    (hη_Q : IsDerivedBaseChange η_Q)
    (θ_Q : T_Q ⟶ (derivedRestrictScalars
      (Algebra.TensorProduct.map q (AlgHom.id D A)).toRingHom).obj K)
    (hθ_Q : η_Q ≫
        (derivedRestrictScalars (Algebra.TensorProduct.includeLeftRingHom :
          MvPolynomial (Fin s) D →+* MvPolynomial (Fin s) D ⊗[D] A)).map θ_Q ≫
        (coefficientConeRestrictionSquareIso q.toRingHom
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[D] A)
          (Algebra.TensorProduct.includeLeftRingHom :
            MvPolynomial (Fin s) D →+* MvPolynomial (Fin s) D ⊗[D] A)
          (Algebra.TensorProduct.map q (AlgHom.id D A)).toRingHom
          (Algebra.TensorProduct.map_comp_includeLeftRingHom q (AlgHom.id D A)).symm).inv.app K =
      (derivedRestrictScalars q.toRingHom).map γ)
    (C_Q : DerivedCategory (ModuleCat.{u} (MvPolynomial (Fin s) D ⊗[D] A)))
    (ι_Q : (derivedRestrictScalars
      (Algebra.TensorProduct.map q (AlgHom.id D A)).toRingHom).obj K ⟶ C_Q)
    (δ_Q : C_Q ⟶ T_Q⟦(1 : ℤ)⟧)
    (hC_Q : Triangle.mk θ_Q ι_Q δ_Q ∈ distTriang _)
    (n : ℤ)
    (hupper : ∀ i : ℤ, n < i → IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{u}
        (MvPolynomial (Fin s) D ⊗[D] A)) i).obj C_Q))
    (hfinite : Module.Finite (MvPolynomial (Fin s) D ⊗[D] A)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u}
        (MvPolynomial (Fin s) D ⊗[D] A)) n).obj C_Q)) :
    ∃ (D' : Type u) (_ : CommRing D') (_ : Algebra D D') (_ : Algebra D' A)
      (_ : IsScalarTower D D' A),
      Algebra.FiniteType D D' ∧
      ∃ (L' : DerivedCategory (ModuleCat.{u} (S ⊗[D] D')))
        (γ' : L' ⟶ (derivedRestrictScalars
          (Algebra.TensorProduct.map (AlgHom.id D S)
            (IsScalarTower.toAlgHom D D' A)).toRingHom).obj K),
        (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (S ⊗[D] D')) i).obj L')) ∧
        (∀ i : ℤ, Module.Finite (S ⊗[D] D')
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} (S ⊗[D] D')) i).obj L')) ∧
        ∃ (T' : DerivedCategory (ModuleCat.{u} A))
          (η' : (derivedRestrictScalars
              (Algebra.TensorProduct.includeRight : D' →ₐ[D] S ⊗[D] D').toRingHom).obj L' ⟶
            (derivedRestrictScalars (algebraMap D' A)).obj T'),
          IsDerivedBaseChange η' ∧
          ∃ (θ' : T' ⟶ (derivedRestrictScalars
                (Algebra.TensorProduct.includeRight : A →ₐ[D] S ⊗[D] A).toRingHom).obj K)
            (C' : DerivedCategory (ModuleCat.{u} A))
            (ι' : (derivedRestrictScalars
                (Algebra.TensorProduct.includeRight : A →ₐ[D] S ⊗[D] A).toRingHom).obj K ⟶ C')
            (δ' : C' ⟶ T'⟦(1 : ℤ)⟧),
            (η' ≫ (derivedRestrictScalars (algebraMap D' A)).map θ' =
              (derivedRestrictScalars
                (Algebra.TensorProduct.includeRight : D' →ₐ[D] S ⊗[D] D').toRingHom).map γ' ≫
              (coefficientConeRestrictionSquareIso
                (Algebra.TensorProduct.includeRight : D' →ₐ[D] S ⊗[D] D').toRingHom
                (Algebra.TensorProduct.map (AlgHom.id D S)
                  (IsScalarTower.toAlgHom D D' A)).toRingHom
                (algebraMap D' A)
                (Algebra.TensorProduct.includeRight : A →ₐ[D] S ⊗[D] A).toRingHom
                (congrArg AlgHom.toRingHom (Algebra.TensorProduct.map_comp_includeRight
                  (AlgHom.id D S) (IsScalarTower.toAlgHom D D' A)))).hom.app K) ∧
            Triangle.mk θ' ι' δ' ∈ distTriang _ ∧
            ∀ i : ℤ, n ≤ i →
              IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj C') := by
  sorry

end ModuleCat
