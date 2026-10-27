module

public import Sheaf.AlgebraicGeometry.GroupScheme.RationalModuleData
public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.RingTheory.FaithfullyFlat.Amitsur

/-! # Normal-kernel invariants descend to the affine fppf quotient

Source: Alper, Adequate moduli spaces, Proposition 9.5.1 proof, printed p.525.
(blueprint: lem-sfb-normal-kernel-invariants-quotient-action)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.RingRationalModule

variable (A : CommRingCat.{u}) (K H Q : Grp (Over (Spec A)))
variable [IsAffine K.X.left] [IsAffine H.X.left] [IsAffine Q.X.left]
variable [hKflat : Flat K.X.hom] [hHflat : Flat H.X.hom] [hQflat : Flat Q.X.hom]
variable [hKfp : LocallyOfFinitePresentation K.X.hom]
variable [hHfp : LocallyOfFinitePresentation H.X.hom] [hQfp : LocallyOfFinitePresentation Q.X.hom]
variable (i : K ⟶ H) (π : H ⟶ Q)
variable [hπflat : Flat π.hom.hom.left] [hπsurj : Surjective π.hom.hom.left]
variable [hπfp : LocallyOfFinitePresentation π.hom.hom.left]
variable (hquot : IsFppfGroupQuotient i π)

include hquot hKflat hHflat hQflat hKfp hHfp hQfp hπflat hπsurj hπfp

/-- Kernel invariants have a unique rational quotient coaction whose inflation makes
inclusion equivariant. Source: Alper, Proposition 9.5.1 proof, p.525.
(blueprint: lem-sfb-normal-kernel-invariants-quotient-action)

Proof:
1. The affine flatness criterion gives flat coordinate algebras B=C_H, D=C_K,
   C=C_Q. The flat surjective spectrum criterion makes C to B faithfully flat.
2. Evaluate coactions on all algebra points. The kernel square gives normality
   and H times K isomorphic to H times_Q H by (h,k) mapped to (h,hk).
3. Put N=ker(rho restricted to K minus the trivial map). Flat tensor exactness
   identifies N tensor S with K_S invariants for flat S, in particular B and D.
4. Conjugation shows rho(N) lies in N tensor B. The injective tensor inclusions
   give a unique H-coaction alpha on N, trivial on K, with the original laws.
5. Its two pullbacks to B tensor_C B agree since K acts trivially. Amitsur exactness
   (lem-pc-cech-exact) for the arbitrary C-module N tensor C descends alpha uniquely
   to beta:N to N tensor C; injectivity of the augmentation gives linearity.
6. Applying Amitsur injectivity twice detects coassociativity after tensoring both
   coordinate factors C to B. It also detects counitality and uniqueness. Flatness
   of B makes the inclusion N tensor B to V tensor B injective. No module is assumed
   flat or finite, and the kernel need not be smooth or reduced.
-/
theorem normalKernelInvariants_unique
    (V : Type v) [AddCommGroup V] [Module A V]
    (ρ : V →ₗ[A] V ⊗[A] Γ(H.X.left, ⊤)) (hρ : IsRational A H V ρ) :
    ∃! β : invariants A K V (restrict A H V i ρ) →ₗ[A]
        invariants A K V (restrict A H V i ρ) ⊗[A] Γ(Q.X.left, ⊤),
      IsRational A Q (invariants A K V (restrict A H V i ρ)) β ∧
      IsEquivariant A H (invariants A K V (restrict A H V i ρ))
        (restrict A Q (invariants A K V (restrict A H V i ρ)) π β) ρ
        (invariants A K V (restrict A H V i ρ)).subtype := by
  sorry

/-- Every H-equivariant map restricts to a Q-equivariant linear map on kernel invariants.
The restriction is characterized by its composite with the inclusion.
Source: Alper, Proposition 9.5.1 proof, p.525.
(blueprint: lem-sfb-normal-kernel-invariants-quotient-action)

Proof: step 7 restricts the coaction square to K, so the map sends ker d to ker d'.
Its ordinary submodule restriction has the asserted inclusion composite. The two
Q-coaction expressions agree after tensoring C_Q to C_H and including in V'.
Amitsur injectivity for arbitrary modules and flat tensor exactness make both maps
injective, so this detects the required Q-equivariance. Identities and composites
are preserved since these are restrictions of the original linear maps.
-/
theorem normalKernelInvariants_maps
    (V : Type v) [AddCommGroup V] [Module A V]
    (V' : Type w) [AddCommGroup V'] [Module A V']
    (ρ : V →ₗ[A] V ⊗[A] Γ(H.X.left, ⊤)) (hρ : IsRational A H V ρ)
    (ρ' : V' →ₗ[A] V' ⊗[A] Γ(H.X.left, ⊤)) (hρ' : IsRational A H V' ρ')
    (β : invariants A K V (restrict A H V i ρ) →ₗ[A]
      invariants A K V (restrict A H V i ρ) ⊗[A] Γ(Q.X.left, ⊤))
    (hβ : IsRational A Q (invariants A K V (restrict A H V i ρ)) β)
    (hβi : IsEquivariant A H (invariants A K V (restrict A H V i ρ))
      (restrict A Q (invariants A K V (restrict A H V i ρ)) π β) ρ
      (invariants A K V (restrict A H V i ρ)).subtype)
    (β' : invariants A K V' (restrict A H V' i ρ') →ₗ[A]
      invariants A K V' (restrict A H V' i ρ') ⊗[A] Γ(Q.X.left, ⊤))
    (hβ' : IsRational A Q (invariants A K V' (restrict A H V' i ρ')) β')
    (hβ'i : IsEquivariant A H (invariants A K V' (restrict A H V' i ρ'))
      (restrict A Q (invariants A K V' (restrict A H V' i ρ')) π β') ρ'
      (invariants A K V' (restrict A H V' i ρ')).subtype)
    (f : V →ₗ[A] V') (hf : IsEquivariant A H V ρ ρ' f) :
    ∃ fN : invariants A K V (restrict A H V i ρ) →ₗ[A]
        invariants A K V' (restrict A H V' i ρ'),
      (invariants A K V' (restrict A H V' i ρ')).subtype ∘ₗ fN =
        f ∘ₗ (invariants A K V (restrict A H V i ρ)).subtype ∧
      IsEquivariant A Q (invariants A K V (restrict A H V i ρ)) β β' fN := by
  sorry

/-- Inflation preserves the invariant submodule, as equality inside the original module.
Source: Alper, Proposition 9.5.1 proof, p.525.
(blueprint: lem-sfb-normal-kernel-invariants-quotient-action)

Proof: step 8 identifies the inflated fixed-vector equation with the image of
rho(w)-w tensor 1 under 1 tensor pi*. Amitsur exactness makes this augmentation
injective for every module, so the inflated and original fixed equations coincide.
-/
theorem inflation_invariants
    (W : Type v) [AddCommGroup W] [Module A W]
    (ρ : W →ₗ[A] W ⊗[A] Γ(Q.X.left, ⊤)) (hρ : IsRational A Q W ρ) :
    IsRational A H W (restrict A Q W π ρ) ∧
      invariants A H W (restrict A Q W π ρ) = invariants A Q W ρ := by
  sorry

/-- Inflation detects equivariance between arbitrary rational quotient modules.
Source: Alper, Proposition 9.5.1 proof, p.525.
(blueprint: lem-sfb-normal-kernel-invariants-quotient-action)

Proof: step 8 applies 1 tensor pi* to the difference between the two expressions
in the Q-coaction square. The resulting equation is exactly the H-coaction square
for inflation. Amitsur injectivity on the target module detects its vanishing;
the converse is immediate by composing with 1 tensor pi*. No finiteness is used.
-/
theorem inflation_equivariant_iff
    (W : Type v) [AddCommGroup W] [Module A W]
    (W' : Type w) [AddCommGroup W'] [Module A W']
    (ρ : W →ₗ[A] W ⊗[A] Γ(Q.X.left, ⊤)) (hρ : IsRational A Q W ρ)
    (ρ' : W' →ₗ[A] W' ⊗[A] Γ(Q.X.left, ⊤)) (hρ' : IsRational A Q W' ρ')
    (f : W →ₗ[A] W') :
    IsEquivariant A Q W ρ ρ' f ↔
      IsEquivariant A H W (restrict A Q W π ρ) (restrict A Q W' π ρ') f := by
  sorry

end AlgebraicGeometry.RingRationalModule
