/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportCompositeTransposeDomains
public import WeilConjectures.AlgebraicGeometry.StandingExceptionalComposition
import WeilConjectures.CategoryTheory.CompositeTensorTranspose
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Constructible exceptional tensor composition

Source: current blueprint, sk-prop-cohsm, lem-pur-co-smooth-composition.proof.md,
opening tensor calculation, and thm-pur-cohomological-smoothness.proof.md, final paragraph
(blueprint: lem-pur-constructible-tensor-composition).

All operations below are the published transported etale adjunction operations at
arbitrary retained compactifications, with no ambient pro-etale adjoint assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory WeilConjectures
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.ConstructibleTensorComposition
open CompactSupportTranspose

variable (P : PurityFiniteSetting.{u}) {X Y Z : SixFunctorSpace P.field}

/-- The dualizing object is bounded constructible of finite Tor amplitude.
Source: sk-prop-cohsm, composition calculation, first domain check
(blueprint: lem-pur-constructible-tensor-composition).
Proof: the coefficient unit is finite free in degree zero (unitCTF). Apply the
constructible exceptional preservation assertion of def-weil-exceptional-inverse-image
at the retained compactification. Finite type over the field supplies Noetherianity;
its proper ambient scheme has the dimension bound retained in Edge. -/
theorem dualizingCTF (e : Edge P X Y) : CTF P X (W P e) := by
  sorry

/-- The displayed r_K, using pullback composition, symmetry, associativity and
pullback monoidality, in that order. No tensor-formula hypothesis enters its data.
Source: sk-prop-cohsm, displayed two-tensor-formula calculation
(blueprint: lem-pur-constructible-tensor-composition). -/
def reassociate (e : Edge P X Y) (d : Edge P Y Z) (K : D P Z) :
    (upperStar (ModuleCat.{u + 1} P.Coefficient)
      (e.f.hom.left ≫ d.f.hom.left)).leftDerivedFunctor.obj K ⊗
        (W P e ⊗ (S P e).obj (W P d)) ⟶
      (S P e).obj ((S P d).obj K ⊗ W P d) ⊗ W P e :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      e.f.hom.left d.f.hom.left).hom.app K ▷ _ ≫
    (S P e).obj ((S P d).obj K) ◁ (braid P X (W P e) ((S P e).obj (W P d))).hom ≫
    (α_ ((S P e).obj ((S P d).obj K)) ((S P e).obj (W P d)) (W P e)).inv ≫
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) e.f.hom.left
      ((S P d).obj K) (W P d)).inv ▷ W P e

variable (e : Edge P X Y) (d : Edge P Y Z)
    (c : Compactification (e.f.hom.left ≫ d.f.hom.left)) (n : ℕ)
    (hn : topologicalKrullDim c.Z ≤ (n : WithBot ℕ∞))

/-- Phi_K is literally r_K, theta_f, G_f(theta_g), and the inverse adjunction conjugate.
The last map is the published inverse transpose, not an arbitrarily chosen isomorphism.
Source: sk-prop-cohsm, composition tensor calculation
(blueprint: lem-pur-constructible-tensor-composition). -/
def phi (K : D P Z) (hK : CTF P Z K) :
    (S P (compositeEdge P e d c n hn)).obj K ⊗
        (W P e ⊗ (S P e).obj (W P d)) ⟶
      (G P (compositeEdge P e d c n hn)).obj K :=
  reassociate P e d K ≫
    theta P e (dualizingCTF P e) _
      (tensorInputCTF P d K (W P d) hK (dualizingCTF P d)) ≫
    (G P e).map (theta P d (dualizingCTF P d) K hK) ≫
    conjugateInv P e d c n hn K hK.plus

/-- The unit component a = Phi_Lambda, with the canonical pullback-unit isomorphism
and left unitor inserted. Its source is omega_f tensor Lf*omega_g.
Source: sk-prop-cohsm, composition tensor calculation, coefficient-unit specialization
(blueprint: lem-pur-constructible-tensor-composition). -/
def unitComponent : W P e ⊗ (S P e).obj (W P d) ⟶
    W P (compositeEdge P e d c n hn) :=
  (λ_ (W P e ⊗ (S P e).obj (W P d))).inv ≫
    (leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient)
      (e.f.hom.left ≫ d.f.hom.left)).inv ▷ _ ≫
    phi P e d c n hn (𝟙_ (D P Z)) (unitCTF P Z)

/-- The specified conjugate is natural and invertible, with the normalized composite
counit; Phi and its unit component are isomorphisms and satisfy the canonical-map identity.
Source: sk-prop-cohsm, lem-pur-co-smooth-composition.proof.md, opening calculation,
and thm-pur-cohomological-smoothness.proof.md, final paragraph
(blueprint: lem-pur-constructible-tensor-composition).

Proof:
1. Exceptional preservation gives dualizingCTF. Finite type over the field gives
Noetherianity. Nagata compactification and finite ambient dimensions give exactly
compactSupportCompositeTransposeDomains, including all tensor and Hom domains,
projection coherence, conjugate invertibility, naturality and counit normalization.
2. At the coefficient unit, the inverse-projection unit equation makes theta_g the
canonical unit identification. Hence a equals symmetry followed by theta_f at omega_g
and conjugateInv, namely the published q after symmetry.
3. Apply composite_tensor_transpose_restricted to these domains and coherent projections.
Both routes have inverse transpose the inverse f-projection, f-counit, inverse
 g-projection and g-counit, in adjunction order. Injectivity of the two Hom bijections
and naturality of theta_f give precisely Phi_K = (1 tensor a) followed by theta_h.
4. tensorInputCTF puts Lg*K tensor omega_g in Dctf, so the two assumed tensor
isomorphisms apply. Functors preserve isomorphisms, and r and c are isomorphisms.
Thus Phi_K and its unit component a are isomorphisms. No inverse dualizing object
or dualizing base-change assumption is used. -/
theorem constructible_tensor_composition
    (hf : ∀ (B : D P Y) (hB : CTF P Y B),
      IsIso (theta P e (dualizingCTF P e) B hB))
    (hg : ∀ (K : D P Z) (hK : CTF P Z K),
      IsIso (theta P d (dualizingCTF P d) K hK)) :
    (∀ (K : D P Z) (hK : CTF P Z K),
      IsIso (conjugate P e d c n hn K hK.plus) ∧
      conjugate P e d c n hn K hK.plus ≫ conjugateInv P e d c n hn K hK.plus = 𝟙 _ ∧
      conjugateInv P e d c n hn K hK.plus ≫ conjugate P e d c n hn K hK.plus = 𝟙 _ ∧
      (image P d).map ((image P e).map (conjugate P e d c n hn K hK.plus)) ≫
          (image P d).map (counit P e _ (exceptionalOriginProperty P d K hK.plus).plus) ≫
          counit P d K hK.plus =
        (alpha P e d c _
          (exceptionalOriginProperty P (compositeEdge P e d c n hn) K hK.plus)).hom ≫
            counit P (compositeEdge P e d c n hn) K hK.plus) ∧
    (∀ (K L : D P Z) (hK : CTF P Z K) (hL : CTF P Z L) (b : K ⟶ L),
      (G P (compositeEdge P e d c n hn)).map b ≫ conjugate P e d c n hn L hL.plus =
        conjugate P e d c n hn K hK.plus ≫ (G P e).map ((G P d).map b)) ∧
    IsIso (unitComponent P e d c n hn) ∧
    (∀ (K : D P Z) (hK : CTF P Z K),
      IsIso (reassociate P e d K) ∧ IsIso (phi P e d c n hn K hK) ∧
      phi P e d c n hn K hK =
        (S P (compositeEdge P e d c n hn)).obj K ◁ unitComponent P e d c n hn ≫
          theta P (compositeEdge P e d c n hn)
            (dualizingCTF P (compositeEdge P e d c n hn)) K hK) := by
  sorry

end AlgebraicGeometry.ProEtale.ConstructibleTensorComposition
