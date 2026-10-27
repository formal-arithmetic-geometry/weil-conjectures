/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import Sheaf.AlgebraicGeometry.ModuliChartNormalization
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Scheme representability of stable abelian-level normalization

Source: Pikaart--de Jong (1995), §§1.1 and 2.3.3--2.3.7, Proposition 2.3.4 and
Remark 2.3.7 (blueprint: lem-sfb-stable-abelian-level-normalization).

The level scheme is supplied with its representing equivalence to the recorded
full frame groupoid. The normalization is specified by integral closure on all
normal finite-type étale charts, with its map from that full level scheme.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The stable unpointed moduli category over schemes over the base.
Source: Pikaart--de Jong §1.1
(blueprint: lem-sfb-stable-abelian-level-normalization). -/
def stableModuliBased (S : Scheme.{u}) (g : ℕ) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor (StablePointedModuli.forget S g 0)

/-- The smooth unpointed subcategory, retaining actual family arrows.
Source: Pikaart--de Jong §1.1
(blueprint: lem-sfb-stable-abelian-level-normalization). -/
def smoothModuliBased (S : Scheme.{u}) (g : ℕ) : BasedCategory (Over S) :=
  BasedCategory.ofFunctor
    (ObjectProperty.ι
      (fun X : StablePointedModuli S g 0 ↦ Smooth X.projection) ⋙
        StablePointedModuli.forget S g 0)

/-- Inclusion of the smooth families into stable families.
Source: Pikaart--de Jong §1.1
(blueprint: lem-sfb-stable-abelian-level-normalization). -/
def smoothModuliInclusion (S : Scheme.{u}) (g : ℕ) :
    BasedFunctor (smoothModuliBased S g) (stableModuliBased S g) where
  toFunctor := ObjectProperty.ι _
  w := rfl

/-- The full abelian level groupoid, without a symplectic restriction.
Source: Pikaart--de Jong §2.3.3
(blueprint: lem-sfb-stable-abelian-level-normalization). -/
def abelianLevelBased (S : Scheme.{u}) (g : ℕ) (ℓ : AbelianLevelPrime S) :
    BasedCategory (Over S) :=
  BasedCategory.ofFunctor (AbelianLevelModuli.forget S g ℓ)

/-- The forgetful map remembers the underlying smooth family and its actual arrows.
Source: Pikaart--de Jong §2.3.3
(blueprint: lem-sfb-stable-abelian-level-normalization). -/
def abelianLevelToSmooth (S : Scheme.{u}) (g : ℕ) (ℓ : AbelianLevelPrime S) :
    BasedFunctor (abelianLevelBased S g ℓ) (smoothModuliBased S g) where
  obj X := X.family
  map b := b.val
  w := rfl

/-- The actual level-cover map into stable moduli, using the supplied representing
 equivalence. Source: Pikaart--de Jong §2.3.3
(blueprint: lem-sfb-stable-abelian-level-normalization). -/
def abelianLevelSchemeMap {S : Scheme.{u}} {g : ℕ} {ℓ : AbelianLevelPrime S}
    {L : Over S} (eL : BasedFunctor (discreteModuli (yoneda.obj L))
      (abelianLevelBased S g ℓ)) :
    BasedFunctor (discreteModuli (yoneda.obj L)) (stableModuliBased S g) :=
  (eL.comp (abelianLevelToSmooth S g ℓ)).comp (smoothModuliInclusion S g)

/-- The integral-closure normalization in the full level cover is a scheme, finite
 over the specified coarse moduli scheme; its smooth inverse image is the original
 level scheme as a fibred groupoid, with the specified comparison isomorphism.

Source: Pikaart--de Jong §§1.1, 2.3.3--2.3.7, Proposition 2.3.4 and Remark 2.3.7
(blueprint: lem-sfb-stable-abelian-level-normalization).

Proof plan:
1. lem-sfb-unpointed-stable-coarse-projective gives the smooth DM stable stack,
   its dense smooth open, and its coarse scheme. lem-sfb-stable-isom-finite-unramified
   supplies finite type and finite diagonal. The actual frame-scheme assertion of
   lem-sfb-smooth-curve-abelian-level-rigidification supplies the finite étale level cover.
2. Apply lem-sfb-dm-finite-normalization-charts to all generic factors of this cover.
   Étale compatibility glues its integral closures with their descent arrows and
   identifies its smooth restriction with the full level scheme. The same construction
   over the perfect prime field commutes with scalar extension to k. The frame pullback
   is the inverse-image frame followed by the canonical degree-one base-change map.
3. Over that prime field, use lem-sfb-stable-level-versal-branch-freeness at every
   geometric stable curve. The completed chart is [Spf B/Aut(C)], and its stabilizers
   are trivial. This includes smooth C, when the node-parameter product is 1.
   Scalar extension preserves these automorphism groups, giving the claim over k.
4. lem-sfb-inertia-free-finite-cover-coarse makes the normalization a scheme finite
   over Q. Transport the normalization map to that representative Z; no tameness
   assumption on the stable curve automorphism group is needed.
5. The smooth-restriction equivalence from Step 2 gives the stated 2-cartesian square.
   Its objects retain the isomorphism of the two stable families and its arrows
   satisfy the comma square. No generic component or frame has been discarded.
-/
theorem exists_stable_abelian_level_normalization
    (k : Type u) [Field k] (g : ℕ) (hg : 2 ≤ g)
    (ℓ : AbelianLevelPrime (Spec (.of k)))
    (L : Over (Spec (.of k)))
    (eL : BasedFunctor (discreteModuli (yoneda.obj L))
      (abelianLevelBased (Spec (.of k)) g ℓ))
    (hL : eL.toFunctor.IsEquivalence)
    (Q : Over (Spec (.of k)))
    (π : BasedFunctor (stableModuliBased (Spec (.of k)) g)
      (discreteModuli (yoneda.obj Q)))
    (hQ : IsCoarseModuliScheme (stableModuliBased (Spec (.of k)) g) Q π) :
    ∃ (Z : Over (Spec (.of k)))
      (a : BasedFunctor (discreteModuli (yoneda.obj Z))
        (stableModuliBased (Spec (.of k)) g)) (c : Z ⟶ Q),
      IsFinite c.left ∧
      Nonempty (ModuliTwoIso (a.comp π) (discreteModuliMap (yoneda.map c))) ∧
      ∃ (i : L ⟶ Z)
        (e : (discreteModuliMap (yoneda.map i)).comp a ≅ abelianLevelSchemeMap eL),
        IsModuliChartNormalization (abelianLevelSchemeMap eL) a
          (discreteModuliMap (yoneda.map i)) e ∧
        (moduliTwoFiberLift (discreteModuliMap (yoneda.map i))
          (eL.comp (abelianLevelToSmooth (Spec (.of k)) g ℓ)) e).toFunctor.IsEquivalence := by
  sorry

end AlgebraicGeometry
