/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q30
-/
module

public import Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.SpaceSquareZeroRingedRealization

/-! # First-order thickenings and their ring sheaves

Source: Stacks Project, Tags 05ZS, 05ZT and 05ZN; the fundamental equivalence in
More on Morphisms of Spaces, Section Thickenings
(blueprint: lem-sfb-space-first-order-ringed-description).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- First-order thickenings have square-zero quasi-coherent kernel extensions on
 their common small étale site; every such extension is realized; maps over the
 base inducing the identity after reduction correspond contravariantly to ring maps.

Source: Stacks Project, Tags 05ZS, 05ZT and 05ZN
(blueprint: lem-sfb-space-first-order-ringed-description).

Proof:
1. Apply lem-sfb-space-square-zero-ringed-realization to identify the small étale
sites, with their coverings, by pullback. The normalized site model records the
actual scheme pullback squares and the quotient on regular functions.
2. By lem-sfb-space-closed-immersion-quasi-coherent-modules, the quotient structure
map is surjective as a sheaf map, and its kernel is quasi-coherent on the thickening.
The kernel has square zero by the first-order assumption. Apply the essential-image
clause of that module lemma to this kernel, which is annihilated by itself, obtaining
G on the reduced space. Its quotient scalar action is well-defined: two lifts differ
by a kernel section, whose product with every kernel section is zero. This supplies
SpaceSquareZeroExtension, including its injective kernel inclusion, local quotient
surjectivity and normalized base action, and the displayed ring isomorphism.
3. Conversely apply the realization clause of lem-sfb-space-square-zero-ringed-realization
with X = Z, B = C and G the given quasi-coherent kernel. Its commutative algebra,
quotient and prescribed quotient scalar action are precisely the extension hypotheses.
The realized ring isomorphism respects both the quotient and the base algebra action.
4. Given the last clause's ring-sheaf map, naturality extends its components to the
identity chart ring map. Apply the maps clause of the same realization theorem with
both reduced spaces equal to X and g the identity. Quotient compatibility is Reduces;
base compatibility is OverBase. It gives a unique map X' to Y' over B restricting to
the identity on X. On every lifted chart its regular-function pullback is the given
component, which is the displayed last condition. This also fixes the opposite direction. -/
theorem space_first_order_ringed_description {S : Scheme.{u}} :
    (∀ (X X' B : AlgebraicSpace S) (f : X ⟶ B) (i : X ⟶ X') (q : X' ⟶ B),
      IsSpaceFirstOrderThickening i → i ≫ q = f →
      ∃ (T : ThickeningOverModel f i q) (G : X.QCoh)
        (A : SpaceSquareZeroExtension f G.obj)
        (γ : T.toThickeningSiteModel.rings ≅ A.algebra.obj),
        γ.hom ≫ A.quotient = T.quotient ∧
        ∀ (U : X.EtaleSite) (V : B.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
          (ha : U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom),
          T.base.app U V a ha ≫ γ.hom.app (op U) = A.base.app U V a ha) ∧
    (∀ (X B : AlgebraicSpace S) (f : X ⟶ B) (G : X.QCoh)
      (A : SpaceSquareZeroExtension f G.obj),
      ∃ (X' : AlgebraicSpace S) (i : X ⟶ X') (q : X' ⟶ B),
        IsSpaceFirstOrderThickening i ∧ i ≫ q = f ∧
        ∃ (T : ThickeningOverModel f i q)
          (γ : T.toThickeningSiteModel.rings ≅ A.algebra.obj),
          γ.hom ≫ A.quotient = T.quotient ∧
          ∀ (U : X.EtaleSite) (V : B.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
            (ha : U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom),
            T.base.app U V a ha ≫ γ.hom.app (op U) = A.base.app U V a ha) ∧
    (∀ (X X' Y' B : AlgebraicSpace S) (f : X ⟶ B)
      (i : X ⟶ X') (j : X ⟶ Y') (q : X' ⟶ B) (r : Y' ⟶ B),
      IsSpaceFirstOrderThickening i → IsSpaceFirstOrderThickening j →
      i ≫ q = f → j ≫ r = f →
      ∀ (T : ThickeningOverModel f i q) (W : ThickeningOverModel f j r)
        (α : W.toThickeningSiteModel.rings ⟶ T.toThickeningSiteModel.rings),
        α ≫ T.quotient = W.quotient →
        (∀ (U : X.EtaleSite) (V : B.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
          (ha : U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom),
          W.base.app U V a ha ≫ α.app (op U) = T.base.app U V a ha) →
        ∃! g' : X' ⟶ Y', i ≫ g' = j ∧ g' ≫ r = q ∧
          ∀ U : X.EtaleSite,
            ∃ a' : (T.equivalence.inverse.obj U).obj.left ⟶
                (W.equivalence.inverse.obj U).obj.left,
              T.reduction.app U ≫ a' = W.reduction.app U ∧
              (T.equivalence.inverse.obj U).obj.hom ≫ g'.hom.hom =
                yoneda.map a' ≫ (W.equivalence.inverse.obj U).obj.hom ∧
              (forget₂ CommRingCat RingCat).map (Scheme.Γ.map a'.left.op) =
                α.app (op U)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
