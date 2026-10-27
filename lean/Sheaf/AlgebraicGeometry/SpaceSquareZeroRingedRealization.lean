/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q149
-/
module

public import Sheaf.AlgebraicGeometry.SpaceSquareZeroExtensionData
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
import Sheaf.AlgebraicGeometry.EtaleRelationQuotient
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Ringed realization of square-zero algebraic-space thickenings

Source: Stacks Project, Tags 05ZS, 05ZT and 05ZN
(blueprint: lem-sfb-space-square-zero-ringed-realization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Site identification, realization, general maps, and marked uniqueness for
square-zero thickenings. Source: Stacks Project, Tags 05ZS, 05ZT and 05ZN
(blueprint: lem-sfb-space-square-zero-ringed-realization).

Proof:
1. Closed-immersion atlas locality makes every scheme test a closed immersion.
Apply lem-sfb-space-thickening-etale-scheme-equivalence to identify the small
étale categories. By lem-sfb-space-thickening-base-change their covering
families agree. Lift maps to base charts by formal étaleness, giving the
normalized base action in the site model.
2. Use lem-sfb-space-change-base-to-integers to forget the base. Restrict the
extension to a scheme atlas U and its relation R. Apply
lem-sfb-scheme-etale-square-zero-chart-construction to produce U+, R+ and all
groupoid maps. Their identities follow by functoriality. The lifted relation
is monic: two arrows agree on the square-zero reduction by monicity of R,
then agree everywhere by formal unramifiedness of the étale source map.
3. Apply lem-trf-etale-relation-quotient to U+/R+. Its kernel-pair description
identifies its pullback over U+ with U. Closed-immersion atlas locality shows
that X embeds in the quotient as a square-zero thickening.
4. The chart construction identifies the entire structure sheaf on U with the
extension algebra. The identifications agree on R and glue, with their
inverses, by the sheaf equalizer. They respect the quotient and kernel maps.
5. For maps, use the site identifications to obtain a ringed-topos morphism.
It is local: an element invertible after reduction is already invertible,
since a local inverse with product 1+j can be corrected by multiplication
by 1-j. Apply lem-sfb-space-locally-ringed-etale-topos-reconstruction after
changing the base to the integers to reconstruct the unique space morphism.
6. Faithfulness in reconstruction identifies its reduction with the specified
g and its composite to B with the source structure map. The latter equality
uses precisely the base algebra compatibility. This proves the general maps
clause for arbitrary g, with no quasi-coherence hypothesis on these kernels.
7. Apply the maps clause with target B and its identity thickening to put the
constructed space over B, and then over S. The glued ring isomorphism respects
the base action and quotient. Transporting the specified inclusion through
its inverse identifies G with the square-zero kernel, with its given action.
8. Apply the maps clause to a specified extension isomorphism and its inverse.
The composites induce identity ring maps, so uniqueness makes them identities.
This gives the unique normalized isomorphism, and allows automorphisms when
the isomorphism of extensions has not been fixed. -/
theorem space_square_zero_ringed_realization {S : Scheme.{u}} :
    (∀ (X X' B : AlgebraicSpace S) (f : X ⟶ B) (i : X ⟶ X') (q : X' ⟶ B),
      IsSpaceFirstOrderThickening i → i ≫ q = f →
      Nonempty (ThickeningOverModel f i q)) ∧
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
    (∀ (X Y X' Y' B : AlgebraicSpace S)
      (f : X ⟶ B) (h : Y ⟶ B) (i : X ⟶ X') (j : Y ⟶ Y')
      (q : X' ⟶ B) (r : Y' ⟶ B),
      IsSpaceFirstOrderThickening i → IsSpaceFirstOrderThickening j →
      i ≫ q = f → j ≫ r = h →
      ∀ (T : ThickeningOverModel f i q) (W : ThickeningOverModel h j r)
        (g : X ⟶ Y), g ≫ h = f →
        ∀ α : ChartRingMap g W.toThickeningSiteModel.rings T.toThickeningSiteModel.rings,
          α.Reduces T.toThickeningSiteModel W.toThickeningSiteModel →
          α.OverBase T W →
          ∃! g' : X' ⟶ Y', i ≫ g' = g ≫ j ∧ g' ≫ r = q ∧
            α.InducedBy T.toThickeningSiteModel W.toThickeningSiteModel g') ∧
    (∀ (X X' Y' B : AlgebraicSpace S) (f : X ⟶ B)
      (i : X ⟶ X') (j : X ⟶ Y') (q : X' ⟶ B) (r : Y' ⟶ B),
      IsSpaceFirstOrderThickening i → IsSpaceFirstOrderThickening j →
      i ≫ q = f → j ≫ r = f →
      ∀ (T : ThickeningOverModel f i q) (W : ThickeningOverModel f j r)
        (θ : W.toThickeningSiteModel.rings ≅ T.toThickeningSiteModel.rings),
        θ.hom ≫ T.quotient = W.quotient →
        (∀ (U : X.EtaleSite) (V : B.EtaleSite) (a : U.obj.left ⟶ V.obj.left)
          (ha : U.obj.hom ≫ f.hom.hom = yoneda.map a ≫ V.obj.hom),
          W.base.app U V a ha ≫ θ.hom.app (op U) = T.base.app U V a ha) →
        ∃! e : X' ≅ Y', i ≫ e.hom = j ∧ e.hom ≫ r = q ∧
          T.toThickeningSiteModel.InducesIso W.toThickeningSiteModel θ e) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
