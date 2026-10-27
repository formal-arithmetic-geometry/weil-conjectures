module

public import Sheaf.AlgebraicGeometry.EtalePushoutTriples
public import Sheaf.AlgebraicGeometry.SchemeAffineThickeningPushout
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-! # Etale patching on a scheme infinitesimal pushout

Source: Stacks Project, More on Morphisms, Tags 07RV and 07RX(5), including
its flat counit (blueprint: lem-sfb-scheme-infinitesimal-etale-patching).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Pullback to compatible etale triples is an equivalence on an infinitesimal
pushout. We express the equivalence by a left adjoint with invertible unit and
counit. Its value on a triple is a scheme pushout with its induced structural
map. The unit components are the canonical maps to the two base changes: their
projections to the pushout are its inclusions. Their compatibility is the
commuting-square condition on a morphism of triples. The counit restricts to
the two projections, identifying every etale scheme with the stated pushout.

Source: Stacks Project, More on Morphisms, Tags 07RV and 07RX(5), including
the flat counit (blueprint: lem-sfb-scheme-infinitesimal-etale-patching).

Proof plan from the node:
1. Etale base-change stability defines the restriction functor. For a triple
   put U = X times_S T, identify it with Y times_T' T by its comparison, and use
   lem-sfb-infinitesimal-pushout-affine-charts to construct Z = X amalg_U Y and
   its map to P. No flatness is needed for this construction.
2. The pushout universal property (lem-sfb-scheme-affine-thickening-pushout)
   defines G on morphisms, with functoriality by uniqueness. Maps from Z to W
   are pairs of maps from X and Y agreeing on U. The fibre-product universal
   property identifies those pairs with morphisms of triples into F(W).
   These inverse operations are natural and give G left adjoint to F.
3. On affine charts provided by lem-sfb-infinitesimal-pushout-affine-charts,
   write R = B times_A A', C = D tensor_B A = C'/IC', E = D times_C C'. Open
   immersions are etale (lem-weil-pbc-open-immersion-etale), and the square
   clause of lem-sfb-scheme-etale-source-target-properties makes the two
   restricted maps etale. The affine etale criterion
   lem-weil-pbc-etale-ring-map-iff-etale-affine gives etaleness of B to D and
   A' to C'. Apply lem-sfb-fibre-product-algebra-etale to get R to E etale.
4. The affine-open basis (lem-weil-pbc-affine-opens-basis) covers Z by these
   charts over affine opens in P. Composition and the jointly-surjective-family
   clause of lem-sfb-scheme-etale-source-target-properties show Z to P etale.
   Thus the construction restricts to etale schemes.
5. The canonical recovery maps of lem-sfb-infinitesimal-pushout-affine-charts
   are the adjunction unit: each pairs an inclusion with its structural map.
   Equality on U and uniqueness of fibre-product lifts prove compatibility
   with the comparison. The same projection argument proves naturality.
6. Etale implies flat by def-weil-etale-morphism, so
   lem-sfb-scheme-pushout-flat-patching makes the canonical map G(F(W)) to W
   an isomorphism. Its restrictions are the two projections, so it is the
   adjunction counit; pushout uniqueness proves its naturality. The invertible
   unit and counit give the equivalence. No quasi-compactness, separation or
   finite-order assumption was used.
-/
theorem scheme_infinitesimal_etale_patching
    {T T' S P : Scheme.{u}} (i : T ⟶ T') (a : T ⟶ S)
    (hi : IsThickening i) [IsAffineHom a] (j : S ⟶ P) (b : T' ⟶ P)
    (hP : IsPushout a i j b) :
    ∃ (G : EtalePushoutTriples a i ⥤ P.Etale)
      (adj : G ⊣ etalePushoutRestriction a i j b hP.w)
      (l : ∀ D : EtalePushoutTriples a i, D.obj.left.left ⟶ (G.obj D).left)
      (r : ∀ D : EtalePushoutTriples a i, D.obj.right.left ⟶ (G.obj D).left),
      IsIso adj.unit ∧ IsIso adj.counit ∧
      (∀ D : EtalePushoutTriples a i,
        IsPushout (pullback.fst D.obj.left.hom a)
          (D.obj.hom.left ≫ pullback.fst D.obj.right.hom i) (l D) (r D) ∧
        l D ≫ (G.obj D).hom = D.obj.left.hom ≫ j ∧
        r D ≫ (G.obj D).hom = D.obj.right.hom ≫ b ∧
        (adj.unit.app D).hom.left.left ≫ pullback.fst (G.obj D).hom j = l D ∧
        (adj.unit.app D).hom.right.left ≫ pullback.fst (G.obj D).hom b = r D) ∧
      (∀ W : P.Etale,
        l ((etalePushoutRestriction a i j b hP.w).obj W) ≫
          (adj.counit.app W).left = pullback.fst W.hom j ∧
        r ((etalePushoutRestriction a i j b hP.w).obj W) ≫
          (adj.counit.app W).left = pullback.fst W.hom b) := by
  sorry

end AlgebraicGeometry
