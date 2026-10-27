module

public import Sheaf.AlgebraicGeometry.IntegralCartierDivisor
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Mathlib.AlgebraicGeometry.Group.Abelian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.AlgebraicGeometry.Morphisms.SmoothConnectedGenericGeometryCore
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Vertical Cartier divisors on smooth connected groups over normal bases

Source: Moret-Bailly, Pinceaux de varietes abeliennes, II 3.2.1--3.2.3, normal-base
uniqueness input; Stacks Project, Tag 0BD7, local generic-unit factorization
(blueprint: lem-sfb-normal-group-vertical-cartier-descent).

The identity pullback is partial in general. The theorem asserts that it is defined
on every vertical divisor, and that its subsequent structural pullback is exactly D.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Vertical Cartier divisors descend through the identity section over a normal base.
The rational-section clause uses the actual generic stalk and regular local frames.

Source: Moret-Bailly, II 3.2.1--3.2.3, normal-base uniqueness input, and Stacks,
Tag 0BD7 (blueprint: lem-sfb-normal-group-vertical-cartier-descent).

Proof:
1. The identity makes p surjective. The smooth-connected generic geometry core gives
   normal integral G; smooth connected fibres are integral. Smoothness gives flatness
   and local finite presentation, hence local Noetherianity over S. Surjectivity maps
   the generic point to the generic point, so the inverse image of U is dense.
2. At x over t, the stalk map A = O(S,t) to B = O(G,x) is flat local, hence faithfully
   flat. Its fibres are integral localizations of fibres of p. A vertical local equation
   is a unit on the generic fibre. The local generic-unit factorization lemma writes it
   as p*(h_x) times a unit of B, with h_x a nonzero rational function on S.
3. Near e(s), choose h and an open W. For t in e^{-1}(W), the nonempty opens in the
   integral fibre through e(t) and through any x intersect. At an intersection point
   unit reflection in the local generic-unit lemma shows h_x/h is a base local unit.
   Consequently the equation p*(h) represents D on the entire inverse image of e^{-1}(W).
4. Ratios of these base equations are units: their pullbacks are units and can be
   restricted along e. Thus they glue to a Cartier divisor E. The base fractions and
   their pullbacks have nonzero numerators and denominators, so the actual partial
   pullbacks satisfy e*D = E and p*E = D. Local unit ratios give uniqueness. E vanishes
   on U by restricting the unit equations of D along e.
5. If E is zero, its pulled-back equations are units, so D is zero.
6. For an invertible module and a nonzero generic section, write s = f_i v_i in local
   regular frames. Transition functions are units, so the f_i give its unique Cartier
   divisor: every divisor with these local coefficient classes equals it. That divisor
   is zero exactly when all f_i are units. In that case the local
   regular generators agree by injectivity into the generic stalk and glue to a global
   regular generator. Conversely an everywhere regular generator has unit coefficients.
-/
theorem normal_group_vertical_cartier_descent
    (S : Scheme.{u}) [IsIntegral S] [IsLocallyNoetherian S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (G : Over S) [GrpObj G] [IsCommMonObj G]
    [Smooth G.hom] [IsSeparated G.hom] [LocallyOfFinitePresentation G.hom]
    [QuasiCompact G.hom] [GeometricallyConnected G.hom]
    (U : S.Opens) (hU : Dense (U : Set S)) :
    IsIntegral G.left ∧
      (∀ x : G.left, IsDomain (G.left.presheaf.stalk x) ∧
        IsIntegrallyClosed (G.left.presheaf.stalk x)) ∧
      Dense (G.hom ⁻¹' (U : Set S)) ∧
      ∀ [IsIntegral G.left],
        (∀ D : IntegralCartierDivisor G.left,
          integralCartierSupport D ⊆ (G.hom ⁻¹' (U : Set S))ᶜ →
          ∃ E : IntegralCartierDivisor S,
            integralCartierPullback? (X := S)
              ((Over.mkIdTerminal.uniqueUpToIso
                CartesianMonoidalCategory.isTerminalTensorUnit).hom ≫
                  MonObj.one (X := G)).left D = some E ∧
            integralCartierSupport E ⊆ (U : Set S)ᶜ ∧
            integralCartierPullback? G.hom E = some D ∧
            (E = integralCartierZero S → D = integralCartierZero G.left)) ∧
        (∀ (L : G.left.Modules) [L.IsInvertible]
          (s : ↑(TopCat.Presheaf.stalk L.val.presheaf (genericPoint G.left))), s ≠ 0 →
          ∃ D : IntegralCartierDivisor G.left,
            (∀ D' : IntegralCartierDivisor G.left, HasIntegralCartierDivisor L s D' ↔ D' = D) ∧
            (IsInvertibleRegularRationalSection L s ↔ D = integralCartierZero G.left)) := by
  sorry

end AlgebraicGeometry.Scheme
