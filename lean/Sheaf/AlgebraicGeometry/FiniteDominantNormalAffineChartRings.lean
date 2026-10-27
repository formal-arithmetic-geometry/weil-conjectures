module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Affine chart rings of finite dominant morphisms to a normal base

Source: Stacks Project, Tags 030B, 01WH, 01HV and 01OV; affine preparation for Tag 0F32.
(blueprint: lem-sfb-finite-dominant-normal-affine-chart-rings)
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- For every nonempty affine Noetherian open cover of the normal locally Noetherian
integral base of a finite dominant map from an integral scheme, the inverse-image charts
are nonempty affine opens. Their canonical coordinate maps are injective and finite,
with normal domain source and domain target. Such a cover of the base exists.
Here the chart rings are the canonical section rings; the equation involving `fromSpec`
expresses that the restricted morphism is induced by `q.app (U i)`.

Source: Stacks Project, Tag 030B (3) implies (1), Tag 01WH (finite morphisms),
Tag 01HV (6) (affine stalks), and Tag 01OV (locally Noetherian schemes).
(blueprint: lem-sfb-finite-dominant-normal-affine-chart-rings)

Proof:
1. By pqf-def-locnoeth choose an affine cover with Noetherian section rings, and discard
   empty members. The remaining opens still cover, proving the existence assertion.
2. For any cover in the statement and any member U, dominance
   (def-sbc-normal-dominant-galois) makes the dense image of q meet U, so its inverse
   image W is nonempty. It is open by continuity. Finiteness
   (def-weil-finite-integral-morphism) makes W affine and its coordinate ring finite
   over that of U. Integrality (def-pc-integral-scheme) makes both rings domains.
   The affine spectrum construction (def-weil-affine-spectrum) identifies the restricted
   map with Spec of the section map, giving the displayed commuting equation.
3. If a nonzero a in the coordinate ring of U mapped to zero, D(a) would be nonempty
   (it contains the zero prime) and open in the base. Dominance supplies a point of V
   mapping into D(a), hence lying in W. Its prime Q contracts to the image prime by
   lem-weil-pbc-spec-map-stalk-localization. Since the image of a is zero in Q, the
   contracted prime contains a, contradicting membership in D(a). Thus the map is injective.
4. By lem-weil-pbc-affine-open-stalk-localization the localization of the coordinate
   ring of U at any maximal ideal is the corresponding stalk of the base. Normality of
   the base makes it a normal domain (def-weil-pbc-normal-ring). Applying
   lem-weil-pbc-normal-domain-of-local-normal to the already established domain proves
   that the coordinate ring of U is integrally closed. This works for each member of
   every cover in the statement. -/
theorem finite_dominant_normal_affine_chart_rings
    {V B : Scheme.{u}} [IsIntegral V] [IsLocallyNoetherian B]
    (q : V ⟶ B) [IsFinite q] [IsDominant q] (hB : IsNormalScheme B) :
    (∀ (I : Type v) (U : I → B.Opens) (hU : ∀ i : I, IsAffineOpen (U i)),
      (⨆ i : I, U i) = ⊤ →
      (∀ i : I, Nonempty (U i)) →
      (∀ i : I, IsNoetherianRing Γ(B, U i)) →
      ∀ i : I, Nonempty (q ⁻¹ᵁ U i) ∧
        ∃ hW : IsAffineOpen (q ⁻¹ᵁ U i),
          hW.fromSpec ≫ q = Spec.map (q.app (U i)) ≫ (hU i).fromSpec ∧
          Function.Injective (q.app (U i)).hom ∧
          IsDomain Γ(B, U i) ∧ IsIntegrallyClosed Γ(B, U i) ∧
          IsDomain Γ(V, q ⁻¹ᵁ U i) ∧ (q.app (U i)).hom.Finite) ∧
    (∃ (I : Type u) (U : I → B.Opens), (⨆ i : I, U i) = ⊤ ∧
      ∀ i : I, IsAffineOpen (U i) ∧ Nonempty (U i) ∧ IsNoetherianRing Γ(B, U i)) := by
  sorry

end AlgebraicGeometry
