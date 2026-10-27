module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.Sober
public import WeilConjectures.Topology.PresheafModuleStalkFunctor

/-!
# Dominant finite-type affine charts and their generic stalk maps

Source: Stacks Project, Morphisms, Tags 02JU and 0CC1; Schemes, Tags 01HV and 01I1
(blueprint: lem-trf-dominant-affine-chart-data).
-/

@[expose] public section

universe u v

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A dominant locally finite-type map of integral schemes has affine neighbourhoods
with an injective finite-type coordinate map, chosen over any prescribed Noetherian
affine covering. The generic stalks are their fraction fields, and the actual stalk
map is the unique embedding extending the coordinate map.

Source: Stacks Project, Morphisms, Tags 02JU (affine reduction), 01T2 and 0CC1
(1), (2), (4); Schemes, Tags 01HV, 01HY and 01I1.
(blueprint: lem-trf-dominant-affine-chart-data)

Proof:
1. Choose a member U of the prescribed covering containing f(x). The locally
   finite-type condition gives an affine neighbourhood V of x inside its preimage
   with finite-type section map (def-weil-finite-type-morphism). The chosen base
   ring is Noetherian (pqf-def-locnoeth), and both rings are domains by integrality
   (def-pc-integral-scheme). Both opens contain a point and hence are nonempty.
2. In an irreducible scheme every nonempty open is dense. The zero prime in an
   affine domain is generic; its closure in the whole scheme is therefore the
   whole scheme. Uniqueness of generic points and their membership in every
   nonempty open show that the two affine primes are zero (def-sc-generic-point,
   def-weil-irreducible-components, lem-weil-pbc-spec-domain-stalks-function-field).
3. Restriction to an open preserves stalks and germs: restrict a representative
   to its intersection with the open, and use the germ equality criterion for
   the inverse. Naturality of section pullback makes the original and restricted
   stalk maps agree on these representatives (def-weil-pbc-module-stalk,
   def-weil-locally-ringed-space-morphism).
4. Apply lem-weil-pbc-spec-domain-stalks-function-field at the zero primes and
   transport along these open-stalk identifications. The generic germ maps make
   the stalks fields of fractions: they are injective, nonzero denominators are
   units, and every element is a quotient of germs.
5. Continuity sends the closure of the source generic point into the closure of
   its image. Dominance makes that image generic in the target, so uniqueness
   gives f(eta_X) = eta_S (def-sc-generic-point).
6. On the affine charts f is Spec of its section map (def-weil-affine-spectrum).
   Contraction of the zero prime is zero by step 5, hence the section map is
   injective. The affine stalk map is localization of that very section map;
   its germ square commutes, and step 3 transports this square to the original
   stalk map (lem-weil-pbc-spec-map-stalk-localization).
7. A unital map between these fields preserves inverses of nonzero germs.
   Applying the commuting germ square gives the displayed quotient formula.
   Every source element is such a quotient, so the extension is unique. A map
   of fields is injective since a nonzero element has an inverse.
-/
theorem dominant_affine_chart_data
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (f : X ⟶ S) (hf : DenseRange f) [LocallyOfFiniteType f] [IsLocallyNoetherian S]
    {I : Type v} (U : I → S.Opens) (hU : ∀ i : I, IsAffineOpen (U i))
    (hN : ∀ i : I, IsNoetherianRing Γ(S, U i)) (hcover : iSup U = ⊤) (x : X) :
    ∃ (i : I) (V : X.Opens) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U i),
      f x ∈ U i ∧ x ∈ V ∧ Set.Nonempty (U i : Set S) ∧ Set.Nonempty (V : Set X) ∧
      IsNoetherianRing Γ(S, U i) ∧ IsDomain Γ(S, U i) ∧ IsDomain Γ(X, V) ∧
      (f.appLE (U i) V e).hom.FiniteType ∧ Function.Injective (f.appLE (U i) V e) ∧
      ∃ (hηS : genericPoint S ∈ U i) (hηX : genericPoint X ∈ V)
        (hη : f (genericPoint X) = genericPoint S),
        ((hU i).primeIdealOf ⟨genericPoint S, hηS⟩).asIdeal = ⊥ ∧
        (hV.primeIdealOf ⟨genericPoint X, hηX⟩).asIdeal = ⊥ ∧
        @IsFractionRing Γ(S, U i) _ S.functionField _
          (S.presheaf.germ (U i) (genericPoint S) hηS).hom.toAlgebra ∧
        @IsFractionRing Γ(X, V) _ X.functionField _
          (X.presheaf.germ V (genericPoint X) hηX).hom.toAlgebra ∧
        (∀ (a b : Γ(S, U i)), b ≠ 0 →
          ((S.presheaf.stalkCongr (.of_eq hη)).inv ≫ f.stalkMap (genericPoint X))
              (S.presheaf.germ (U i) (genericPoint S) hηS a /
                S.presheaf.germ (U i) (genericPoint S) hηS b) =
            X.presheaf.germ V (genericPoint X) hηX (f.appLE (U i) V e a) /
              X.presheaf.germ V (genericPoint X) hηX (f.appLE (U i) V e b)) ∧
        Function.Injective
          ((S.presheaf.stalkCongr (.of_eq hη)).inv ≫ f.stalkMap (genericPoint X)) ∧
        (∀ ψ : S.functionField →+* X.functionField,
          (∀ a : Γ(S, U i),
            ψ (S.presheaf.germ (U i) (genericPoint S) hηS a) =
              X.presheaf.germ V (genericPoint X) hηX (f.appLE (U i) V e a)) →
          ψ = ((S.presheaf.stalkCongr (.of_eq hη)).inv ≫
            f.stalkMap (genericPoint X)).hom) := by
  sorry

end AlgebraicGeometry
