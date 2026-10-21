/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.CategoryTheory.CondensedUnipotentClass
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-! # Derived restriction calculus for internal condensed group actions

Source: main-20261015 direct-images proof (sk-thm-sf-ctf-stability-direct-images.proof.md),
paragraph (3), agent-formulated formal restriction and cup-product infrastructure;
exact reference wanted
(blueprint: lem-sfb-condensed-derived-restriction-calculus).

## Main statements

* `coefficientSquare`: c_H ∘ b_u(N) = s(b_u(N')) ∘ c_J in the derived category, no flatness.
* `restrictionDegreeZero`, `boundedBelowComputation`, `identityRestriction`: degree-zero,
  bounded-below and identity normalizations of b_u.
* `cupLaws`, `restrictionCup`, `restrictionClass`, `restrictionOrderedProducts`: the unital
  cup algebra and its preservation by group restriction, [a] ↦ [a ∘ u].
* `coefficientCup`, `coefficientClass`, `coefficientOrderedProducts`: the same for the
  coefficient map, [a] ↦ [φ ∘ a].

## Proof outline (the node's steps)

1. Action-site presentation (def-weil-pbc-internal-abelian-sheaf-module-equivalence,
   lem-sfb-internal-action-site-presentation, lem-pur-ringed-site-grothendieck-abelian):
   actions are module sheaves on a ringed site; forgetting creates exactness.
2. Fixed sections give Γ_J and the adjunction T_J ⊣ Γ_J; T_J, u^*, s are exact.
3. Bounded-below injective and K-injective resolutions compute F_J = RΓ_J, additive and
   triangulated; D(T_J) ⊣ F_J is the canonical derived adjunction, shift compatible.
4. b_u = F_H(Uε_J) ∘ η_H is the mate of the inclusion
   (lem-sfb-action-topos-geometric-restriction, lem-trf-bounded-below-derived-mate-model).
5. Shifts, triangles, degree zero and the identity case (lem-sp-canonical-right-derived-
   adjunction-shift, lem-weil-pbc-commshift-nattrans-comp-whisker).
6. d_J : F_J^R s_J ≅ s_0 F_J^R' by conjugating E_J L_J ≅ L_J E_0
   (lem-sfb-ringed-derived-monoidal-comparisons,
   lem-weil-pbc-ringed-topoi-derived-pushforward-composition); c_J = d_J ∘ F_J(f).
7. Both sides of the coefficient square transpose to U(f) ∘ Uε_J (lem-weil-pbc-mate-pasting).
8. The lax pairing is the tensor-of-counits mate (lem-sfb-monoidal-adjunction-mates).
9. Restriction preserves the pairing and unit by the same transpose.
10. d_J is monoidal; φ is an algebra map; induction gives all ordered products.
11. [a] is F_J of the connecting arrow of 0 → R → E_a → R → 0 after the unit
    (lem-weil-pbc-complex-ses-triangle); the splitting t(1) = (0,1) gives cocycle +a.
12. Restriction and scalar change map E_a to E_{a∘u} and E_{φ∘a}
    (lem-weil-pbc-exact-functor-ses-triangle-image), giving the class formulas.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open Profinite.CondensedAction (inflate trivial)
open CategoryTheory.CondensedBar
namespace CategoryTheory.CondensedDerivedRestriction
variable {A A' : CondensedBar.Ring.{u}} {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]
variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The derived coefficient/restriction square, without a flatness hypothesis.
Source: paragraph (3) (blueprint: lem-sfb-condensed-derived-restriction-calculus).
Proof: transpose both composites through the canonical derived adjunctions. The unit,
counit and composition comparisons turn both into U(f) after U of the J-counit.
Injectivity of the adjunction Hom bijection proves equality before taking cohomology. -/
theorem coefficientSquare (a : A ⟶ A') (v : H →ₜ* G)
    {N : DerivedCategory.{u + 1} (Equivariant A G)}
    {N' : DerivedCategory.{u + 1} (Equivariant A' G)}
    (f : N ⟶ (scalarDerived a G).obj N') :
    (groupMap A v).app N ≫
      coefficientMap a ((groupDerived A v).map f ≫ (scalarGroupDerived a v).hom.app N') =
    coefficientMap a f ≫ (scalarBase a).map ((groupMap A' v).app N') := by
  sorry


/-- On modules the actual H-zero restriction map is the invariant inclusion under the
computation-unit-normalized degree-zero identifications.
Source: paragraph (3) (blueprint: lem-sfb-condensed-derived-restriction-calculus).
Proof: apply H-zero to groupMapNormalization on the single complex. Substitute the
normalization equations of degreeZeroIso on both sides and cancel the invertible
H-zero computation units. This gives precisely the original invariant inclusion. -/
theorem restrictionDegreeZero (v : H →ₜ* G) (M : Equivariant A G) :
    (DerivedCategory.homologyFunctor (Modules A) 0).map
        ((groupMap A v).app ((DerivedCategory.singleFunctor (Equivariant A G) 0).obj M) ≫
          (derived A H).map
            (((inflate (R := A.toMon) v).mapDerivedCategorySingleFunctor 0).hom.app M)) ≫
      (degreeZeroIso (A := A) (G := H)).hom.app ((inflate v).obj M) =
    (degreeZeroIso (A := A) (G := G)).hom.app M ≫
      (invariantRestriction (invariants A G) (invariants A H) v).app M := by
  sorry

/-- Bounded-below complexes of equivariant injectives compute the ordinary total derived
functor, with its actual computation unit.
Source: paragraph (3) (blueprint: lem-sfb-condensed-derived-restriction-calculus).
Proof: every bounded-below complex of injectives is K-injective. The canonical total
right-derived unit is invertible on K-injectives. Mapping a quasi-isomorphism from any
bounded-below object to such a resolution gives the claimed computation, compatibly
with the underived invariant inclusions. -/
theorem boundedBelowComputation (K : CochainComplex (Equivariant A G) ℤ)
    (hb : ∃ n : ℤ, ∀ i < n, IsZero (K.X i)) (hi : ∀ i : ℤ, Injective (K.X i)) :
    IsIso ((invariants A G).functor.rightDerivedFunctorUnitQ K) := by
  sorry

/-- The derived restriction is the identity for the identity homomorphism of a trivial
group, retaining the required case of two trivial groups.
Source: paragraph (3) (blueprint: lem-sfb-condensed-derived-restriction-calculus).
Proof: its underived transpose is the identity counit. The identity normalization of
exact localization and the triangle identity identify its derived mate with identity. -/
theorem identityRestriction [Subsingleton G] (N : DerivedCategory.{u + 1} (Equivariant A G)) :
    (groupMap A (ContinuousMonoidHom.id G)).app N ≫
      (derived A G).map ((identityGroup (A := A) (G := G)).hom.app N) =
    𝟙 ((derived A G).obj N) := by
  sorry

/-- The actual derived cup multiplication is associative and has the indicated two-sided
unit. All tensor products here are the ordinary K-flat derived module tensor products.
Source: paragraph (3) (blueprint: lem-sfb-condensed-derived-restriction-calculus).
Proof: transfer the strong monoidal trivial-action tensor comparison through its
normalized derived adjunction. The tensor-of-counits mate satisfies lax monoidal
associativity and both unit identities. Apply it to the regular coefficient algebra. -/
theorem cupLaws :
    (cup (A := A) (G := G) ▷ cohomology A G) ≫ cup (A := A) (G := G) =
      (α_ (cohomology A G) (cohomology A G) (cohomology A G)).hom ≫
        (cohomology A G ◁ cup (A := A) (G := G)) ≫ cup (A := A) (G := G) ∧
    (cupUnit (A := A) (G := G) ▷ cohomology A G) ≫ cup (A := A) (G := G) =
      (λ_ (cohomology A G)).hom ∧
    (cohomology A G ◁ cupUnit (A := A) (G := G)) ≫ cup (A := A) (G := G) =
      (ρ_ (cohomology A G)).hom := by
  sorry

/-- Restriction preserves the actual binary cup pairing and unit.
Source: paragraph (3) (blueprint: lem-sfb-condensed-derived-restriction-calculus).
Proof: transpose both binary composites through the normalized H-adjunction. Both are
the restriction of the tensor of the two J-counits. The same transpose with the regular
unit proves the unit equation. Hence the equations hold before applying cohomology. -/
theorem restrictionCup (v : H →ₜ* G) :
    cup (A := A) (G := G) ≫ groupCupMap (A := A) v =
      (groupCupMap (A := A) v ⊗ₘ groupCupMap (A := A) v) ≫ cup (A := A) (G := H) ∧
    cupUnit (A := A) (G := G) ≫ groupCupMap (A := A) v = cupUnit (A := A) (G := H) := by
  sorry

/-- Restriction carries the positive unipotent connecting class to precomposition by u.
Source: paragraph (3) (blueprint: lem-sfb-condensed-derived-restriction-calculus).
Proof: restricting the unipotent action leaves its biproduct and both endpoint maps
unchanged and replaces a by a composed with u on every test object. Naturality of the
short-exact-sequence boundary, shift compatibility of restriction, and unit compatibility
give the equality after shifting the boundary down by one. The positive section
normalization is the unchanged identity j(0,1)-(0,1)=(a(j),0). -/
theorem restrictionClass (v : H →ₜ* G) (a : Character A G) :
    characterClass a ≫ groupCupMap (A := A) v = characterClass (a.restrict v) := by
  sorry

/-- Ordered finite cup products, including length zero, commute with group restriction.
Source: paragraph (3) (blueprint: lem-sfb-condensed-derived-restriction-calculus).
Proof: induct on the number of factors. Length zero is the unit equation, and the
successor case uses the binary equation, tensor functoriality and the induction
hypothesis. No factor is permuted, so the ordered graded signs are retained. -/
theorem restrictionOrderedProducts (v : H →ₜ* G) (n : ℕ) :
    orderedProduct (cupUnit (A := A) (G := G)) (cup (A := A) (G := G)) n ≫
      groupCupMap (A := A) v =
    tensorPowerMap (groupCupMap (A := A) v) n ≫
      orderedProduct (cupUnit (A := A) (G := H)) (cup (A := A) (G := H)) n := by
  sorry

/-- The scalar-restricted cup product uses the canonical lax scalar tensor comparison.
Source: paragraph (3) (blueprint: lem-sfb-condensed-derived-restriction-calculus). -/
def restrictedCup (φ : A ⟶ A') :
    (scalarBase φ).obj (cohomology A' G) ⊗ (scalarBase φ).obj (cohomology A' G) ⟶
      (scalarBase φ).obj (cohomology A' G) :=
  Functor.LaxMonoidal.μ (scalarBase φ) (cohomology A' G) (cohomology A' G) ≫
    (scalarBase φ).map (cup (A := A') (G := G))

/-- The scalar-restricted unit, including the original coefficient ring morphism.
Source: paragraph (3) (blueprint: lem-sfb-condensed-derived-restriction-calculus). -/
def restrictedCupUnit (φ : A ⟶ A') : 𝟙_ (DerivedCategory.{u + 1} (Modules A)) ⟶
    (scalarBase φ).obj (cohomology A' G) :=
  Functor.LaxMonoidal.ε (scalarBase φ) ≫ (scalarBase φ).map (cupUnit (A := A') (G := G))

/-- The coefficient map is a map of the specified cup algebras, with no flatness assumption.
Source: paragraph (3) (blueprint: lem-sfb-condensed-derived-restriction-calculus).
Proof: the scalar-extension/trivial-action square is monoidal on K-flat representatives.
Conjugating it through the derived adjunctions gives a comparison of the right-adjoint
lax pairings. Its unit and tensor equations, applied to the regular ring morphism,
are precisely these two equalities; multiplicativity and preservation of 1 hold on
every section. Scalar restriction need not preserve injectives or flat objects. -/
theorem coefficientCup (φ : A ⟶ A') :
    cup (A := A) (G := G) ≫ coefficientCupMap (G := G) φ =
      (coefficientCupMap (G := G) φ ⊗ₘ coefficientCupMap (G := G) φ) ≫
        restrictedCup (G := G) φ ∧
    cupUnit (A := A) (G := G) ≫ coefficientCupMap (G := G) φ =
      restrictedCupUnit (G := G) φ := by
  sorry

/-- The coefficient map sends the specified unipotent extension class to phi composed
with a, retaining the actual shifted regular-ring scalar map in the domain.
Source: paragraph (3) (blueprint: lem-sfb-condensed-derived-restriction-calculus).
Proof: apply phi in both biproduct coordinates. Multiplicativity gives an equivariant
map of the two unipotent short exact sequences, and both endpoint maps are the regular
scalar map. The normalized scalar-derived comparison commutes with the resulting
boundaries and with shifts. Applying its unit equation and shifting down proves the
formula, with the same positive section splitting on both sides. -/
theorem coefficientClass (φ : A ⟶ A') (a : Character A G) :
    characterClass a ≫ coefficientCupMap (G := G) φ =
    (baseRingArrow φ)⟦(-1 : ℤ)⟧' ≫
      ((scalarBase φ).commShiftIso (-1 : ℤ)).inv.app
        ((DerivedCategory.singleFunctor (Modules A') 0).obj (Mod.regular A'.X)) ≫
      (scalarBase φ).map (characterClass (a.coefficients φ)) := by
  sorry

/-- Every ordered finite product is preserved by the coefficient map, with the canonical
lax scalar tensor pairing on the target. This includes the empty product.
Source: paragraph (3) (blueprint: lem-sfb-condensed-derived-restriction-calculus).
Proof: induct on length, starting with the unit equation of coefficientCup; use its
binary equation, tensor functoriality and the induction hypothesis at each successor.
Tensoring any ordered list of shifted cohomology classes into these tensor powers
recovers the corresponding assertion for all their ordered cup products. -/
theorem coefficientOrderedProducts (φ : A ⟶ A') (n : ℕ) :
    orderedProduct (cupUnit (A := A) (G := G)) (cup (A := A) (G := G)) n ≫
      coefficientCupMap (G := G) φ =
    tensorPowerMap (coefficientCupMap (G := G) φ) n ≫
      orderedProduct (restrictedCupUnit (G := G) φ) (restrictedCup (G := G) φ) n := by
  sorry

end CategoryTheory.CondensedDerivedRestriction
