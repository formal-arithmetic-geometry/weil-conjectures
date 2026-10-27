/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.InternalAdjunctionPairingChange
public import WeilConjectures.ConstructibleSheaf.Defs

/-! # Coefficient Hom from a locally finite projective sheaf

Source: blueprint thm-coef-finite-hom, the finite-projective local calculation in
proof paragraphs 2--3 (blueprint: lem-coef-locally-projective-coefficient-hom).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Etale
open CoefficientPairingChange

/-- The local finite-projective calculation, with arbitrary finite coefficients and
an arbitrary second argument of finite-Tor bounded constructibility.
Source: blueprint thm-coef-finite-hom, proof paragraphs 2--3
(blueprint: lem-coef-locally-projective-coefficient-hom).

Proof: On each member of the given etale trivializing cover, write the finite
projective constant module as a retract of a finite free module. Its degree-zero
complex is flat and constructible. The internal Hom from it is its finite
projective dual tensored with the second argument. This preserves the second
argument's Tor interval and bounded cohomology. Intersect the trivializing cover
with the constructibility stratification of the second argument to see that its
Hom cohomology sheaves are constructible. All these properties descend along the
etale cover. For a finite free constant module the reduced evaluation pairing is
the usual sum of coordinate products, so its transpose is the identity under the
finite-sum identifications. The comparison is natural under the inclusion and
retraction of the projective summand. Thus it is an isomorphism for that summand.
Restriction commutes with these evaluation comparisons; the cone restricts to
zero on the cover, so its geometric stalks vanish and the cone is zero. This
proves invertibility of the specified evaluation transpose, including rank zero,
empty schemes, zero rings and identity coefficient maps. No flatness of the
coefficient map and no global constant-rank assumption is used. -/
theorem locallyProjectiveCoefficientHom
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (L : Sheaf T.smallEtaleTopology (ModuleCat A))
    (hL : ∃ d : Scheme.LocallyConstantDatum L, ∀ i : d.cover.I₀,
      ∃ P : ModuleCat A, Module.Finite A P ∧ Module.Projective A P ∧
        Nonempty (L.over (d.cover.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat A)).obj P))
    (N : DerivedCategoryModule A T)
    (hN : DerivedCategory.isBoundedConstructible A T N ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b N) :
    (DerivedCategory.isBoundedConstructible A T
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)) ∧
    (DerivedCategory.isBoundedConstructible A T
        (((derivedHom (ModuleCat A) T).obj
          (op ((_root_.DerivedCategory.singleFunctor _ 0).obj L))).obj N) ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b
        (((derivedHom (ModuleCat A) T).obj
          (op ((_root_.DerivedCategory.singleFunctor _ 0).obj L))).obj N)) ∧
    IsIso (evaluationComparison φ T ((_root_.DerivedCategory.singleFunctor _ 0).obj L) N) := by
  sorry

end AlgebraicGeometry.Etale
