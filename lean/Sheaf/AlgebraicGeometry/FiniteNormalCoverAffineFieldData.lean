module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Curve.DivisorPullback
public import WeilConjectures.Topology.PresheafModuleStalkFunctor

import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Affine field data for finite covers of normal integral schemes

Source: Stacks Project, Divisors, Tag 0BD3, lemma-norm-in-normal-case, first paragraph;
Properties, Tags 033L and 0358
(blueprint: lem-sfb-finite-normal-cover-affine-field-data).

The extension map is the existing generic stalk map `Scheme.Hom.functionFieldMap`.
All affine rings are actual structure-sheaf section rings and their embeddings are the
existing `Scheme.germToFunctionField` maps. No choices of abstract fraction fields occur.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- A finite surjective cover of integral schemes with normal base has a single finite
extension of generic stalk fields, compatible with all nonempty affine section rings
and their restrictions.

Source: Stacks Project, Divisors, Tag 0BD3, lemma-norm-in-normal-case, first paragraph;
Properties, Tags 033L and 0358
(blueprint: lem-sfb-finite-normal-cover-affine-field-data).

Proof:
1. Every nonempty open of the target has nonempty open inverse image by surjectivity.
The generic point of the integral source belongs to that inverse image. Thus its image
is generic, and scheme sobriety (`lem-sc-scheme-sober`) identifies the image with the
chosen generic point of the target.
2. Finiteness (`def-weil-finite-integral-morphism`) makes the inverse image of each
nonempty affine open affine and its section ring finite over the base section ring.
Apply `lem-sc-integral-function-field-affine-fraction` to the two integral schemes:
their section rings are domains and the generic germs embed them as subrings of their
respective fraction fields. Surjectivity ensures the inverse image is nonempty.
3. The actual generic stalk map is injective because it is a unital map of fields.
The definition of stalk maps on germs (`def-weil-locally-ringed-space-morphism` and
`def-weil-pbc-module-stalk`) gives the commuting square. Its three injective sides
show that the map on affine sections is injective as well.
4. Apply `lem-trf-finite-domain-fraction-degree` to the finite injective domain algebra.
Identify its induced map on quotients with the generic stalk map using the square.
Every element is a quotient, so these are the same extension. Its dimension is finite
and positive, since the target field is a nonzero vector space. A nonempty affine
open exists by local affineness and nonemptiness of the integral target.
5. An element of the base function field integral over the affine section ring is
integral over every local ring. By `lem-sc-integral-scheme-stalks-in-function-field`,
these local rings embed into the same function field; their assumed integral closedness
puts the element in every local ring. `lem-sc-function-field-sections-glue` glues its
local representatives to an affine section. Hence the affine base ring is integrally
closed, without a Noetherian hypothesis or normality of the source.
6. Germs commute with restriction by `def-weil-pbc-module-stalk`, on both schemes.
The section maps of the morphism also commute with restriction. Therefore every affine
fraction-field extension is the same generic stalk map and has the single degree `d`.
-/
theorem finite_normal_cover_affine_field_data
    {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    (p : Y ⟶ Z) [IsFinite p] [Surjective p]
    (hZ : ∀ z : Z, IsDomain (Z.presheaf.stalk z) ∧
      IsIntegrallyClosed (Z.presheaf.stalk z)) :
    ∃ hη : p (genericPoint Y) = genericPoint Z,
      Function.Injective (p.functionFieldMap hη).hom ∧
      (p.functionFieldMap hη).hom.Finite ∧
      ∃ d : ℕ,
        d = @Module.finrank Z.functionField Y.functionField _ _
          (p.functionFieldMap hη).hom.toAlgebra.toModule ∧
        1 ≤ d ∧
        ∀ (U : Z.Opens) (_hU : IsAffineOpen U) [Nonempty U],
          ∃ _hpre : Nonempty (p ⁻¹ᵁ U),
            IsAffineOpen (p ⁻¹ᵁ U) ∧
            IsDomain Γ(Z, U) ∧ IsDomain Γ(Y, p ⁻¹ᵁ U) ∧
            Function.Injective (p.app U).hom ∧ (p.app U).hom.Finite ∧
            IsIntegrallyClosed Γ(Z, U) ∧
            Function.Injective (Z.germToFunctionField U).hom ∧
            Function.Injective (Y.germToFunctionField (p ⁻¹ᵁ U)).hom ∧
            IsFractionRing Γ(Z, U) Z.functionField ∧
            IsFractionRing Γ(Y, p ⁻¹ᵁ U) Y.functionField ∧
            (∀ b : Γ(Z, U),
              Y.germToFunctionField (p ⁻¹ᵁ U) (p.app U b) =
                p.functionFieldMap hη (Z.germToFunctionField U b)) ∧
            (∀ (W : Z.Opens) (_hW : IsAffineOpen W) [Nonempty W]
                (hWU : W ≤ U) [Nonempty (p ⁻¹ᵁ W)],
              (∀ b : Γ(Z, U),
                Z.germToFunctionField W (Z.presheaf.map (homOfLE hWU).op b) =
                  Z.germToFunctionField U b) ∧
              (∀ a : Γ(Y, p ⁻¹ᵁ U),
                Y.germToFunctionField (p ⁻¹ᵁ W)
                    (Y.presheaf.map (homOfLE (p.preimage_mono hWU)).op a) =
                  Y.germToFunctionField (p ⁻¹ᵁ U) a)) := by
  sorry

end AlgebraicGeometry
