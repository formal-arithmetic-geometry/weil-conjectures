/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.SemiRepresentableObject
public import Sheaf.CategoryTheory.ProperFaceMatchingObject

/-!
# Matching schemes and one-member semi-representable families

Source: Stacks Project, Hypercoverings, Tags 01G2, 01G3, 01G5; Simplicial Methods,
Tag 0186 (blueprint: lem-weil-pbc-sr-matching-object-one-member).
-/

@[expose] public section

universe w u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace AlgebraicGeometry.Scheme

/-- Matching objects of one-member families are their scheme-theoretic matching schemes.
A simplicial object of `X.Etale` is exactly an augmented simplicial `X`-scheme all of whose
terms are étale over `X`. The cones below are limiting after forgetting to `Over X`, so
universality is tested on all schemes over `X`, rather than only the étale ones. The empty
proper-face diagram in degree zero has the specified vertex `id_X` and its unique matching
map is the augmentation.

Source: Stacks, Tags 01G2, 01G3, 01G5, 0186
(blueprint: lem-weil-pbc-sr-matching-object-one-member).

Proof, following the six steps of the node:
1. The small étale category has terminal object `id_X` and scheme-theoretic pullbacks
   [lem-weil-pbc-etale-base-change-finite-limits]. Its inclusion into `Over X` preserves
   these, hence finite limits [lem-weil-pbc-finite-limits-from-terminal-pullbacks].
2. Take the matching objects in `X.Etale`. Their boundary cones are also proper-face limits
   [lem-weil-pbc-matching-object-proper-faces, lem-weil-pbc-simplicial-matching-object].
   Preservation gives limiting cones in `Over X`, with étale vertices and matching maps
   whose proper-face components are precisely the simplicial operators.
3. The singleton inclusion preserves terminal objects and pullbacks by the memberwise
   formulas [lem-weil-pbc-semi-representable-finite-limits], hence finite limits by
   [lem-weil-pbc-finite-limits-from-terminal-pullbacks].
4. Apply this to the matching boundary diagram. Limit uniqueness identifies the recorded
   SR matching object with the singleton matching scheme, and identifies their matching
   maps by their face components. In degree zero both vertices are `{id_X}`.
5. Isomorphisms in SR are coverings. Covering permanence
   [lem-weil-pbc-semi-representable-covering-permanence] transports the covering condition
   across the comparison. A singleton is covering exactly when its component is étale and
   surjective. The component is étale since it is a morphism between étale `X`-schemes
   [lem-weil-pbc-etale-composition-cancellation].
6. Apply the equivalence in every degree to the definition of an SR hypercover
   [def-weil-pbc-semi-representable-object], obtaining the final equivalence. -/
theorem sr_matching_object_one_member (X : Scheme.{u}) (U : SimplicialObject X.Etale) :
    ∃ (M : ℕ → X.Etale)
      (π : ∀ n : ℕ, (Functor.const _).obj (M n) ⟶ U.properFaceDiagram n)
      (μ : ∀ n : ℕ, U _⦋n⦌ ⟶ M n),
      M 0 = Etale.mk (𝟙 X) ∧
      (∀ n : ℕ,
        Nonempty (IsLimit ((Etale.forget X).mapCone (Cone.mk (M n) (π n))))) ∧
      (∀ (n : ℕ) (a : SimplicialObject.ProperFaceCategory n),
        μ n ≫ (π n).app (op a) = U.map a.obj.hom.op) ∧
      (∀ n : ℕ,
        ∃ ψ : semiRepresentableMatchingObject (U ⋙ FormalCoproduct.incl.{w} X.Etale) n ≅
            (FormalCoproduct.incl.{w} X.Etale).obj (M n),
          semiRepresentableMatchingMap (U ⋙ FormalCoproduct.incl.{w} X.Etale) n ≫ ψ.hom =
            (FormalCoproduct.incl.{w} X.Etale).map (μ n)) ∧
      (∀ n : ℕ,
        IsSemiRepresentableCovering
          (semiRepresentableMatchingMap (U ⋙ FormalCoproduct.incl.{w} X.Etale) n) ↔
            Surjective (μ n).left) ∧
      (IsSemiRepresentableHypercover (U ⋙ FormalCoproduct.incl.{w} X.Etale) ↔
        ∀ n : ℕ, Etale (μ n).left ∧ Surjective (μ n).left) := by
  sorry

end AlgebraicGeometry.Scheme
