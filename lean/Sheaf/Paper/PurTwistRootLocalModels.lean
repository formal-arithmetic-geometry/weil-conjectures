/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B7
-/
module

public import Sheaf.Paper.PurTwistSheaves
public import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk

/-! # Compatible local bases of the root tower

Source: coefficient-twist blueprint, proof steps 1--4.
(blueprint: lem-pur-twist-root-local-models)
-/

@[expose] public section
set_option autoImplicit false
universe u d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme

/-- Finite roots have étale local bases, and compatible lifts on weakly contractible
covers trivialize the entire inverse limit and identify its finite quotients.

Source: Stacks Project, Tags 03PK and 03RV; Bhatt--Scholze, Sections 6.5 and 6.8;
coefficient-twist blueprint, proof steps 1--4.
(blueprint: lem-pur-twist-root-local-models)

Proof: on affine opens the primitive-root scheme is étale and surjective, since l
is invertible. The universal primitive root identifies the constant cyclic group
with the roots sheaf. The comparison inverse image from the étale site preserves
this isomorphism and its normalized finite scalar action. Kummer lifting on every test
scheme makes consecutive power transitions locally surjective, hence epimorphisms.
Refine the level-one primitive-root cover by affine weakly contractible pro-étale
covers. On each member epimorphisms of sheaves are surjective on sections, so choose
lifts recursively. An l-th root of a primitive l^r-th root is primitive of order
l^(r+1): in the cyclic local model its exponent reduces to a unit modulo l. Thus
these chosen roots give compatible cyclic bases at every level. Restriction to a
slice commutes with sectionwise limits, so their limits identify the completed
coefficient module with the original root limit. The coordinatewise action is the
specified action by its uniqueness theorem. The quotient comparison for constant
completion then identifies ordinary scalar reduction with the finite root module.
All assertions allow the empty base: the cover and its section calculations remain
valid, and there are no geometric points there. -/
theorem purTwistRootLocalModels (S : Scheme.{u}) (l : ℕ) [Fact l.Prime]
    [∀ x : S, Invertible (l : S.residueField x)] :
    (∀ n : ℕ,
      (∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        (∀ i : I, Etale (U i).hom) ∧
        ∀ i : I, Nonempty ((purTwistRootsModule S l n).over (U i) ≅
          (SheafOfModules.unit (purTwistRing S (purTwistFiniteRing S l n))).over (U i))) ∧
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S),
        Finite ((proEtaleGeometricStalk (C := AddCommGrpCat.{u + 1}) s
          (proEtaleRootsOfUnitySheaf S (l ^ (n + 1)))) : Type (u + 1)))) ∧
    ((∃ (I : Type (u + 1)) (U : I → S.ProEt)
        (f : ∀ i : I, U i ⟶ ProEt.mk (𝟙 S)),
        Presieve.ofArrows U f ∈ (ProEt.precoverage S).coverings _ ∧
        ∀ i : I, Nonempty ((purTwistZlModule S l).over (U i) ≅
          (SheafOfModules.unit (purTwistRing S (purTwistZlCompletion S l))).over (U i))) ∧
      ∀ n : ℕ, Nonempty
        (SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1}
          (purTwistZlProjection S l n)
          (purTwistZlModule S l) ≅ purTwistRootsModule S l n)) := by
  sorry

end AlgebraicGeometry.Scheme
