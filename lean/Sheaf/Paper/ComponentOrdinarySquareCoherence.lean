/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z6
-/
module

public import Sheaf.Paper.ComponentOrdinaryEdges

/-! # Coefficient-normalized ordinary component square coherence

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ComponentDerivedSquare

/-- Normalized ordinary squares satisfy the identity and composition equations.

Source: Hemo--Richarz--Scholbach, construction (4.1), pp. 8--9 and the naturality
used in Corollary 4.4(2)
(blueprint: lem-zl-component-ordinary-square-coherence).

Proof: first forget module structures. The specified tests in Square agree with
the relative lift base-change isomorphisms. For the identity these are the
identity test comparison; for a composite they paste to the composite comparison
after the canonical pullback associators. The prescribed first and second
projection equations on s.identity and s.composition identify their tests with
the canonical slice comparisons, by pullback uniqueness. Applying an arbitrary
sheaf contravariantly yields the right-adjoint identity and composition equations.
Use Square.abelian_mate and the slice abelian_mate formulas to identify the left
comparisons as their adjunction mates. Injectivity of conjugateIsoEquiv and its
whiskering and pasting equations give the abelian identities. The scheme
identity and composition on modules are also the canonical adjunction mates.
Their underlying abelian maps, after schemeUnderlying, agree with the abelian
ones: apply the adjunction homEquiv, use the formula for its underlying morphism,
and cancel the extension unit followed by extendScalarsIsoComapInv. Thus the
underlying maps in the two desired equations are equal, by ordinary_underlying
for each square and slice comparison and naturality of schemeUnderlying.
Faithfulness of Mod.forget proves the module equations. This lemma assumes all
edges, squares and their local normalizations; it constructs none of them. -/
theorem component_ordinary_square_coherence
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] (s : OrdinaryEdges Λ)
    (sq : ∀ {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : Y ⟶ X),
      Square Λ f (s.corner X) (s.corner Y) (s.slice f)) :
    (∀ (X : Scheme.{u}) [IsAffine X]
      (M : Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        Ab.{u + 1}) (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    ((sq (𝟙 X)).ordinary).hom.app M ≫
        ((s.corner X).modules Λ X).map ((s.identity X).ordinary.hom.app M) =
      (CondensedRing.upperStarId Λ.X X).hom.app (((s.corner X).modules Λ X).obj M)) ∧
    (∀ (X Y Z : Scheme.{u}) [IsAffine X] [IsAffine Y] [IsAffine Z]
      (f : Y ⟶ X) (g : Z ⟶ Y)
      (M : Mod (Sheaf ((coherentTopology Profinite.{u}).over (affineComponentSpace X))
        Ab.{u + 1}) (CondensedRing.profiniteCoefficient Λ.X (affineComponentSpace X))),
    (CondensedRing.upperStarComp Λ.X g f).hom.app (((s.corner X).modules Λ X).obj M) ≫
        (CondensedRing.upperStar Λ.X g).map (((sq f).ordinary).hom.app M) ≫
        ((sq g).ordinary).hom.app (((s.slice f).modules Λ).obj M) =
      ((sq (g ≫ f)).ordinary).hom.app M ≫
        ((s.corner Z).modules Λ Z).map ((s.composition f g).ordinary.hom.app M)) := by sorry

end AlgebraicGeometry.ProEtale.ComponentDerivedSquare
