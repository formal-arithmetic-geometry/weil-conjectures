/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.CategoryTheory.Localization.Predicate

/-! # Canonical localization of a bounded-below exact square

Source: WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/PlusAdjunction.lean,
`derivedPlus_mateEquiv_app_fac`, hypothesis `hθ`; Stacks Project, Tags 014X, 015F, 05RW.
(blueprint: lem-trf-bounded-below-square-localization)

The functors in the conclusion have source `DerivedCategory.Plus B` and target
`DerivedCategory A'`. The homotopy-category comparisons retain the prescribed
unbounded exact derived functors, restricted along the bounded-below inclusion.
-/

@[expose] public section

set_option autoImplicit false

universe uA uB uA' uB' vA vB vA' vB' wA wB wA' wB'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An arbitrary natural square of exact additive functors has a unique localization on
bounded-below derived objects. The first equality is the commuting localization square;
the second gives its component as the termwise map conjugated by the comparisons.
Here `mapDerivedCategoryFactorsh` is the homotopy version of the exact-functor comparison,
and the composition isomorphisms identify successive termwise applications with the
termwise composite. Thus the resulting transformation is precisely `D(σ)`.

Source: PlusAdjunction.lean, `derivedPlus_mateEquiv_app_fac`, hypothesis `hθ`, and
Sheaf/CategoryTheory/BoundedBelowDerivedMateModel.lean, `boundedBelowDerivedSquare`;
Stacks Project, derived.tex, Tags 014X, 015F, and 05RW(1).
(blueprint: lem-trf-bounded-below-square-localization)

Proof:
1. Apply the four additive functors termwise. They preserve lower bounds and homotopies.
Naturality of σ with each differential makes its termwise components a chain map;
naturality with each chain map makes this a natural transformation on the homotopy category.
Exactness preserves quasi-isomorphisms and supplies the comparisons φ (the node
lem-weil-pbc-exact-functor-derived-factorization).
2. Whisker and compose the comparisons to obtain A_N = E'(φ_G,N) followed by
φ_L',K(G)N and B_N = S(φ_L,N) followed by φ_H,K(L)N. The canonical inclusion comparison
identifies qN with the ambient homotopy localization, naturally in N
(lem-weil-pbc-bounded-below-cochain-localization).
3. Bounded-below cochain localization is a localization without enough injectives.
Apply natural-transformation descent, with target D(A'), to the termwise square
and the two composite comparisons. Its component formula is A_N followed by q(σ^K_N)
and B_N inverse, and multiplication by B_N gives the first equality. Passing through
the homotopy quotient gives these equalities for every N in K⁺(B)
(lem-weil-pbc-localization-universal-property, clause (2)).
4. If two transformations satisfy the square, cancel B_N to equate their components
at every qN. Localization's natural-transformation extensionality makes them equal
(lem-weil-pbc-localization-universal-property, clause (3)). The second equality is
therefore also forced by the first. This is the canonical descent D(σ); only the
comparison isomorphisms are inverted, with no invertibility hypothesis on σ and no
choice of injective resolutions.
-/
theorem existsUnique_boundedBelowSquareLocalization
    {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
    [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
    [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
    [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wB} B]
    [HasDerivedCategory.{wA'} A'] [HasDerivedCategory.{wB'} B']
    (L : B ⥤ A) (L' : B' ⥤ A') (G : B ⥤ B') (H : A ⥤ A')
    [L.Additive] [L'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (σ : G ⋙ L' ⟶ L ⋙ H) :
    ∃! θ : DerivedCategory.Plus.ι ⋙ (G.mapDerivedCategory ⋙ L'.mapDerivedCategory) ⟶
        DerivedCategory.Plus.ι ⋙ (L.mapDerivedCategory ⋙ H.mapDerivedCategory),
      ∀ N : HomotopyCategory.Plus B,
        (θ.app (DerivedCategory.Plus.Qh.obj N) ≫
            H.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app N.obj) ≫
            H.mapDerivedCategoryFactorsh.hom.app
              ((L.mapHomotopyCategory (ComplexShape.up ℤ)).obj N.obj) =
          L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N.obj) ≫
            L'.mapDerivedCategoryFactorsh.hom.app
              ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj N.obj) ≫
            DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L'))
                  (ComplexShape.up ℤ)).hom.app N.obj ≫
                (NatTrans.mapHomotopyCategory σ (ComplexShape.up ℤ)).app N.obj ≫
                (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H))
                  (ComplexShape.up ℤ)).inv.app N.obj)) ∧
        (θ.app (DerivedCategory.Plus.Qh.obj N) =
          L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N.obj) ≫
            L'.mapDerivedCategoryFactorsh.hom.app
              ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj N.obj) ≫
            DerivedCategory.Qh.map
              ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L'))
                  (ComplexShape.up ℤ)).hom.app N.obj ≫
                (NatTrans.mapHomotopyCategory σ (ComplexShape.up ℤ)).app N.obj ≫
                (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H))
                  (ComplexShape.up ℤ)).inv.app N.obj) ≫
            H.mapDerivedCategoryFactorsh.inv.app
              ((L.mapHomotopyCategory (ComplexShape.up ℤ)).obj N.obj) ≫
            H.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.inv.app N.obj)) := by
  let a : DerivedCategory.Qh ⋙ (G.mapDerivedCategory ⋙ L'.mapDerivedCategory) ≅
      (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        L'.mapHomotopyCategory (ComplexShape.up ℤ)) ⋙ DerivedCategory.Qh :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight G.mapDerivedCategoryFactorsh L'.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ L'.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm
  let b : DerivedCategory.Qh ⋙ (L.mapDerivedCategory ⋙ H.mapDerivedCategory) ≅
      (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        H.mapHomotopyCategory (ComplexShape.up ℤ)) ⋙ DerivedCategory.Qh :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight L.mapDerivedCategoryFactorsh H.mapDerivedCategory ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ H.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm
  let τ := (Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L'))
      (ComplexShape.up ℤ)).hom ≫
    NatTrans.mapHomotopyCategory σ (ComplexShape.up ℤ) ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H))
      (ComplexShape.up ℤ)).inv
  let δ := a.hom ≫ Functor.whiskerRight τ DerivedCategory.Qh ≫ b.inv
  let ff := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso B) (DerivedCategory A')
  let θ : DerivedCategory.Plus.ι ⋙ (G.mapDerivedCategory ⋙ L'.mapDerivedCategory) ⟶
      DerivedCategory.Plus.ι ⋙ (L.mapDerivedCategory ⋙ H.mapDerivedCategory) :=
    ff.preimage (Functor.whiskerLeft (HomotopyCategory.Plus.ι B) δ)
  have hθ (N : HomotopyCategory.Plus B) :
      θ.app (DerivedCategory.Plus.Qh.obj N) =
        a.hom.app N.obj ≫ DerivedCategory.Qh.map (τ.app N.obj) ≫ b.inv.app N.obj := by
    have hmap : Functor.whiskerLeft DerivedCategory.Plus.Qh θ =
        Functor.whiskerLeft (HomotopyCategory.Plus.ι B) δ := ff.map_preimage _
    exact congr_app hmap N
  refine ⟨θ, ?_, ?_⟩
  · intro N
    have hformula := hθ N
    dsimp [a, b, τ] at hformula
    simp only [Category.id_comp, Category.comp_id, Category.assoc] at hformula
    refine ⟨?_, hformula⟩
    have hsquare : θ.app (DerivedCategory.Plus.Qh.obj N) ≫ b.hom.app N.obj =
        a.hom.app N.obj ≫ DerivedCategory.Qh.map (τ.app N.obj) := by
      rw [hθ N]
      simp only [Category.assoc, Iso.inv_hom_id_app]
      erw [Category.comp_id]
    dsimp [a, b, τ] at hsquare
    simpa only [Category.id_comp, Category.comp_id, Category.assoc] using hsquare
  · intro θ' hθ'
    apply Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso B)
    intro N
    rw [(hθ' N).2, hθ N]
    dsimp [a, b, τ]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]

end CategoryTheory
