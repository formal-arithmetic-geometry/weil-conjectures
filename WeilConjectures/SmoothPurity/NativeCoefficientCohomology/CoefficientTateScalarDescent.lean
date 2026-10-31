/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical

/-! # Descent of a completed-module scalar square to rational coefficients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance_reducible] WeilConjectures.PurCompactSupport.completed
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.NativeCoefficientCohomology
open FrobeniusCoefficientTwists

private theorem invert_scalar_square
    {C : Type*} [Category C] [Preadditive C] (F : C ⥤ C)
    {X Y : C} (b : X ≅ Y) (tX : F.obj X ⟶ X) (tY : F.obj Y ⟶ Y)
    (n : ℕ) (h : n • (F.map b.hom ≫ tY) = tX ≫ b.hom) :
    n • (tY ≫ b.inv) = F.map b.inv ≫ tX := by
  apply (cancel_epi (F.map b.hom)).mp
  rw [Preadditive.comp_nsmul, ← Category.assoc, ← Preadditive.nsmul_comp, h,
    Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.id_comp]

/-- An ordinary completed-module scalar square descends to the prescribed
rational coefficient-line structures, with no change of coefficient field.

Source: coefficient-twist blueprint, normalized derived pullback and rationalization.
(blueprint: lem-sf-coefficient-tate-scalar-descent).

Proof: invert the basis to orient the square toward the degree-zero line. Apply
single in degree zero. Naturality of the exact pullback/single comparison identifies
the ordinary derived square. Naturality of the specified completed-to-ordinary
comparison gives the integral completed square. Regard its arrows as arrows of
the full constructible subcategory. Apply additive rationalization. Its normalized
pullback-on-integral-arrows formula cancels the two unchanged-object identifications,
leaving precisely the rational scalar square. All functors preserve natural multiples. -/
theorem coefficient_tate_scalar_descent
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (S : Scheme.{u}) (g : S ⟶ S) [IsIso g]
    [∀ x : S, Invertible (l : S.residueField x)]
    (q d : ℕ) (b : positiveLine l E S 0 ≅ positiveLine l E S d)
    (hsquare : q ^ d • ((modulePull l E g).map b.hom ≫
        (positiveLineMaps l E g d).hom) = (positiveLineMaps l E g 0).hom ≫ b.hom) :
    ∃ c : rationalLine l E S (d : ℤ) ≅ rationalLine l E S 0,
      q ^ d • ((rationalDerivedLineMap l E g (d : ℤ)).hom ≫ c.hom) =
        (rationalDerivedPullback l E g).map c.hom ≫
          (rationalDerivedLineMap l E g 0).hom := by
  let single := DerivedCategory.singleFunctor (integralTowerModules l E S) 0
  let c : line l E S (d : ℤ) ≅ line l E S 0 := b.symm
  have hc : q ^ d • ((positiveLineMaps l E g d).hom ≫ c.hom) =
      (modulePull l E g).map c.hom ≫ (positiveLineMaps l E g 0).hom :=
    invert_scalar_square (modulePull l E g) b _ _ (q ^ d) hsquare
  have ht (n : ℕ) : signedLineMaps l E g (n : ℤ) = positiveLineMaps l E g n :=
    eq_of_heq ((existsUnique_signedLineMaps l E g).exists.choose_spec.1 n)
  have ho : q ^ d • ((ordinaryDerivedLineMap l E g (d : ℤ)).hom ≫
        single.map c.hom) =
      (PurCompactSupport.pull (PurCompactSupport.completed l E) g).map
        (single.map c.hom) ≫ (ordinaryDerivedLineMap l E g 0).hom := by
    dsimp only [ordinaryDerivedLineMap, Iso.trans_hom, Functor.mapIso_hom,
      Iso.app_hom]
    erw [ht d, ht 0]
    erw [Category.assoc, ← single.map_comp, ← Preadditive.comp_nsmul,
      ← single.map_nsmul, hc, single.map_comp]
    erw [← Category.assoc,
      ← ((modulePull l E g).mapDerivedCategorySingleFunctor 0).hom.naturality c.hom,
      Category.assoc]
    rfl
  let ci : sfIntegralTwistingCoefficient l E S (d : ℤ) ≅
      sfIntegralTwistingCoefficient l E S 0 := ObjectProperty.isoMk _ (single.mapIso c)
  have hi : q ^ d • ((integralDerivedLineMap l E g (d : ℤ)).hom ≫
        ci.hom.hom) =
      (integralDerivedPullback l E g).map ci.hom.hom ≫
        (integralDerivedLineMap l E g 0).hom := by
    dsimp only [integralDerivedLineMap, Iso.trans_hom, Iso.app_hom]
    rw [Category.assoc]
    change q ^ d • ((completedToOrdinary l E g).hom.app
        (sfIntegralTwistingCoefficient l E S (d : ℤ)) ≫
        (ordinaryDerivedLineMap l E g (d : ℤ)).hom ≫ single.map c.hom) =
      (integralDerivedPullback l E g).map (single.map c.hom) ≫
        (completedToOrdinary l E g).hom.app (sfIntegralTwistingCoefficient l E S 0) ≫
          (ordinaryDerivedLineMap l E g 0).hom
    erw [← Preadditive.comp_nsmul, ho, ← Category.assoc]
    simpa only [Category.assoc, Functor.comp_map, ObjectProperty.ι_map,
      ci, ObjectProperty.isoMk, ObjectProperty.homMk, Functor.mapIso_hom] using
      congrArg (fun f ↦ f ≫ (ordinaryDerivedLineMap l E g 0).hom)
        ((completedToOrdinary l E g).hom.naturality ci.hom).symm
  let Q := sfRationalConstructibleLocalization l E S
  refine ⟨Q.mapIso ci, ?_⟩
  let ti (n : ℤ) :
      (constructibleIntegralPullback l E g).obj (sfIntegralTwistingCoefficient l E S n) ≅
        sfIntegralTwistingCoefficient l E S n :=
    ObjectProperty.isoMk _ (integralDerivedLineMap l E g n)
  have hi' : q ^ d • ((ti (d : ℤ)).hom ≫ ci.hom) =
      (constructibleIntegralPullback l E g).map ci.hom ≫ (ti 0).hom := by
    apply ObjectProperty.hom_ext
    exact hi
  have hQ := congrArg Q.map hi'
  rw [Q.map_nsmul, Q.map_comp, Q.map_comp] at hQ
  have hm := (rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.2
    _ _ ci.hom 1
  have he := (conj_eqToHom_iff_heq _ _
    ((rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1
      (Q.obj (sfIntegralTwistingCoefficient l E S (d : ℤ))))
    ((rationalDerivedPullback_existsUnique l E g).exists.choose_spec.2.1
      (Q.obj (sfIntegralTwistingCoefficient l E S 0)))).2 hm
  change (rationalDerivedPullback l E g).map (Q.map ci.hom) = _ at he
  dsimp only [rationalDerivedLineMap, Iso.trans_hom, eqToIso.hom,
    Functor.mapIso_hom]
  rw [he]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Preadditive.comp_nsmul, hQ]
  rfl

end WeilConjectures.NativeCoefficientCohomology
