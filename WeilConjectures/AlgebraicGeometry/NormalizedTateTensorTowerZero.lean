/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedTateIntegralTowerData

/-! The zero-tensor unit comparison for a normalized Tate tower.

Source: smooth-purity transport, construction of the normalized Tate-unit tower.
(blueprint: lem-pur-normalized-tate-tensor-unit)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

private theorem unitSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (F : C ⥤ D) (G : A ⥤ B) (P : A ⥤ C) (Q : B ⥤ D)
    (t : P ⋙ F ≅ G ⋙ Q) {x x₀ : A} {y y₀ : B} {c₀ : C} {d₀ : D}
    (ub : x ≅ x₀) (ua : y ≅ y₀) (vb : P.obj x₀ ≅ c₀)
    (va : Q.obj y₀ ≅ d₀) (w : G.obj x₀ ≅ y₀) :
    F.map (P.map ub.hom ≫ vb.hom) ≫
        (F.map vb.inv ≫ t.hom.app x₀ ≫ Q.map w.hom ≫ va.hom) =
      (t.hom.app x ≫ Q.map (G.map ub.hom ≫ w.hom ≫ ua.inv)) ≫
        (Q.map ua.hom ≫ va.hom) := by
  simp only [Functor.map_comp, Category.assoc, Iso.map_hom_inv_id_assoc,
    Iso.map_inv_hom_id_assoc]
  have hn : F.map (P.map ub.hom) ≫ t.hom.app _ =
      t.hom.app _ ≫ Q.map (G.map ub.hom) := t.hom.naturality ub.hom
  simpa only [Category.assoc] using
    congrArg (fun z ↦ z ≫ Q.map w.hom ≫ va.hom) hn

private theorem finiteZeroIso_reduction
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime] (b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    (proScalar (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) T).map
        (finiteZeroIso T ell b).hom ≫ (unitReduction T ell b a hab).hom =
      proTwistMap 0 r ≫ (finiteZeroIso T ell a).hom := by
  exact unitSquare
    (proScalar (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) T)
    (ordinaryScalar (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) T)
    (comparison (coefficient ell (b + 1)) T) (comparison (coefficient ell (a + 1)) T)
    (ProEtale.pbcComparisonReduction T
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)))
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} (coefficient ell (b + 1))) T)
    (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} (coefficient ell (a + 1))) T)
    (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
      (coefficient ell (b + 1)) T)
    (ProEtale.DerivedCategory.mapDerivedCategoryComparisonUpperStarUnitIso
      (coefficient ell (a + 1)) T)
    (Etale.ExceptionalCoefficients.unitIso
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1)) T)

/-- The d=0 normalization follows from the scalar unit comparison and the
comparison square of an already normalized tower. This is strictly one clause of
`normalizedTateTensorTower`; it constructs no tower and proves no constructibility.

Proof: at zero, tensorPower is scalarZeroLineIso. After substituting finiteZeroIso
and unitReduction, cancel the two comparison-unit isomorphisms. Naturality of the
site/scalar comparison at the etale single-unit isomorphism gives precisely the
remaining equality. Apply derivedRealization to that equality, use naturality of
scalarComparison at finiteZeroIso, and postcompose the assumed tower square with
derivedRealization.map(finiteZeroIso). This proves the required equation for e₀.
The calculation uses coefficient multiplication and includes equal indices and
the empty scheme.
Source: smooth-purity transport, proof Step 4, zero-fold tensor clause.
(blueprint: lem-pur-normalized-tate-tensor-unit)
-/
theorem normalizedTateTensorTower_zero
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ)
    (M : AdicTower T (datum.{u} ell))
    (e : ∀ n : ℕ, M.level n ≅
      (derivedRealization T ell n).obj (finiteTwist T ell n d))
    (h : M.tower = strictDerivedTower T ell d)
    (hp : ProjectionNormalized T ell hT d M e h)
    (hsquare : ∀ (b a : ℕ) (hab : a ≤ b)
      (r : CoefficientLineComparison
        (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
        (ell ^ (b + 1)) (ell ^ (a + 1))
        (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T),
      (pbcDerivedExtend (pbcAdicQuotient T (datum.{u} ell) b a hab)).map (e b).hom ≫
          (scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
          (derivedRealization T ell a).map (proTwistMap d r) =
        (M.normalization b a hab).hom ≫ (e a).hom)
    (hcomparisons : ∀ (b a : ℕ) (hab : a ≤ b), Nonempty
      (CoefficientLineComparison
        (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
        (ell ^ (b + 1)) (ell ^ (a + 1))
        (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T)) :
    ∀ hd : d = 0, ∀ (b a : ℕ) (hab : a ≤ b),
      let e₀ (n : ℕ) := e n ≪≫ (derivedRealization T ell n).mapIso
        (eqToIso (congrArg (finiteTwist T ell n) hd) ≪≫ finiteZeroIso T ell n);
      (pbcDerivedExtend (pbcAdicQuotient T (datum.{u} ell) b a hab)).map (e₀ b).hom ≫
          (scalarComparison T ell b a hab).hom.app (𝟙_ _) ≫
          (derivedRealization T ell a).map (unitReduction T ell b a hab).hom =
        (M.normalization b a hab).hom ≫ (e₀ a).hom := by
  intro hd b a hab
  subst d
  obtain ⟨r⟩ := hcomparisons b a hab
  have hs := hsquare b a hab r
  have hn := (scalarComparison T ell b a hab).hom.naturality
    (finiteZeroIso T ell b).hom
  dsimp only [Functor.comp_map] at hn
  have hz := congrArg (derivedRealization T ell a).map
    (finiteZeroIso_reduction T ell b a hab r)
  simp only [Functor.map_comp] at hz
  dsimp only
  simp only [eqToIso_refl, Iso.refl_trans, Iso.trans_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, hz, reassoc_of% hs]

end AlgebraicGeometry.Scheme.PurityIntegralTower
