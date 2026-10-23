/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.HyperplaneClass

/-!
# Naturality of the map of the projective bundle formula

The component `chernPowMap q h a : Λ_S(-a)[-2a] ⟶ Rq_* Λ_P` of the map of the projective bundle
formula is the adjoint of a morphism `chernPowAdj q h a : Lq^* (Λ_S(-a)[-2a]) ⟶ Λ_P`. For a
morphism `f : X ⟶ Y` over `S`, its formation commutes with pullback along `f`
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_chernPowAdj`), hence

`chernPowMap (f ≫ q) (f^* h) a = chernPowMap q h a ≫ Rq_* (Λ_Y ⟶ Rf_* Λ_X)`

(`AlgebraicGeometry.Etale.chernPowMap_comp`). In particular the projective space formula is
invariant under isomorphisms over `S` (`AlgebraicGeometry.Etale.projectiveFormula_of_equiv`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open ProjectiveSpace

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasKummerClass Λ]

section Adjoint

variable {S P : Scheme.{u}} [HasInvertibleExponent Λ S] [HasInvertibleExponent Λ P]

/-- The adjoint `Lq^*(Λ_S(-a)[-2a]) ⟶ Λ_P` of the component `chernPowMap q h a` of the map of the
projective bundle formula: `Lq^*(Λ_S(-a)[-2a]) ≅ Λ ⊗ Λ(-a)[-2a] ⟶ Λ(a)[2a] ⊗ Λ(-a)[-2a] ≅ Λ`,
the middle map being `hᵃ ⊗ 1`. -/
noncomputable def chernPowAdj (q : P ⟶ S)
    (h : constantComplex Λ P ⟶ (tateObject Λ P 1)⟦2 * (1 : ℤ)⟧) (a : ℕ) :
    (L((q)^*[ModuleCat.{u + 1} Λ])).obj ((tateObject Λ S (-(a : ℤ)))⟦2 * (-(a : ℤ))⟧) ⟶
      constantComplex Λ P :=
  (leftDerivedUpperStarTateShiftIso Λ q (-(a : ℤ))).hom ≫
    (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) P _).inv ≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) P).map (chernPow h a)).app _ ≫
    (shiftTateObjectAddIso Λ P a (-(a : ℤ))).hom ≫
    (tateObjectShiftAddNegIso (a : ℤ)).hom

lemma chernPowMap_eq_homEquiv (q : P ⟶ S)
    (h : constantComplex Λ P ⟶ (tateObject Λ P 1)⟦2 * (1 : ℤ)⟧) (a : ℕ) :
    chernPowMap q h a =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).homEquiv _ _
        (chernPowAdj q h a) :=
  rfl

end Adjoint

section Naturality

variable {X Y S : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]
  [HasInvertibleExponent Λ S]

/-- The composite of derived direct images `Rq_* ∘ Rf_* ≅ R(f ≫ q)_*`, conjugate to
`L(f ≫ q)^* ≅ Lf^* ∘ Lq^*`. -/
noncomputable def rightDerivedLowerStarCompIso (f : X ⟶ Y) (q : Y ⟶ S) (c : X ⟶ S)
    (hc : c = f ≫ q) :
    R((f)_*[ModuleCat.{u + 1} Λ]) ⋙ R((q)_*[ModuleCat.{u + 1} Λ]) ≅
      R((c)_*[ModuleCat.{u + 1} Λ]) :=
  conjugateIsoEquiv ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f))
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) c)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f q c hc)

/-- **The adjoint of the projective bundle map commutes with pullback**: for `f : X ⟶ Y` and
`q : Y ⟶ S`, `Lf^*` of `chernPowAdj q h a` is `chernPowAdj (f ≫ q) (f^* h) a`, through
`L(f ≫ q)^* ≅ Lf^* Lq^*` and `Lf^* Λ_Y ≅ Λ_X`. -/
theorem leftDerivedUpperStar_map_chernPowAdj (f : X ⟶ Y) (q : Y ⟶ S) (c : X ⟶ S)
    (hc : c = f ≫ q) (h : constantComplex Λ Y ⟶ (tateObject Λ Y 1)⟦2 * (1 : ℤ)⟧) (a : ℕ) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f q c hc).hom.app _ ≫
        (L((f)^*[ModuleCat.{u + 1} Λ])).map (chernPowAdj q h a) ≫
        (leftDerivedUpperStarConstantComplexIso Λ f).hom =
      chernPowAdj c (VectorBundle.classRestriction Λ (r := 1) f h) a := by
  sorry

/-- **Naturality of the projective bundle map**: for `f : X ⟶ Y` and `q : Y ⟶ S`,

`chernPowMap (f ≫ q) (f^* h) a = chernPowMap q h a ≫ Rq_*(Λ_Y ⟶ Rf_* Λ_X)`

through `Rq_* Rf_* ≅ R(f ≫ q)_*`. -/
theorem chernPowMap_comp (f : X ⟶ Y) (q : Y ⟶ S) (c : X ⟶ S) (hc : c = f ≫ q)
    (h : constantComplex Λ Y ⟶ (tateObject Λ Y 1)⟦2 * (1 : ℤ)⟧) (a : ℕ) :
    chernPowMap c (VectorBundle.classRestriction Λ (r := 1) f h) a =
      chernPowMap q h a ≫ (R((q)_*[ModuleCat.{u + 1} Λ])).map (constantComplexUnit Λ f) ≫
        (rightDerivedLowerStarCompIso f q c hc).hom.app (constantComplex Λ X) := by
  sorry

/-- Naturality of the map of the projective bundle formula
(`AlgebraicGeometry.Etale.chernPowMap_comp`). -/
theorem projectiveFormulaMap_comp (f : X ⟶ Y) (q : Y ⟶ S) (c : X ⟶ S) (hc : c = f ≫ q)
    (h : constantComplex Λ Y ⟶ (tateObject Λ Y 1)⟦2 * (1 : ℤ)⟧) (r : ℕ) :
    projectiveFormulaMap c (VectorBundle.classRestriction Λ (r := 1) f h) r =
      projectiveFormulaMap q h r ≫ (R((q)_*[ModuleCat.{u + 1} Λ])).map (constantComplexUnit Λ f) ≫
        (rightDerivedLowerStarCompIso f q c hc).hom.app (constantComplex Λ X) := by
  sorry

/-- For an isomorphism `f`, the unit `Λ_Y ⟶ Rf_* Λ_X` is an isomorphism. -/
theorem isIso_constantComplexUnit_of_isIso (f : X ⟶ Y) [IsIso f] :
    IsIso (constantComplexUnit Λ f) := by
  sorry

/-- The projective bundle formula is invariant under isomorphisms over the base. -/
theorem isIso_projectiveFormulaMap_comp_iff (f : X ⟶ Y) [IsIso f] (q : Y ⟶ S) (c : X ⟶ S)
    (hc : c = f ≫ q) (h : constantComplex Λ Y ⟶ (tateObject Λ Y 1)⟦2 * (1 : ℤ)⟧) (r : ℕ) :
    IsIso (projectiveFormulaMap c (VectorBundle.classRestriction Λ (r := 1) f h) r) ↔
      IsIso (projectiveFormulaMap q h r) := by
  sorry

end Naturality

variable {S : Scheme.{u}} [HasInvertibleExponent Λ S]

variable [HasKummerClass.IsNormalized Λ] {k : Type u} [Field k] (aS : S ⟶ Spec (.of k))
  [IsSeparated aS] [LocallyOfFiniteType aS]

include aS in
/-- *Invariance under renaming the coordinates* of the projective-space formula: an equivalence
`e : n ≃ n'` induces an isomorphism `ℙ(Option n; S) ≅ ℙ(Option n'; S)` over `S` along which the
first Chern class of the hyperplane class restricts to that of the hyperplane class
(`AlgebraicGeometry.Etale.classRestriction_reindex_hyperplaneChernClass`), and the projective
bundle map is natural (`AlgebraicGeometry.Etale.isIso_projectiveFormulaMap_comp_iff`). -/
lemma projectiveFormula_of_equiv {n n' : Type u} [Fintype n] [Fintype n'] (e : n ≃ n')
    (h : ProjectiveFormula Λ S n) : ProjectiveFormula Λ S n' := by
  sorry

end Etale

end AlgebraicGeometry
