/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.Paper.ContinuousCoefficientRealizations
public import Mathlib.Data.Matrix.Basic

/-! # Continuous functions for integral matrix charts

The analytic part of the pivot argument supplies a dominating, nowhere zero entry.
The module-object block decomposition is constructed separately.
-/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory MonObj Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Evaluate the regular-module coefficients of a finite free map at the unit section,
after a supplied continuous-function realization of the coefficient ring.
Source: Bhatt--Scholze, Section 6.8, continuous coefficient realization.
(blueprint: lem-weil-pbc-integral-matrix-analytic-cover) -/
noncomputable def integralMatrixFunctions (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u})
    (e : condensedRingObj (integralCoeff ℓ E) X ⟶
      (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf X (continuousIntegers ℓ E))) [IsIso e]
    {n t : ℕ}
    (f : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t) :
    Matrix (Fin t) (Fin n) C(X, continuousIntegers ℓ E) := fun i j ↦
  let p := biproduct.ι _ j ≫ f ≫ biproduct.π _ i
  (((inv e ≫ p.hom ≫ e).hom.app (op (Scheme.ProEt.mk (𝟙 X)))) (ULift.up 1)).down

/-- The inclusion of continuous integral functions into continuous field-valued functions.
Source: the continuous coefficient inclusion O_E to E.
(blueprint: lem-weil-pbc-integral-matrix-analytic-cover) -/
noncomputable def integralFunctionInclusion (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    (continuousMapRingSheafMap X (continuousIntegers ℓ E).subtype continuous_subtype_val)

instance (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) :
    IsMonHom (integralFunctionInclusion ℓ E X) := by
  dsimp [integralFunctionInclusion]
  infer_instance

/-- The actual standard basis after normalized integral coefficient pullback.
Source: preservation of finite biproducts and the coefficient pullback isomorphism.
(blueprint: lem-weil-pbc-integral-matrix-analytic-cover) -/
noncomputable def integralFiniteFreePullbackIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) :
    let R := condensedRingObj (integralCoeff ℓ E) X
    let T := (ProEtale.upperStar Ab.{u + 1} f).mapMod R ⋙
      Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) f))
    T.obj (Mod.finiteFree R n) ≅
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) Y) n := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let P := (ProEtale.upperStar Ab.{u + 1} f).mapMod R
  let α := condensedPullbackHom (integralCoeff ℓ E) f
  let Q := Mod.comap (D := Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (inv α)
  let T := P ⋙ Q
  let e₀ : P.obj (Mod.regular R) ≅
      Mod.regular ((ProEtale.upperStar Ab.{u + 1} f).obj R) :=
    Mod.isoMk (Iso.refl _) (by simp [Mod.act])
  let e₁ : T.obj (Mod.regular R) ≅
      Mod.regular (condensedRingObj (integralCoeff ℓ E) Y) :=
    Q.mapIso e₀ ≪≫ Mod.regularIsoOfIsIso α
  exact T.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
    biproduct.mapIso (fun _ ↦ e₁)

/-- After a rational cokernel trivialization, a map between standard finite free modules
admits analytic pivot charts.

Source: Bhatt--Scholze, Section 6.8, Definition 6.8.10 and Proposition 6.8.11(1);
the continuous-function pivot argument is an agent reduction.
(blueprint: lem-weil-pbc-integral-matrix-analytic-cover)

Proof: refine the supplied cover, transport the standard finite-free bases along the
coefficient pullback comparisons, and use the canonical comparison with continuous
O_E-functions. Its monoid property, isomorphism and compatibility with O_E to E are
proved in ContinuousCoefficientRealizations.
Exact geometric-field evaluation computes the rational cokernel dimension as target
rank minus matrix rank. The rank is therefore constant on each cover member. If the
matrix is zero at any point, it is zero everywhere, and faithfulness of the continuous
matrix realization gives the zero alternative. Otherwise every point has a nonzero
entry. Choose one of maximal norm there. Intersect the finitely many open loci where
the change in each entry has norm strictly below this positive maximum. The ultrametric
inequality makes the chosen entry nowhere zero with constant norm on this neighborhood
and bounds every other entry by it. Transport the bases and realization to these opens
and compose covers. Empty members and zero source or target ranks use the zero branch.
The conclusion only concerns continuous coefficients, not divisibility or module blocks. -/
theorem integralMatrix_analytic_cover (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (n t₀ : ℕ) (X : Scheme.{u})
    (a : Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) n ⟶
      Mod.finiteFree (condensedRingObj (integralCoeff ℓ E) X) t₀)
    (hC : ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (V.f k)).obj
          (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj
            (cokernel a)))) :
    ∃ V : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ k,
      let R := condensedRingObj (integralCoeff ℓ E) (V.X k)
      let T := (ProEtale.upperStar Ab.{u + 1} (V.f k)).mapMod
          (condensedRingObj (integralCoeff ℓ E) X) ⋙
        Mod.comap (inv (condensedPullbackHom (integralCoeff ℓ E) (V.f k)))
      let f := (integralFiniteFreePullbackIso ℓ E (V.f k) n).inv ≫ T.map a ≫
        (integralFiniteFreePullbackIso ℓ E (V.f k) t₀).hom
      T.map a = 0 ∨ ∃ (i : Fin t₀) (j : Fin n),
        (∀ x, (integralMatrixFunctions ℓ E (V.X k)
          (chartComparison (V.X k) (continuousIntegers ℓ E)) f i j x).val ≠ 0) ∧
        ∀ r s x,
          ‖(integralMatrixFunctions ℓ E (V.X k)
            (chartComparison (V.X k) (continuousIntegers ℓ E)) f r s x).val‖ ≤
          ‖(integralMatrixFunctions ℓ E (V.X k)
            (chartComparison (V.X k) (continuousIntegers ℓ E)) f i j x).val‖ := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
