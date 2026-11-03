/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.CondensedTateIntegralTowerData
import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.TateTensorDerivedOrdinaryNormalization
import WeilConjectures.AlgebraicGeometry.PurityIntegralTower.TateTensorRealizedSingleModel
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor

/-! The finite Tate transition on ordinary root generators.

Source: smooth-purity transport, normalized Tate tower, Step 4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

private theorem finiteModelIso_eq_realizedShiftModel
    (T : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (n d : ℕ)
    (hu : IsUnit ((ell ^ (n + 1) : ℕ) : Γ(T, ⊤))) :
    finiteModelIso T ell hT n d =
      realizedShiftModel T ell n (2 * (d : ℤ))
        (Etale.CoordinateCounitArrows.baseTateIso (coefficient ell (n + 1))
          (ell ^ (n + 1)) (pow_pos (Fact.out : ell.Prime).pos _)
          (CharP.cast_eq_zero _ _) T hu d) := by
  apply Iso.ext
  rfl

attribute [local irreducible] finiteModelIso in
private theorem finiteTateTensor_transition_model_core
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d b a : ℕ) (hab : a ≤ b)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
          ((pbcDerivedScalarAdjunction (pbcAdicQuotient T (datum.{u} ell) b a hab)).homEquiv
            _ _ ((scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
              (derivedRealization T ell a).map (proTwistMap d r))) ≫
        (pbcDerivedRestrictComp (pbcAdicProjection T (datum.{u} ell) b)
          (pbcAdicQuotient T (datum.{u} ell) b a hab)
          (pbcAdicProjection T (datum.{u} ell) a)
          (pbcAdicProjection_comp T (datum.{u} ell) b a hab)).hom.app _ ≫
        (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) a)).map
          (finiteModelIso T ell hT a d).hom ≫
        (Functor.mapDerivedCategorySingleFunctor
          (pbcRestrict (pbcAdicProjection T (datum.{u} ell) a)) (-(2 * (d : ℤ)))).hom.app _ =
      (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) b)).map
          (finiteModelIso T ell hT b d).hom ≫
        (Functor.mapDerivedCategorySingleFunctor
          (pbcRestrict (pbcAdicProjection T (datum.{u} ell) b)) (-(2 * (d : ℤ)))).hom.app _ ≫
        (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).map
          (finiteTateOrdinaryTransition T ell d b a hab r) := by
  have hb : IsUnit ((ell ^ (b + 1) : ℕ) : Γ(T, ⊤)) := by
    simpa only [Nat.cast_pow] using hT.pow (b + 1)
  have ha : IsUnit ((ell ^ (a + 1) : ℕ) : Γ(T, ⊤)) := by
    simpa only [Nat.cast_pow] using hT.pow (a + 1)
  have ht := finiteTateEtaleTransition_derived r
    (pow_pos (Fact.out : ell.Prime).pos _) (pow_pos (Fact.out : ell.Prime).pos _) hb ha d
  have h := realizedSemilinear_derived T ell b a hab (2 * (d : ℤ))
    (Etale.CoordinateCounitArrows.baseTateIso (coefficient ell (b + 1))
      (ell ^ (b + 1)) (pow_pos (Fact.out : ell.Prime).pos _) (CharP.cast_eq_zero _ _)
      T hb d)
    (Etale.CoordinateCounitArrows.baseTateIso (coefficient ell (a + 1))
      (ell ^ (a + 1)) (pow_pos (Fact.out : ell.Prime).pos _) (CharP.cast_eq_zero _ _)
      T ha d)
    (r.tensorPower d).hom (finiteTateEtaleTransition r d) ht
  rw [finiteModelIso_eq_realizedShiftModel T ell hT a d ha,
    finiteModelIso_eq_realizedShiftModel T ell hT b d]
  exact h

end AlgebraicGeometry.Scheme.PurityIntegralTower

namespace AlgebraicGeometry.ProEtale

/-- The universal derived scalar counit, followed by the canonical single-complex
comparison, is natural in an ordinary module sheaf.

Source: det-sp-scalar-extension-functor (1), functoriality on representatives.
(blueprint: lem-sp-finite-tate-transition-derived)
Proof: apply naturality of the universal complex counit to the single of the map,
then naturality of the single-complex comparison and functoriality of localization. -/
private theorem scalarSingleCounit_naturality
    {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (T : Scheme.{u})
    {M N : proEtaleRingModules T (proEtaleConstantRing T A)} (v : M ⟶ N) :
    (scalarExtensionFunctor f T).map ((DerivedCategory.singleFunctor _ 0).map v) ≫
        scalarExtensionFunctorCounit f T ((HomologicalComplex.single _ (.up ℤ) 0).obj N) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)) (.up ℤ) 0).hom.app
              N) =
      scalarExtensionFunctorCounit f T ((HomologicalComplex.single _ (.up ℤ) 0).obj M) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex
            (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)) (.up ℤ) 0).hom.app
              M) ≫
        (DerivedCategory.singleFunctor _ 0).map
          ((proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)).map v) := by
  have h := scalarExtensionFunctor_map f T
    ((HomologicalComplex.single _ (.up ℤ) 0).map v)
  have hs := (HomologicalComplex.singleMapHomologicalComplex
    (proEtaleRingExtension (proEtaleConstantRingMap (T := T) f)) (.up ℤ) 0).hom.naturality v
  dsimp only [Functor.comp_map] at hs
  erw [reassoc_of% h]
  erw [← DerivedCategory.Q.map_comp, hs, DerivedCategory.Q.map_comp]
  rfl

/-- The canonical derived Tate comparison commutes with the Kummer exponent
transition. Both sides use ordinary constant coefficient sheaves on the small
pro-etale site; scalar extension is the K-flat derived tensor product.

Source: det-sp-scalar-extension-functor (3), exponent independence;
sk-thm-purity-transport, Step 1.
(blueprint: lem-sp-finite-tate-transition-derived)
Proof: the ordinary scalar/Tate square commutes on root tensors, positive tensor
powers and dual evaluations, by the canonical exponent-naturality theorem.
Apply the degree-zero single functor to that square. The universal derived
counit is natural on single complexes, as is the single-complex comparison.
Compose these two naturality squares with the ordinary square. Expanding the
specified derived Tate comparison gives the displayed equation. Rank-one
flatness makes its counit invertible even for a nonflat coefficient quotient. -/
theorem finiteTateTensor_transition_model
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (f : A →+* B) (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (m n : ℕ) (hmn : m ≤ n) (a : ZMod (ℓ ^ (m + 1)) →+* A) (r : ℤ) :
    (scalarExtensionFunctor f T).map
        ((DerivedCategory.singleFunctor _ 0).map
          (scalarExtensionTateLevelIso T ℓ A m n hmn a r).hom) ≫
      (scalarExtensionFunctorTateIso f T ℓ m a r).hom =
    (scalarExtensionFunctorTateIso f T ℓ n
        (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hmn))
          (ZMod (ℓ ^ (m + 1))))) r).hom ≫
      (DerivedCategory.singleFunctor _ 0).map
        (scalarExtensionTateLevelIso T ℓ B m n hmn (f.comp a) r).hom := by
  have h := scalarSingleCounit_naturality f T
    (scalarExtensionTateLevelIso T ℓ A m n hmn a r).hom
  have ho := scalarExtensionTateIso_exponent_naturality f T ℓ m n hmn a r
  have hd := congrArg
    (fun v ↦ (DerivedCategory.singleFunctor
      (proEtaleRingModules T (proEtaleConstantRing T B)) 0).map v) ho
  simp only [Functor.map_comp] at hd
  simp only [scalarExtensionFunctorTateIso, Iso.trans_hom, asIso_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  erw [reassoc_of% h]
  erw [hd]

end AlgebraicGeometry.ProEtale
