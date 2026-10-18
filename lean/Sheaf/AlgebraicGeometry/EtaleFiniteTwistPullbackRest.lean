/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine
import Sheaf.AlgebraicGeometry.Sites.InverseImageRepresentable
import Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayCoverEtale
import Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.CategoryTheory.SiteInverseImageTensor
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import Sheaf.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Paper.RingedTopoiCanonicalTensorPullback
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageCompositionUnits
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme
/-! Remaining coherence package for finite Tate pullback.
(blueprint: lem-asd-etale-finite-twist-pullback). -/
/-- Strict intermediate package for the finite Tate pullback theorem. The construction first
chooses the primitive-root etale cover, identifies the roots sheaf there with the constant
cyclic sheaf, extends scalars to `A`, and forms signed tensor powers and duals. The normalized
adjunction, unit, tensor, evaluation, identity, composition and local-trivialization equations
are then checked on the local basis and descend by etale-cover detection. This intermediate
package is used by the parent theorem; its proof is the corresponding group of steps in the
parent blueprint and remains available as a named proof obligation.
Source: Stacks Project, Tags 03PK, 03Q1, 03EK, 03EM.
(blueprint: lem-asd-etale-finite-twist-pullback-rest). -/
theorem etaleFiniteTwistPullback_rest (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hm : 0 < m) (hA : (m : A) = 0)
    (r : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) →
        ((Etale.upperStar AddCommGrpCat.{u + 1} v).obj (T.rootsOfUnitySheaf m) ≅
          T'.rootsOfUnitySheaf m))
    (c : ∀ {T T' : Scheme.{u}} (v : T' ⟶ T),
        IsUnit (m : Γ(T, ⊤)) → IsUnit (m : Γ(T', ⊤)) → ∀ a : ℤ,
        (Etale.upperStar (ModuleCat.{u + 1} A) v).obj (finiteEtaleTateSheaf A m T hA a) ≅
          finiteEtaleTateSheaf A m T' hA a)
    (p : ∀ (T : Scheme.{u}), IsUnit (m : Γ(T, ⊤)) → ∀ a b : ℤ,
        finiteEtaleTateSheaf A m T hA a ⊗ finiteEtaleTateSheaf A m T hA b ≅
          finiteEtaleTateSheaf A m T hA (a + b)) :
        (∀ {T T' : Scheme.{u}} (v : T' ⟶ T) (hT : IsUnit (m : Γ(T, ⊤)))
        (hT' : IsUnit (m : Γ(T', ⊤))) (a b : ℤ),
      ∃ d : ((Etale.derivedTensorRight (ModuleCat.{u + 1} A) T
          ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a)) ⋙
          shiftFunctor _ b) ⋙ (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor ≅
        (Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor ⋙
          Etale.derivedTensorRight (ModuleCat.{u + 1} A) T'
            ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T' hA a)) ⋙
              shiftFunctor _ b),
        ∀ K : Etale.DerivedCategoryModule A T,
          d.app K =
            ((Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.commShiftIso b).app
              (((Etale.derivedTensor (ModuleCat.{u + 1} A) T).obj K).obj
                ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a))) ≪≫
            (shiftFunctor _ b).mapIso
              (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) v K
                ((DerivedCategory.singleFunctor _ 0).obj (finiteEtaleTateSheaf A m T hA a)) ≪≫
              ((Etale.derivedTensor (ModuleCat.{u + 1} A) T').obj
                ((Etale.upperStar (ModuleCat.{u + 1} A) v).leftDerivedFunctor.obj K)).mapIso
                ((Etale.singleFunctorCompLeftDerivedUpperStarIso
                  (ModuleCat.{u + 1} A) v).app (finiteEtaleTateSheaf A m T hA a) ≪≫
                (DerivedCategory.singleFunctor _ 0).mapIso (c v hT hT' a)))) ∧
    (∀ (m' : ℕ), 0 < m' → ∀ (hdiv : m ∣ m')
        (T : Scheme.{u}),
      IsUnit (m' : Γ(T, ⊤)) →
      ∃ (q : T.rootsOfUnitySheaf m' ⟶ T.rootsOfUnitySheaf m)
        (t : ∀ a : ℤ, finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) a ≅
          finiteEtaleTateSheaf A m T hA a),
      q ≫ kernel.ι (m • 𝟙 T.gmSheaf) = (m' / m) • kernel.ι (m' • 𝟙 T.gmSheaf) ∧
      (∀ (W : T.Etaleᵒᵖ) (a : A) (z : (T.rootsOfUnitySheaf m').obj.obj W),
        (t 1).hom.hom.app W (finiteEtaleTateOneGenerator A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) W a z) =
          finiteEtaleTateOneGenerator A m T hA W a (q.hom.app W z)) ∧
      t 0 = Iso.refl _ ∧
      (∀ n : ℕ, t (.ofNat (n + 2)) =
        tensorIso (t (.ofNat (n + 1))) (t 1)) ∧
      (∀ n : ℕ,
        tensorHom (t (.ofNat (n + 1))).hom (t (.negSucc n)).hom ≫
            (ihom.ev (finiteEtaleTateSheaf A m T hA (.ofNat (n + 1)))).app
              (finiteEtaleTateSheaf A m T hA 0) =
          (ihom.ev (finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv))
            (.ofNat (n + 1)))).app
            (finiteEtaleTateSheaf A m' T
          ((CharP.cast_eq_zero_iff A (ringChar A) m').mpr
            (dvd_trans ((CharP.cast_eq_zero_iff A (ringChar A) m).mp hA) hdiv)) 0))) := by
  sorry

end AlgebraicGeometry.Scheme
