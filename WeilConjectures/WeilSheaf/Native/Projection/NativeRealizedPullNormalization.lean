/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.NativePullTensorNormalization
public import WeilConjectures.WeilSheaf.Native.Projection.ModelSquareCancellation
import WeilConjectures.Tactic.ExactModProofs

/-! # Realization of the normalized native pullback tensor model -/

@[expose] public noncomputable section

set_option Elab.async false
attribute [local instance 0] ModuleCat.isGrothendieckAbelian_of_commRing

universe u
open CategoryTheory MonoidalCategory Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtaleWeilSheaf
open ProEtale

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]

/-- Map the native restriction normalization through an exact realization functor,
keeping both functors abstract during kernel checking. -/
lemma projection_realized_nativePullTensor_normalization
    {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
    (L : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z)
    [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (V : ProEtaleWeilSheaf k₀ l Z ⥤ B)
    [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (hL : ∀ P, NativeIsKFlat k₀ l Y P →
      NativeIsKFlat k₀ l Z ((L.mapHomologicalComplex (.up ℤ)).obj P))
    (t : Functor.uncurry.obj (nativeTensorTotal k₀ l Y) ⋙
        L.mapHomologicalComplex (.up ℤ) ≅
      (L.mapHomologicalComplex (.up ℤ)).prod (L.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (nativeTensorTotal k₀ l Z))
    (rho : nativeDerivedTensor k₀ l Y ⋙ L.mapDerivedCategory ≅
      L.mapDerivedCategory.prod L.mapDerivedCategory ⋙ nativeDerivedTensor k₀ l Z)
    (hn : ProjectionRestrictionTensorNormalization k₀ l L hL t rho)
    (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Y) ℤ)
    (hP : NativeIsKFlat k₀ l Y P) (hT : NativeIsKFlat k₀ l Y T)
    (hLP : NativeIsKFlat k₀ l Z ((L.mapHomologicalComplex (.up ℤ)).obj P))
    (hLT : NativeIsKFlat k₀ l Z ((L.mapHomologicalComplex (.up ℤ)).obj T)) :
    V.mapDerivedCategory.map (rho.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T)) ≫
        V.mapDerivedCategory.map ((nativeDerivedTensor k₀ l Z).map
          (Prod.mkHom (L.mapDerivedCategoryFactors.hom.app P)
            (L.mapDerivedCategoryFactors.hom.app T))) ≫
        V.mapDerivedCategory.map (nativeOpenTensorModel k₀ l Z
          ((L.mapHomologicalComplex (.up ℤ)).obj P)
          ((L.mapHomologicalComplex (.up ℤ)).obj T) hLP hLT).hom =
      V.mapDerivedCategory.map
          (L.mapDerivedCategory.map (nativeOpenTensorModel k₀ l Y P T hP hT).hom) ≫
        V.mapDerivedCategory.map
          (L.mapDerivedCategoryFactors.hom.app (((nativeTensorTotal k₀ l Y).obj P).obj T)) ≫
        V.mapDerivedCategory.map (DerivedCategory.Q.map
          (NativeRestrictionDescentProof.totalFamily L (nativeTensorTotal k₀ l Z)
            (nativeTensorTotal k₀ l Y) t P T).hom) := by
  have h := V.mapDerivedCategory.projection_map_comp3_eq (hn P T hP hT)
  with_reducible exact_mod_proofs h

end AlgebraicGeometry.ProEtaleWeilSheaf
