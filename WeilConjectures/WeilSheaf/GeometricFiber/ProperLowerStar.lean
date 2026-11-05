/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.GeometricFiber.Forget
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationLowerStar
public import WeilConjectures.WeilSheaf.ProperLowerStarAdjoint
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointCounitForget
public import WeilConjectures.CategoryTheory.Adjunction.MateIsIsoOfCounitPasting
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import WeilConjectures.SixFunctors.ProEtale.Adic.ProperLowerStarCondensedAdjoint

/-!
# Forgetting the Weil structure commutes with the proper direct image

Let `g : Z ⟶ Y` be a proper morphism of separated `k₀`-schemes of finite type and `ḡ` its base
change to the geometric fibres. Forgetting the Weil structures (`For`,
`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctor`) commutes with the
direct images: `For ∘ Rg_* ≅ Rḡ_* ∘ For`
(`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorLowerStarIso`), the
inverse of the derived base change map of the condensed realization. Its mate
`For ∘ Rg^! ⟶ Rḡ^! ∘ For` is invertible for all right adjoints `Rg^!`, `Rḡ^!`
(`AlgebraicGeometry.WeilComplex.isIso_mateEquiv_geometricFiberBoundedConstructibleFunctorLowerStarIso`).

## Proof of the invertibility of the mate

Forgetting the Weil structures factors through the bounded constructible complexes of `ℓ`-adic
sheaves, `For = Φ ∘ U`, `Φ` the comparison of the two models. Along `U`, the counit of the right
adjoint `Rg^!` of Weil complexes lies over the counit of the right adjoint of the `ℓ`-adic `Rḡ_*`
(`CategoryTheory.Endofunctor.IsoAlgebra.exists_forget_map_counit_eq`), and `Φ` is an equivalence,
so the mate is invertible (`CategoryTheory.isIso_mateEquiv_app_of_counit_of_pasting`). The
derived base change map of the condensed realization is, through `For = Φ ∘ U`, the pasting of
the comparison of `U` with the direct images and of the comparison of `Φ` with the direct images
(`AlgebraicGeometry.ProEtaleWeilSheaf.mateEquiv_derivedCondensedRealizationUpperStarIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))] [IsProper g]

/-- **Forgetting the Weil structure commutes with the proper direct image**:
`For ∘ Rḡ_* ≅ Rg_* ∘ For`, the inverse of the derived base change map
`Rg_* ⋙ D(N_Y) ⟶ D(N_Z) ⋙ Rḡ_*` of the condensed realization (the mate of
`AlgebraicGeometry.ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso`), restricted to
Weil complexes. -/
noncomputable def geometricFiberBoundedConstructibleFunctorLowerStarIso :
    geometricFiberBoundedConstructibleFunctor k₀ l Z ⋙
        CondensedRing.boundedConstructibleLowerStar l (geometricFiberHom (k₀ := k₀) g) ≅
      derivedLowerStar g ⋙ geometricFiberBoundedConstructibleFunctor k₀ l Y :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (CondensedRing.boundedConstructibleLowerStarCompatibility l
          (geometricFiberHom (k₀ := k₀) g)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l Z) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (objectProperty k₀ l Z).ι
        (asIso (mateEquiv (ProEtaleWeilSheaf.derivedUpperStarLowerStarAdjunction k₀ l g)
          (CondensedRing.derivedUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l)
            (Scheme.Hom.geometricFiberMap g (comp_over g (Spec (CommRingCat.of k₀)))))
          (ProEtaleWeilSheaf.derivedCondensedRealizationUpperStarIso k₀ l g).hom).natTrans).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((objectProperty k₀ l Z).liftFullSubcategoryCompιIso (objectProperty k₀ l Y)
          (ProEtaleWeilSheaf.lowerStar k₀ l g).rightDerivedFunctor
          (objectProperty_rightDerivedLowerStar g)).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (derivedLowerStar g)
        (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l Y).symm ≪≫
      (Functor.associator _ _ _).symm)

end AlgebraicGeometry.WeilComplex
