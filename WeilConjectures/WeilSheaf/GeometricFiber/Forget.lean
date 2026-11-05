/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.NativeCompactProjectionFormula
public import WeilConjectures.WeilSheaf.Native.NativeCondensedRealizationDerivedTensor
public import WeilConjectures.WeilSheaf.UpperShriekGeometric

/-!
# The underlying bounded constructible complex of a Weil complex

For a separated `k₀`-scheme of finite type `X`, forgetting the Weil structure of a Weil complex
on `X` and passing to the condensed model gives a functor `For` from Weil complexes on `X` to
bounded constructible complexes of `ℚ̄_ℓ`-modules on the geometric fibre `X̄`
(`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctor`). It is the derived
condensed realization of pro-étale Weil sheaves
(`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorCompιIso`), and it
carries the native tensor product of Weil complexes to the tensor product of bounded
constructible complexes
(`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleFunctorTensorIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.WeilComplex

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section GeometricFiberMap

variable {k : Type u} [Field k] {X₀ Y₀ : Scheme.{u}} {s : X₀ ⟶ Spec (.of k)}
  {t : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ t = s)

/-- The base change to `k̄` of an open immersion is an open immersion. -/
instance [IsOpenImmersion φ] : IsOpenImmersion (Scheme.Hom.geometricFiberMap φ h) :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsOpenImmersion) φ h ‹_›

/-- The base change to `k̄` of a proper morphism is proper. -/
instance [IsProper φ] : IsProper (Scheme.Hom.geometricFiberMap φ h) :=
  Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) φ h ‹_›

end GeometricFiberMap

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

open scoped CategoryTheory.Obj in
/-- The underlying bounded constructible complex on the geometric fibre `X̄`, in the condensed
model, of a Weil complex on `X`, as a functor
(`AlgebraicGeometry.WeilComplex.geometricFiberBoundedConstructibleObj`). -/
noncomputable def geometricFiberBoundedConstructibleFunctor :
    WeilComplex k₀ l X ⥤ BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left) :=
  ObjectProperty.lift _ (forget ⋙ (adicSheafDerivedEquivCondensedMod l _).functor)
    (fun L ↦ (geometricFiberBoundedConstructibleObj L).property)

/-- The underlying complex of a Weil complex is its derived condensed realization. -/
noncomputable def geometricFiberBoundedConstructibleFunctorCompιIso :
    geometricFiberBoundedConstructibleFunctor k₀ l X ⋙ ObjectProperty.ι _ ≅
      (objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.derivedCondensedRealization k₀ l X :=
  Functor.isoWhiskerLeft (objectProperty k₀ l X).ι
    (Functor.mapDerivedCategoryCompIso _ _).symm

set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
set_option backward.isDefEq.respectTransparency false in
-- `Mod.monoidalClosed` needs `IsCommMonObj (condensedRingObj _ _)` up to instance unfolding
open scoped CategoryTheory.Obj in
/-- The tensor product of bounded constructible complexes is that of the ambient derived
category. -/
noncomputable def boundedConstructibleιTensorIso :
    (ObjectProperty.ι (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left))).prod
      (ObjectProperty.ι (boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left))) ⋙
        Functor.uncurry.obj (curriedTensor _) ≅
      tensor (BoundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
        (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure).left)) ⋙
        ObjectProperty.ι _ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {A B} f ↦ by
    dsimp
    simp only [Category.comp_id, Category.id_comp, MonoidalCategory.tensorHom_def])

set_option synthInstance.maxHeartbeats 400000 in
-- the monoidal structure of the derived category of condensed modules is found slowly
set_option backward.isDefEq.respectTransparency false in
-- `Mod.monoidalClosed` needs `IsCommMonObj (condensedRingObj _ _)` up to instance unfolding
/-- Forgetting the Weil structure carries the native tensor product of Weil complexes to the
tensor product of bounded constructible complexes: it is the comparison of the derived condensed
realization with the tensor products
(`AlgebraicGeometry.ProEtaleWeilSheaf.condensedRealizationTensor`). -/
noncomputable def geometricFiberBoundedConstructibleFunctorTensorIso :
    nativeConstructibleTensor k₀ l X ⋙ geometricFiberBoundedConstructibleFunctor k₀ l X ≅
      (geometricFiberBoundedConstructibleFunctor k₀ l X).prod
        (geometricFiberBoundedConstructibleFunctor k₀ l X) ⋙ tensor _ :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X) ≪≫
      Functor.isoWhiskerLeft ((objectProperty k₀ l X).ι.prod (objectProperty k₀ l X).ι)
        (ProEtaleWeilSheaf.condensedRealizationTensor k₀ l X) ≪≫
      Iso.refl (((objectProperty k₀ l X).ι ⋙
          ProEtaleWeilSheaf.derivedCondensedRealization k₀ l X).prod
        ((objectProperty k₀ l X).ι ⋙ ProEtaleWeilSheaf.derivedCondensedRealization k₀ l X) ⋙
          Functor.uncurry.obj (curriedTensor _)) ≪≫
      Functor.isoWhiskerRight
        (NatIso.prod (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X).symm
          (geometricFiberBoundedConstructibleFunctorCompιIso k₀ l X).symm) _ ≪≫
      Iso.refl ((geometricFiberBoundedConstructibleFunctor k₀ l X).prod
        (geometricFiberBoundedConstructibleFunctor k₀ l X) ⋙
          (ObjectProperty.ι _).prod (ObjectProperty.ι _) ⋙ Functor.uncurry.obj (curriedTensor _)) ≪≫
      Functor.isoWhiskerLeft ((geometricFiberBoundedConstructibleFunctor k₀ l X).prod
        (geometricFiberBoundedConstructibleFunctor k₀ l X))
        (boundedConstructibleιTensorIso k₀ l X) ≪≫
      (Functor.associator _ _ _).symm)


end AlgebraicGeometry.WeilComplex

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated φ] [LocallyOfFiniteType φ]
  [QuasiCompact φ]

instance [IsOpenImmersion φ] : IsOpenImmersion (geometricFiberHom (k₀ := k₀) φ).left :=
  inferInstanceAs (IsOpenImmersion (Scheme.Hom.geometricFiberMap φ (comp_over φ _)))

instance [IsProper φ] : IsProper (geometricFiberHom (k₀ := k₀) φ).left :=
  inferInstanceAs (IsProper (Scheme.Hom.geometricFiberMap φ (comp_over φ _)))

end AlgebraicGeometry.WeilComplex
