/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-!
# The bounded below right derived functor in degree zero

Let `F : C ⥤ D` be a left exact additive functor between abelian categories, where `C` has
enough injectives. On a bounded below complex `K` concentrated in degrees `≥ 0`, the degree-zero
homology of the unit `F(K) ⟶ R⁺F(K)` is an isomorphism: both sides are `F(H⁰(K))`, since `F`
preserves kernels. In particular `H⁰(R⁺F(X[0])) = F(X)`, compatibly with the unit.

We also record how the degree-`n` homology of the image of a levelwise natural transformation
`τ : Φ ⟶ Ψ` in `DerivedCategory.Plus D` is computed on complexes.

## Main statements

- `CategoryTheory.Functor.isIso_homologyMap_zero_mapHomologicalComplex_map`: a left exact
  functor preserves the property that a morphism of complexes concentrated in degrees `≥ 0`
  induces an isomorphism on `H⁰`.
- `CategoryTheory.Functor.isIso_homologyFunctor_zero_map_rightDerivedFunctorPlusUnit_app`:
  `H⁰` of the unit `F(K) ⟶ R⁺F(K)` is an isomorphism for `K` concentrated in degrees `≥ 0`.
- `CategoryTheory.NatTrans.homologyFunctorMapQhMapArrowIso`: the degree-`n` homology of
  `NatTrans.mapHomotopyCategoryPlus τ` at a complex `K` is the map induced by `τ` on `Hⁿ(K)`.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]

namespace Functor

/-- A left exact functor `F` preserves the property that a morphism `φ` of cochain complexes
concentrated in degrees `≥ 0` induces an isomorphism on `H⁰`: on such complexes `H⁰` is the
kernel of the first differential, which `F` preserves. -/
lemma isIso_homologyMap_zero_mapHomologicalComplex_map (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] {K L : CochainComplex C ℤ} (φ : K ⟶ L)
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] [IsIso (HomologicalComplex.homologyMap φ 0)] :
    IsIso (HomologicalComplex.homologyMap ((F.mapHomologicalComplex _).map φ) 0) := by
  have hK : (K.sc 0).f = 0 :=
    (K.isZero_of_isStrictlyGE 0 ((ComplexShape.up ℤ).prev 0) (by simp)).eq_of_src _ _
  have hL : (L.sc 0).f = 0 :=
    (L.isZero_of_isStrictlyGE 0 ((ComplexShape.up ℤ).prev 0) (by simp)).eq_of_src _ _
  have := F.preservesLeftHomology_of_zero_f _ hK
  have := F.preservesLeftHomology_of_zero_f _ hL
  have e := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor C _ 0).map φ) F
  have : IsIso (ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor C _ 0).map φ)) :=
    inferInstanceAs (IsIso (HomologicalComplex.homologyMap φ 0))
  have : IsIso (ShortComplex.homologyMap (F.mapShortComplex.map
      ((HomologicalComplex.shortComplexFunctor C _ 0).map φ))) := by
    rw [← (Iso.comp_inv_eq _).2 e.symm]
    infer_instance
  exact this

variable [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]

/-- For a left exact functor `F` and a bounded below complex `K` concentrated in degrees `≥ 0`,
the degree-zero homology of the unit `F(K) ⟶ R⁺F(K)` is an isomorphism. Choose a
quasi-isomorphism `i : K ⟶ T` to a complex of injectives concentrated in degrees `≥ 0`. The unit
at `T` and `R⁺F(i)` are isomorphisms, and `H⁰(F(i))` is an isomorphism by
`Functor.isIso_homologyMap_zero_mapHomologicalComplex_map`, so the naturality square of the
unit along `i` gives the claim. -/
lemma isIso_homologyFunctor_zero_map_rightDerivedFunctorPlusUnit_app (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] (K : CochainComplex.Plus C) [K.obj.IsStrictlyGE 0] :
    IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj K))) := by
  obtain ⟨T, _, i, hi⟩ := CochainComplex.Plus.exists_quasiIso_injective K 0
  let T' := (InjectiveObject.ι C).mapCochainComplexPlus.obj T
  have : QuasiIso i.hom := hi
  have : T'.obj.IsStrictlyGE 0 :=
    (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ _ _).2 ‹_›
  have h₂ : IsIso (F.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i))) := by
    have : IsIso (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i)) :=
      Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C) _
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hi)
    infer_instance
  have h₃ : IsIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient C).obj T')) := inferInstance
  have hFi : IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex _).map i.hom) 0) :=
    F.isIso_homologyMap_zero_mapHomologicalComplex_map i.hom
  have h₁ : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (DerivedCategory.Plus.Qh.map
        (F.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient C).map i)))) := by
    have e := DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality
      (F.mapCochainComplexPlus.map i) 0
    have : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
        (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map i))) := by
      rw [(Iso.eq_comp_inv _).2 e]
      have : IsIso (HomologicalComplex.homologyMap (F.mapCochainComplexPlus.map i).hom 0) := hFi
      infer_instance
    exact this
  have hnat := F.rightDerivedFunctorPlusUnit.naturality ((HomotopyCategory.Plus.quotient C).map i)
  dsimp only [Functor.comp_map] at hnat
  have : IsIso ((DerivedCategory.Plus.homologyFunctor D 0).map
      (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj K) ≫
      F.rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i)))) := by
    rw [← hnat, Functor.map_comp]
    infer_instance
  rw [Functor.map_comp] at this
  exact IsIso.of_isIso_comp_right _ ((DerivedCategory.Plus.homologyFunctor D 0).map
    (F.rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient C).map i))))

end Functor

namespace NatTrans

/-- At the image of a bounded below complex `K`, the transformation
`NatTrans.mapHomotopyCategoryPlus τ` is the image of the levelwise transformation `τ` on `K`. -/
lemma mapHomotopyCategoryPlus_app_quotient_obj {Φ Ψ : C ⥤ D} [Φ.Additive] [Ψ.Additive]
    (τ : Φ ⟶ Ψ) (K : CochainComplex.Plus C) :
    (NatTrans.mapHomotopyCategoryPlus τ).app ((HomotopyCategory.Plus.quotient C).obj K) =
      (HomotopyCategory.Plus.quotient D).map (ObjectProperty.homMk
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K.obj) :
          Φ.mapCochainComplexPlus.obj K ⟶ Ψ.mapCochainComplexPlus.obj K) := by
  apply (HomotopyCategory.Plus.ι D).map_injective
  rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  rfl

variable [HasDerivedCategory D]

/-- The degree-`n` homology of the image of `NatTrans.mapHomotopyCategoryPlus τ` in
`DerivedCategory.Plus D` at a bounded below complex `K` is, as an arrow, the map induced by the
levelwise transformation `τ` on `Hⁿ(K)`. -/
noncomputable def homologyFunctorMapQhMapArrowIso {Φ Ψ : C ⥤ D} [Φ.Additive] [Ψ.Additive]
    (τ : Φ ⟶ Ψ) (K : CochainComplex.Plus C) (n : ℤ) :
    Arrow.mk ((DerivedCategory.Plus.homologyFunctor D n).map (DerivedCategory.Plus.Qh.map
      ((NatTrans.mapHomotopyCategoryPlus τ).app ((HomotopyCategory.Plus.quotient C).obj K)))) ≅
      Arrow.mk (HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K.obj) n) := by
  rw [NatTrans.mapHomotopyCategoryPlus_app_quotient_obj]
  exact Arrow.isoMk (DerivedCategory.Plus.homologyFunctorObjQIso (Φ.mapCochainComplexPlus.obj K) n)
    (DerivedCategory.Plus.homologyFunctorObjQIso (Ψ.mapCochainComplexPlus.obj K) n)
    (DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality (ObjectProperty.homMk
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K.obj) :
          Φ.mapCochainComplexPlus.obj K ⟶ Ψ.mapCochainComplexPlus.obj K) n).symm

end NatTrans

end CategoryTheory
