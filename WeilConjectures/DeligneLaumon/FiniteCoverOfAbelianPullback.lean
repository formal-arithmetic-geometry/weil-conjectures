/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseQlbarRepresentations
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
import WeilConjectures.AlgebraicGeometry.GaloisCategories
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent
import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison
import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback

/-! # Finite covers representing the inverse image of a finite module sheaf -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia

/-- An abelian inverse-image comparison for finite module sheaves gives a
representative pulled back from a finite étale cover on the original scheme.
Source: Stacks Tags 03RV and 03Q1; normalized finite reductions in
`thm-lisse-qlbar-representations`.
(blueprint: lem-dl-a1-finite-cover-of-abelian-pullback).

Proof: forget the abelian comparison to sets and commute forgetting with inverse
image. Represent the finite locally constant set sheaf on the original scheme by
a finite étale cover. Inverse image of a representable is represented by its base
change. The Yoneda comparison in the given finite correspondence identifies that
representable with the chosen image of the pulled-back cover. -/
theorem finite_cover_of_abelian_pullback
    {U C : Scheme.{u}} (j : U ⟶ C)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (G : ProfiniteGrp.{u}) [∀ P, MulAction G ((FiniteEtale.fiber b).obj P)]
    (d : GaloisLisseFiniteCorrespondence b G)
    (A : Type (u + 1)) [Ring A]
    (FC : Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} A))
    (FU : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hFC : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf A FC))
    (e : LisseQlbar.underlyingAb A FU ≅
      (Etale.upperStar Ab.{u + 1} j).obj (LisseQlbar.underlyingAb A FC)) :
    ∃ P : C.FiniteEtale, Nonempty
      ((d.Φ.functor.obj ((FiniteEtale.pullback j).obj P)).obj ≅
        galoisUnderlyingSetSheaf A FU) := by
  classical
  obtain ⟨Φ, ⟨α⟩, _, _⟩ := exists_finiteEtale_flc_equivalence_sheaf C
  let V : C.FLC := ⟨galoisUnderlyingSetSheaf A FC, hFC⟩
  let P := Φ.inverse.obj V
  let eC : C.smallEtaleTopology.uliftYoneda.obj P.obj ≅
      galoisUnderlyingSetSheaf A FC :=
    (α.app P).symm ≪≫ (ObjectProperty.ι _).mapIso (Φ.counitIso.app V)
  obtain ⟨β⟩ := AlgebraicGeometry.nonempty_inverseImage_representable_iso.{u, u + 1} j
    (etaleSetPullback j)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous j.Etale
      (Type (u + 1)) C.smallEtaleTopology U.smallEtaleTopology)
  obtain ⟨δ⟩ := d.yonedaComparison
  let : PreservesFilteredColimitsOfSize.{u, u + 1}
      (CategoryTheory.forget Ab.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  let : (CategoryTheory.forget Ab.{u + 1}).PreservesLeftKanExtensions j.Etale.op :=
    fun F ↦ by
      let : (CategoryTheory.forget Ab.{u + 1}).PreservesPointwiseLeftKanExtension
          F j.Etale.op := fun _ ↦ by infer_instance
      infer_instance
  let ε := (sheafPullbackForgetIso C.smallEtaleTopology U.smallEtaleTopology j.Etale
    (CategoryTheory.forget Ab.{u + 1})).app (LisseQlbar.underlyingAb A FC)
  let ζ := (sheafCompose U.smallEtaleTopology
    (CategoryTheory.forget Ab.{u + 1})).mapIso e
  refine ⟨P, ⟨?_⟩⟩
  exact δ.app ((FiniteEtale.pullback j).obj P) ≪≫ (β.app P.obj).symm ≪≫
    (etaleSetPullback j).mapIso eC ≪≫ ε.symm ≪≫ ζ.symm

end AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia
