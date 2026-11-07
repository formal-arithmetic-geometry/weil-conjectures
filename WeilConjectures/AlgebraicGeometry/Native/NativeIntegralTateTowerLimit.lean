/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists

import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTateFiniteRepresentation
import WeilConjectures.AlgebraicGeometry.Limits.AffineOverLimitProperties
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Sites.PreservesLimits
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat

set_option linter.privateModule false

/-! # Inverse image preserves the native integral Tate tower limit

Source: the Integral twist paragraph of the blueprint proof of
`sk-prop-sfb-cartesian-coefficients-twists`.
(blueprint: lem-pur-native-integral-tate-tower-limit).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace AlgebraicGeometry.ProEtale

private theorem lift_representable_diagram
    {C B I : Type*} [Category C] [Category B] [Category I]
    (F : C ⥤ B) [F.Full] [F.Faithful] (A : I ⥤ B)
    (V : I → C) (e : ∀ i, F.obj (V i) ≅ A.obj i) :
    ∃ D : I ⥤ C, (∀ i, D.obj i = V i) ∧ Nonempty (D ⋙ F ≅ A) := by
  let D : I ⥤ C :=
    { obj := V
      map {i j} g := F.preimage ((e i).hom ≫ A.map g ≫ (e j).inv)
      map_id i := by
        apply F.map_injective
        simp
      map_comp g h := by
        apply F.map_injective
        simp [Category.assoc] }
  refine ⟨D, fun _ ↦ rfl, ⟨NatIso.ofComponents e ?_⟩⟩
  intro i j g
  change F.map (F.preimage _) ≫ (e j).hom = _
  simp [Category.assoc]

private theorem finiteEtale_geometric_limit
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Y.ProEt)
    (hfin : ∀ i, IsFinite (D.obj i).hom) (het : ∀ i, Etale (D.obj i).hom) :
    HasLimit D ∧ PreservesLimit D (Scheme.proEtaleBaseChange f) := by
  let A := D ⋙ Scheme.ProEt.forget Y ⋙ Over.forget Y
  let p (i : I) : A.obj i ⟶ Y := (D.obj i).hom
  have hp {i j : I} (g : i ⟶ j) : A.map g ≫ p j = p i := (D.map g).w
  let (i : I) : IsFinite (p i) := hfin i
  let (i : I) : Etale (p i) := het i
  let (i : I) : IsAffineHom (p i) := inferInstance
  let cA := Scheme.AffineOverLimit.limitCone A p hp
  let hcA := Scheme.AffineOverLimit.isLimitLimitCone A p hp
  let q := Scheme.AffineOverLimit.limitHom A p hp
  have hq (i : I) : cA.π.app i ≫ p i = q := Scheme.AffineOverLimit.π_p A p hp i
  let : WeaklyEtale q := Scheme.weaklyEtale_of_isLimit A hcA p hp q hq
  let c : Cone D :=
    { pt := Scheme.ProEt.mk q
      π :=
        { app i := MorphismProperty.Over.homMk (cA.π.app i) (hq i)
          naturality i j g := by
            apply MorphismProperty.Over.Hom.ext
            change 𝟙 _ ≫ cA.π.app j = cA.π.app i ≫ A.map g
            exact (Category.id_comp _).trans (cA.w g).symm } }
  have hcOver : IsLimit ((Scheme.ProEt.forget Y).mapCone c) := by
    apply isLimitOfReflects (Over.forget Y)
    exact hcA
  have hc : IsLimit c := isLimitOfReflects (Scheme.ProEt.forget Y) hcOver
  have hfc : IsLimit ((Scheme.proEtaleBaseChange f).mapCone c) := by
    apply isLimitOfReflects (Scheme.ProEt.forget X)
    exact isLimitOfPreserves (Over.pullback f) hcOver
  exact ⟨⟨⟨⟨c, hc⟩⟩⟩, preservesLimit_of_preserves_limit_cone hc hfc⟩

private noncomputable def representableInverseImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.proEtaleBaseChange f ⋙ (Scheme.ProEt.topology X).uliftYoneda.{u + 1} ≅
      (Scheme.ProEt.topology Y).uliftYoneda.{u + 1} ⋙
        Scheme.proEtaleSheafInverseImage f (Type (u + 1)) := by
  let e := Presheaf.compULiftYonedaIsoULiftYonedaCompLan.{u + 1}
    (Scheme.proEtaleBaseChange f)
  exact Functor.isoWhiskerLeft
    (Scheme.proEtaleBaseChange f ⋙ (Scheme.ProEt.topology X).uliftYoneda.{u + 1})
    (sheafificationNatIso (Scheme.ProEt.topology X) (Type (u + 1))) ≪≫
    Functor.isoWhiskerRight e
      (presheafToSheaf (Scheme.ProEt.topology X) (Type (u + 1)))

private noncomputable def abelianForgetInverseImageIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    upperStar AddCommGrpCat.{u + 1} f ⋙
      sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1}) ≅
    sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1}) ⋙
      Scheme.proEtaleSheafInverseImage f (Type (u + 1)) := by
  let : RepresentablyFlat (Scheme.proEtaleBaseChange f) := flat_of_preservesFiniteLimits _
  let : (forget AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions
      (Scheme.proEtaleBaseChange f).op := by
    intro P
    let : PreservesFilteredColimitsOfSize.{u, u + 1}
        (forget AddCommGrpCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
    let : ∀ V, Functor.PreservesPointwiseLeftKanExtensionAt
        (forget AddCommGrpCat.{u + 1}) P (Scheme.proEtaleBaseChange f).op V := by
      intro V
      infer_instance
    infer_instance
  exact sheafPullbackForgetIso (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.proEtaleBaseChange f) (forget AddCommGrpCat.{u + 1})

end AlgebraicGeometry.ProEtale
