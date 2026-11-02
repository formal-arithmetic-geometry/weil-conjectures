/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization

/-! # Scalar comparison and the open-extension compositor

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-prop-scalar-six/
det-prop-scalar-six-compact-support.proof.md, Composition paragraph
(blueprint: lem-sfb-scalar-open-compositor-coherence).

The open compositor is written out as the `Adjunction.leftAdjointCompIso` of the three
derived open-immersion adjunctions and the inverse of the canonical pullback compositor
`scalarSixPullComp` of det-prop-scalar-six-pullback. This is the body of `sfbScalarOpenComp`
in `Sheaf.SixFunctors.ScalarCompositeModelPasting` (whose `RootCoordinateFace.upperComp` has
the same definition as `scalarSixPullComp`). That module is not imported: its node cites this
lemma as a proof dependency, so the import would close an import cycle at stage 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem scalarComposition
    {A B C D E F : Type*}
    [Category* A] [Category* B] [Category* C]
    [Category* D] [Category* E] [Category* F]
    {La : A ⥤ D} {Ra : D ⥤ A} {Lb : B ⥤ E} {Rb : E ⥤ B}
    {Lc : C ⥤ F} {Rc : F ⥤ C}
    {H : A ⥤ B} {S : B ⥤ A} {I : B ⥤ C} {T : C ⥤ B}
    {J : A ⥤ C} {U : C ⥤ A}
    {P : D ⥤ E} {Rp : E ⥤ D} {Q : E ⥤ F} {Rq : F ⥤ E}
    {R : D ⥤ F} {Rr : F ⥤ D}
    (a : La ⊣ Ra) (b : Lb ⊣ Rb) (c : Lc ⊣ Rc)
    (h : H ⊣ S) (i : I ⊣ T) (j : J ⊣ U)
    (p : P ⊣ Rp) (q : Q ⊣ Rq) (r : R ⊣ Rr)
    (α01 : Rp ⋙ Ra ≅ Rb ⋙ S) (α12 : Rq ⋙ Rb ≅ Rc ⋙ T)
    (α02 : Rr ⋙ Ra ≅ Rc ⋙ U) (β : U ≅ T ⋙ S) (γ : Rq ⋙ Rp ≅ Rr)
    (μ : J ≅ H ⋙ I) (κ : R ≅ P ⋙ Q)
    (hμ : conjugateIsoEquiv (h.comp i) j μ = β.symm)
    (hκ : conjugateIsoEquiv (p.comp q) r κ = γ)
    (hr : α02 = Functor.isoWhiskerRight γ.symm Ra ≪≫
      Functor.associator Rq Rp Ra ≪≫ Functor.isoWhiskerLeft Rq α01 ≪≫
      (Functor.associator Rq Rb S).symm ≪≫ Functor.isoWhiskerRight α12 S ≪≫
      Functor.associator Rc T S ≪≫ Functor.isoWhiskerLeft Rc β.symm)
    (K : A) :
    Lc.map (μ.inv.app K) ≫
        ((conjugateIsoEquiv (a.comp r) (j.comp c)).symm α02).hom.app K =
      ((conjugateIsoEquiv (b.comp q) (i.comp c)).symm α12).hom.app (H.obj K) ≫
        Q.map (((conjugateIsoEquiv (a.comp p) (h.comp b)).symm α01).hom.app K) ≫
          κ.inv.app (La.obj K) := by
  let t01 := (conjugateIsoEquiv (a.comp p) (h.comp b)).symm α01
  let t12 := (conjugateIsoEquiv (b.comp q) (i.comp c)).symm α12
  let t02 := (conjugateIsoEquiv (a.comp r) (j.comp c)).symm α02
  have he := adjunctionSquareComposition a b c h i j p q r
    α01 α12 α02 β γ t01.symm t12.symm t02.symm μ κ.symm
    (by simp only [t01, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply])
    (by simp only [t12, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply])
    (by simp only [t02, conjugateIsoEquiv_iso_symm, Equiv.apply_symm_apply]) hμ
    (by rw [conjugateIsoEquiv_iso_symm, hκ]) hr
  have he' := congrArg (fun z ↦ z.inv.app K) he
  simp only [Iso.trans_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Iso.symm_inv,
    Category.id_comp, Category.comp_id] at he'
  have hh := congrArg (fun z ↦ z ≫ κ.inv.app (La.obj K)) he'.symm
  simpa only [Functor.comp_obj, Category.assoc, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app_assoc, Category.comp_id] using hh

set_option maxHeartbeats 800000 in
-- Keep the concrete derived square and the composite adjunctions folded.
end AlgebraicGeometry.ProEtale.CondensedRing
