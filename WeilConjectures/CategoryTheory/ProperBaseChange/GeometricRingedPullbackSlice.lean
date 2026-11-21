/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.Ringed.Sheaf.RingedSheafSliceAdjunction
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.ProperBaseChange.OrdinaryRingedToposPullback
public import WeilConjectures.CategoryTheory.Ringed.RingedPresentationData
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import WeilConjectures.CategoryTheory.ProperBaseChange.GeometricRingedPullbackSliceData
import WeilConjectures.Algebra.Homology.ProperBaseChange.GeometricRingedPullbackSliceModules
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Ordinary ringed pullback and localization at a sheaf

Source: Stacks Project, Sites, Tag 04H1; Modules on Sites, Tags 04IF, 04IE,
03D6 (2), 03EL and 03EK.

## Main definitions

- `CategoryTheory.geometricSliceProductOver`: the product in the sheaf slice.
- `CategoryTheory.geometricSliceProductFibreIso`: its canonical fibre identification.
- `CategoryTheory.geometricSliceProductPostIso`: the finite-product comparison in slices.
- `CategoryTheory.geometricSliceSetComparison`: the specified restriction comparison.

## Main statements

- `SheafOfModules.geometric_ringed_pullback_slice`: ringed localization and its
  natural, linear ordinary-pullback comparison, normalized on local pure tensors.

The sites are arbitrary small sites. The slice morphism is specified through the
existing fibre equivalences, and its structural map through the inverse-image square.
Ordinary pullbacks use the existing sheafified tensor construction. The final equation
fixes the comparison on local pure tensors, including the target-ring scalar factor.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u uE vE uE' vE'

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.MonoidalCategory
open scoped ChangeOfRings

namespace CategoryTheory

/-- The product over a sheaf used in the slice inverse-image comparison.
Source: Stacks Project, Sites, Tag 04H1. -/
def geometricSliceProductOver {E : Type uE} [Category.{vE} E] [CartesianMonoidalCategory E]
    (A : E) : E ⥤ Over A where
  obj H := Over.mk (CartesianMonoidalCategory.fst A H)
  map h := Over.homMk (𝟙 A ⊗ₘ h) (by simp)
  map_id H := by apply Over.OverMorphism.ext; simp
  map_comp h k := by apply Over.OverMorphism.ext; simp

/-- The fibre of `A × H -> A` is canonically the sectionwise restriction of H.
Source: Stacks Project, Sites, Tag 0791; Modules on Sites, Tag 04IE. -/
noncomputable def geometricSliceProductFibreIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (A : Sheaf J (Type u))
    (s : RingedSheafSliceAdjunctionData R A) :
    geometricSliceProductOver A ⋙ s.fibreEquivalence.inverse ≅ elementSheafPullback A := by
  apply Functor.fullyFaithfulCancelRight (sheafToPresheaf (elementTopology A) (Type u))
  refine Functor.isoWhiskerLeft (geometricSliceProductOver A) s.fibre_iso ≪≫ ?_
  refine NatIso.ofComponents (fun H ↦ NatIso.ofComponents (fun U ↦ ?_) ?_) ?_
  · exact Equiv.toIso
      { toFun := fun x ↦ x.val.2
        invFun := fun x ↦ ⟨(U.unop.unop.2, x), rfl⟩
        left_inv := fun x ↦ Subtype.ext (Prod.ext x.property.symm rfl)
        right_inv := fun x ↦ rfl }
  · intro U V h
    ext x
    rfl
  · intro H H' h
    ext U x
    rfl

/-- Finite-product preservation gives the slice product comparison.
Its two components are the images of the two projections.
Source: Stacks Project, Sites, Tag 04H1. -/
noncomputable def geometricSliceProductPostIso
    {E : Type uE} {E' : Type uE'} [Category.{vE} E] [Category.{vE'} E']
    [CartesianMonoidalCategory E] [CartesianMonoidalCategory E']
    (L : E ⥤ E') [PreservesFiniteLimits L] (A : E) :
    geometricSliceProductOver A ⋙ Over.post L ≅
      L ⋙ geometricSliceProductOver (L.obj A) := by
  refine NatIso.ofComponents (fun H ↦ Over.isoMk
    (CartesianMonoidalCategory.prodComparisonIso L A H) ?_) ?_
  · exact CartesianMonoidalCategory.prodComparison_fst L A H
  · intro H H' h
    apply Over.OverMorphism.ext
    change L.map (𝟙 A ⊗ₘ h) ≫
      (CartesianMonoidalCategory.prodComparisonIso L A H').hom =
      (CartesianMonoidalCategory.prodComparisonIso L A H).hom ≫ (𝟙 (L.obj A) ⊗ₘ L.map h)
    simpa only [Functor.map_id, CartesianMonoidalCategory.prodComparisonIso_hom] using
      CartesianMonoidalCategory.prodComparison_natural L (𝟙 A) h

/-- The canonical comparison between inverse image and restriction, constructed from
finite-product comparisons and the fibre equivalences, with no existence choice.
Source: Stacks Project, Sites, Tag 04H1; Modules on Sites, Tag 04IF. -/
noncomputable def geometricSliceSetComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {RX : Sheaf J RingCat.{u}} {RY : Sheaf K RingCat.{u}}
    (L : Sheaf K (Type u) ⥤ Sheaf J (Type u)) (hL : PreservesFiniteLimits L)
    (A : Sheaf K (Type u))
    (y : RingedSheafSliceAdjunctionData RY A)
    (x : RingedSheafSliceAdjunctionData RX (L.obj A)) :
    elementSheafPullback A ⋙
        (y.fibreEquivalence.functor ⋙ Over.post L ⋙ x.fibreEquivalence.inverse) ≅
      L ⋙ elementSheafPullback (L.obj A) := by
  letI := hL
  let p := geometricSliceProductFibreIso A y
  let q := geometricSliceProductFibreIso (L.obj A) x
  let h : L ⋙ elementSheafPullback (L.obj A) ≅
      (geometricSliceProductOver A ⋙ Over.post L) ⋙ x.fibreEquivalence.inverse :=
    Functor.isoWhiskerLeft L q.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (geometricSliceProductPostIso L A).symm x.fibreEquivalence.inverse
  let r : geometricSliceProductOver A ≅
      elementSheafPullback A ⋙ y.fibreEquivalence.functor :=
    (Functor.rightUnitor _).symm ≪≫
      Functor.isoWhiskerLeft _ y.fibreEquivalence.counitIso.symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight p y.fibreEquivalence.functor
  exact (h ≪≫ Functor.isoWhiskerRight
    (Functor.isoWhiskerRight r (Over.post L)) x.fibreEquivalence.inverse).symm

end CategoryTheory

namespace SheafOfModules

/-- Localization at an arbitrary sheaf commutes with ordinary ringed-topos pullback.

Source: Stacks Project, Sites, Tag 04H1; Modules on Sites, Tags 04IF, 04IE,
03D6 (2), 03EL and 03EK.

`y` and `x` are presentations of the two localizations, supplied by
`ringed_sheaf_slice_adjunction`. The slice inverse image, under these equivalences,
is `Over.post f.inverse`. The comparison `a` is directed from sliced inverse image
of restriction to restriction of inverse image. The structural-map equation specifies
exactly the restriction of `f.ringMap` under `a`.

For every algebraic presentation `I,c` of the ordinary pullback, the conclusion supplies
a compatible presentation `IA,ca` on the slices, with isomorphisms `e` in the category
of modules over the restricted source ring, compatible with the module-sheafification unit
on pure tensors `r tensor m`. -/
theorem geometric_ringed_pullback_slice
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (RX : Sheaf J CommRingCat.{u}) (RY : Sheaf K CommRingCat.{u})
    (f : RingedToposMorphism (localCoefficientRings RX) (localCoefficientRings RY))
    (A : Sheaf K (Type u))
    (y : RingedSheafSliceAdjunctionData (localCoefficientRings RY) A)
    (x : RingedSheafSliceAdjunctionData (localCoefficientRings RX) (f.inverse.obj A)) :
    ∃ (fA : RingedToposMorphism
        (localCoefficientRings (presentationElementRing RX (f.inverse.obj A)))
        (localCoefficientRings (presentationElementRing RY A)))
      (slice : fA.inverse ≅ y.fibreEquivalence.functor ⋙ Over.post f.inverse ⋙
        x.fibreEquivalence.inverse)
      (a : elementSheafPullback A ⋙ fA.inverse ≅
        f.inverse ⋙ elementSheafPullback (f.inverse.obj A)),
      a = Functor.isoWhiskerLeft (elementSheafPullback A) slice ≪≫
        geometricSliceSetComparison f.inverse f.leftExact A y x ∧
      fA.ringMap = a.hom.app
          ((sheafCompose K (CategoryTheory.forget RingCat.{u})).obj (localCoefficientRings RY)) ≫
        (elementSheafPullback (f.inverse.obj A)).map f.ringMap ∧
      ∀ (RI : Sheaf J CommRingCat.{u}) (I : AlgebraicInverseImage f.inverse RY RI)
        (c : RI ⟶ RX),
        I.ringUnderlying.hom ≫ (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map c =
          f.ringMap →
        ∃ (RIA : Sheaf (elementTopology (f.inverse.obj A)) CommRingCat.{u})
          (IA : AlgebraicInverseImage fA.inverse (presentationElementRing RY A) RIA)
          (ca : RIA ⟶ presentationElementRing RX (f.inverse.obj A)),
          IA.ringUnderlying.hom ≫
              (sheafCompose (elementTopology (f.inverse.obj A))
                (CategoryTheory.forget CommRingCat.{u})).map ca = fA.ringMap ∧
          ∃ e : ∀ M : ringedSiteModules.{u} (localCoefficientRings RY),
            ordinaryRingedToposPullback IA ca
                ((elementModulePullback.{u, u} (localCoefficientRings RY) A).obj M) ≅
              (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)).obj
                (ordinaryRingedToposPullback I c M),
            (∀ (M N : ringedSiteModules.{u} (localCoefficientRings RY)) (h : M ⟶ N),
              changeOfRingsHom.{u, u, u} ca
                  (IA.modules.obj
                    ((elementModulePullback.{u, u} (localCoefficientRings RY) A).obj M))
                  (IA.modules.map
                    ((elementModulePullback.{u, u} (localCoefficientRings RY) A).map h)) ≫
                  (e N).hom =
                (e M).hom ≫
                  (elementModulePullback.{u, u} (localCoefficientRings RX) (f.inverse.obj A)).map
                    (changeOfRingsHom.{u, u, u} c (I.modules.obj M) (I.modules.map h))) ∧
            ∀ (M : ringedSiteModules.{u} (localCoefficientRings RY))
              (W : Cᵒᵖ) (b : (f.inverse.obj A).obj.obj W) (r : RX.obj.obj W)
              (m : (IA.modules.obj
                ((elementModulePullback.{u, u} (localCoefficientRings RY) A).obj M)).val.obj
                  (elementObj (f.inverse.obj A) W b)),
              (e M).hom.val.app (elementObj (f.inverse.obj A) W b)
                  (((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
                    (𝟙 (localCoefficientRings
                      (presentationElementRing RX (f.inverse.obj A))).obj)).unit.app
                      (changeOfRingsPresheaf.{u, u, u} ca (IA.modules.obj
                        ((elementModulePullback.{u, u} (localCoefficientRings RY) A).obj M)))).app
                          (elementObj (f.inverse.obj A) W b)
                            ((@id ((presentationElementRing RX (f.inverse.obj A)).obj.obj
                              (elementObj (f.inverse.obj A) W b)) r) ⊗ₜ[
                              RIA.obj.obj (elementObj (f.inverse.obj A) W b),
                              (ca.hom.app (elementObj (f.inverse.obj A) W b)).hom] m)) =
                ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
                  (𝟙 (localCoefficientRings RX).obj)).unit.app
                    (changeOfRingsPresheaf.{u, u, u} c (I.modules.obj M))).app W
                      (r ⊗ₜ[RI.obj.obj W, (c.hom.app W).hom]
                        (@id ((I.modules.obj M).val.obj W)
                          ((IA.moduleUnderlying.hom.app
                            ((elementModulePullback.{u, u} (localCoefficientRings RY) A).obj M) ≫
                          a.hom.app ((toSheaf.{u, u, u, u} (localCoefficientRings RY) ⋙
                            sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
                          (elementSheafPullback (f.inverse.obj A)).map
                            (I.moduleUnderlying.inv.app M)).hom.app
                              (elementObj (f.inverse.obj A) W b) m))) := by
  exact (geometric_ringed_pullback_slice_data RX RY f A y x
    (geometricSliceSetComparison f.inverse f.leftExact A y x)).elim fun fA h ↦
    h.elim fun slice h ↦ h.elim fun a h ↦
      ⟨fA, slice, a, h.1, h.2,
        geometric_ringed_pullback_slice_modules RX RY f A y x fA slice a h.2⟩

end SheafOfModules
