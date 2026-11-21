/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.CategoryTheory.RingedCocontinuousMonoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-! # Ordinary tensor transport through a ringed-site equivalence

## References

* Stacks Project, Tags 03D1, 03EK and 03EL (Modules on Sites)
-/

@[expose] public section
set_option autoImplicit false
universe u v u' v' w
open CategoryTheory CategoryTheory.MonoidalCategory

namespace SheafOfModules

/-- A site equivalence and an invertible coefficient comparison preserve the ordinary
binary sheaf tensor product. Only existence is needed for transport of predicates;
no tensor comparison is chosen as data by this theorem. -/
theorem pushforward_equivalence_tensor_iso
    {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {D : Type u'} [Category.{v'} D] [EssentiallySmall.{w} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (e : C ≌ D) [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
    (R : Sheaf K CommRingCat.{w}) (S : Sheaf J CommRingCat.{w})
    (c : S ≅ (e.functor.sheafPushforwardContinuous CommRingCat.{w} J K).obj R) :
    letI := isMonoidal_W_independentCoefficients R
    letI := isMonoidal_W_independentCoefficients S
    letI := monoidalCategory R
    letI := monoidalCategory S
    let F := pushforward.{w} (F := e.functor) (J := J) (K := K)
      (R := (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
      (S := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S)
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map c.hom)
    Nonempty (tensor _ ⋙ F ≅ F.prod F ⋙ tensor _) := by
  let := isMonoidal_W_independentCoefficients R
  let := isMonoidal_W_independentCoefficients S
  let := monoidalCategory R
  let := monoidalCategory S
  let F := pushforward.{w} (F := e.functor) (J := J) (K := K)
    (R := (sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj R)
    (S := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S)
    ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map c.hom)
  change Nonempty (tensor _ ⋙ F ≅ F.prod F ⋙ tensor _)
  have : e.functor.IsCocontinuous J K :=
    (e.toAdjunction.isCocontinuous_iff_coverPreserving J K).2
      (CoverPreserving.of_isContinuous e.inverse K J)
  let a : (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj S ≅
      (e.functor.sheafPushforwardContinuous RingCat.{w} J K).obj
        ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).obj R) :=
    (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).mapIso c
  obtain ⟨h⟩ := ringed_cocontinuous_monoidal e.functor S R a
  let : F.Monoidal := h
  exact ⟨(Functor.Monoidal.μNatIso F).symm⟩

end SheafOfModules
