/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.QuotSMulTopAdjunction
public import WeilConjectures.CategoryTheory.Sites.Point.Flat
public import WeilConjectures.CategoryTheory.Sites.ReductionFlat
public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension

/-!
# Extension of scalars of étale sheaves along a quotient ring

Let `J` be an ideal of a commutative ring `Λ`. Extension of scalars
`E = (Λ ⧸ J) ⊗_Λ - : Sh(X_ét, Λ) ⥤ Sh(X_ét, Λ ⧸ J)`
(`AlgebraicGeometry.ProEtale.etaleSheafExtendScalars`) is left adjoint to restriction of
scalars. This file records its properties needed to derive it:

- it is the reduction `F ↦ F / J F` (`CategoryTheory.Sheaf.quotSMulTop`), so restricting the
  scalars of `E F` back to `Λ` gives `F ⊗ (Λ ⧸ J)_X`
  (`AlgebraicGeometry.Etale.etaleSheafExtendScalarsCompRestrictScalarsIso`);
- it is strong monoidal;
- it preserves flat sheaves (`AlgebraicGeometry.Etale.preservesFlat_etaleSheafExtendScalars`),
  flatness being checked on stalks, where it is the base change of a flat module.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ] (J : Ideal Λ) (X : Scheme.{u})

/-- The small étale site of a scheme is locally small. Instance search does not find this in the
presence of the imports of this file. -/
local instance (X : Scheme.{u}) : LocallySmall.{u + 1} X.Etale :=
  @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)

/-- The small étale site of a scheme is essentially small. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  essentiallySmall_of_small_of_locallySmall _

/-- Extension of scalars of étale sheaves along `Λ ⟶ Λ ⧸ J` is the reduction `F ↦ F / J F`, both
being left adjoint to restriction of scalars. -/
noncomputable def etaleSheafExtendScalarsIsoQuotSMulTop :
    ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X ≅
      Sheaf.quotSMulTop X.smallEtaleTopology J :=
  (ProEtale.etaleSheafExtendScalarsAdjunction _ X).leftAdjointUniq
    (Sheaf.adjunction _ (ModuleCat.quotSMulTopAdj J))

/-- Restricting the scalars of `(Λ ⧸ J) ⊗_Λ F` back to `Λ` gives `F ⊗ (Λ ⧸ J)_X`. -/
noncomputable def etaleSheafExtendScalarsCompRestrictScalarsIso :
    ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X ⋙
        Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J) ≅
      tensorRight ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ J))) :=
  Functor.isoWhiskerRight (etaleSheafExtendScalarsIsoQuotSMulTop J X) _ ≪≫
    Sheaf.quotSMulTopCompRestrictScalarsIso J

/-- The stalks of the reduction `F / J F` are the reductions of the stalks. -/
noncomputable def quotSMulTopCompSheafFiberIso (P : X.smallEtaleTopology.Point.{u + 1}) :
    Sheaf.quotSMulTop X.smallEtaleTopology J ⋙ P.sheafFiber ≅
      P.sheafFiber ⋙ ModuleCat.quotSMulTop J :=
  Functor.isoWhiskerLeft (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (ModuleCat.quotSMulTop J))
    (P.presheafToSheafCompSheafFiberIso (ModuleCat.{u + 1} (Λ ⧸ J))) ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf _ _)
      (P.presheafFiberCompIso (ModuleCat.quotSMulTop.{u + 1} J))

/-- Extension of scalars along `Λ ⟶ Λ ⧸ J` preserves flat étale sheaves: on stalks it is the
reduction of a flat module, which is flat. -/
instance preservesFlat_etaleSheafExtendScalars :
    (ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X).PreservesFlat where
  flat_obj {F} hF := by
    have hP := isConservativeFamilyOfPoints_ulift_pointSmallEtale X
    refine ObjectProperty.prop_of_iso _ ((etaleSheafExtendScalarsIsoQuotSMulTop J X).app F).symm ?_
    rw [GrothendieckTopology.flat_iff_forall_flat_sheafFiber_obj hP] at hF ⊢
    intro Φ
    exact ObjectProperty.prop_of_iso _ ((quotSMulTopCompSheafFiberIso J X Φ.obj).app F).symm
      (ModuleCat.flat_quotSMulTop_obj J (hF Φ))

instance additive_etaleSheafExtendScalars :
    (ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X).Additive :=
  (ProEtale.etaleSheafExtendScalarsAdjunction _ X).left_adjoint_additive

instance isLeftAdjoint_etaleSheafExtendScalars :
    (ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X).IsLeftAdjoint :=
  (ProEtale.etaleSheafExtendScalarsAdjunction _ X).isLeftAdjoint

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly; the instance going
-- through enough points of the site is tried first and makes the search time out.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

attribute [local instance] Sheaf.monoidalCategory in
/-- Extension of scalars of étale sheaves is oplax monoidal, being left adjoint to the lax
monoidal restriction of scalars. -/
noncomputable instance oplaxMonoidal_etaleSheafExtendScalars :
    (ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X).OplaxMonoidal :=
  composeAndSheafifyOplaxMonoidal _ (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} _)

attribute [local instance] Sheaf.monoidalCategory in
instance isIso_δ_etaleSheafExtendScalars
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (Functor.OplaxMonoidal.δ
      (ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X) F G) :=
  isIso_δ_composeAndSheafify _
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} (Ideal.Quotient.mk J)) F G

attribute [local instance] Sheaf.monoidalCategory in
instance isIso_η_etaleSheafExtendScalars :
    IsIso (Functor.OplaxMonoidal.η (ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X)) :=
  isIso_η_composeAndSheafify _
    (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u + 1} (Ideal.Quotient.mk J))

attribute [local instance] Sheaf.monoidalCategory in
/-- Extension of scalars of étale sheaves is strong monoidal. -/
noncomputable instance monoidal_etaleSheafExtendScalars :
    (ProEtale.etaleSheafExtendScalars (Ideal.Quotient.mk J) X).Monoidal :=
  .ofOplaxMonoidal _

end AlgebraicGeometry.Etale
