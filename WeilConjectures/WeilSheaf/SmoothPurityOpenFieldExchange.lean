/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityOpenFieldBaseChange
public import WeilConjectures.WeilSheaf.CondensedModelBaseChange
public import WeilConjectures.WeilSheaf.SmoothPurityFullyFaithfulBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedComplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint

/-! # Cross-field compact-support exchange for open immersions

The ambient extension-by-zero comparison restricts to bounded constructible complexes.
Combined with the fully faithful mate theorem, it gives the Step 2 open case.
-/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}


variable [IsOpenImmersion f.left] [IsOpenImmersion f'.left]
  (sq : IsPullback πX f'.left f.left πY)

/-- The ambient extension-by-zero exchange, with left-derived pullbacks. -/
noncomputable def purityOpenFieldAmbientExchange :
    D((f.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        L((πY)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ≅
      L((πX)^*⟦Profinite.padicAlgClRingObj ℓ⟧) ⋙
        D((f'.left)_!open⟦Profinite.padicAlgClRingObj ℓ⟧) :=
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory _ πY) ≪≫
    openImmersionLowerShriekMapDerivedCategoryBaseChangeIso _ sq.flip ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory _ πX).symm _

/-- Extension by zero commutes with weakly étale pullback across different fields. -/
noncomputable def purityOpenFieldExtensionExchange :
    boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f ⋙
        boundedConstructibleUpperStarOfMap ℓ πY ≅
      boundedConstructibleUpperStarOfMap ℓ πX ⋙
        boundedConstructibleOpenImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f' :=
  NatIso.ofComponents
    (fun K ↦ ObjectProperty.isoMk _ ((purityOpenFieldAmbientExchange ℓ f f' sq).app K.obj))
    (fun m ↦ by
      apply ObjectProperty.hom_ext
      exact (purityOpenFieldAmbientExchange ℓ f f' sq).hom.naturality m.hom)

/-- Forgetting the restricted open exchange gives the specified ambient comparison. -/
lemma purityOpenFieldExtensionExchange_hom_app_hom
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((purityOpenFieldExtensionExchange ℓ f f' sq).hom.app K).hom =
      (purityOpenFieldAmbientExchange ℓ f f' sq).hom.app K.obj := rfl

/-- The inverse restricted open exchange has the specified ambient inverse component. -/
lemma purityOpenFieldExtensionExchange_inv_app_hom
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((purityOpenFieldExtensionExchange ℓ f f' sq).inv.app K).hom =
      (purityOpenFieldAmbientExchange ℓ f f' sq).inv.app K.obj := rfl

/-- Cross-field compact-support base change for the actual chosen lower-shriek functors. -/
noncomputable def purityOpenFieldLowerShriekExchange :
    boundedConstructibleLowerShriek ℓ f ⋙ boundedConstructibleUpperStarOfMap ℓ πY ≅
      boundedConstructibleUpperStarOfMap ℓ πX ⋙ boundedConstructibleLowerShriek ℓ f' :=
  Functor.isoWhiskerRight
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f) _ ≪≫
    purityOpenFieldExtensionExchange ℓ f f' sq ≪≫
    Functor.isoWhiskerLeft _
      (boundedConstructibleLowerShriekIsoOpenImmersionLowerShriek_padicAlgCl ℓ f').symm

/-- The mate of the constructed open exchange is invertible at every bounded constructible object. -/
theorem isIso_purityOpenFieldLowerShriekExchange_mate
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((mateEquiv (boundedConstructibleUpperShriekAdjunction ℓ f)
      (boundedConstructibleUpperShriekAdjunction ℓ f')
      (purityOpenFieldLowerShriekExchange ℓ f f' sq).inv).app N) :=
  isIso_smoothExceptionalMate_of_isOpenImmersion ℓ f f' sq.toCommSq
    (purityOpenFieldLowerShriekExchange ℓ f f' sq) N

/-- The open-immersion unit case of the cross-field smooth trace criterion. -/
theorem isIso_smoothUnitBaseChange_purityOpenFieldLowerShriekExchange
    (e : (boundedConstructibleUpperStarOfMap ℓ πY).obj (𝟙_ _) ⟶ 𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange ℓ f f'
      (purityOpenFieldLowerShriekExchange ℓ f f' sq) e) :=
  isIso_smoothUnitBaseChange_of_isOpenImmersion ℓ f f' sq.w _ e

end AlgebraicGeometry.ProEtale.CondensedRing
