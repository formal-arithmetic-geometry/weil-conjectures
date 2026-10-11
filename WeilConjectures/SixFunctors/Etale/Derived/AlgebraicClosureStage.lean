/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.CoextendScalarsComp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompCoherence
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientExtension

/-!
# The transition functors of the `ℚ̄_ℓ` coefficient stage

The coefficient stage `ℚ̄_ℓ` of blueprint `def-weil-algebraically-closed-coefficients` is a
`2`-colimit over the finite extensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ` (`PadicAlgCl.FiniteSubext`), along the
transition functors `K ↦ K ⊗_E L`. This file builds these transition functors on the derived
categories of étale sheaves of `𝒪_E`-modules, as right derived coextension of scalars along
`𝒪_E → 𝒪_L` (`AlgebraicGeometry.Etale.stageTransition`), with composition isomorphisms
(`AlgebraicGeometry.Etale.stageTransitionComp`) satisfying the cocycle condition
(`AlgebraicGeometry.Etale.stageTransitionComp_cocycle`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type*} [Category C] (J : GrothendieckTopology C) {A B D : Type*} [Category A]
  [Category B] [Category D]

/-- An isomorphism `F ⋙ G ≅ H` of functors induces an isomorphism of the functors they induce on
sheaves by postcomposition. -/
noncomputable def sheafComposeCompIso {F : A ⥤ B} {G : B ⥤ D} {H : A ⥤ D} [J.HasSheafCompose F]
    [J.HasSheafCompose G] [J.HasSheafCompose H] (α : F ⋙ G ≅ H) :
    sheafCompose J F ⋙ sheafCompose J G ≅ sheafCompose J H where
  hom :=
    { app P := ⟨Functor.whiskerLeft P.obj α.hom⟩
      naturality _ _ f := Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ α.hom.naturality _)) }
  inv :=
    { app P := ⟨Functor.whiskerLeft P.obj α.inv⟩
      naturality _ _ f := Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ α.inv.naturality _)) }
  hom_inv_id := NatTrans.ext (funext fun P ↦ Sheaf.hom_ext (NatTrans.ext (funext fun U ↦
    α.hom_inv_id_app (P.obj.obj U))))
  inv_hom_id := NatTrans.ext (funext fun P ↦ Sheaf.hom_ext (NatTrans.ext (funext fun U ↦
    α.inv_hom_id_app (P.obj.obj U))))

/-- The isomorphisms `CategoryTheory.sheafComposeCompIso` inherit the cocycle condition. -/
lemma sheafComposeCompIso_cocycle {E : Type*} [Category E] {F₁ : A ⥤ B} {F₂ : B ⥤ D} {F₃ : D ⥤ E}
    {F₁₂ : A ⥤ D} {F₂₃ : B ⥤ E} {F₁₃ : A ⥤ E} [J.HasSheafCompose F₁] [J.HasSheafCompose F₂]
    [J.HasSheafCompose F₃] [J.HasSheafCompose F₁₂] [J.HasSheafCompose F₂₃]
    [J.HasSheafCompose F₁₃] (e₁₂ : F₁ ⋙ F₂ ≅ F₁₂) (e₂₃ : F₂ ⋙ F₃ ≅ F₂₃) (e : F₁₂ ⋙ F₃ ≅ F₁₃)
    (e' : F₁ ⋙ F₂₃ ≅ F₁₃)
    (h : Functor.whiskerRight e₁₂.hom F₃ ≫ e.hom = Functor.whiskerLeft F₁ e₂₃.hom ≫ e'.hom) :
    Functor.whiskerRight (sheafComposeCompIso J e₁₂).hom (sheafCompose J F₃) ≫
        (sheafComposeCompIso J e).hom =
      Functor.whiskerLeft (sheafCompose J F₁) (sheafComposeCompIso J e₂₃).hom ≫
        (sheafComposeCompIso J e').hom := by
  exact NatTrans.ext (funext fun P ↦ Sheaf.hom_ext (NatTrans.ext (funext fun U ↦
    congr_app h (P.obj.obj U))))

end CategoryTheory

namespace PadicAlgCl

variable (l : ℕ) [Fact l.Prime]

/-- The finite extensions of `ℚ_ℓ` inside `ℚ̄_ℓ`, ordered by inclusion: the index of the
`2`-colimit defining the coefficient stage `ℚ̄_ℓ`. -/
def FiniteSubext : Type :=
  {E : IntermediateField ℚ_[l] (PadicAlgCl l) // FiniteDimensional ℚ_[l] E}

namespace FiniteSubext

variable {l}

instance : Preorder (FiniteSubext l) :=
  inferInstanceAs (Preorder {E : IntermediateField ℚ_[l] (PadicAlgCl l) //
    FiniteDimensional ℚ_[l] E})

/-- The field underlying a finite subextension. -/
abbrev field (E : FiniteSubext l) : Type := E.1

instance (E : FiniteSubext l) : FiniteDimensional ℚ_[l] E.field := E.2

/-- Two finite subextensions are contained in a third one, their compositum. -/
lemma exists_ge (E L : FiniteSubext l) : ∃ M : FiniteSubext l, E ≤ M ∧ L ≤ M :=
  have : FiniteDimensional ℚ_[l] E.1 := E.2
  have : FiniteDimensional ℚ_[l] L.1 := L.2
  ⟨⟨E.1 ⊔ L.1, inferInstance⟩, le_sup_left (a := E.1), le_sup_right (a := E.1)⟩

/-- The inclusion of fields `E → L` for `E ≤ L`. -/
noncomputable def incl {E L : FiniteSubext l} (h : E ≤ L) : E.field →+* L.field :=
  (IntermediateField.inclusion h).toRingHom

lemma incl_compat {E L : FiniteSubext l} (h : E ≤ L) (x : E.field) :
    algebraMap L.field (PadicAlgCl l) (incl h x) = algebraMap E.field (PadicAlgCl l) x :=
  rfl

lemma integersShrinkMap_incl_comp {E L L' : FiniteSubext l} (h : E ≤ L) (h' : L ≤ L') :
    integersShrinkMap.{0, u} l (incl (h.trans h')) (incl_compat (h.trans h')) =
      (integersShrinkMap.{0, u} l (incl h') (incl_compat h')).comp
        (integersShrinkMap.{0, u} l (incl h) (incl_compat h)) :=
  integersShrinkMap_comp l (incl h) (incl_compat h) (incl h') (incl_compat h')

end FiniteSubext

end PadicAlgCl

namespace AlgebraicGeometry.Etale

open PadicAlgCl PadicAlgCl.FiniteSubext

variable {l : ℕ} [Fact l.Prime] (X : Scheme.{u})

/-- The sheaf-level transition functor `Sh(X_ét, 𝒪_E) ⥤ Sh(X_ét, 𝒪_L)`: coextension of scalars
along `𝒪_E → 𝒪_L`. -/
noncomputable abbrev sheafStageTransition {E L : FiniteSubext l} (h : E ≤ L) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l E.field))) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Shrink.{u + 1} (integers l L.field))) :=
  coextendScalars (integersShrinkMap.{0, u} l (incl h) (incl_compat h)) X

/-- The composition isomorphisms of the sheaf-level transition functors. -/
noncomputable def sheafStageTransitionComp {E L L' : FiniteSubext l} (h : E ≤ L) (h' : L ≤ L') :
    sheafStageTransition X h ⋙ sheafStageTransition X h' ≅
      sheafStageTransition X (h.trans h') :=
  sheafComposeCompIso _ (ModuleCat.coextendScalarsCompIso
    (integersShrinkMap.{0, u} l (incl h) (incl_compat h))
    (integersShrinkMap.{0, u} l (incl h') (incl_compat h'))
    (integersShrinkMap.{0, u} l (incl (h.trans h')) (incl_compat (h.trans h')))
    (integersShrinkMap_incl_comp h h'))

/-- The cocycle condition for the sheaf-level transition functors. -/
lemma sheafStageTransitionComp_cocycle {E L L' L'' : FiniteSubext l} (h : E ≤ L) (h' : L ≤ L')
    (h'' : L' ≤ L'') :
    Functor.whiskerRight (sheafStageTransitionComp X h h').hom (sheafStageTransition X h'') ≫
        (sheafStageTransitionComp X (h.trans h') h'').hom =
      Functor.whiskerLeft (sheafStageTransition X h) (sheafStageTransitionComp X h' h'').hom ≫
        (sheafStageTransitionComp X h (h'.trans h'')).hom :=
  sheafComposeCompIso_cocycle _ _ _ _ _ (ModuleCat.coextendScalarsCompIso_cocycle
    (integersShrinkMap.{0, u} l (incl h) (incl_compat h))
    (integersShrinkMap.{0, u} l (incl h') (incl_compat h'))
    (integersShrinkMap.{0, u} l (incl h'') (incl_compat h''))
    (integersShrinkMap.{0, u} l (incl (h.trans h')) (incl_compat (h.trans h')))
    (integersShrinkMap.{0, u} l (incl (h'.trans h'')) (incl_compat (h'.trans h'')))
    (integersShrinkMap.{0, u} l (incl ((h.trans h').trans h''))
      (incl_compat ((h.trans h').trans h'')))
    (integersShrinkMap_incl_comp h h') (integersShrinkMap_incl_comp h' h'')
    (integersShrinkMap_incl_comp (h.trans h') h'') (integersShrinkMap_incl_comp h (h'.trans h'')))

/-- The derived transition functor `D(X_ét, 𝒪_E) ⥤ D(X_ét, 𝒪_L)`: right derived coextension of
scalars along `𝒪_E → 𝒪_L`. -/
noncomputable abbrev derivedStageTransition {E L : FiniteSubext l} (h : E ≤ L) :=
  (sheafStageTransition X h).rightDerivedFunctor

/-- The composition isomorphisms of the derived transition functors. -/
noncomputable def derivedStageTransitionComp {E L L' : FiniteSubext l} (h : E ≤ L)
    (h' : L ≤ L') :
    derivedStageTransition X h ⋙ derivedStageTransition X h' ≅
      derivedStageTransition X (h.trans h') :=
  Functor.rightDerivedFunctorCompIso' _ _ (sheafStageTransitionComp X h h')

/-- The cocycle condition for the derived transition functors. -/
lemma derivedStageTransitionComp_cocycle {E L L' L'' : FiniteSubext l} (h : E ≤ L)
    (h' : L ≤ L') (h'' : L' ≤ L'') :
    Functor.whiskerRight (derivedStageTransitionComp X h h').hom (derivedStageTransition X h'') ≫
        (derivedStageTransitionComp X (h.trans h') h'').hom =
      Functor.whiskerLeft (derivedStageTransition X h) (derivedStageTransitionComp X h' h'').hom ≫
        (derivedStageTransitionComp X h (h'.trans h'')).hom :=
  Functor.rightDerivedFunctorCompIso'_cocycle _ _ _ _ (sheafStageTransitionComp_cocycle X h h' h'')

section Integral

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- The transition functor `D_comp(X_ét, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_L)` of the integral stages. -/
noncomputable abbrev integralStageTransition {E L : FiniteSubext l} (h : E ≤ L) :
    DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E.field ⥤
      DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l L.field :=
  coextendScalarsDerivedCompleteIntegral l (incl h) (incl_compat h) X

lemma integralStageTransition_comp_ι {E L : FiniteSubext l} (h : E ≤ L) :
    integralStageTransition X h ⋙ DerivedCategoryDerivedCompleteIntegral.ι _ l L.field =
      DerivedCategoryDerivedCompleteIntegral.ι _ l E.field ⋙ derivedStageTransition X h :=
  rfl

/-- The composition isomorphisms of the integral transition functors. -/
noncomputable def integralStageTransitionComp {E L L' : FiniteSubext l} (h : E ≤ L)
    (h' : L ≤ L') :
    integralStageTransition X h ⋙ integralStageTransition X h' ≅
      integralStageTransition X (h.trans h') :=
  NatIso.ofComponents
    (fun K ↦ (ObjectProperty.fullyFaithfulι _).preimageIso
      ((derivedStageTransitionComp X h h').app
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E.field).obj K)))
    (fun f ↦ (ObjectProperty.fullyFaithfulι _).map_injective
      ((derivedStageTransitionComp X h h').hom.naturality
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E.field).map f)))

lemma integralStageTransitionComp_hom_app {E L L' : FiniteSubext l} (h : E ≤ L)
    (h' : L ≤ L') (K : DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E.field) :
    (DerivedCategoryDerivedCompleteIntegral.ι _ l L'.field).map
        ((integralStageTransitionComp X h h').hom.app K) =
      (derivedStageTransitionComp X h h').hom.app
        ((DerivedCategoryDerivedCompleteIntegral.ι _ l E.field).obj K) :=
  rfl

/-- The cocycle condition for the integral transition functors. -/
lemma integralStageTransitionComp_cocycle {E L L' L'' : FiniteSubext l} (h : E ≤ L)
    (h' : L ≤ L') (h'' : L' ≤ L'') :
    Functor.whiskerRight (integralStageTransitionComp X h h').hom (integralStageTransition X h'') ≫
        (integralStageTransitionComp X (h.trans h') h'').hom =
      Functor.whiskerLeft (integralStageTransition X h) (integralStageTransitionComp X h' h'').hom ≫
        (integralStageTransitionComp X h (h'.trans h'')).hom := by
  ext K
  apply (ObjectProperty.fullyFaithfulι _).map_injective
  exact congr_app (derivedStageTransitionComp_cocycle X h h' h'')
    ((DerivedCategoryDerivedCompleteIntegral.ι _ l E.field).obj K)

end Integral

end AlgebraicGeometry.Etale
