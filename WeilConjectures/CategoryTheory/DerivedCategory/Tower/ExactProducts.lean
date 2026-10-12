/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Tower.Products
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim

/-!
# Products in the derived category of an abelian category with exact products

Let `A` be an abelian category in which products of shape `J` are exact
(`HasExactLimitsOfShape (Discrete J) A`).

* `HomologicalComplex.quasiIso_limMap`: a limit (of shape `J`) of quasi-isomorphisms is a
  quasi-isomorphism; in particular so is a product of quasi-isomorphisms
  (`HomologicalComplex.quasiIso_piMap`).
* `HomologicalComplex.homologyPiIso`: the homology of a product of complexes is the product of
  the homologies.
* `DerivedCategory.isLimitFanQPi`: if `A` moreover has K-injective resolutions, the image in
  `D(A)` of the termwise product `∏ⱼ Kⱼ` of complexes is a product of the `Q Kⱼ`: products of
  shape `J` exist in `D(A)` and are represented by termwise products of any representatives.
-/

@[expose] public section

open CategoryTheory Limits

namespace HomologicalComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The limit of a diagram of complexes is computed by the limit functor on complexes in the
functor category. -/
noncomputable def functorEquivalenceInverseCompMapHomologicalComplexLim
    (C : Type*) [Category* C] [HasZeroMorphisms C]
    {ι : Type*} (c : ComplexShape ι) (J : Type*) [Category* J] [HasLimitsOfShape J C] :
    (functorEquivalence C c J).inverse ⋙ lim.mapHomologicalComplex c ≅ lim :=
  NatIso.ofComponents (fun F ↦
    (Hom.isoOfComponents (fun i ↦ IsLimit.conePointUniqueUpToIso (limit.isLimit _)
        (isLimitOfPreserves (eval C c i) (limit.isLimit F))) (fun i j _ ↦
          (isLimitOfPreserves (eval C c j) (limit.isLimit F)).hom_ext fun k ↦ by
            simp only [Category.assoc]
            erw [IsLimit.conePointUniqueUpToIso_hom_comp]
            simp [← comp_f]))) (by
          intro F G f
          ext i
          dsimp
          ext j
          simp [← comp_f])

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
  {J : Type*} [Category* J] [HasLimitsOfShape J C] [HasExactLimitsOfShape J C]

set_option backward.defeqAttrib.useBackward true in
/-- In an abelian category with exact limits of shape `J`, a limit of quasi-isomorphisms of
complexes is a quasi-isomorphism. -/
lemma quasiIso_limMap {F₁ F₂ : J ⥤ HomologicalComplex C c} (f : F₁ ⟶ F₂)
    (hf : (quasiIso C c).functorCategory J f) : QuasiIso (limMap f) := by
  have : QuasiIso ((functorEquivalence.inverse C c J).map f) := by
    rwa [quasiIso_functorCategory_iff]
  refine ((quasiIso C c).arrow_mk_iso_iff (((Functor.mapArrowFunctor _ _).mapIso
    ((functorEquivalenceInverseCompMapHomologicalComplexLim C c J))).app (Arrow.mk f))).1 ?_
  dsimp
  simp only [mem_quasiIso_iff]
  infer_instance

/-- In an abelian category with exact products of shape `J`, a product of quasi-isomorphisms of
complexes is a quasi-isomorphism. -/
lemma quasiIso_piMap {J : Type*} [HasLimitsOfShape (Discrete J) C]
    [HasExactLimitsOfShape (Discrete J) C] {K L : J → HomologicalComplex C c}
    (f : ∀ j, K j ⟶ L j) [∀ j, QuasiIso (f j)] : QuasiIso (Limits.Pi.map f) :=
  quasiIso_limMap _ fun j ↦ by
    rw [mem_quasiIso_iff]
    exact inferInstanceAs (QuasiIso (f j.as))

end HomologicalComplex

namespace DerivedCategory

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [Abelian.HasKInjectiveResolutions A] {J : Type*} [HasLimitsOfShape (Discrete J) A]
  [HasExactLimitsOfShape (Discrete J) A]

/-- **Blueprint `lem-weil-derived-limit-existence`** (assertion 2). In the derived category of
an abelian category with exact products of shape `J` (and K-injective resolutions), products of
shape `J` exist and are represented by termwise products of any representatives: the image in
`D(A)` of the product `∏ⱼ Kⱼ` of complexes is a product of the `Q Kⱼ`. -/
noncomputable def isLimitFanQPi (K : J → CochainComplex A ℤ) :
    IsLimit (Fan.mk (Q.obj (∏ᶜ K)) fun j ↦ Q.map (Pi.π K j)) := by
  choose I hI i hi using fun j ↦ Abelian.HasKInjectiveResolutions.exists_isKInjective (K j)
  have := fun j ↦ (hi j).2
  have h := isLimitFanQOfIsKInjective (productIsProduct I)
  have : IsIso (Q.map (Limits.Pi.map i)) := by
    have := HomologicalComplex.quasiIso_piMap i
    infer_instance
  refine IsLimit.ofIsoLimit ((IsLimit.postcomposeHomEquiv
    (Discrete.natIso fun j ↦ (asIso (Q.map (i j.as))).symm) _).symm h)
    (Fan.ext (asIso (Q.map (Limits.Pi.map i))).symm fun j ↦ ?_)
  simp only [fan_mk_proj, Iso.symm_hom, asIso_inv, Cone.postcompose_obj_pt, Cone.postcompose_obj_π,
    NatTrans.comp_app, Discrete.natIso_hom_app, IsIso.eq_inv_comp]
  change Q.map (Limits.Pi.map i) ≫ Q.map (Pi.π I j) ≫ inv (Q.map (i j)) = _
  rw [← Q.map_comp_assoc, Pi.map_π, Q.map_comp_assoc, IsIso.hom_inv_id, Category.comp_id]

end DerivedCategory
