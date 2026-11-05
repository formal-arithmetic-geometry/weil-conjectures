/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Limits of towers of complexes with surjective transitions are homotopy limits

Let `T : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ` be a tower of complexes of modules whose transitions are
degreewise surjective, and let `c` be a limit cone of `T` (computed degreewise). In each degree
the sequence `0 ⟶ lim Tₙ ⟶ ∏ Tₙ ──1 - t──▶ ∏ Tₙ ⟶ 0` is exact, so that it is a short exact
sequence of complexes. Its image in the derived category is the Milnor triangle, hence the
image of `c` in the derived category is a homotopy limit cone.

This uses that the localization functor `Q` to the derived category preserves products when
products are exact (`AB4*`) and there are K-injective resolutions: products of K-injective
complexes are K-injective, and a product of quasi-isomorphisms is a quasi-isomorphism.

## Main statements

- `HomologicalComplex.quasiIso_limMap`: if limits of shape `J` are exact, then a limit of
  quasi-isomorphisms is a quasi-isomorphism.
- `DerivedCategory.isLimitFanQ`: `Q` sends products of complexes to products.
- `DerivedCategory.isHomotopyLimit_mapCone_Q_of_epi`: the image in the derived category of a
  limit cone of a tower of complexes of modules with degreewise surjective transitions is a
  homotopy limit cone.
-/

@[expose] public section

open CategoryTheory Category Limits Opposite Pretriangulated

namespace HomologicalComplex

variable (C : Type*) [Category* C] [Abelian C] {ι : Type*} (c : ComplexShape ι)
  (J : Type*) [Category* J] [HasLimitsOfShape J C]

variable {C c J} in
/-- The degree `i` term of the limit of a diagram of complexes is the limit of the degree `i`
terms. -/
noncomputable def limitXIso (F : J ⥤ HomologicalComplex C c) (i : ι) :
    limit (F ⋙ eval C c i) ≅ (limit F).X i :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    (isLimitOfPreserves (eval C c i) (limit.isLimit F))

variable {C c J} in
@[reassoc (attr := simp)]
lemma limitXIso_hom_π_f (F : J ⥤ HomologicalComplex C c) (i : ι) (k : J) :
    (limitXIso F i).hom ≫ (limit.π F k).f i = limit.π (F ⋙ eval C c i) k :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ k

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The limit of a diagram of complexes is computed degreewise. -/
noncomputable def functorEquivalenceInverseCompMapHomologicalComplexLim :
    (functorEquivalence C c J).inverse ⋙ lim.mapHomologicalComplex c ≅ lim :=
  NatIso.ofComponents (fun F ↦ Hom.isoOfComponents (limitXIso F) fun i j _ ↦
    (isLimitOfPreserves (eval C c j) (limit.isLimit F)).hom_ext fun k ↦ by
      dsimp
      rw [assoc, ← Hom.comm, limitXIso_hom_π_f_assoc, assoc, limitXIso_hom_π_f, limMap_π]
      rfl) fun {F G} f ↦ by
    ext i
    refine (isLimitOfPreserves (eval C c i) (limit.isLimit G)).hom_ext fun k ↦ ?_
    dsimp
    simp only [assoc, limitXIso_hom_π_f, ← comp_f, limMap_π]
    rw [comp_f, limitXIso_hom_π_f_assoc]
    simp

variable {C c J}

set_option backward.defeqAttrib.useBackward true in
/-- If limits of shape `J` are exact, a limit of quasi-isomorphisms of complexes is a
quasi-isomorphism. -/
lemma quasiIso_limMap [HasExactLimitsOfShape J C] {F₁ F₂ : J ⥤ HomologicalComplex C c}
    (f : F₁ ⟶ F₂) [∀ j, QuasiIso (f.app j)] : QuasiIso (limMap f) := by
  have : QuasiIso ((functorEquivalence.inverse C c J).map f) := by
    rw [quasiIso_functorCategory_iff]
    intro j
    exact inferInstanceAs (QuasiIso (f.app j))
  refine ((quasiIso C c).arrow_mk_iso_iff (((Functor.mapArrowFunctor _ _).mapIso
    (functorEquivalenceInverseCompMapHomologicalComplexLim C c J)).app (Arrow.mk f))).1 ?_
  have : (lim : (J ⥤ C) ⥤ C).PreservesHomology := inferInstance
  dsimp
  simp only [mem_quasiIso_iff]
  infer_instance

end HomologicalComplex

namespace DerivedCategory

open Abelian

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  [HasKInjectiveResolutions C] {J : Type*}

set_option backward.defeqAttrib.useBackward true in
/-- The image in the derived category of a product of K-injective complexes is a product. -/
noncomputable def isLimitFanQOfIsKInjective [HasLimitsOfShape (Discrete J) C]
    (I : J → CochainComplex C ℤ) [∀ j, (I j).IsKInjective] :
    IsLimit (Fan.mk (Q.obj (∏ᶜ I)) fun j ↦ Q.map (Pi.π I j)) := by
  let hK := HomotopyCategory.isLimitFanQuotient C (.up ℤ) (productIsProduct I)
  have hprop : (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
      ((HomotopyCategory.quotient _ _).obj (∏ᶜ I)) :=
    ObjectProperty.prop_of_isLimit _ hK fun j ↦
      (CochainComplex.isKInjective_iff_rightOrthogonal _).1 inferInstance
  let X : HomotopyCategory.KInjectives C := ⟨_, hprop⟩
  let F' : Fan fun j ↦ HomotopyCategory.KInjectives.mk (I j) :=
    Fan.mk X fun j ↦ ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map (Pi.π I j))
  have hF' : IsLimit F' := isLimitOfReflects (ObjectProperty.ι _)
    ((isLimitMapConeFanMkEquiv _ _ _).symm hK)
  let hQh := isLimitMapConeFanMkEquiv _ _ _
    (isLimitOfPreserves HomotopyCategory.KInjectives.Qh hF')
  refine Fan.IsLimit.ofIsos hQh (fun j ↦ ((quotientCompQhIso C).app (I j)).symm)
    ((quotientCompQhIso C).app (∏ᶜ I)).symm fun j ↦ ?_
  rw [Iso.symm_hom, Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact (quotientCompQhIso C).hom.naturality (Pi.π I j)

/-- If products of shape `J` are exact, the localization functor `Q` to the derived category
sends products of complexes to products. -/
noncomputable def isLimitFanQ [HasLimitsOfShape (Discrete J) C]
    [HasExactLimitsOfShape (Discrete J) C] (K : J → CochainComplex C ℤ) :
    IsLimit (Fan.mk (Q.obj (∏ᶜ K)) fun j ↦ Q.map (Pi.π K j)) := by
  choose I hI i _ hi using fun j ↦ HasKInjectiveResolutions.exists_isKInjective (K j)
  have (j : Discrete J) :
      QuasiIso ((Discrete.natTrans (F := Discrete.functor K) (G := Discrete.functor I)
        fun j ↦ i j.as).app j) := hi j.as
  have : QuasiIso (Limits.Pi.map i) := HomologicalComplex.quasiIso_limMap _
  refine Fan.IsLimit.ofIsos (isLimitFanQOfIsKInjective I)
    (fun j ↦ asIso (Q.map (i j))) (asIso (Q.map (Limits.Pi.map i))) fun j ↦ ?_
  simp [← Functor.map_comp]

instance [HasLimitsOfShape (Discrete J) C] [HasExactLimitsOfShape (Discrete J) C] :
    PreservesLimitsOfShape (Discrete J) (Q (C := C)) :=
  have (K : J → CochainComplex C ℤ) : PreservesLimit (Discrete.functor K) Q :=
    preservesLimit_of_preserves_limit_cone (productIsProduct K)
      ((isLimitMapConeFanMkEquiv _ _ _).symm (isLimitFanQ K))
  preservesLimitsOfShape_of_discrete Q

end DerivedCategory

namespace CategoryTheory.Limits

/-- For a cone `c` over a tower `F` and an endomorphism `t` of a product `∏ Fₙ` with components
`∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`, the composite `c.pt ⟶ ∏ Fₙ ──1 - t──▶ ∏ Fₙ` vanishes. -/
lemma Fan.IsLimit.lift_π_comp_one_sub_eq_zero {C : Type*} [Category* C] [Preadditive C]
    {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (Opposite.op n)} (hP : IsLimit P)
    (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    (c : Cone F) :
    Fan.IsLimit.lift hP (fun n ↦ c.π.app (Opposite.op n)) ≫ (𝟙 P.pt - t) = 0 :=
  Fan.IsLimit.hom_ext hP _ _ fun n ↦ by
    simp [Preadditive.sub_comp, Preadditive.comp_sub, ht]

/-- For a limit cone `c` over a tower `F`, the map `c.pt ⟶ ∏ Fₙ` is a kernel of `1 - t`, where
`t : ∏ Fₙ ⟶ ∏ Fₙ` has components `∏ Fₙ ⟶ Fₙ₊₁ ⟶ Fₙ`. -/
noncomputable def Fan.IsLimit.isLimitKernelForkOneSub {C : Type*} [Category* C] [Preadditive C]
    {F : ℕᵒᵖ ⥤ C} {P : Fan fun n : ℕ ↦ F.obj (Opposite.op n)} (hP : IsLimit P)
    (t : P.pt ⟶ P.pt)
    (ht : ∀ n : ℕ, t ≫ P.proj n = P.proj (n + 1) ≫ F.map (homOfLE n.le_succ).op)
    {c : Cone F} (hc : IsLimit c) :
    IsLimit (KernelFork.ofι _ (Fan.IsLimit.lift_π_comp_one_sub_eq_zero hP t ht c)) :=
  KernelFork.IsLimit.ofι _ _
    (fun {W} h hh ↦ hc.lift (Cone.mk W (NatTrans.ofOpSequence (fun n ↦ h ≫ P.proj n)
      fun n ↦ by
        rw [Preadditive.comp_sub, comp_id, sub_eq_zero] at hh
        have hh' : h ≫ t ≫ P.proj n = h ≫ P.proj n := by rw [← Category.assoc, ← hh]
        rw [Category.assoc, ← ht, hh']
        simp)))
    (fun {W} h hh ↦ Fan.IsLimit.hom_ext hP _ _ fun n ↦ by simp)
    (fun {W} h hh m hm ↦ hc.hom_ext fun n ↦ by
      rw [hc.fac]
      simp [← hm])

end CategoryTheory.Limits

namespace ModuleCat

universe u

variable {R : Type u} [Ring R]

end ModuleCat

namespace DerivedCategory

universe u

variable {R : Type u} [CommRing R] [HasDerivedCategory (ModuleCat.{u} R)]

end DerivedCategory
