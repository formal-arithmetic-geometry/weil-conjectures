/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.CategoryTheory.SiteDerivedConstantModuleFunctor
public import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.CategoryTheory.PerfectConstantDerivedMapLocal
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Constant realization reflects isomorphisms on a nondegenerate site object

Source: Stacks Project, Tags 093J, 00WB and 00WK.
(blueprint: lem-sfb-constant-realization-reflects-isomorphism-general).
This is the empty-cover criterion behind the pro-etale specialization, with independent
site, coefficient and derived-localization universes.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v wR wS wU
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R]
variable [HasSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasSheafify J RingCat.{max u v}]

private theorem detects_zero (U : C) (hU : (⊥ : Sieve U) ∉ J U)
    (M : ModuleCat.{max u v} R)
    (hM : IsZero (((siteConstantModuleFunctorGeneral J R).obj M).over U)) :
    IsZero M := by
  let P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
    ((siteConstantModulePresheafGeneral (C := C) R).obj M).presheaf
  have hinj : Function.Injective ((toSheafify J P).app (op U)) := by
    intro a b hab
    have hS := Presheaf.equalizerSieve_mem J (toSheafify J P) a b hab
    by_contra hab'
    apply hU
    convert hS using 1
    ext V g
    simp only [Sieve.bot_apply, Presheaf.equalizerSieve_apply, false_iff]
    change ¬ a = b
    exact hab'
  have : (SheafOfModules.evaluation.{max u v}
      (((constantSheaf J RingCat.{max u v}).obj (RingCat.of R)).over U)
      (op (Over.mk (𝟙 U)))).PreservesZeroMorphisms := ⟨by intros; ext x; rfl⟩
  have hz := (SheafOfModules.evaluation _ (op (Over.mk (𝟙 U)))).map_isZero hM
  have hsub := ModuleCat.subsingleton_of_isZero hz
  change Subsingleton ((sheafify J P).obj (op U)) at hsub
  have := hsub
  have : Subsingleton M := ⟨fun a b ↦ hinj (Subsingleton.elim _ _)⟩
  exact ModuleCat.isZero_of_subsingleton M

variable [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- Exact constant realization reflects a derived isomorphism if its restriction is an
isomorphism on an object not covered by the empty sieve.

Source: Stacks Project, Tags 093J, 00WB, 00WK and derived.tex Tags 05RU and 05RT.
(blueprint: lem-sfb-constant-realization-reflects-isomorphism-general).

Proof: the sheafification unit is injective on U. Indeed, equality of two constant
sections gives a covering equalizer sieve; if the elements differed, this sieve would
be empty, contrary to the hypothesis. A constant module with zero restriction to U
therefore vanishes. Constant realization and restriction are exact, so homology commutes
with their derived functors. The kernel and cokernel of each cohomology map have zero
constant realizations on U and hence vanish. Every cohomology map is thus an isomorphism,
which implies the original derived map is invertible. No boundedness assumption is used. -/
theorem constantRealizationReflectsIsomorphismGeneral (U : C) (hU : (⊥ : Sieve U) ∉ J U)
    [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
    [HasDerivedCategory.{wS} (SheafOfModules.{max u v}
      ((constantSheaf J RingCat.{max u v}).obj (RingCat.of R)))]
    [HasDerivedCategory.{wU}
      (SheafOfModules.{max u v}
        (((constantSheaf J RingCat.{max u v}).obj (RingCat.of R)).over U))]
    {E F : DerivedCategory (ModuleCat.{max u v} R)} (f : E ⟶ F)
    (hf : IsIso ((ringedDerivedRestrictionGeneral.{u, v, max u v, max u v, wS, wU}
        (((constantSheaf J RingCat.{max u v}).obj (RingCat.of R))) U).map
      ((siteDerivedConstantModuleFunctor.{u, v, wR, wS} J R).map f))) : IsIso f := by
  let T := siteConstantModuleFunctorGeneral J R
  have : T.Additive := (siteConstantModuleFunctorGeneral_exact J R).1
  have : PreservesFiniteLimits T := (siteConstantModuleFunctorGeneral_exact J R).2.1
  have : PreservesFiniteColimits T := (siteConstantModuleFunctorGeneral_exact J R).2.2
  let S := ((constantSheaf J RingCat.{max u v}).obj (RingCat.of R))
  let G := SheafOfModules.overFunctor S U
  have : G.Additive := (ringedOverFunctor_exactGeneral S U).1
  have : PreservesFiniteLimits G := (ringedOverFunctor_exactGeneral S U).2.1
  have : PreservesFiniteColimits G := (ringedOverFunctor_exactGeneral S U).2.2
  have comparison (i : ℤ) :
      Nonempty ((T.mapDerivedCategory ⋙ G.mapDerivedCategory ⋙
          DerivedCategory.homologyFunctor _ i) ≅
        (DerivedCategory.homologyFunctor _ i ⋙ T ⋙ G)) := by
    exact ⟨Functor.isoWhiskerLeft _ (G.mapDerivedCategoryHomologyFunctorIso i).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (T.mapDerivedCategoryHomologyFunctorIso i).symm _ ≪≫
      Functor.associator _ _ _⟩
  change IsIso (G.mapDerivedCategory.map (T.mapDerivedCategory.map f)) at hf
  have := hf
  apply (DerivedCategory.isIso_iff (ModuleCat.{max u v} R) f).2
  intro i
  let g := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map f
  have : IsIso ((T ⋙ G).map g) :=
    (NatIso.isIso_map_iff (comparison i).some f).1 (by
      change IsIso ((DerivedCategory.homologyFunctor _ i).map
        (G.mapDerivedCategory.map (T.mapDerivedCategory.map f)))
      infer_instance)
  have hk : IsZero ((T ⋙ G).obj (kernel g)) :=
    (isZero_kernel_of_mono ((T ⋙ G).map g)).of_iso (PreservesKernel.iso (T ⋙ G) g)
  have hc : IsZero ((T ⋙ G).obj (cokernel g)) :=
    (isZero_cokernel_of_epi ((T ⋙ G).map g)).of_iso (PreservesCokernel.iso (T ⋙ G) g)
  have : Mono g := Preadditive.mono_of_isZero_kernel g
    (detects_zero J R U hU (kernel g) hk)
  have : Epi g := Preadditive.epi_of_isZero_cokernel g
    (detects_zero J R U hU (cokernel g) hc)
  exact isIso_of_mono_of_epi g
end CategoryTheory


namespace CategoryTheory

private theorem exists_nondegenerate_cover_member
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (X : C)
    (hX : (⊥ : Sieve X) ∉ J X) {I : Type*} (U : I → C) (f : ∀ i, U i ⟶ X)
    (hf : Sieve.generate (Presieve.ofArrows U f) ∈ J X) :
    ∃ i, (⊥ : Sieve (U i)) ∉ J (U i) := by
  classical
  by_contra h
  push Not at h
  apply hX
  apply J.transitive hf ⊥
  rintro V g ⟨Y, a, b, hb, rfl⟩
  cases hb with
  | mk i => simpa using J.pullback_stable a (h i)

/-- Perfectness of a constant complex is reflected on a site with a nondegenerate
terminal object, without imposing a common site and coefficient universe.

Source: Stacks Project, Tags 09BE and 09C5, first proof paragraph.
(blueprint: lem-sfb-constant-realization-reflects-isomorphism-general).

Proof: locally lift the isomorphism out of the perfect constant complex to an algebraic
map. Some covering member is not covered by the empty sieve: otherwise the transitivity
condition would make the empty sieve cover the terminal object. On this member, the lifted
map realizes an isomorphism. The preceding conservativity result makes the algebraic
map invertible. Transport the bounded finite-projective representative along this map. -/
theorem perfect_of_constant_realization_iso
    {C : Type u} [Category.{v} C] (J : Precoverage C) (hJ : J.IsSiteForCoverings)
    (X : C) (hX : IsTerminal X) (hX' : (⊥ : Sieve X) ∉ J.toGrothendieck X)
    (R : Type (max u v)) [CommRing R]
    [HasSheafify J.toGrothendieck AddCommGrpCat.{max u v}]
    [J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasSheafify J.toGrothendieck RingCat.{max u v}]
    [∀ U : C, HasSheafify (J.toGrothendieck.over U) AddCommGrpCat.{max u v}]
    [∀ U : C, (J.toGrothendieck.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
    [HasDerivedCategory.{wR} (ModuleCat.{max u v} R)]
    [siteModuleHasDerivedCategory.{u, v, wS}
      ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R))]
    [∀ U : C, siteModuleHasDerivedCategory.{max u v, v, wU}
      (((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)).over U)]
    (P L : DerivedCategory (ModuleCat.{max u v} R))
    (hP : DerivedCategory.IsPerfectRingComplex P)
    (e : Nonempty
      ((siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).obj P ≅
        (siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).obj L)) :
    DerivedCategory.IsPerfectRingComplex L := by
  obtain ⟨e⟩ := e
  obtain ⟨I, U, f, hf, hlocal⟩ :=
    exists_perfect_constant_derived_map_local.{u, v, wR, wS, wU} J hJ X hX R P L hP e.hom
  obtain ⟨i, hi⟩ := exists_nondegenerate_cover_member J.toGrothendieck X hX' U f
    (J.generate_mem_toGrothendieck hf)
  obtain ⟨α, hα⟩ := hlocal i
  have hαiso : IsIso ((ringedDerivedRestrictionGeneral.{u, v, max u v, max u v, wS, wU}
      ((constantSheaf J.toGrothendieck RingCat.{max u v}).obj (RingCat.of R)) (U i)).map
      ((siteDerivedConstantModuleFunctor.{u, v, wR, wS} J.toGrothendieck R).map α)) := by
    dsimp only [ringedDerivedRestrictionSized] at hα
    rw [← hα]
    infer_instance
  have : IsIso α :=
    constantRealizationReflectsIsomorphismGeneral.{u, v, wR, wS, wU} 
      J.toGrothendieck R (U i) hi α hαiso
  obtain ⟨F, a, b, ha, hb, hterms, ⟨eP⟩⟩ := hP
  exact ⟨F, a, b, ha, hb, hterms, ⟨(asIso α).symm ≪≫ eP⟩⟩

end CategoryTheory
