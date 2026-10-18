/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.CategoryTheory.RingedSiteCompleteElement
import Sheaf.CategoryTheory.RingedSiteCompleteElementRestriction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! Locality of the localization-Hom vanishing criterion. -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

set_option autoImplicit false

namespace CategoryTheory

private theorem sheaf_zero_of_cover
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (U : C) (S : Sieve U) (hS : S ∈ J U)
    (M : SheafOfModules.{u} (R.over U))
    (hM : ∀ (V : C) (a : V ⟶ U), S a →
      IsZero ((SheafOfModules.overMap R a).obj M)) : IsZero M := by
  apply (IsZero.iff_id_eq_zero _).mpr
  ext X x
  change x = 0
  let T : Sieve X.unop := (Sieve.overEquiv X.unop).symm (S.pullback X.unop.hom)
  have hT : T ∈ J.over U X.unop :=
    J.overEquiv_symm_mem_over X.unop _ (J.pullback_stable X.unop.hom hS)
  apply M.isSheaf.isSeparated X.unop T hT x 0
  intro Y b hb
  have ha : S Y.hom := by
    change S (b.left ≫ X.unop.hom) at hb
    simpa only [Over.w b] using hb
  have hz := (IsZero.iff_id_eq_zero _).mp (hM Y.left Y.hom ha)
  have hx := ConcreteCategory.congr_hom
    (congrArg (fun t ↦ t.val.app (op (Over.mk (𝟙 Y.left)))) hz)
  dsimp at hx
  change ∀ y : M.val.obj (op (Over.mk ((𝟙 Y.left) ≫ Y.hom))), y = 0 at hx
  have hy : Over.mk ((𝟙 Y.left) ≫ Y.hom) = Y := by
    simpa only [Category.id_comp, Over.mk] using (CostructuredArrow.eq_mk Y).symm
  rw [hy] at hx
  change M.val.map b.op x = M.val.map b.op 0
  exact (hx _).trans (map_zero _).symm

/-- The localization-Hom vanishing criterion can be checked on any covering sieve.

Source: Stacks Project, algebraization.tex, Tag 0998, and sites-cohomology.tex, Tag 08JB.
(blueprint: lem-weil-pbc-ringed-complete-element-local).

Proof: Exact slice restriction identifies the restriction of
RHom(O_U[1/f], K|U) along a : V → U with
RHom(O_V[1/(f|V)], K|V). The coefficient comparison is induced by restricting
fractions, or equivalently the sequential colimit; the comparison for K follows
from the canonical composition of restrictions. Hence vanishing implies vanishing
on each member of a sieve. Conversely, assume the displayed vanishing on a covering
sieve. Slice restriction commutes with cohomology because it is exact. Thus every
cohomology sheaf of the original derived Hom restricts to zero on this sieve.
Over an arbitrary W → U, pull back the sieve, which remains covering. Every
section of the cohomology sheaf restricts to zero on that covering sieve and
vanishes by the separatedness axiom. Therefore every cohomology sheaf is zero,
and the derived Hom is zero. This also covers empty covering sieves.
-/
theorem ringedSite_complete_element_local
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))]
    [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).over U))]
    (K : DerivedCategory (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))) (U : C) (S : Sieve U) (hS : S ∈ J U)
    (f : R.obj.obj (op U)) :
    IsRingedSiteCompleteElement J R K U f ↔
      ∀ (V : C) (a : V ⟶ U), S a →
        IsRingedSiteCompleteElement J R K V (R.obj.map a.op f) := by
  let R₀ := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
  let : ∀ W : C, HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over W) (forget₂ CommRingCat RingCat)).obj (R.over W))) :=
    fun W ↦ inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u} (R₀.over W)))
  let H := (derivedInternalHom (J.over U) (R.over U)).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj (ringedSiteSectionLocalization R₀ U f)),
      ringedSiteDerivedRestriction R₀ U K)
  change IsZero H ↔ _
  constructor
  · intro hH V a _
    obtain ⟨e⟩ := ringedSite_complete_element_restriction J R K U V a f
    exact (((SheafOfModules.overMap.{u} R₀ a).mapDerivedCategory).map_isZero hH).of_iso e.symm
  · intro h
    apply DerivedCategory.isZero_of_forall_isZero_homology
    intro n
    apply sheaf_zero_of_cover R₀ U S hS
    intro V a ha
    obtain ⟨e⟩ := ringedSite_complete_element_restriction J R K U V a f
    have hz : IsZero (((SheafOfModules.overMap.{u} R₀ a).mapDerivedCategory).obj H) :=
      (h V a ha).of_iso e
    exact ((DerivedCategory.homologyFunctor _ n).map_isZero hz).of_iso
      (((SheafOfModules.overMap.{u} R₀ a).mapDerivedCategoryHomologyFunctorIso n).app H)

end CategoryTheory
