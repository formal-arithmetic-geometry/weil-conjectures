/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.Adjunctions
public import Submission.WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Section localization with independent site universes

Source: Stacks Project, algebraization.tex, Tags 0996 and 099E
(blueprint: def-weil-pbc-ringed-section-localization).
The construction is the same sectionwise localization followed by sheafification.
This interface allows a site with different object and morphism universes. Sheafification
is parameterized by its existing instances in the chosen coefficient universe. The previous
small-category interface is retained by the public import.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uC vC

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (O : Sheaf J CommRingCat.{u})

set_option linter.unusedSectionVars false in
/-- The sectionwise units form a section of the localization presheaf.
Source: Stacks Project, algebraization.tex, Tag 0996
(blueprint: def-weil-pbc-ringed-section-localization).
Proof: the restriction maps are ring homomorphisms and therefore preserve one. -/
theorem ringedSectionLocalizationPresheaf_one_naturalOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) {X Y : Cᵒᵖ} (a : X ⟶ Y) :
    (ringedSectionLocalizationPresheafOfUniverses O s).map a
      (1 : ringedSectionLocalizationCarrierOfUniverses O s X) =
        (1 : ringedSectionLocalizationCarrierOfUniverses O s Y) := by
  exact (ringedSectionLocalizationMapOfUniverses O s a).map_one

/-- The canonical map from the ring sheaf to its localization as a module sheaf.
Source: Stacks Project, algebraization.tex, Tag 0996
(blueprint: def-weil-pbc-ringed-section-localization). -/
def ringedSectionLocalizationUnitOfUniverses
    (s : (O.obj ⋙ forget CommRingCat).sections) :
    SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) ⟶
      ringedSectionLocalizationOfUniverses O s :=
  (SheafOfModules.fullyFaithfulForget _).preimage
    ((ringedSectionLocalizationPresheafOfUniverses O s).unitHomEquiv.symm
      (PresheafOfModules.sectionsMk
        (fun X ↦ (1 : ringedSectionLocalizationCarrierOfUniverses O s X))
        (fun {_ _} a ↦ ringedSectionLocalizationPresheaf_one_naturalOfUniverses O s a)) ≫
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).obj)).unit.app
          (ringedSectionLocalizationPresheafOfUniverses O s))

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasSheafify J CommRingCat.{u}]
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable (R : Sheaf J CommRingCat.{u})
variable (s : (R.obj ⋙ forget CommRingCat).sections)

section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option linter.unusedSectionVars false

/- The additive sheafification has a canonical multiplication: multiply local representatives
and glue. Local injectivity makes the product independent of the representatives. The ring laws
and the compatibility of lifts are checked on covering sieves. This realizes the sheafification
argument in the comparison theorem below without identifying the site and coefficient universes. -/
namespace RingedLocalizationComparison

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable {P : Cᵒᵖ ⥤ CommRingCat.{u}} {A : Sheaf J AddCommGrpCat.{u}}
variable (η : (P ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶ A.obj)
variable [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η]

private lemma natural {X Y : Cᵒᵖ} (f : X ⟶ Y) (p : P.obj X) :
    η.app Y (P.map f p) = A.obj.map f (η.app X p) :=
  NatTrans.naturality_apply η f p

private lemma ext {X : Cᵒᵖ} {x y : A.obj.obj X} (S : Sieve X.unop) (hS : S ∈ J X.unop)
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X.unop), S g → A.obj.map g.op x = A.obj.map g.op y) :
    x = y :=
  A.isSeparated _ _ hS x y (fun _ g hg ↦ h g hg)

private lemma image_ext {X : Cᵒᵖ} (a b c : A.obj.obj X) {x y : A.obj.obj X}
    (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X.unop) (p q r : P.obj (op Y)),
      η.app _ p = A.obj.map g.op a → η.app _ q = A.obj.map g.op b →
      η.app _ r = A.obj.map g.op c → A.obj.map g.op x = A.obj.map g.op y) : x = y := by
  refine ext (Presheaf.imageSieve η a ⊓ Presheaf.imageSieve η b ⊓
    Presheaf.imageSieve η c) (J.intersection_covering (J.intersection_covering
      (Presheaf.imageSieve_mem J η a) (Presheaf.imageSieve_mem J η b))
      (Presheaf.imageSieve_mem J η c)) ?_
  rintro Y g ⟨⟨⟨p, hp⟩, ⟨q, hq⟩⟩, ⟨r, hr⟩⟩
  exact h g p q r hp hq hr

private lemma mul_eq {X : Cᵒᵖ} {p p' q q' : P.obj X}
    (hp : η.app X p = η.app X p') (hq : η.app X q = η.app X q') :
    η.app X (p * q) = η.app X (p' * q') := by
  refine ext _ (J.intersection_covering
    (Presheaf.equalizerSieve_mem J η p p' hp)
    (Presheaf.equalizerSieve_mem J η q q' hq)) ?_
  rintro Y g ⟨hg, hg'⟩
  rw [← natural η, ← natural η]
  rw [(P.map g.op).hom.map_mul, (P.map g.op).hom.map_mul]
  have hg : P.map g.op p = P.map g.op p' := hg
  have hg' : P.map g.op q = P.map g.op q' := hg'
  rw [hg, hg']

private def mulFamily {X : Cᵒᵖ} (a b : A.obj.obj X) :
    Presieve.FamilyOfElements (A.obj ⋙ forget AddCommGrpCat.{u})
      (Presheaf.imageSieve η a ⊓ Presheaf.imageSieve η b).arrows :=
  fun Y _ h ↦ η.app _ ((show P.obj (op Y) from h.1.choose) *
    (show P.obj (op Y) from h.2.choose))

private lemma mulFamily_compatible {X : Cᵒᵖ} (a b : A.obj.obj X) :
    (mulFamily η a b).Compatible := by
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hcomm
  dsimp only [mulFamily]
  erw [← natural η, ← natural η]
  change η.app _ ((P.map g₁.op) (_ * _)) = η.app _ ((P.map g₂.op) (_ * _))
  rw [(P.map g₁.op).hom.map_mul, (P.map g₂.op).hom.map_mul]
  apply mul_eq η
  · rw [natural η, natural η,
      h₁.1.choose_spec, h₂.1.choose_spec, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]
  · rw [natural η, natural η,
      h₁.2.choose_spec, h₂.2.choose_spec, ← Functor.map_comp_apply,
      ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomm]

private def mul {X : Cᵒᵖ} (a b : A.obj.obj X) : A.obj.obj X :=
  ((show Presieve.IsSheaf J (A.obj ⋙ forget AddCommGrpCat.{u}) from
    (isSheaf_iff_isSheaf_of_type J _).1
      ((sheafCompose J (forget AddCommGrpCat.{u})).obj A).property) _
      (J.intersection_covering (Presheaf.imageSieve_mem J η a)
        (Presheaf.imageSieve_mem J η b))).amalgamate
    (mulFamily η a b) (mulFamily_compatible η a b)

private lemma map_mul' {X : Cᵒᵖ} {Y : C} (a b : A.obj.obj X) (g : Y ⟶ X.unop)
    (p q : P.obj (op Y))
    (hp : η.app _ p = A.obj.map g.op a) (hq : η.app _ q = A.obj.map g.op b) :
    A.obj.map g.op (mul η a b) = η.app _ (p * q) := by
  have hS := J.intersection_covering (Presheaf.imageSieve_mem J η a)
    (Presheaf.imageSieve_mem J η b)
  refine ext _ (J.pullback_stable g hS) ?_
  intro Z h hh
  rw [← Functor.map_comp_apply, ← op_comp, mul]
  have hv := Presieve.IsSheafFor.valid_glue
    ((show Presieve.IsSheaf J (A.obj ⋙ forget AddCommGrpCat.{u}) from
      (isSheaf_iff_isSheaf_of_type J _).1
        ((sheafCompose J (forget AddCommGrpCat.{u})).obj A).property) _ hS)
      (mulFamily_compatible η a b) (h ≫ g) hh
  change A.obj.map (h ≫ g).op _ = _ at hv
  rw [hv]
  rw [← natural η]
  change η.app _ (_ * _) = η.app _ ((P.map h.op) (p * q))
  rw [(P.map h.op).hom.map_mul]
  apply mul_eq η
  · rw [hh.1.choose_spec, natural η, hp,
      ← Functor.map_comp_apply, ← op_comp]
  · rw [hh.2.choose_spec, natural η, hq,
      ← Functor.map_comp_apply, ← op_comp]

private lemma mul_comm' {X : Cᵒᵖ} (a b : A.obj.obj X) : mul η a b = mul η b a := by
  apply image_ext η a b 0
  intro Y g p q r hp hq hr
  rw [map_mul' η a b g p q hp hq, map_mul' η b a g q p hq hp, mul_comm]

private lemma mul_assoc' {X : Cᵒᵖ} (a b c : A.obj.obj X) :
    mul η (mul η a b) c = mul η a (mul η b c) := by
  apply image_ext η a b c
  intro Y g p q r hp hq hr
  rw [map_mul' η (mul η a b) c g (p * q) r (map_mul' η a b g p q hp hq).symm hr,
    map_mul' η a (mul η b c) g p (q * r) hp (map_mul' η b c g q r hq hr).symm,
    mul_assoc]

private lemma one_mul' {X : Cᵒᵖ} (a : A.obj.obj X) : mul η (η.app X (1 : P.obj X)) a = a := by
  apply image_ext η a 0 0
  intro Y g p q r hp hq hr
  rw [map_mul' η (η.app X (1 : P.obj X)) a g 1 p (by rw [← natural η]; simp) hp, one_mul, hp]

private lemma mul_add' {X : Cᵒᵖ} (a b c : A.obj.obj X) :
    mul η a (b + c) = mul η a b + mul η a c := by
  apply image_ext η a b c
  intro Y g p q r hp hq hr
  rw [(A.obj.map g.op).hom.map_add,
    map_mul' η a b g p q hp hq, map_mul' η a c g p r hp hr,
    map_mul' η a (b + c) g p (q + r) hp
      (by rw [(η.app _).hom.map_add, (A.obj.map g.op).hom.map_add, hq, hr]),
    mul_add, (η.app _).hom.map_add]

private lemma zero_mul' {X : Cᵒᵖ} (a : A.obj.obj X) : mul η 0 a = 0 := by
  apply image_ext η a 0 0
  intro Y g p q r hp hq hr
  rw [map_mul' η 0 a g 0 p (by simp) hp, zero_mul,
    (η.app _).hom.map_zero, (A.obj.map g.op).hom.map_zero]

@[instance_reducible]
private def ring (X : Cᵒᵖ) : CommRing (A.obj.obj X) where
  toAddCommGroup := inferInstance
  one := η.app X (1 : P.obj X)
  mul := mul η
  mul_assoc := mul_assoc' η
  mul_comm := mul_comm' η
  one_mul := one_mul' η
  mul_one a := (mul_comm' η a _).trans (one_mul' η a)
  right_distrib a b c := (mul_comm' η _ c).trans
    ((mul_add' η c a b).trans (congrArg₂ (· + ·) (mul_comm' η c a) (mul_comm' η c b)))
  left_distrib := mul_add' η
  zero_mul := zero_mul' η
  mul_zero a := (mul_comm' η a _).trans (zero_mul' η a)

variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

private lemma comparison {B : Sheaf J RingCat.{u}}
    (P : PresheafOfModules.{u} B.obj) (A : SheafOfModules.{u} B)
    (φ : P ⟶ A.val)
    [PresheafOfModules.IsLocallyInjective J φ]
    [PresheafOfModules.IsLocallySurjective J φ] :
    ∃ e : A ≅ (PresheafOfModules.sheafification (𝟙 B.obj)).obj P,
      φ ≫ e.hom.val = (PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P := by
  let S := (PresheafOfModules.sheafification (𝟙 B.obj)).obj P
  let η : P ⟶ S.val := (PresheafOfModules.sheafificationAdjunction (𝟙 B.obj)).unit.app P
  let g : S ⟶ A := (PresheafOfModules.sheafificationHomEquiv (𝟙 B.obj)).symm φ
  have hg : η ≫ g.val = φ := by
    exact (PresheafOfModules.sheafificationHomEquiv (𝟙 B.obj)).apply_symm_apply φ
  let f : A ⟶ S := ⟨(PresheafOfModules.homEquivOfIsLocallyBijective
    (f := φ) S.isSheaf).symm η⟩
  have hf : φ ≫ f.val = η := by
    exact (PresheafOfModules.homEquivOfIsLocallyBijective
      (f := φ) S.isSheaf).apply_symm_apply η
  have hfg : f ≫ g = 𝟙 A := by
    apply (SheafOfModules.fullyFaithfulForget _).map_injective
    apply (PresheafOfModules.homEquivOfIsLocallyBijective (f := φ) A.isSheaf).injective
    change φ ≫ (f.val ≫ g.val) = φ ≫ 𝟙 A.val
    rw [← Category.assoc, hf, hg, Category.comp_id]
  have hgf : g ≫ f = 𝟙 S := by
    apply (PresheafOfModules.sheafificationHomEquiv (𝟙 B.obj)).injective
    change η ≫ (g.val ≫ f.val) = η ≫ 𝟙 S.val
    rw [← Category.assoc, hg, hf, Category.comp_id]
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

end RingedLocalizationComparison

end

end CategoryTheory
