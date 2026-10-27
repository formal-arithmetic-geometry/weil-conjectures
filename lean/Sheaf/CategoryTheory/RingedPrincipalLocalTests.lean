/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import Sheaf.CategoryTheory.RingedSectionLocalizationOfUniverses
public import Sheaf.Algebra.Homology.SitePerfectModelRestriction

/-! # Principal local tests with independent site and coefficient universes

Source: Stacks 0999.
(blueprint: def-pur-ringed-principal-local-tests). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

/-- Restrict one section to all objects of its slice.
Source: Stacks 0999.
(blueprint: def-pur-ringed-principal-local-tests). -/
def principalSliceSection {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{max c v r})
    (U : C) (x : R.obj.obj (op U)) :
    ((R.over U).obj ⋙ forget CommRingCat).sections where
  val X := R.obj.map X.unop.hom.op x
  property {X Y} f := by
    change R.obj.map f.unop.left.op (R.obj.map X.unop.hom.op x) =
      R.obj.map Y.unop.hom.op x
    rw [← ConcreteCategory.comp_apply, ← R.obj.map_comp, ← op_comp, Over.w]

/-- A section on a slice is determined by its value on the terminal object.
Source: Stacks 0999.
(blueprint: def-pur-ringed-principal-local-tests).
Proof: naturality for the unique arrow from an object to the identity arrow. -/
theorem principalSliceSection_eta {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{max c v r})
    (U : C) (s : ((R.over U).obj ⋙ forget CommRingCat).sections) :
    s = principalSliceSection.{c, v, r} R U (s.val (op (Over.mk (𝟙 U)))) := by
  ext X
  have h := s.property (show op (Over.mk (𝟙 U)) ⟶ X from
    (Over.homMk X.unop.hom (by simp)).op)
  exact h.symm

/-- Local divisibility by the principal generator, expressed by a covering sieve.
Source: Stacks 0999.
(blueprint: def-pur-ringed-principal-local-tests). -/
def principalLocallyDivisible {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{max c v r})
    (a : (R.obj ⋙ forget CommRingCat).sections) (U : C)
    (s : ((R.over U).obj ⋙ forget CommRingCat).sections) : Prop :=
  ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (f : V ⟶ U), S f →
    ∃ b : R.obj.obj (op V),
      s.val (op (Over.mk f)) = (show R.obj.obj (op V) from a.val (op V)) * b

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max c v r}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ U : C, HasSheafify (J.over U) CommRingCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

set_option hygiene false in
local notation "Rg" =>
  (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R

variable [HasDerivedCategory.{w} (SheafOfModules.{max c v r} Rg)]
  [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((Rg).over U))]

/-- The localization test using exact derived restriction.
Source: Stacks 0999.
(blueprint: def-pur-ringed-principal-local-tests). -/
def principalLocalTest (N : DerivedCategory (SheafOfModules.{max c v r} Rg))
    (U : C) (s : ((R.over U).obj ⋙ forget CommRingCat).sections) :
    DerivedCategory (SheafOfModules.{max c v r} ((Rg).over U)) :=
  letI := (SheafOfModules.overFunctor_exact_ofUniverses.{c, v, max c v r} Rg U).1
  letI := (SheafOfModules.overFunctor_exact_ofUniverses.{c, v, max c v r} Rg U).2
  letI : HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj (R.over
        U))) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((Rg).over U)))
  (derivedInternalHomOfUniverses.{max c v, v, max c v r, w}
    (J.over U) (R.over U)).obj
      (op ((DerivedCategory.singleFunctor _ 0).obj
        (ringedSectionLocalizationOfUniverses (R.over U) s)),
        (SheafOfModules.overFunctor.{max c v r} Rg U).mapDerivedCategory.obj N)

/-- Vanishing for sections locally divisible by the specified compatible section.
Source: Stacks 0999.
(blueprint: def-pur-ringed-principal-local-tests). -/
def principalLocallyComplete (a : (R.obj ⋙ forget CommRingCat).sections)
    (N : DerivedCategory (SheafOfModules.{max c v r} Rg)) : Prop :=
  ∀ (U : C) (s : ((R.over U).obj ⋙ forget CommRingCat).sections),
    principalLocallyDivisible.{c, v, r} R a U s →
    IsZero (principalLocalTest.{c, v, r, w} R N U s)

/-- Principal local completeness is invariant under isomorphism of derived objects.
Source: Stacks 0999.
(blueprint: def-pur-ringed-principal-local-tests).
Proof: exact derived restriction and internal Hom carry an isomorphism in the
second argument to an isomorphism of each localization test; zero objects are
invariant under this isomorphism. Apply the construction in both directions. -/
theorem principalLocallyComplete_iso
    (a : (R.obj ⋙ forget CommRingCat).sections)
    {N M : DerivedCategory (SheafOfModules.{max c v r} Rg)} (e : N ≅ M) :
    principalLocallyComplete.{c, v, r, w} R a N ↔
      principalLocallyComplete.{c, v, r, w} R a M := by
  have ht (U : C) (s : ((R.over U).obj ⋙ forget CommRingCat).sections) :
      principalLocalTest.{c, v, r, w} R N U s ≅
        principalLocalTest.{c, v, r, w} R M U s := by
    letI := (SheafOfModules.overFunctor_exact_ofUniverses.{c, v, max c v r} Rg U).1
    letI := (SheafOfModules.overFunctor_exact_ofUniverses.{c, v, max c v r} Rg U).2
    letI : HasDerivedCategory.{w} (SheafOfModules.{max c v r}
        ((sheafCompose (J.over U) (forget₂ CommRingCat.{max c v r}
          RingCat.{max c v r})).obj (R.over U))) := inferInstanceAs
      (HasDerivedCategory.{w} (SheafOfModules.{max c v r} ((Rg).over U)))
    exact (derivedInternalHomOfUniverses.{max c v, v, max c v r, w}
      (J.over U) (R.over U)).mapIso ((Iso.refl _).prod
        ((SheafOfModules.overFunctor.{max c v r} Rg U).mapDerivedCategory.mapIso e))
  constructor
  · intro h U s hs
    exact (h U s hs).of_iso (ht U s).symm
  · intro h U s hs
    exact (h U s hs).of_iso (ht U s)

end CategoryTheory
