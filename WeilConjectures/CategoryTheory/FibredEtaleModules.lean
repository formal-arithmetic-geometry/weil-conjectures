/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FibredRelativeCech
public import WeilConjectures.AlgebraicGeometry.StackBigEtaleModuleFunctors
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! # Modules on the big etale site of a fibred groupoid

Source: Stacks Project, stacks-sheaves.tex, Tags 06TV, 06WX and 06X7
(blueprint: def-sfb-fibred-big-etale-modules).

The module category, precomposition, direct image and higher images are the shared
Q22 interface. This module supplies only composition and canonical relative nerve
restriction constructions on that interface.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- Additivity of the shared precomposition, inherited from sectionwise module maps.
Source: Stacks 06WE (blueprint: def-sfb-fibred-big-etale-modules). -/
instance fibredEtalePrecomposition_additive
    {X Y : BasedCategory.{v, w} (Over S)}
    (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y) (a : BasedFunctor X Y) :
    (moduliBigEtalePrecomposition.{u, v, w} hX hY a).Additive where
  map_add := rfl

/-- Expose the defining right-adjoint instance of the shared direct image.
Source: Stacks 06WE (blueprint: def-sfb-fibred-big-etale-modules). -/
instance fibredEtaleDirectImage_isRightAdjoint
    {X Y : BasedCategory.{v, w} (Over S)}
    (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y) (a : BasedFunctor X Y) :
    (moduliBigEtaleDirectImage.{u, v, w} hX hY a).IsRightAdjoint :=
  (Adjunction.ofIsLeftAdjoint (moduliBigEtalePrecomposition.{u, v, w} hX hY a)).isRightAdjoint

/-- Precomposition respects composition strictly, including the canonical ring transport.
Source: Stacks 06WX (blueprint: def-sfb-fibred-big-etale-modules).
Proof: on each object and arrow both sides are iterated precomposition; the two
regular-function transports are equal by a.w and b.w and proof irrelevance. -/
theorem fibredEtaleInverse_comp
    {X Y Z : BasedCategory.{v, max (u + 1) v w} (Over S)}
    (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
    (hZ : IsFibredInGroupoids Z) (a : BasedFunctor X Y) (b : BasedFunctor Y Z) :
    moduliBigEtalePrecomposition.{u, v, max (u + 1) v w} hX hZ (a.comp b) =
      moduliBigEtalePrecomposition.{u, v, max (u + 1) v w} hY hZ b ⋙
      moduliBigEtalePrecomposition.{u, v, max (u + 1) v w} hX hY a := by
  sorry



/-- The relative module term for a test stack over X and direct image along f.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-big-etale-modules). -/
def fibredEtaleRelativeTerm
    {A X Y : BasedCategory.{v, max (u + 1) v w} (Over S)}
    (hA : IsFibredInGroupoids A) (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (a : BasedFunctor A X) (f : BasedFunctor X Y) :=
  moduliBigEtalePrecomposition.{u, v, max (u + 1) v w} hA hX a ⋙
    moduliBigEtaleDirectImage.{u, v, max (u + 1) v w} hA hY (a.comp f)

/-- Additivity of the relative term is inherited from its two factors.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-big-etale-modules). -/
instance fibredEtaleRelativeTerm_additive
    {A X Y : BasedCategory.{v, max (u + 1) v w} (Over S)}
    (hA : IsFibredInGroupoids A) (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (a : BasedFunctor A X) (f : BasedFunctor X Y) :
    (fibredEtaleRelativeTerm.{u, v, w} hA hX hY a f).Additive :=
  inferInstanceAs ((moduliBigEtalePrecomposition.{u, v, max (u + 1) v w} hA hX a ⋙
    moduliBigEtaleDirectImage.{u, v, max (u + 1) v w} hA hY (a.comp f)).Additive)

/-- Restriction on compatible sections, as the mate of the precomposition counit.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-big-etale-modules). -/
def fibredEtaleRelativeRestrictionApp
    {B A X Y : BasedCategory.{v, max (u + 1) v w} (Over S)}
    (hB : IsFibredInGroupoids B) (hA : IsFibredInGroupoids A)
    (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
    (d : BasedFunctor B A) (a : BasedFunctor A X) (f : BasedFunctor X Y)
    (M : ModuliBigEtaleModules.{u, v, max (u + 1) v w} X hX) :
    (fibredEtaleRelativeTerm.{u, v, w} hA hX hY a f).obj M ⟶
      (fibredEtaleRelativeTerm.{u, v, w} hB hX hY (d.comp a) f).obj M :=
  ((Adjunction.ofIsLeftAdjoint
    (moduliBigEtalePrecomposition.{u, v, max (u + 1) v w} hB hY ((d.comp a).comp f))).homEquiv _ _)
    (eqToHom (Functor.congr_obj
      (fibredEtaleInverse_comp.{u, v, w} hB hA hY d (a.comp f)) _) ≫
      (moduliBigEtalePrecomposition.{u, v, max (u + 1) v w} hB hA d).map
        ((Adjunction.ofIsLeftAdjoint
          (moduliBigEtalePrecomposition.{u, v, max (u + 1) v w} hA hY (a.comp f))).counit.app
          ((moduliBigEtalePrecomposition.{u, v, max (u + 1) v w} hA hX a).obj M)) ≫
      eqToHom (Functor.congr_obj
        (fibredEtaleInverse_comp.{u, v, w} hB hA hX d a).symm M))

/-- Compatible-section restriction is natural in the coefficient module.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-big-etale-modules).
Proof: both adjuncts evaluate a compatible family on its image under d.
Coefficient maps commute with every restriction. Adjunction injectivity gives
naturality, equivalently naturality of its counit and of precomposition. -/
theorem fibredEtaleRelativeRestriction_naturality
    {B A X Y : BasedCategory.{v, max (u + 1) v w} (Over S)}
    (hB : IsFibredInGroupoids B) (hA : IsFibredInGroupoids A)
    (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
    (d : BasedFunctor B A) (a : BasedFunctor A X) (f : BasedFunctor X Y)
    {M N : ModuliBigEtaleModules.{u, v, max (u + 1) v w} X hX} (k : M ⟶ N) :
    (fibredEtaleRelativeTerm.{u, v, w} hA hX hY a f).map k ≫
        fibredEtaleRelativeRestrictionApp.{u, v, w} hB hA hX hY d a f N =
      fibredEtaleRelativeRestrictionApp.{u, v, w} hB hA hX hY d a f M ≫
        (fibredEtaleRelativeTerm.{u, v, w} hB hX hY (d.comp a) f).map k := by
  sorry

/-- The coefficient-natural restriction of compatible families.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-big-etale-modules). -/
def fibredEtaleRelativeRestriction
    {B A X Y : BasedCategory.{v, max (u + 1) v w} (Over S)}
    (hB : IsFibredInGroupoids B) (hA : IsFibredInGroupoids A)
    (hX : IsFibredInGroupoids X) (hY : IsFibredInGroupoids Y)
    (d : BasedFunctor B A) (a : BasedFunctor A X) (f : BasedFunctor X Y) :
    fibredEtaleRelativeTerm.{u, v, w} hA hX hY a f ⟶
      fibredEtaleRelativeTerm.{u, v, w} hB hX hY (d.comp a) f where
  app := fibredEtaleRelativeRestrictionApp.{u, v, w} hB hA hX hY d a f
  naturality _ _ k := fibredEtaleRelativeRestriction_naturality.{u, v, w} hB hA hX hY d a f k

/-- The p-th nerve is the existing common-target tuple category of p+1 entries.
This presentation also works in degree zero, where it is equivalent over X to U.
Source: Stacks 06X3 (blueprint: def-sfb-fibred-big-etale-modules). -/
def fibredModuleCechLevel
    {U X : BasedCategory.{v, max (u + 1) v w} (Over S)} (a : BasedFunctor U X) (p : ℕ) :
    BasedCategory.{v, max (u + 1) v w} (Over S) :=
  BasedCategory.ofFunctor
    (fibredCechTupleProjection.{u, v, max (u + 1) w} a (p + 1) ⋙ X.p)

/-- Projection from the actual nerve presentation to its common target.
Source: Stacks 06X3 (blueprint: def-sfb-fibred-big-etale-modules). -/
def fibredModuleCechProjection
    {U X : BasedCategory.{v, max (u + 1) v w} (Over S)} (a : BasedFunctor U X) (p : ℕ) :
    BasedFunctor (fibredModuleCechLevel.{u, v, w} a p) X where
  toFunctor := fibredCechTupleProjection.{u, v, max (u + 1) w} a (p + 1)
  w := rfl

/-- Delete entry j, retaining the common target and its projection strictly.
Source: Stacks 06X3 (blueprint: def-sfb-fibred-big-etale-modules). -/
def fibredModuleCechFace
    {U X : BasedCategory.{v, max (u + 1) v w} (Over S)} (a : BasedFunctor U X)
    (p : ℕ) (j : Fin (p + 2)) :
    BasedFunctor (fibredModuleCechLevel.{u, v, w} a (p + 1))
      (fibredModuleCechLevel.{u, v, w} a p) where
  toFunctor := fibredCechTupleReindex.{u, v, max (u + 1) w} a j.succAbove
  w := rfl

/-- The nerve levels remain fibred groupoids, including the empty test scheme.
Source: Stacks 06X3 (blueprint: def-sfb-fibred-big-etale-modules).
Proof: lift a base arrow in each entry and in the common target. The cartesian
universal property uniquely lifts all vertical comparison isomorphisms. It also
proves the strong cartesian property for every tuple arrow, componentwise. -/
theorem fibredModuleCechLevel_isFibred
    {U X : BasedCategory.{v, max (u + 1) v w} (Over S)}
    (hU : IsFibredInGroupoids U) (hX : IsFibredInGroupoids X) (a : BasedFunctor U X)
    (p : ℕ) : IsFibredInGroupoids (fibredModuleCechLevel.{u, v, w} a p) := by
  sorry

/-- Cech term, as a functor in all module sheaves on X.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-big-etale-modules). -/
def fibredModuleCechTerm
    {U X Y : BasedCategory.{v, max (u + 1) v w} (Over S)}
    (hU : IsFibredInGroupoids U) (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (a : BasedFunctor U X) (f : BasedFunctor X Y) (p : ℕ) :=
  fibredEtaleRelativeTerm.{u, v, w} (fibredModuleCechLevel_isFibred.{u, v, w} hU hX a p)
    hX hY (fibredModuleCechProjection.{u, v, w} a p) f

/-- Additivity of the Cech term.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-big-etale-modules). -/
instance fibredModuleCechTerm_additive
    {U X Y : BasedCategory.{v, max (u + 1) v w} (Over S)}
    (hU : IsFibredInGroupoids U) (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (a : BasedFunctor U X) (f : BasedFunctor X Y) (p : ℕ) :
    (fibredModuleCechTerm.{u, v, w} hU hX hY a f p).Additive :=
  inferInstanceAs ((fibredEtaleRelativeTerm.{u, v, w}
    (fibredModuleCechLevel_isFibred.{u, v, w} hU hX a p)
    hX hY (fibredModuleCechProjection.{u, v, w} a p) f).Additive)

/-- Canonical coface on compatible families, with no arbitrary comparison map.
Source: Stacks 06X7 (blueprint: def-sfb-fibred-big-etale-modules). -/
def fibredModuleCechCoface
    {U X Y : BasedCategory.{v, max (u + 1) v w} (Over S)}
    (hU : IsFibredInGroupoids U) (hX : IsFibredInGroupoids X)
    (hY : IsFibredInGroupoids Y) (a : BasedFunctor U X) (f : BasedFunctor X Y)
    (p : ℕ) (j : Fin (p + 2)) :
    fibredModuleCechTerm.{u, v, w} hU hX hY a f p ⟶
      fibredModuleCechTerm.{u, v, w} hU hX hY a f (p + 1) :=
  fibredEtaleRelativeRestriction.{u, v, w}
    (fibredModuleCechLevel_isFibred.{u, v, w} hU hX a (p + 1))
    (fibredModuleCechLevel_isFibred.{u, v, w} hU hX a p) hX hY
    (fibredModuleCechFace.{u, v, w} a p j) (fibredModuleCechProjection.{u, v, w} a p) f



/-- Nerve projections of a representable algebraic-stack map are representable,
and the tuple presentations are algebraic stacks.
Source: Stacks 04TF and 06X3 (blueprint: def-sfb-fibred-big-etale-modules).
Proof: the one-entry tuple presentation is equivalent over X to U. For the
induction step adjoin one more entry by the 2-fibre product over X. Algebraic
stacks are closed under these products, and representability is stable under
base change and composition. These equivalences retain the common-target
projection, so they give the assertion for this exact tuple presentation. -/
theorem fibredModuleCechLevel_algebraic
    {U X : BasedCategory.{v, max (u + 1) v w} (Over S)}
    (hU : IsAlgebraicModuliStack U) (hX : IsAlgebraicModuliStack X)
    (a : BasedFunctor U X) (ha : IsRepresentableByAlgebraicSpaces a) (p : ℕ) :
    IsAlgebraicModuliStack (fibredModuleCechLevel.{u, v, w} a p) ∧
      IsRepresentableByAlgebraicSpaces (fibredModuleCechProjection.{u, v, w} a p) := by
  sorry

end CategoryTheory
