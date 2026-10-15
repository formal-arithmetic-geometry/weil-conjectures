/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
/-!
# Ringed-topos pullback preserves K-flat complexes with flat terms
Source: Stacks Project, Cohomology on Sites, Tag 0G7E, lemma-pullback-K-flat
(blueprint: lem-weil-pbc-ringed-pullback-preserves-kflat).
-/
@[expose] public section
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules
/-- Termwise pullback along a morphism of ringed topoi preserves K-flatness and flat
terms. Source: Stacks Project, Tag 0G7E, lemma-pullback-K-flat
(blueprint: lem-weil-pbc-ringed-pullback-preserves-kflat).
`I` presents the algebraic inverse image of rings and modules along `uInv`. The equations
`hobj` and `hmap` identify the additive functor `uStar` with inverse image followed by
extension of scalars along `c`, on objects and morphisms. Additivity is the structure of
this module pullback, used to apply it termwise. No flatness of `c` is assumed.
Proof plan: apply `lem-weil-pbc-ringed-topos-kflat-pullback` to the two small sites, their
ring sheaves, the adjunction `adj`, its left exact inverse image, the algebraic inverse
image `I`, and the ring map `c`. The hypotheses are precisely K-flatness of `P` and flatness
of each `P.X n`. The conclusion identifies the termwise pullback as K-flat with flat terms;
renaming the input complex from the general theorem does not change the assertion.
-/
theorem ringedPullbackPreservesKFlat
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
    {R : Sheaf JC CommRingCat.{w}} {S RI : Sheaf JD CommRingCat.{w}}
    (uInv : Sheaf JC (Type (w)) ⥤ Sheaf JD (Type (w)))
    (uPush : Sheaf JD (Type (w)) ⥤ Sheaf JC (Type (w)))
    (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
    (uStar : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⥤
      ringedSiteModules.{w} ((sheafCompose JD
        (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hobj : ∀ M : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      uStar.obj M = changeOfRings c (I.modules.obj M))
    (hmap : ∀ {M N : ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)} (a : M ⟶ N),
      uStar.map a = eqToHom (hobj M) ≫
        changeOfRingsHom c (I.modules.obj M) (I.modules.map a) ≫ eqToHom (hobj N).symm)
    [uStar.Additive]
    (P : CochainComplex (ringedSiteModules.{w} ((sheafCompose JC
      (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ)
    (hP : P.IsKFlat) (hflat : ∀ n : ℤ, (P.X n).IsFlat) :
    CochainComplex.IsKFlat ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ∧
      ∀ n : ℤ, (((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P).X n).IsFlat := by
  sorry
end SheafOfModules
