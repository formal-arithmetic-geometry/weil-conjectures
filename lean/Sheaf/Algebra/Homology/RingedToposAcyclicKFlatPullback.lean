/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
import Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import Sheaf.Algebra.Homology.FilteredColimitsTensor
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Sheaf.Algebra.Homology.RingedToposPullbackFilteredColimits
import Sheaf.Algebra.Homology.AcyclicKFlatCyclesFlat

/-! # RingedToposAcyclicKFlatPullback

Source: Stacks Project, Tag 0G7E (lemma-pullback-K-flat), acyclic case.
(blueprint: lem-weil-pbc-ringed-topos-acyclic-kflat-pullback). -/

@[expose] public section
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

/-- The acyclic case of K-flat pullback along a morphism of ringed topoi.
Source: Stacks Project, Cohomology on Sites, Tag 0G7E, the acyclic-case paragraph,
using Tag 0G7C for flatness of cycles.
(blueprint: lem-weil-pbc-ringed-topos-acyclic-kflat-pullback).

Proof: because P is acyclic, K-flat, and flat in every degree, its cycles are flat
by the acyclic K-flat cycles criterion. Its good truncation at n therefore has flat
terms: the old terms below n, the flat cycle sheaf in degree n, and zero above n.
Flat pullback makes the terms of its image flat; additivity sends zero to zero, so
the image remains bounded above. Every such image is K-flat by the bounded-above
flat criterion. The good truncations for n in the natural numbers have degreewise
colimit P, since in every degree they are eventually equal to P. The filtered-colimit preservation
theorem for the specified module pullback implies
that uStar preserves this colimit, including all transition maps and differentials.
Filtered-colimit closure of K-flatness now proves that the
image of P is K-flat. No exactness of uStar on arbitrary short exact sequences is used. -/
theorem isKFlat_ringedToposPullback_of_acyclic
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
    (hacyclic : P.Acyclic) (hP : P.IsKFlatIndependentCoefficients)
    (hflat : ∀ n : ℤ, IsFlatOnSite (J := JC) (R := R) (P.X n)) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((uStar.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  sorry

end SheafOfModules
