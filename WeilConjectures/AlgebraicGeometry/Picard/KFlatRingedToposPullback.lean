/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.ProperBaseChange.FlatAlgebraicInverseImageOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.ProperBaseChange.RingedToposPullbackFilteredColimits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
/-!
# Ringed-topos pullback preserves K-flat complexes with flat terms
Source: Stacks Project, Cohomology on Sites, Tag 0G7E, lemma-pullback-K-flat
(blueprint: lem-weil-pbc-ringed-topos-kflat-pullback).
-/
@[expose] public section
universe uC vC uD vD w
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

open CategoryTheory.Functor MonoidalCategory

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  {R : Sheaf JC CommRingCat.{w}} {RI : Sheaf JD CommRingCat.{w}}
  {L : Sheaf JC (Type w) ⥤ Sheaf JD (Type w)}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
section ConeHelpers

universe u v
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{w})

private theorem kFlat_iso_independent
    {K L : CochainComplex (SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)) ℤ}
    (e : K ≅ L) (hK : K.IsKFlatIndependentCoefficients) :
    L.IsKFlatIndependentCoefficients := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  let := preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro A hA
  let e' := ((curriedTensor _).map₂CochainComplex.obj A).mapIso e
  have h := hK A hA
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h ⊢
  exact (HomotopyCategory.subcategoryAcyclic _).prop_of_iso
    ((HomotopyCategory.quotient _ _).mapIso e') h

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
private theorem flatOnSite_of_iso
    {M N : SheafOfModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R)}
    (e : M ≅ N) (hM : IsFlatOnSite (J := J) (R := R) M) :
    IsFlatOnSite (J := J) (R := R) N := by
  let := isMonoidal_W_independentCoefficients R
  let := monoidalCategory R
  have hM' : exactFunctor _ _ (tensorRight M) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R M) hM
  have hN' : exactFunctor _ _ (tensorRight N) :=
    (exactFunctor _ _).prop_of_iso ((curriedTensor _).flip.mapIso e) hM'
  exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R N).symm hN'

end ConeHelpers

end SheafOfModules
