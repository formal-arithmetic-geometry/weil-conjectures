/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Closed.ProEtaleClosedLiftOverlapRelations
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperClosedLiftLocalChains

/-! # Resolving elementary overlaps through the proper closed fibre

Source: Steps 2--3 of `lem-sp-proetale-proper-closed-lift-relations`.
(blueprint: lem-sp-proetale-proper-closed-overlap-chains).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Each elementary overlap relation vanishes modulo closed-lift relations.
The overlap itself need not have the closed-specialization property.

Source: Steps 2--3 of `lem-sp-proetale-proper-closed-lift-relations`.
(blueprint: lem-sp-proetale-proper-closed-overlap-chains).

Proof: an elementary overlap identifies two arrows into P. Lift the base
specializations from W through the proper closure of their common image.
After affine closed localization the base is henselian along its closed
fibre. Stein connectedness makes the closed-fibre intersection of each
irreducible closure nonempty and connected. The two local lifts can thus
be joined by a finite chain of overlaps through that closed fibre. Refine
the chain by affine weakly contractible closed-site objects and their
henselian lifts; the required covers on W split by its evaluation property.
Each adjacent difference is now the restriction of a kernel map defined on
a closed-lift test. It vanishes in the displayed cokernel by
closedLiftTestRelation_cokernel. The finite sum telescopes to the original
overlap difference. Equality is local for a sheaf, so its cokernel composite
is zero. This uses connected chains, not the false assertion that the
original overlap has a closed-specialization cover. Empty overlaps and zero
coefficients contribute zero maps and require no choice of a point. -/
theorem proper_closedLift_overlap_cokernel
    (A : Type u) [CommRing A] [Finite A]
    {B D E : Scheme.{u}} (p : B ⟶ D) (i : E ⟶ D)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i]
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hspecializes : ∀ x : W.left, ∃ z : ↥(pullback W.hom i.closedComplement),
      Specializes x ((pullback.fst W.hom i.closedComplement) z)) :
    let z := (pullback.fst p i).closedComplement
    let P := (proEtaleBaseChange p).obj W
    let Q := (ProEtale.freeSheaf (ULift.{u + 1, u} A) B).obj P
    let e := closedLiftGeneratorAugmentation A z Q
    let d := closedLiftGeneratorAugmentation A z (kernel e.hom)
    ∀ t s : ClosedLiftArrowIndex z P,
      closedLiftOverlapRelation A z P t s ≫ cokernel.π d.hom = 0 := by
  dsimp only
  intro t s
  obtain ⟨κ, V, a, hcover, hchain⟩ :=
    proper_closed_lift_local_chains p i W hW
      (proper_test_closed_fibre_connectedness p i W hW hspecializes) t s
  exact ClosedLiftChain.overlap_cokernel_of_chains A _ _ t s V a hcover hchain

end AlgebraicGeometry.Scheme
