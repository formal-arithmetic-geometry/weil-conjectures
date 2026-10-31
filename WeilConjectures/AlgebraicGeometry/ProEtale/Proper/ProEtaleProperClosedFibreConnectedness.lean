/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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

/-! # Stein connectedness over a closed-specializing pro-etale test

Source: Steps 1--2 of `lem-sp-proetale-proper-closed-overlap-chains`.
(blueprint: lem-sp-proetale-proper-test-closed-fibre-connectedness).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- Every irreducible closed subset of the proper pullback meets its closed fibre
in a nonempty connected set. This is a topological assertion, without coefficients,
free sheaves, augmentation maps, or choices of overlap arrows.

Source: Steps 1--2 of `lem-sp-proetale-proper-closed-overlap-chains`;
Stein connectedness for a henselian pair, Stacks Tag 0A0B.
(blueprint: lem-sp-proetale-proper-test-closed-fibre-connectedness).

Proof: write the affine scheme W as Spec R and its closed fibre as V(J).
Every maximal point of Spec R specializes into V(J), hence belongs to V(J), so
J is contained in the Jacobson radical. Evaluation at W splits epimorphisms of
set sheaves. In particular an etale neighbourhood of V(J) admits a section:
its image contains V(J), and is open, so the specialization assumption makes
it surjective over W. To lift a specified section over V(J), first remove the
closed complement of that section in the etale closed fibre. The remaining
etale neighbourhood is still surjective and its section lifts the specified
one. The etale section-lifting characterization of henselian pairs therefore
makes (R,J) henselian. The projection B times_D W to W is proper by base
change. Apply Stein connectedness to this proper morphism over Spec R and
transport V(J) back to the inverse image of the closed complement in B.
This proves both nonemptiness and connectedness, including nonreduced closed
fibres. If W or the proper pullback is empty there is no irreducible C. -/
theorem proper_test_closed_fibre_connectedness
    {B D E : Scheme.{u}} (p : B ⟶ D) (i : E ⟶ D)
    [IsProper p] [IsOpenImmersion i] [QuasiCompact i]
    (W : D.ProEt) [IsAffine W.left]
    (hW : ∀ (F G : Sheaf (ProEt.topology D) (Type (u + 1))) (e : F ⟶ G),
      Epi e → Function.Surjective (e.hom.app (op W)))
    (hspecializes : ∀ x : W.left, ∃ z : ↥(pullback W.hom i.closedComplement),
      Specializes x ((pullback.fst W.hom i.closedComplement) z)) :
    let z := (pullback.fst p i).closedComplement
    let P := (proEtaleBaseChange p).obj W
    ∀ C : Set P.left, IsClosed C → IsIrreducible C →
      IsConnected (C ∩ P.hom ⁻¹' Set.range z) := by sorry

end AlgebraicGeometry.Scheme
