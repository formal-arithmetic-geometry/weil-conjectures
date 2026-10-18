/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.ConstantEtaleSheafShortExact
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.Henselian
import Sheaf.RingTheory.CompletionDimension
import Sheaf.RingTheory.GRing
import Sheaf.AlgebraicGeometry.RegularEtaleDirectImageBaseChange
import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
import Sheaf.AlgebraicGeometry.StrictLocalTotalCohomologyExchange
import Sheaf.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Sheaf.RingTheory.CompleteLocalQuotient
import Sheaf.RingTheory.StrictlyHenselianQuotient
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance
import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf

/-!
# Constant-coefficient affine Lefschetz bound over a strictly local base

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XV, Corollary 1.2.4,
printed p. 220; proof in XV 1.2.3, 1.2.5--1.2.6 and sections 2--3, pp. 220--224
(blueprint: lem-per-affine-open-strict-local-constant-bound).

The strictly local scheme is expressed as an affine scheme with strictly henselian
ring of global sections. Cohomology is right-derived global sections of the constant
abelian sheaf placed in degree zero. The universe lift changes only its size.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Constant finite coefficients on an affine open of a quasi-excellent strictly local
scheme of dimension `e` have zero cohomology in degrees greater than `e`.

Source: ILO, Travaux de Gabber, Expose XV, Corollary 1.2.4, printed p. 220
(blueprint: lem-per-affine-open-strict-local-constant-bound).

Proof:
1. Induct strongly on `m`. For `m = 1` the constant sheaf is zero. Otherwise choose
   a prime `p` dividing `m`. The exact sequence Z/(m/p) -> Z/m -> Z/p yields an
   exact sequence of constant module sheaves by lem-constructible-constant-exact.
   Forget scalars exactly by lem-weil-pbc-module-sheaves-colimits-forgetful and use
   lem-weil-pbc-pullback-cohomology-long-exact-ladder for the identity map. The two
   smaller moduli remain invertible. It suffices to establish every prime case.
2. Complete the local ring at its maximal ideal. The completion is Noetherian,
   local with the same residue field, henselian, and of dimension `e`, by
   lem-weil-pbc-adic-completion-noetherian, lem-weil-pbc-local-completion-local-ring,
   lem-weil-pbc-complete-pair-henselian and lem-weil-pbc-completion-dimension.
   The G-ring clause of quasi-excellence makes the completion map regular, by
   def-weil-pbc-g-ring. The prime remains invertible.
3. Base change the affine open to the completion. Its immersion is qcqs. Apply
   lem-per-regular-etale-direct-image-base-change, identify constant inverse images
   by lem-pe-constant-left-module-inverse-image, and evaluate at the closed point
   by lem-weil-pbc-strict-local-total-cohomology-exchange. Cohomology is unchanged.
4. The empty open has zero cohomology. Otherwise take the reduced closure of the
   completed open by lem-weil-pbc-reduced-induced-closed-subscheme. Its intersection
   with the open is its reduction, and is affine and dense. The closure is complete
   Noetherian strictly local by lem-weil-pbc-complete-local-quotient and
   lem-weil-pbc-strictly-henselian-quotient, of dimension `d <= e`. Reduction is a
   universal homeomorphism by lem-weil-pbc-reduction-universal-homeomorphism, so
   thm-weil-pbc-universal-homeomorphism-invariance and constant inverse-image
   compatibility reduce to this dense affine open.
5. For each `q > d`, choose `L = q + 1` and apply
   lem-per-complete-local-branch-approximation. It supplies an intermediate strictly
   local model, an affine open and hypercovers through degree `L`, together with
   a close section model of dimension exactly `d`, strictly locally of finite type
   over a complete trait. The prime is invertible on the intermediate model.
6. Apply lem-per-truncated-branch-descent to the two local maps from the complete
   model and the section model to the intermediate model. Approximation supplies
   regularity and independent normal-crossing branch equations at all closed-fibre
   geometric points in levels at most `L`. Since `q < L`, both cohomology maps in
   degree `q` are isomorphisms. No dimension bound on the intermediate model is used.
7. The open in the section model is affine and its immersion is finite type, by
   lem-weil-pbc-affine-scheme-qcqs and lem-weil-pbc-qc-open-immersion-finite-type.
   Apply lem-per-trait-affine-lefschetz to the constant constructible sheaf
   (def-weil-pbc-etale-constructible-sheaf). Its dimension function is at most `d`:
   residue fields are unchanged and point closures have dimension at most `d`.
   Thus its cohomology vanishes for `q > d`.
8. Undo the two descent comparisons, reduction and completion to obtain vanishing
   for `q > e`. The strong induction in step 1 gives every positive invertible `m`. -/
theorem isZero_cohomology_constant_affineOpen_of_quasiExcellent_strictlyHenselian
    (S : Scheme.{u}) [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    [IsStrictlyHenselianLocalRing Γ(S, ⊤)] (hS : IsQuasiExcellent Γ(S, ⊤))
    (e m : ℕ) (hm : 1 ≤ m) (hunit : IsUnit (m : Γ(S, ⊤)))
    (he : ringKrullDim Γ(S, ⊤) = (e : WithBot ℕ∞))
    {U : Scheme.{u}} [IsAffine U] (j : U ⟶ S) [IsOpenImmersion j]
    (q : ℕ) (hq : e < q) :
    IsZero ((cohomology AddCommGrpCat.{u + 1} U (q : ℤ)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} (ZMod m)))))) := by
  sorry

end AlgebraicGeometry.Etale
