/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedFiniteEtaleStalkCycles
public import WeilConjectures.AlgebraicGeometry.CondensedStrictWeilComplex
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import WeilConjectures.AlgebraicGeometry.PullbackConstantModelConstructible
import WeilConjectures.RingTheory.ProEtale.WContractible
import WeilConjectures.RingTheory.WContractibleGeometricCriterion
import WeilConjectures.AlgebraicGeometry.CondensedPointCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.ProperBaseChangeRationalPushforward
import WeilConjectures.AlgebraicGeometry.CondensedExchangeOpenRestriction
import WeilConjectures.AlgebraicGeometry.CondensedModulePullbackExact
import WeilConjectures.CategoryTheory.RightDerivedSingleH0
import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafTopologicalInvariance
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Finite condensed fibres and their Frobenius return maps

Source: latest blueprint, sec-deligne-laumon-general/sk-l-dl-general-quasifinite/
lem-zl-quasi-finite.proof.md, final paragraph (4) and (5), before the weight calculation
(blueprint: lem-zl-condensed-finite-fibre-frobenius).

The existing finite-etale module supplies general definitions of the geometric map,
ordinary direct image, counit restrictions and the complete Frobenius comparison. None
of those definitions assumes etaleness. Here the comparison is asserted for every finite
map, including nonreduced fibres. The sheaf comparison is a bilimit bicone of functors:
this is a finite direct sum, and its functor isomorphism includes naturality in M.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj DirectSum

namespace WeilConjectures.CondensedFinite

open CondensedModule CondensedFiniteEtale

set_option maxHeartbeats 0 in
-- Checking the combined natural comparison and return equations needs a larger kernel budget.
/-- Finite-dimensional terminal-section fibres, the canonical finite direct-sum comparison
as module sheaves and on sections, and the geometric Frobenius cycles and return maps.

Source: latest blueprint lem-zl-quasi-finite.proof.md, paragraph (4) and (5)
(blueprint: lem-zl-condensed-finite-fibre-frobenius).

Proof plan, following the eight steps of the node:
1. Pullback preserves constructibility (lem-sfb-pullback-constant-model-constructible).
   On Spec(k) the coefficient heart makes the pullback lisse. The algebraically closed
   field is w-contractible (det-pe-wlocal-strict-contractible); split a finite affine
   trivializing cover by det-pe-wcb-split-cover. Thus the pullback is finite free.
   det-pe-condensed-point-coefficients evaluates its coefficient unit at the singleton
   as Qlbar, proving finite dimensionality, including rank zero.
2. Localize around the image of b to an affine open. The finite map there is proper
   (lem-weil-pbc-finite-morphism-permanence, lem-weil-pbc-finite-proper). Apply clause 3
   of det-thm-sfb-proper-base-change-rational. The global comparison agrees with it by
   lem-sfb-condensed-exchange-one-open-restriction. Exact module pullback and
   lem-kun-right-derived-single-h0 identify H0 with the actual underived exchange.
3. The finite geometric fibre is Spec(D) for a finite-dimensional k-algebra D. Its
   finitely many primes are maximal. Each residue field equals k, by algebraic
   closedness. The Chinese remainder theorem identifies D modulo its nilradical with
   a finite product of copies of k. Thus the reduction is the disjoint union of the
   geometric points. D=0 gives the empty union; reduction is a universal homeomorphism.
4. lem-trf-proetale-topological-invariance removes the nilpotents, including for module
   objects with their canonical coefficient comparisons. Finite disjoint-union
   evaluation (lem-weil-pbc-proetale-finite-coproduct-evaluation) gives the finite
   product, hence biproduct. The mate formula (def-weil-pbc-adjunction-mate) identifies
   every projection with stalkLowerStarProj, the pullback of the counit. All these
   maps are natural. Terminal sections preserve this finite biproduct.
5. Write t=Spec(z -> z^(1/q)) and T(z)=t^(-1) z g. The existing CondensedModule.transport
   restricts sections along t, uses coherent point-pullback comparisons, and applies
   the iterated Weil isomorphism. It is coefficient-linear; successive transports
   compose to the transport of the corresponding iterate.
6. The model map commutes with geometric Frobenius. Its canonical exchange is
   invertible because the horizontal maps are isomorphisms. Compose that exchange
   with h_*theta, exactly directImageWeil. Transposing the exchange gives the
   pulled-back counit. Naturality of the counit and point-pullback coherence show
   that restriction after the direct-image Frobenius equals the next restriction
   followed by the summand transport. Iteration gives the permutation of summands.
7. Closed-point residue fields are finite. Above x over y the compatible embeddings
   kappa(x) -> k form a torsor for the cyclic finite-field Galois group generated by
   q_y-power Frobenius. Hence there is one cycle of length e=[kappa(x):kappa(y)]>=1.
   Counting coordinates in a field basis gives q_x=q_y^e and deg(x)=deg(y)*e.
8. Concatenating e transports of length deg(y) gives precisely the deg(x)-fold Weil
   map with the same source reparametrization, hence the local operator at x.
   Consecutive cyclic products are conjugate by their first invertible factor.
   This proves conjugacy without semisimplicity, including e=1 and zero summands.
-/
theorem condensed_finite_fibre_frobenius
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [QuasiSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [QuasiSeparated Y₀.hom]
    (g₀ : X₀ ⟶ Y₀) [IsFinite g₀.left] :
    (∀ (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber X₀).left)
      (a : Over.mk (𝟙 (Spec (.of D.k))) ⟶ D.geometricFiber X₀),
      FiniteDimensional (ULift.{u + 1} (PadicAlgCl l)) (fibre l D M.obj a.left)) ∧
    (∀ b : Over.mk (𝟙 (Spec (.of D.k))) ⟶ D.geometricFiber Y₀,
      Finite (CondensedRing.FibrePoints (geometricMap D g₀) b.left) ∧
      ∃ C : Bicone (fun a : CondensedRing.FibrePoints (geometricMap D g₀) b.left ↦
        ObjectProperty.ι (IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
          (D.geometricFiber X₀).left) ⋙
            CondensedRing.upperStar (Profinite.padicAlgClRingObj l) a.val),
        Nonempty C.IsBilimit ∧
        ∃ e : (ObjectProperty.ι
          (IsConstantModelConstructible (Profinite.padicAlgClRingObj l)
            (D.geometricFiber X₀).left) ⋙
          CondensedRing.lowerStar (Profinite.padicAlgClRingObj l) (geometricMap D g₀) ⋙
          CondensedRing.upperStar (Profinite.padicAlgClRingObj l) b.left) ≅ C.pt,
          ∀ M a, e.hom.app M ≫ (C.π a).app M =
            CondensedRing.stalkLowerStarProj (Profinite.padicAlgClRingObj l) a.property M.obj) ∧
    (∀ (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber X₀).left)
      (b : Over.mk (𝟙 (Spec (.of D.k))) ⟶ D.geometricFiber Y₀),
      ∃ e : fibre l D (directImage D l g₀ M.obj) b.left ≃ₗ[ULift.{u + 1} (PadicAlgCl l)]
        ⨁ a : CondensedRing.FibrePoints (geometricMap D g₀) b.left, fibre l D M.obj a.val,
        ∀ v a, e v a = restriction D l g₀ M.obj b.left a v) ∧
    (∀ (M : ConstantModelConstructible (Profinite.padicAlgClRingObj l)
        (D.geometricFiber X₀).left)
      (θ : (CondensedRing.upperStar (Profinite.padicAlgClRingObj l)
        (D.geometricFrobenius X₀).hom).obj M.obj ≅ M.obj),
      ∃ h : (D.geometricFrobenius X₀).hom ≫ geometricMap D g₀ =
        geometricMap D g₀ ≫ (D.geometricFrobenius Y₀).hom,
        ∀ (y : {y : Y₀.left // y ∈ closedPoints Y₀.left})
          (ι : Y₀.left.residueField y.val →+* D.k)
          (hι : ι.comp (Y₀.hom.residueFieldAlgebraMap y.val) = algebraMap D.k₀ D.k),
          ∃ C : FibreComparison D l g₀ h M.obj θ y ι hι,
            ∀ (x : ModelPoints D g₀ y.val)
              (z z' : Points D g₀ y.val (localClosedPoint D Y₀ y ι hι) x),
              ∃ e : fibre l D M.obj z.val.val ≅ fibre l D M.obj z'.val.val,
                e.hom ≫ operator l D (D.geometricFrobenius X₀).hom M.obj θ z'.val.val
                    (localClosedPointDegree D X₀ ⟨x.val, C.closed_model x⟩ - 1)
                    (C.local_return x z') =
                  operator l D (D.geometricFrobenius X₀).hom M.obj θ z.val.val
                    (localClosedPointDegree D X₀ ⟨x.val, C.closed_model x⟩ - 1)
                    (C.local_return x z) ≫ e.hom) := by
  sorry

end WeilConjectures.CondensedFinite
