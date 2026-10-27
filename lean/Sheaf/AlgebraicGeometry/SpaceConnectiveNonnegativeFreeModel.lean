/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSmallRingedModel
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.AlgebraicGeometry.SpaceDerivedPullback
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity
public import Mathlib.Data.Matrix.Basic
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import WeilConjectures.RingTheory.FiniteProjectiveStandardFreeCover
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
import WeilConjectures.AlgebraicGeometry.FlatComplexDerivedPullback
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.Algebra.Homology.FlatOpcyclesTorCriterion
import Mathlib.RingTheory.Flat.EquationalCriterion

/-! # Nonnegative finite free models of universally connective perfect complexes

Source: Stacks Project, quot.tex, Tag 08JX, lemma-cohomology-perfect-complex,
final cokernel and affine trivialization argument
(blueprint: lem-sfb-space-connective-nonnegative-free-model).

The small affine ringed model is the existing equivalent model of the small etale
module topos. Finite products of structure modules are finite free modules. The
section equation below states the matrix formula on every affine etale test chart.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- A universally connective perfect object has affine etale local finite free models
supported in nonnegative degrees, with matrix differentials over each coordinate ring.

Source: Stacks Project, quot.tex, Tag 08JX, lemma-cohomology-perfect-complex,
final cokernel and affine trivialization argument
(blueprint: lem-sfb-space-connective-nonnegative-free-model).

Proof:
1. Refine an etale scheme atlas by affine opens (lem-weil-pbc-affine-opens-basis),
   then by the local strict-perfect models and affine opens again. Exact restriction
   and composition in lem-sfb-space-derived-etale-chart-calculus identify these with
   derived pullbacks. The size convention makes the family small.
2. Split each finite-free idempotent over its affine coordinate ring A. Its image is
   a finite projective A-module and the differential matrices preserve these images.
   Apply lem-sfb-affine-etale-derived-module-realization to identify the sheaf complex.
   The finite-projective standard-free-cover lemma gives a common principal-open
   refinement on which every term is finite free. The affine QCoh derived equivalence
   puts its Zariski realization in D_QCoh.
3. For every A-algebra D, apply the universal hypothesis to Spec D -> Spec A -> B.
   The chart calculus, lem-sfb-derived-etale-zariski-equivalence, flat-complex derived
   pullback, and module-pullback-affine-sections identify the pullback with the etale
   realization of M tensor_A D. Its exact faithful realization detects vanishing of
   every negative cohomology module.
4. For an arbitrary A-module N use the square-zero algebra D = A direct-sum N.
   The tensor complex splits as M direct-sum (M tensor_A N), so its degree-minus-one
   vanishing gives H^{-1}(M tensor_A N) = 0. Taking D = A gives H^j(M) = 0 for j < 0.
5. The terms are flat. Apply lem-pc-module-flat-opcycles-tor-criterion at zero to
   obtain flatness of Z = coker(M^{-1} -> M^0). This module is finitely presented;
   Module.Flat.projective_of_finitePresentation makes it finite projective.
6. Replace degrees below zero by zero and degree zero by Z. The quotient chain map
   induces isomorphisms on cohomology: in degree zero use ker(d^0)/im(d^{-1}), in
   positive degrees the same kernels and images, and in negative degrees step 4.
   Exact affine etale realization and localization give an isomorphism of derived
   objects with this actual complex.
7. Trivialize Z on principal opens by the finite-projective standard-free-cover
   lemma. Restrict the isomorphism by the chart calculus. All terms are then finite
   free and all differentials have matrices over A. Choose b = max(0,d), where d
   was the old upper bound. These refinements still cover B. Bounds and ranks vary
   independently between charts; the construction includes empty and zero cases.
-/
theorem exists_etale_nonnegative_finiteFree_model
    {S : Scheme.{u}} (B : AlgebraicSpace S)
    [HasDerivedCategory.{w} B.SmallModules]
    [∀ T : Over S, HasDerivedCategory.{w} (schemeSpace T).SmallModules]
    (K : B.DerivedModules)
    (hperfect : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      B.smallStructureSheaf K)
    (hconnective : ∀ (T : Over S) (g : schemeSpace T ⟶ B) (i : ℤ), i < 0 →
      IsZero ((DerivedCategory.homologyFunctor (schemeSpace T).SmallModules i).obj
        ((spaceDerivedPullback g).obj K))) :
    ∃ (I : Type u) (A : I → CommRingCat.{u})
      (s : ∀ a : I, Spec (A a) ⟶ S)
      (v : ∀ a : I, schemeSpace (Over.mk (s a)) ⟶ B),
      (∀ a : I, IsEtale (v a).hom.hom) ∧
      IsJointlySurjective (fun a : I ↦ (v a).hom.hom) ∧
      ∀ a : I, ∃ (b : ℤ) (P : CochainComplex
          (schemeSpace (Over.mk (s a))).SmallModules ℤ),
        0 ≤ b ∧
        (∀ n : ℤ, n < 0 ∨ b < n → IsZero (P.X n)) ∧
        Nonempty ((spaceDerivedPullback (v a)).obj K ≅ DerivedCategory.Q.obj P) ∧
        ∃ (r : ℤ → ℕ)
          (e : ∀ n : ℤ, P.X n ≅ ∏ᶜ fun _ : Fin (r n) ↦
            SheafOfModules.unit (schemeSpace (Over.mk (s a))).smallStructureRings)
          (m : ∀ n : ℤ, Matrix (Fin (r (n + 1))) (Fin (r n)) (A a)),
          ∀ (n : ℤ) (W : (schemeSpace (Over.mk (s a))).SmallEtaleModelᵒᵖ)
            (x : (P.X n).val.obj W) (j : Fin (r (n + 1))),
            (((P.d n (n + 1) ≫ (e (n + 1)).hom) ≫
                Pi.π (fun _ : Fin (r (n + 1)) ↦
                  SheafOfModules.unit (schemeSpace (Over.mk (s a))).smallStructureRings) j
              ).val.app W x) =
              ∑ k : Fin (r n),
                (((Scheme.ΓSpecIso (A a)).inv ≫
                  Scheme.Γ.map (chartToScheme (Over.mk (s a)) (𝟙 _)
                    ((schemeSpace (Over.mk (s a))).smallEtaleInclusion.obj W.unop)).op
                  ).hom (m n j k)) •
                (((e n).hom ≫ Pi.π (fun _ : Fin (r n) ↦
                  SheafOfModules.unit (schemeSpace (Over.mk (s a))).smallStructureRings) k
                  ).val.app W x) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
