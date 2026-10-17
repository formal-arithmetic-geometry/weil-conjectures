/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import Sheaf.AlgebraicGeometry.ConstructibleAbelianSheaf
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantSheafGeometricStalk
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import Sheaf.CategoryTheory.SitePullbackAbelianExact
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.CategoryTheory.Sites.Sheafification
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.ProperSmoothConnectedFibreDimensionLoci
import Sheaf.AlgebraicGeometry.ProperSmoothCurvesPrimeCoefficients
import Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-!
# Constructibility for proper smooth families of curves with finite coefficients

Source: Stacks Project, more-etale.tex, Tag 0GKW; Tag 0GK3 for dimension zero,
and morphisms.tex, Tag 02G1 for the fibre-dimension decomposition
(blueprint: lem-weil-pbc-etale-proper-smooth-curves-finite-module).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Higher direct images of a finite constant module in a proper smooth family with
nonempty geometrically connected fibres of dimension at most one are constructible.
The coefficient exponent need not be invertible on the base. `GeometricallyConnected`
includes nonempty fibres; dimension is measured on the residue-field fibres.

Source: Stacks Project, Tag 0GKW (dimension one), Tag 0GK3 (dimension zero),
and Tag 02G1 (locally constant smooth fibre dimension).
(blueprint: lem-weil-pbc-etale-proper-smooth-curves-finite-module)

Proof plan:
1. For finite coefficient rings, constructibility of the underlying abelian sheaf is
   equivalent to module constructibility. On constant finite abelian charts, trivialize
   each of the finitely many scalar endomorphisms using
   `lemma-constructible-hom-constant-locally` and refine the covers simultaneously.
   Read the module identities on a geometric stalk, using
   `lem-weil-pbc-constant-sheaf-geometric-stalk`; the constant values become modules.
   Forgetting scalars gives the converse; restrictions commute with forgetting by
   `lem-weil-pbc-exchange-forget-coefficients`.
2. By `lem-weil-pbc-proper-smooth-connected-fibre-dimension-loci`, split the base into
   open and closed dimension-zero and dimension-one loci, either of which may be empty.
   Exact restriction preserves injectives by `lem-weil-pbc-etale-restriction-injectives`
   and `lem-weil-pbc-site-pullback-abelian-exact`, so higher direct images restrict to
   the corresponding higher direct images. Constant inputs restrict to constants by
   `lemma-constructible-pullback-constant`. Finite stratifications concatenate.
3. On the dimension-zero locus the morphism is quasi-finite, proper and finitely
   presented. The base is Noetherian and quasi-compact; source and base are qcqs by
   `lem-weil-pbc-locally-noetherian-quasi-separated` and
   `lem-weil-pbc-qcqs-morphism-permanence`. Use the identity compactification and
   `lem-weil-pbc-etale-quasifinite-shriek-constructible` on the constant sheaf in
   degree zero. Identity extension by zero identifies proper shriek and direct image.
4. On the dimension-one locus, a finite abelian group killed by a prime is a finite
   dimensional vector space over the prime field. By `lem-weil-pbc-vector-space-free`
   choose a finite basis, including the empty basis for zero. Constant sheafification
   and additive derived functors preserve finite sums, by
   `lem-weil-pbc-sheafification-exact` and
   `lem-weil-pbc-right-derived-universal-delta-functor`. Apply
   `lem-weil-pbc-proper-smooth-curves-prime-coefficients`, and combine the summands
   using `thm-constructible-serre` and the coefficient comparison from step 1.
5. Induct on a positive integer n killing the finite abelian group B. For n = 1,
   B is zero. For n = l n' with l prime, use the exact sequence from B[l] to B
   onto l B. The kernel is killed by l and the quotient by n' < n. Constant
   sheafification is exact; the derived delta functor gives a five-term exact
   segment. The outer terms are constructible by step 4 and induction; the middle
   term is an extension of a cokernel by a kernel, so apply `thm-constructible-serre`.
   This uses `lem-weil-pbc-module-direct-image-left-exact` and
   `lem-weil-pbc-module-sheaves-enough-injectives`. In degree zero the preceding
   negative term is zero. No invertibility assumption enters.
6. The product of the additive orders kills the finite underlying group of M.
   Apply step 5, and upgrade to the given module structure using step 1 and
   `lem-weil-pbc-exchange-forget-coefficients`. Negative-degree cohomology is zero
   because the injective resolution starts in degree zero. Glue the two loci from
   step 2. This includes M = 0 and the zero coefficient ring.
-/
theorem properSmoothCurves_finiteModule_higherDirectImage_constructible
    {C S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : C ⟶ S) [IsProper f] [Smooth f] [GeometricallyConnected f]
    (h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) ≤ 1)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (M : ModuleCat.{u + 1} Λ) [Finite M] (q : ℤ) :
    Scheme.IsConstructibleEtaleModuleSheaf
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
            ((constantSheaf C.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)))) := by
  sorry

end AlgebraicGeometry.Etale
