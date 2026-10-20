/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.Paper.CompletedConstantConstructibility
public import Sheaf.Paper.AdicStratifiedPerfect
public import Sheaf.AlgebraicGeometry.IntegralConstantCompletion
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.CategoryTheory.TruncationTriangle
import Sheaf.CategoryTheory.RingedDerivedRestrictionGeneral
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.FinitePresentation
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Sheaf.Paper.CondensedConstantConstructibility
import Sheaf.Paper.ConstantModuleSectionProperties

/-!
# The integral cohomological adic criterion

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), using Definition 6.5.1,
Remark 6.3.2 and Proposition 6.6.11; Stacks Project, Tag 09C0
(blueprint: lem-sfb-integral-cohomological-adic-criterion).

The completed ring is the actual limit of positive constant quotients. ULift only places
scalars in the sheaf universe. The residue quotient and its finite Tor condition are those
of the published adic-constructibility predicate, without any dimension or characteristic
restriction on the Noetherian scheme.

## Main definitions

* `integralCriterionWEquals`: the canonical small-site instance at the fixed coefficient size.

## Main statements

* `integral_cohomological_adic_criterion`: the cohomological integral criterion.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The existing small-site criterion at the standard coefficient universe. Fixing the
auxiliary enlargement universe to zero avoids an undetermined maximum during synthesis.
Source: Stacks Tag 03DA; Mathlib small-site equivalence transport
(blueprint: lem-sfb-integral-cohomological-adic-criterion). -/
instance (priority := 3000) integralCriterionWEquals (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{u, u + 1,
    u + 1, u + 2, u + 1} (ProEt.topology X)

/-- Bounded cohomology with finite constant stratified models is equivalent to local
uniformizer-adic completeness and bounded constructible etale origin of the first derived
reduction, with finite Tor amplitude. Here `IsSfbAdicConstructible` includes the actual
coefficient-linear derived isomorphism and tests tensor with every degree-zero etale
residue-module sheaf. Torsion finitely presented integer modules are allowed.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), Definition 6.5.1,
Remark 6.3.2 and Proposition 6.6.11; Stacks Tag 09C0
(blueprint: lem-sfb-integral-cohomological-adic-criterion).

Proof:
1. The extension-integers DVR theorem makes R Noetherian. Write r = |pi| < 1.
Compatible residue lifts x_n satisfy |x_m-x_n| <= r^n for m >= n. Completeness of E
and the nonarchimedean inequality give a limit in R realizing every residue. The
intersection of all pi^n R is zero by the same estimate. Thus R is pi-adically complete.
The integral-coefficient-limit theorem identifies the given coefficients with B, and
integral-criterion-constant-coefficients supplies flatness of R_X -> B and B/pi = k_X.
These are the coefficient hypotheses of lem-sfb-adic-stratified-perfect; its condition
(a), IsSfbAdicConstructible, is precisely the right hand side here.
2. A finite presentation of an R-module P gives a finite surjection R^m -> P.
Its kernel N is finite by lem-weil-pbc-noetherian-submodule-finite and torsion-free
as a submodule of R^m. By lem-sc-dvr-fg-torsionfree-free it is finite free. Hence
[N -> R^m] in degrees -1,0 resolves P, including torsion P. Constant-module-section-
properties preserves this exact sequence, and flatness of B over R_X preserves it
after scalar extension. Thus B tensor_R P has a two-term finite free model.
3. On every constructible stratum the cohomology sheaf has these constant local
models. Step 2 and (b) implies (a) of lem-sfb-adic-stratified-perfect show that a
constructible module in degree zero satisfies the right hand side.
4. For bounded K, choose cohomological bounds u <= v. Starting with tau_{<=u-1}K = 0,
apply lem-weil-pbc-truncation-triangle successively for q = u,...,v. Each third term
H^q(K)[-q] satisfies (a) by step 3 and shift closure. The triangulated closure of
lem-sfb-adic-stratified-perfect gives (a) for tau_{<=v}K, hence for K.
5. Conversely that lemma gives boundedness and stratified perfect R-complex models.
Proetale-immersion-limit-preservation identifies inverse-image B with the completion
on each stratum and makes module restriction exact; ringed-derived-restriction gives
exact slice restriction. Constant-module-section-properties and coefficient flatness
identify local cohomology with B tensor_R H^q(P). Noetherian-submodule-finite makes
kernels and images in the finite projective terms finite; their cohomology quotients
are finite and hence finitely presented by noetherian-finite-module-finite-presentation.
These are precisely IsCompletedConstantStratified's models for every cohomology sheaf.
Together with boundedness this proves the left hand side. -/
theorem integral_cohomological_adic_criterion (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) [IsNoetherian X]
    (K : DerivedCategory (proEtaleRingModules X
      (adicLisseCompletedRing X (ProEtale.IntegralConstantCompletion.ideal l E)))) :
    (DerivedCategory.TStructure.t.bounded K ∧
      ∀ q : ℤ, IsCompletedConstantStratified X
        (ProEtale.IntegralConstantCompletion.ideal l E)
        ((DerivedCategory.homologyFunctor _ q).obj K)) ↔
      IsSfbAdicConstructible X (ProEtale.IntegralConstantCompletion.ideal l E) K := by
  sorry

end AlgebraicGeometry.Scheme
