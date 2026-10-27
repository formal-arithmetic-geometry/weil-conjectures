/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
public import Mathlib.RingTheory.KrullDimension.Basic
public import Sheaf.AlgebraicGeometry.UnramifiedMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated
import WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteAtPoint
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.TraceFormula.FiniteSingletonFibreStalkRing
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Ideal.Height
import Sheaf.AlgebraicGeometry.UnramifiedLocusBaseChange
import Mathlib.RingTheory.FinitePresentation
import Sheaf.AlgebraicGeometry.EtaleAtPrimeFlatUnramifiedCriterion
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Sheaf.AlgebraicGeometry.EtaleDescentThroughSourceCover
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.RingTheory.RegularRingNormal
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.GoingDown
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularLocalPuncturedEtalePurity
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenComparison

/-! # Local purity of the branch locus

Source: Stacks Project, Fundamental Groups of Schemes, Tag 0BMB, Lemma `purity`
(blueprint: lem-per-local-quasi-finite-branch-purity).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Local purity of the branch locus for a morphism quasi-finite at the specified point.
Source: Stacks Project, Tag 0BMB, Lemma `purity`.
(blueprint: lem-per-local-quasi-finite-branch-purity).

Proof plan, following the node's thirteen steps:
1. The Noetherian local dimension theorem makes the common dimension a finite integer.
   Use strong induction on it; take affine finite-type neighbourhoods using quasi-finiteness
   (`lem-weil-pbc-noetherian-local-finite-krull-dimension`, `pqf-def-quasifinite`,
   `lem-weil-pbc-quasi-finite-at-point-isolated`). Generalizations and stalks persist.
2. The isolated-fibre finite-neighbourhood theorem gives an etale base neighbourhood U and
   a finite open V in its pullback, with a single point v over u. The projection V to X is
   etale by base change and composition. Shrink U affine; V is affine and both rings are
   Noetherian (`lem-weil-pbc-etale-local-finite-at-point-elementary`, etale base change,
   composition cancellation, finite locality, and finite-algebra Noetherianity).
3. Write A and B for the stalks at u and v. The singleton-fibre stalk theorem makes B finite
   over A; etale stalk invariance preserves regularity, normality and dimension. Localizing
   the affine ring of V at the base prime gives a local ring, since every maximal ideal
   contracts to the base maximal ideal and the fibre is a singleton. This localization is
   B, so Spec B is the base change to Spec A. Use the singleton-fibre stalk, affine-open
   stalk, local-radical and iterated-localization lemmas in the node.
4. A height-one prime of B gives a generalization of v whose image in X has local dimension
   one by etale stalk invariance. Apply the hypothesis and unramified-locus base change
   (`lem-trf-unramified-locus-base-change`) to make Spec B unramified there.
5. Etaleness of Spec B over Spec A implies etaleness near v: finite algebras over Noetherian
   rings are finitely presented; the etale-at-a-prime criterion gives flatness and vanishing
   differentials. Localization of differentials and the fact that every R-derivation kills
   R localized at the base prime identify these with the required affine conditions. Use
   `lem-sc-etale-at-prime-flat-unramified-criterion` and differential localization.
6. The etale neighbourhood N of v maps etale to X and to Y. Its image is an open O containing
   x; N to O is surjective etale. Etale descent through that source cover makes f restricted
   to O etale (`lem-trf-etale-descent-through-source-cover`).
7. A is a normal domain by regular-local localization and regular-ring normality. The kernel
   of A to the domain B is prime. Integral dimension equality and the common dimension force
   that kernel to be zero: otherwise prepend the zero prime to a maximal chain in A/kernel.
   Thus B is torsion free over A.
8. In dimension one, A is a DVR and hence a PID, so torsion-free B is flat. The closed point
   of Spec B has height one, hence is unramified by step 4. Its localized differentials
   vanish, and localization at the maximal ideal of a local ring changes nothing. Apply the
   flat-unramified criterion; an open containing the closed point is the whole spectrum.
9. For any prime Q of B with contraction P, incomparability contracts strict prime chains;
   going down over the normal domain A lifts chains backwards from the prescribed Q. The
   localization dimension formula gives equal local dimensions at Q and P.
10. At a nonzero, nonmaximal Q these equal dimensions are positive and strictly smaller than
    the common dimension. Normality and regularity localize; the finite morphism is
    quasi-finite. Step 4 supplies its height-one hypothesis, so induction gives etaleness.
11. A maximal-length chain in the domain B starts at zero and ends at its maximal ideal.
    Its first nonzero prime has height one and, in dimension at least two, is nonmaximal.
    Its etale neighbourhood from step 10 contains the generic point. Thus the morphism is
    etale on the punctured spectrum, including the generic point.
12. Incomparability identifies the inverse image of the punctured Spec A with punctured
    Spec B. The restriction is finite etale by source locality. Punctured-spectrum purity
    (`lem-sbc-regular-local-punctured-etale-purity`, Tag 0BMA(1)) extends it to a finite
    etale scheme E over Spec A, with the specified isomorphism on the puncture.
13. Normality localizes on both schemes; the puncture is nonempty and its inverse image is
    dense since it contains the generic point. Finite-normal dense-open comparison
    (`lem-sbc-finite-normal-dense-open-comparison`) extends the isomorphism to Spec B and E
    over Spec A. Hence Spec B is etale, and steps 5 and 6 give the conclusion at x.
-/
theorem exists_etale_neighborhood_of_unramified_codimension_one
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)]
    [IsRegularLocalRing (Y.presheaf.stalk (f x))]
    (hqf : f.IsQuasiFiniteAtPoint x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (hpos : (1 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    (hunram : ∀ x' : X, x ∈ closure ({x'} : Set X) →
      ringKrullDim (X.presheaf.stalk x') = 1 →
      ∃ U : X.Opens, x' ∈ U ∧ IsUnramified (U.ι ≫ f)) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  sorry

end AlgebraicGeometry
