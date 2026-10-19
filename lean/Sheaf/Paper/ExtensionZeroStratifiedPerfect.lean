/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N8
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import Sheaf.SixFunctors.IntrinsicDerivedTensor
public import Mathlib.CategoryTheory.Sites.Over
public import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Sheaf.Paper.BoundedConstructibleComplete
public import Sheaf.Paper.CompletedExtensionZeroComparison
public import Sheaf.Paper.IntegralStratifiedPerfectCharacterization
import Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
import Sheaf.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.SiteMorphismComposition

/-!
# Extension by zero preserves stratified perfect local models

Source: Bhatt--Scholze, Lemma 6.1.12, Proposition 6.6.11 and Definition 6.7.6/Lemma 6.7.7
(blueprint: lem-cbc-extension-zero-stratified-perfect).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Extension by zero carries an integral stratified-perfect object on a quasi-compact open
into an integral stratified-perfect object on the ambient Noetherian scheme, and its pullback to
any complementary closed subscheme is zero.  The stratified-perfect predicate is the canonical
finite locally closed pro-etale model predicate; the coefficient datum is the canonical
uniformizer-adic datum attached to a finite extension of `ℚ_ℓ`.

Source: Bhatt--Scholze, Lemma 6.1.12, Proposition 6.6.11 and Definition 6.7.6/Lemma 6.7.7
(blueprint: lem-cbc-extension-zero-stratified-perfect).

Proof: use the exact completed-coefficient extension by zero `cbcDerivedOpenShriek`.  The
open restriction identity transports every original perfect model along the actual inverse
image and the canonical quotient-compatible coefficient identifications.  The complementary
closed inverse image is zero by the ringed pro-etale open-closed localization theorem.  Adding
that closed immersion to the original finite locally closed stratification gives the asserted
finite stratification of the ambient scheme, with the zero complex as its model on the new
closed stratum.
-/
theorem cbc_extension_zero_stratified_perfect
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T U Z : Scheme.{u}} [IsNoetherian T]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (i : Z ⟶ T) [IsClosedImmersion i]
    (hcover : Set.range j ∪ Set.range i = Set.univ)
    (hdisjoint : Disjoint (Set.range j) (Set.range i))
    (K : DerivedCategory (pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))))
    (hK : IsIntegralStratifiedPerfect U (pbcIntegralDatum l E) K) :
    IsIntegralStratifiedPerfect T (pbcIntegralDatum l E)
        ((cbcDerivedOpenShriek (pbcIntegralDatum l E) j inferInstance).obj K) ∧
      IsZero
        ((adicTowerPullback i (pbcAdicCompletion T (pbcIntegralDatum l E))).obj
          ((cbcDerivedOpenShriek (pbcIntegralDatum l E) j inferInstance).obj K)) := by
  sorry

end AlgebraicGeometry.Scheme
