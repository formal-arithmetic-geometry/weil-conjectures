/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.CategoryTheory.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import Sheaf.AlgebraicGeometry.ProEtaleDirectImageComparison

/-!
# Direct-image amplitude for bounded complexes of etale origin

Source: Stacks Project, derived.tex, Tags 08J5 and 05TC; proetale.tex, Tags 099T and 09A6
(blueprint: lem-sf-etale-origin-pushforward-amplitude).

The comparison is the published termwise inverse image with canonical constant-ring
realization. Direct images are ordinary uncompleted unbounded right derived functors.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- A bound on all etale heart objects controls the direct image of a bounded etale-origin
complex, including the zero-image conclusion when the bound is negative.
Source: Stacks Project, derived.tex, Tags 08J5 and 05TC; proetale.tex, Tags 099T and 09A6
(blueprint: lem-sf-etale-origin-pushforward-amplitude).

Proof:
1. By det-pe-classical-sheaves-modules, comparison inverse image is exact and fully
faithful. Its canonical coefficient realization is an exact equivalence by
def-weil-pbc-proetale-modules. Exactness commutes with cohomology, and faithfulness
reflects zero objects (apply it to the identity and zero maps). Thus the assumed
cohomological range of the comparison image gives the same range for L.
2. Module sheaf categories are Grothendieck abelian and admit K-injective resolutions by
prop-pur-kinjective-resolutions-exist. Ordinary etale direct image is additive and left
exact by lem-weil-pbc-module-direct-image-left-exact. Its unbounded right derived functor
is triangulated and commutes with integer shifts by lem-pc-right-derived-functor-triangulated.
On bounded-below inputs its K-injective computation agrees with def-weil-pbc-direct-image;
on a sheaf in degree zero its cohomology is the higher direct image in the hypothesis.
3. If N is nonnegative, lem-weil-pbc-derived-functor-negative-vanishing gives vanishing
in negative degrees on heart objects, and the hypothesis gives vanishing above N.
4. Apply lem-pur-bounded-heart-amplitude to this triangulated functor, the class of all
sheaves, and the heart interval [0,N]. The input range [a,b] gives [a,b+N]. This uses
a finite tower of successive cohomology triangles (08J5), with no completeness assumption.
5. If N is negative, degree zero is covered by the hypothesis. The degree-zero
identification of lem-weil-pbc-right-derived-universal-delta-functor makes ordinary etale
direct image zero on every sheaf. Applying it termwise to a K-injective resolution of L
therefore gives a zero complex, so its ordinary total derived direct image is zero.
6. Boundedness implies boundedness below, so sk-thm-pe-direct-image-comparison applies
to f, which is qcqs: comparison of the etale derived image is isomorphic to the pro-etale
derived image of the comparison of L. Exact comparison commutes with cohomology and
preserves zero. Transfer the interval bound when N is nonnegative and the zero-object
conclusion when N is negative. A zero object has zero cohomology in every degree,
including when b+N<a. No claim on arbitrary pro-etale sheaves is used. -/
theorem etaleOrigin_pushforward_amplitude
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (B : Type u) [CommRing B] [Finite B] (N : ℤ)
    (_hN : ∀ (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))
      (q : ℤ), 0 ≤ q → N < q →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))))
    (a b : ℤ) (_hab : a ≤ b)
    (L : FiniteCoefficientEtaleDerivedCategory X (ULift.{u + 1, u} B))
    (_hL : ∃ c d : ℤ, c ≤ d ∧ ∀ r : ℤ, r < c ∨ d < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj L))
    (_hC : ∀ r : ℤ, r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj
        ((finiteCoefficientIntrinsicDerivedComparison X B).obj L))) :
    (∀ r : ℤ, r < a ∨ b < r →
      IsZero ((DerivedCategory.homologyFunctor _ r).obj L)) ∧
    (∀ i : ℤ, i < a ∨ b + N < i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj
        ((Scheme.proEtaleConstantDerivedDirectImage f B).obj
          ((finiteCoefficientIntrinsicDerivedComparison X B).obj L)))) ∧
    (N < 0 →
      IsZero
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).rightDerivedFunctor.obj L) ∧
      IsZero ((Scheme.proEtaleConstantDerivedDirectImage f B).obj
        ((finiteCoefficientIntrinsicDerivedComparison X B).obj L))) := by
  sorry

end AlgebraicGeometry.ProEtale
