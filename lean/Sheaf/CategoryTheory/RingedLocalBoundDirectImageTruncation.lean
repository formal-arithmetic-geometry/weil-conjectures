/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Sheaf.CategoryTheory.RingedLocalBoundProperty
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import WeilConjectures.Algebra.Homology.LowerTruncationStepTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.ShiftIdentification
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.CategoryTheory.TruncationHypercohomology

/-! # Unbounded direct image and lower truncation under local bounds

Source: Stacks Project, Cohomology on Sites, Tag 0D6U,
`lemma-olsson-laszlo-map-version-one`, with Tag 0D6R
(blueprint: lem-sfb-ringed-local-bound-direct-image-truncation).
-/

@[expose] public section

set_option autoImplicit false

universe u w e

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Unbounded direct image preserves the prescribed weak Serre cohomology class,
and its canonical lower-truncation comparison is an isomorphism in the stated range.
Source: Stacks Tag 0D6U, `lemma-olsson-laszlo-map-version-one`
(blueprint: lem-sfb-ringed-local-bound-direct-image-truncation).

The functor `Rf` and its resolution unit specify the total right derived direct image;
the unit is required to be invertible on K-injectives, so it is computed by their
resolutions. The two commutativity predicates concern the existing ring structures.

Proof (the four steps of the node):
1. Set T_n = tau_{>=-n} K and L_n = Rf T_n. Good truncation puts T_n in D_A^+.
Module categories admit K-injective resolutions. Direct image is additive and left
exact, since the underlying right adjoint preserves kernels and its induced action
makes their factorizations linear. The bounded-below hypercohomology spectral sequence
(thm-sp-truncation-e2) has E2 = R^p f_* H^q(T_n). Weak Serre kernel, cokernel and extension
closure puts its pages and its finite-filtration abutments in B. Hence L_n lies in D_B^+.
2. Apply the triangulated derived functor to the successive lower-truncation triangle
(lem-pc-derived-lower-truncation-step-triangle). Shift identification and the bound N
annihilate the two outer terms of the long exact sequence in degree j >= N-n for
r >= n+1. Thus H^j(L_r) -> H^j(L_{r-1}) is invertible, including j = N-n.
3. Source local-bound reconstruction identifies K with Rlim T_n
(lem-sfb-ringed-local-bound-truncation-reconstruction). Pushforward-limit comparison
(lem-weil-ringed-tower-pushforward-limit-comparison) identifies Rf K with Rlim L_n,
compatibly with every canonical projection. This requires no flatness of f.
4. Put n_j = max(0,N-j). The stationary-limit cohomology theorem
(lem-sfb-ringed-local-bound-stationary-limit-cohomology) identifies H^j(Rlim L_m)
with H^j(L_n) for n >= n_j. Those objects lie in B, proving the first conclusion.
The inequality j >= N-n implies n >= n_j, giving precisely the displayed map. -/
theorem ringedLocalBoundDirectImageTruncation
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : Precoverage C) (L : Precoverage D)
    (_hJ : J.IsSiteForCoverings) (_hL : L.IsSiteForCoverings)
    (O : Sheaf J.toGrothendieck RingCat.{u})
    (R : Sheaf L.toGrothendieck RingCat.{u})
    (_hO : ∀ (U : Cᵒᵖ) (a b : O.obj.obj U), a * b = b * a)
    (_hR : ∀ (U : Dᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasExt.{e} (Sheaf J.toGrothendieck AddCommGrpCat.{u})]
    [HasExt.{e} (Sheaf L.toGrothendieck AddCommGrpCat.{u})]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} O)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R)]
    (f : RingedToposMorphism O R)
    (P : ObjectProperty (ringedSiteModules.{u, u, u, u} O))
    (Q : ObjectProperty (ringedSiteModules.{u, u, u, u} R))
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]
    [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms]
    [Q.IsClosedUnderKernels] [Q.IsClosedUnderCokernels] [Q.IsClosedUnderExtensions]
    (_hlocalO : HasRingedLocalBoundProperty J O P)
    (_hlocalR : HasRingedLocalBoundProperty L R Q)
    (Rf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} O) ⥤
      DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R))
    (η : f.modules.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ Rf)
    (_hderived : Rf.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} O) (ComplexShape.up ℤ)))
    (_hKI : ∀ I : CochainComplex (ringedSiteModules.{u, u, u, u} O) ℤ,
      I.IsKInjective → IsIso (η.app I))
    (N : ℤ)
    (_himage : ∀ F : ringedSiteModules.{u, u, u, u} O, P F → ∀ p : ℕ,
      Q ((DerivedCategory.homologyFunctor _ (p : ℤ)).obj
        (Rf.obj ((DerivedCategory.singleFunctor _ 0).obj F))))
    (_hvanish : ∀ F : ringedSiteModules.{u, u, u, u} O, P F → ∀ p : ℕ,
      N < (p : ℤ) → IsZero ((DerivedCategory.homologyFunctor _ (p : ℤ)).obj
        (Rf.obj ((DerivedCategory.singleFunctor _ 0).obj F))))
    (K : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} O))
    (_hK : ∀ j : ℤ, P ((DerivedCategory.homologyFunctor _ j).obj K)) :
    (∀ j : ℤ, Q ((DerivedCategory.homologyFunctor _ j).obj (Rf.obj K))) ∧
      ∀ (n : ℕ) (j : ℤ), N - (n : ℤ) ≤ j →
        IsIso ((DerivedCategory.homologyFunctor _ j).map
          (Rf.map ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) := by
  sorry

end CategoryTheory
