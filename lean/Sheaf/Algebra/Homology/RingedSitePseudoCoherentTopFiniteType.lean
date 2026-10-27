/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import Sheaf.Algebra.Homology.RingedSitePseudoCoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Sheaf.Algebra.Homology.SitePerfectModelRestriction
import Sheaf.Algebra.Homology.SitePerfectUpperModel

/-! # Finite type of the top cohomology of a pseudo-coherent site complex

Source: Stacks Project, sites-cohomology.tex, Tag 08FX, lemma-finite-cohomology (1)
(blueprint: lem-sfb-ringed-site-pseudocoherent-top-finite-type).
-/

@[expose] public section

set_option autoImplicit false

universe u v r w w'

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- The highest possibly nonzero cohomology of an `m`-pseudo-coherent derived object
on a commutative ringed site is locally of finite type, without coherence assumptions.

Source: Stacks Project, Tag 08FX, lemma-finite-cohomology (1)
(blueprint: lem-sfb-ringed-site-pseudocoherent-top-finite-type).

Proof:
1. On a covering of an arbitrary object choose the strictly perfect approximations
   from the definition. Exact slice restriction (lem-sf-site-perfect-restriction-exact)
   identifies restricted cohomology with cohomology of restriction. Thus each approximation
   has vanishing cohomology above m and maps epimorphically onto H^m(K) on that slice.
2. Regard the approximation itself as site-perfect, via its identity local models
   (def-weil-pbc-strict-perfect-coefficient-package). Apply lem-sf-site-perfect-upper-model
   to it, refining the covering to obtain a strictly perfect model zero above m.
3. Its degree-m cohomology is the cokernel of the previous differential. Compose the
   degree-m finite-free retraction with the cokernel projection, the cohomology isomorphism,
   and the restricted epimorphism to H^m(K). Exact restriction preserves that epimorphism.
   Cokernels are sheaf cokernels (def-weil-sheaf-of-modules-category). Covering transitivity
   and successive restriction (def-pur-localized-ringed-site) give the required local
   finite generators on every original object. -/
theorem isFiniteType_top_homology_of_isMPseudoCoherentOnRingedSite
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{max u v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v r}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v r}]
    (R : Sheaf J CommRingCat.{max u v r})
    [HasDerivedCategory.{w} (SheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R))]
    [∀ U : C, HasDerivedCategory.{w'} (SheafOfModules.{max u v r}
      (((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R).over U))]
    (m : ℤ) (K : DerivedCategory (SheafOfModules.{max u v r}
      ((sheafCompose J (forget₂ CommRingCat.{max u v r} RingCat.{max u v r})).obj R)))
    (hK : IsMPseudoCoherentOnRingedSite.{u, v, r, w, w'} R m K)
    (hvan : ∀ i : ℤ, m < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) :
    IsFiniteType ((DerivedCategory.homologyFunctor _ m).obj K) := by
  sorry

end SheafOfModules
