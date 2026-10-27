/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Sheaf.TraceFormula.ZariskiEtaleFunctorComparisonSquare
public import Sheaf.AlgebraicGeometry.DerivedEtaleZariskiEquivalence
public import Sheaf.AlgebraicGeometry.ProperSupportTensorPerfect
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import WeilConjectures.AlgebraicGeometry.PerfectOfPseudoCoherentLocallyFiniteTor

/-! # Étale pullback detects Zariski perfectness

Source: Stacks Project, spaces-perfect.tex, Tag 08HG (lemma-descend-perfect), and
sites-cohomology.tex, Tag 08G5 (definition-perfect)
(blueprint: lem-sfb-etale-detects-perfect).

The derived extension in `DerivedEtaleZariskiEquivalenceData` is characterized by its
factorization of termwise canonical tensor extension on the homotopy category. It is
defined on all objects, even though its equivalence assertions concern quasi-coherent
cohomology. Site-perfectness uses the existing predicate at the actual section size.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

attribute [instance] CategoryTheory.hasSheafify_addCommGrp_of_weak

namespace AlgebraicGeometry.Scheme.Modules

/-- Canonical étale tensor pullback detects perfectness of arbitrary derived objects.
The parameter `d` presents the canonical pullback: `d.context.extension` is the ringed-site
tensor pullback and `d.extension_factors` identifies its termwise localization with
`d.extension`. No quasi-coherence assumption on the object is made.

Source: Stacks Project, spaces-perfect.tex, Tag 08HG (lemma-descend-perfect), with
sites-cohomology.tex, Tag 08G5 (definition-perfect)
(blueprint: lem-sfb-etale-detects-perfect).

Proof, following the four DAG steps:
1. For a Zariski perfect object, choose strictly perfect models on an open cover
   using def-pc-perfect-complex. Exactness of tensor extension from
   lem-sfb-derived-etale-zariski-equivalence carries their derived isomorphisms to
   the étale site and commutes with restriction to these opens. Pull back each
   degreewise splitting into a finite free module: functoriality preserves its
   identity composite, and tensor pullback preserves the finite free module.
   Bounds are unchanged and the open cover is also an étale cover.
2. Conversely, lem-sfb-ringed-site-perfect-criterion makes the site-perfect
   pullback pseudo-coherent and locally of finite Tor dimension.
3. For every integer m, apply lem-sfb-etale-pseudocoherence-descent to descend
   m-pseudo-coherence, then quantify over m. Apply the local clause of
   lem-sfb-etale-tor-dimension-descent to descend locally finite Tor dimension.
   The bounds vary over the covering; no uniform bound is inferred.
4. Apply lem-pc-pseudo-coherent-locally-finite-tor-perfect to conclude Zariski
   perfectness. None of these steps assumes quasi-coherence, quasi-compactness,
   Noetherianness, or global boundedness. -/
theorem isPerfect_iff_smallEtale_perfect
    [∀ X : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ X : Scheme.{u}, HasDerivedCategory.{w} (SmallEtaleModules X)]
    (T : Scheme.{u})
    [∀ U : T.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings T.toRingedSpace).over U))]
    (d : DerivedEtaleZariskiEquivalenceData T) (A : schemeDerivedCategory T) :
    Scheme.IsPerfect T A ↔
      SheafOfModules.IsPerfectAtCoefficientSize (smallEtaleModuleRing T) (d.extension.obj A) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
