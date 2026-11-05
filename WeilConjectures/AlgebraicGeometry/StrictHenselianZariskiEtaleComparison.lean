/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.LocallyInjective
import WeilConjectures.AlgebraicGeometry.StrictHenselianCohomologyLocallyZero
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCanonicalLeray

/-!
# Étale and Zariski cohomology over strictly henselian schemes

Source: literature/stacks-project/etale-cohomology.tex, Lemma 09AX
(blueprint: lem-weil-pbc-gabber-strict-henselian-zariski-comparison)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

