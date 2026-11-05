/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleObjectCohomologyStalkComplex
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.CategoryTheory.Functor.EpiMono
import WeilConjectures.AlgebraicGeometry.StrictHenselianStalkSectionsComparison
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian

/-! # Local lifting of etale sections

Source: Stacks Project, Etale Cohomology, Tags 03Q6, 03QO and 09AX.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

