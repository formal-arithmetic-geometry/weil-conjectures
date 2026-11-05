/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAlgebra
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
import WeilConjectures.CategoryTheory.SheafAlgebrasDirectedColimit

/-! # Directed colimits of quasi-coherent algebra sheaves

Source: Stacks Project, Schemes, Lemma 01ID and Section 26.24; Sheaves,
Section 009E and Lemma 0087; Modules, Lemmas 01AH and 01AJ
(blueprint: lem-weil-pbc-quasi-coherent-algebra-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
