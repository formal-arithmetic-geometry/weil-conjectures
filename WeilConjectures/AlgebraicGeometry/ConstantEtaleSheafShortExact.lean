/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-!
# Short exact sequences of finite constant etale sheaves

Source: Stacks Project, Etale Cohomology, Tag 03RX (3), via Modules on Sites,
Tag 093U, extension argument; Tag 03EI, exactness of module sheafification.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- An exact sequence `0 → K → L → N → 0` of finite left modules over a finite ring
induces an exact sequence of constant sheaves on the small etale site.
Source: Stacks Project, Tags 03RX (3), 093U (extension argument), and 03EI. -/
theorem constantEtaleSheaf_shortExact (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ] [Finite Λ]
    (S : ShortComplex (ModuleCat.{u + 1} Λ)) [Finite S.X₁] [Finite S.X₂] [Finite S.X₃]
    (hS : S.ShortExact) :
    (S.map (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))).ShortExact := by
  exact hS.map_of_exact (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))

end AlgebraicGeometry.Scheme
