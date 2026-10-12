/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.IdealModuleProductStalk
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.Algebra.Homology.ShortComplex.Exact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Sheaf.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting

/-! # Annihilator calculus for sheaves of modules

Source: Stacks Project, proof of Lemma 0CYV, part (2).
(blueprint: lem-weil-pbc-ideal-module-product-exact-calculus).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Annihilation passes to submodules and quotients. In an exact complex, the product
of ideals annihilating the outer terms annihilates the middle term.

Source: Stacks Project, proof of Lemma 0CYV, part (2), the annihilator argument.
(blueprint: lem-weil-pbc-ideal-module-product-exact-calculus).

Proof: An ideal product is the image of the multiplication map. Its sections are locally
finite sums of products of ideal sections and module sections. Thus its vanishing means
that every such product is zero. For a monomorphism, multiplying a section of the source
and then mapping to the target gives zero; sectionwise injectivity makes the source
product zero. For an epimorphism, lift each target section on an open cover; its product
with an ideal section is locally the image of a zero product, hence zero by the sheaf
condition. Finally, if J annihilates the first term and K the third term, then for a middle
section b and k in K, the section kb maps to zero in the third term. Exactness gives
local lifts of kb to the first term, so jkb vanishes for every j in J. Sections of the
product ideal J*K are locally sums of such jk, so (J*K) annihilates the middle term.
The argument works for zero ideals, zero modules and the empty scheme; it uses exactness
at the middle term only, and does not assume the first arrow is injective. -/
theorem idealModuleProduct_exact_calculus (X : Scheme.{u}) :
    (∀ (J : X.IdealSheafData) {F G : X.Modules} (a : F ⟶ G) [Mono a],
      IsZero (idealModuleProduct J.toModulesι G) →
        IsZero (idealModuleProduct J.toModulesι F)) ∧
    (∀ (J : X.IdealSheafData) {F G : X.Modules} (a : F ⟶ G) [Epi a],
      IsZero (idealModuleProduct J.toModulesι F) →
        IsZero (idealModuleProduct J.toModulesι G)) ∧
    (∀ (J K : X.IdealSheafData) (T : ShortComplex X.Modules), T.Exact →
      IsZero (idealModuleProduct J.toModulesι T.X₁) →
      IsZero (idealModuleProduct K.toModulesι T.X₃) →
        IsZero (idealModuleProduct (J * K).toModulesι T.X₂)) := by sorry

end AlgebraicGeometry.Scheme
