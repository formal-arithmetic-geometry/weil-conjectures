/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.RingTheory.Noetherian.Basic
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.Paper.ConstantModuleSectionProperties
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-!
# Finite type locally constant module sheaves form a weak Serre subcategory

Source: Stacks Project, Modules on Sites, Tag 093U (3)
(blueprint: lem-weil-pbc-locally-constant-derived-serre).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

/-- Finite type locally constant module sheaves are closed under kernels, cokernels and
extensions. Source: Stacks Project, Modules on Sites, Tag 093U (3)
(blueprint: lem-weil-pbc-locally-constant-derived-serre).

Proof plan:
1. On each object pass to its slice and successively trivialize both sheaves. Compose covers
and use relocalization. Restriction is exact: kernels are sectionwise and epimorphisms are
locally surjective, also on slices. The faithful exact forgetful functor transfers this to
module sheaves. Constants restrict canonically to constants.
2. A morphism between constant finite modules is locally induced by a linear map. Constant
module section exactness identifies its kernel and cokernel with constants of the algebraic
kernel and cokernel. Noetherianity makes the kernel finite; quotient generators give finite
cokernel. Empty-cover members have zero restriction.
3. For an extension trivialize the outer terms to constants M and N. Choose a finite free
surjection B^t onto N. Its kernel K is finite by Noetherianity. Constant section exactness
provides the corresponding constant short exact sequence, including t = 0.
4. Local surjectivity lifts the finitely many generators of N after successive refinements.
Their linear combination defines a map from the constant free module to the middle sheaf;
the constant sheafification universal property extends it and verifies its composite.
5. The kernel property gives g from the constant K to the constant M. The maps
k ↦ (-g(k), k) and (m, v) ↦ i(m) + lift(v) present the middle sheaf as the cokernel of the
first map: the second is locally surjective and its kernel is the image of the first.
6. Refine until g comes from a linear h. Additivity identifies the constant direct sum;
constant section exactness identifies the cokernel with the constant algebraic quotient
(M ⊕ B^t)/{(-h(k), k)}. Images of finite generators generate this quotient. Empty-cover
members are zero; composition of all covers proves extension closure without using points.
The proof uses the localized-ringed-site construction, local surjectivity, exact forgetful
functor, constant restriction, local constant morphisms, constant section exactness and
Noetherian finite-submodule lemmas recorded in the node. -/
theorem finiteTypeLocallyConstant_closedUnder_kernels_cokernels_extensions
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (B : Type u) [CommRing B] [IsNoetherianRing B] :
    (∀ (F G : CategoryTheory.ringedSiteModules.{u}
        ((constantSheaf J RingCat.{u}).obj (RingCat.of B))) (f : F ⟶ G),
      IsFiniteTypeLocallyConstant J B F → IsFiniteTypeLocallyConstant J B G →
        IsFiniteTypeLocallyConstant J B (kernel f) ∧
        IsFiniteTypeLocallyConstant J B (cokernel f)) ∧
    (∀ S : ShortComplex (CategoryTheory.ringedSiteModules.{u}
        ((constantSheaf J RingCat.{u}).obj (RingCat.of B))),
      S.ShortExact → IsFiniteTypeLocallyConstant J B S.X₁ →
        IsFiniteTypeLocallyConstant J B S.X₃ → IsFiniteTypeLocallyConstant J B S.X₂) := by
  sorry

end SheafOfModules
