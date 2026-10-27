/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Abelian.Subcategory

import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Mathlib.CategoryTheory.Abelian.Subcategory
import Sheaf.AlgebraicGeometry.QuasiCoherentBoundedSubmoduleUnion

/-!
# Grothendieck generators for quasi-coherent sheaves on arbitrary schemes

Source: Stacks Project, Properties, Tag 077P, proposition-coherator (1), and Schemes,
Tag 01LA, section-quasi-coherent
(blueprint: lem-sfb-qcoh-grothendieck-generators).

The category and inclusion are Mathlib's full subcategory for `isQuasicoherent`.
The abelian structure is part of the conclusion, rather than a hypothesis.
Small diagrams have both object and morphism universes `u`, the module universe.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- On every scheme, quasi-coherent modules form a Grothendieck abelian category.
Their inclusion is exact and creates all small colimits, and there is a generator
whose covariant Hom functor is faithful. Exact filtered colimits are the `ab5OfSize`
field of `IsGrothendieckAbelian`; existence of all small colimits follows from its
`hasColimits` instance. No quasi-compactness, quasi-separatedness or Noetherian
hypothesis is required.

Source: Stacks Project, Properties, Tag 077P, proposition-coherator (1), and Schemes,
Tag 01LA, section-quasi-coherent
(blueprint: lem-sfb-qcoh-grothendieck-generators).

Proof:
1. Form any small ambient colimit using
   `lem-pc-scheme-modules-grothendieck-abelian`. On each affine open, restriction
   preserves it (`lem-weil-pbc-module-restriction-open-immersion-colimits`). The
   colimit M of the section modules exists
   (`lem-weil-pbc-ring-modules-grothendieck-abelian`). The tilde/global-sections
   counit identifies each quasi-coherent term with the tilde of its sections, and
   tilde preserves colimits (both clauses of
   `lem-weil-pbc-affine-tilde-gamma-adjunction`), so the restricted colimit is the
   tilde of M, quasi-coherent by `lem-weil-pbc-spec-module-tilde-sections`. Thus the
   ambient colimit is quasi-coherent by `pqf-def-coherent`. Fullness restricts its
   universal property, proving creation, including the empty and finite colimits.
2. Ambient kernels and cokernels are quasi-coherent by
   `lem-weil-pbc-quasi-coherent-module-kernel` and
   `lem-weil-pbc-quasi-coherent-module-cokernel-image`. With zero and finite sums
   from step 1, `lem-weil-pbc-abelian-full-subcategory-exact` gives the abelian
   structure and exact inclusion, expressed by preservation of finite limits and
   finite colimits.
3. The ambient filtered colimit of short exact sequences is exact by
   `lem-pc-scheme-modules-grothendieck-abelian`. Creation of colimits and reflection
   of exactness by the full inclusion give exact filtered colimits here.
4. Choose the cardinal from `lem-sfb-qcoh-bounded-submodule-union`. By
   `lem-sfb-bounded-generated-module-isoclasses`, the bounded-generated modules have
   a small set of representatives. Retain the quasi-coherent ones, using invariance
   under isomorphism (`pqf-def-coherent`), and take their coproduct G by step 1.
   Distinct maps out of F differ on some bounded quasi-coherent submodule N, since
   those inclusions are jointly epimorphic by their colimit description. Choose a
   representative M isomorphic to N. The coproduct map G to M which is identity on
   its own summand and zero on the others, followed by M to N to F, distinguishes
   the maps. Hence Hom(G,-) is faithful, also when X is empty.
5. Steps 1--4 give precisely `def-sp-grothendieck-abelian`, with the exact inclusion,
   colimit creation and faithful Hom functor already established. All sets and
   cardinals have the fixed sizes of `def-weil-size-convention`.
-/
theorem quasiCoherent_grothendieck_generators (X : Scheme.{u}) :
    ∃ hAb : Abelian (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory,
      @IsGrothendieckAbelian.{u} _ _ hAb ∧
      PreservesFiniteLimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ∧
      PreservesFiniteColimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ∧
      Nonempty (CreatesColimitsOfSize.{u, u}
        (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι) ∧
      ∃ G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory,
        (coyoneda.obj (Opposite.op G)).Faithful := by
  sorry

/-- Closure properties and exactness for the induced abelian structure, with the
ambient addition and ambient kernels and cokernels.
Source: Stacks Project, Properties, Tag 077P (1), and Schemes, Tag 01LA
(blueprint: lem-sfb-qcoh-grothendieck-generators).

Proof: The zero module and finite sums are quasi-coherent by the affine tilde
construction. The kernel and cokernel closure assertions follow from
`lem-weil-pbc-quasi-coherent-module-kernel` and
`lem-weil-pbc-quasi-coherent-module-cokernel-image`, transporting along the
unique isomorphisms between limiting cones. Finite products equal finite sums.
Mathlib's full-subcategory abelian construction therefore uses precisely the
ambient addition, kernels and cokernels. Its inclusion preserves kernels and
finite products, and cokernels and finite coproducts, hence finite limits and
finite colimits. This is the exact inclusion in the Grothendieck theorem above. -/
theorem quasiCoherent_inducedAbelianClosure (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero ∧
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderKernels ∧
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderCokernels ∧
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderFiniteProducts ∧
    PreservesFiniteLimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι ∧
    PreservesFiniteColimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι := by
  sorry

/-- The zero quasi-coherent module. Source: Stacks Tag 077P (1)
(blueprint: lem-sfb-qcoh-grothendieck-generators). -/
instance quasiCoherent_containsZero (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).ContainsZero :=
  (quasiCoherent_inducedAbelianClosure X).1

/-- Closure under ambient kernels. Source: Stacks Tag 077P (1)
(blueprint: lem-sfb-qcoh-grothendieck-generators). -/
instance quasiCoherent_closedUnderKernels (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderKernels :=
  (quasiCoherent_inducedAbelianClosure X).2.1

/-- Closure under ambient cokernels. Source: Stacks Tag 077P (1)
(blueprint: lem-sfb-qcoh-grothendieck-generators). -/
instance quasiCoherent_closedUnderCokernels (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderCokernels :=
  (quasiCoherent_inducedAbelianClosure X).2.2.1

/-- Closure under ambient finite products. Source: Stacks Tag 077P (1)
(blueprint: lem-sfb-qcoh-grothendieck-generators). -/
instance quasiCoherent_closedUnderFiniteProducts (X : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).IsClosedUnderFiniteProducts :=
  (quasiCoherent_inducedAbelianClosure X).2.2.2.1

/-- Left exactness of the full inclusion. Source: Stacks Tag 077P (1)
(blueprint: lem-sfb-qcoh-grothendieck-generators). -/
instance quasiCoherent_inclusion_preservesFiniteLimits (X : Scheme.{u}) :
    PreservesFiniteLimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
  (quasiCoherent_inducedAbelianClosure X).2.2.2.2.1

/-- Right exactness of the full inclusion. Source: Stacks Tag 077P (1)
(blueprint: lem-sfb-qcoh-grothendieck-generators). -/
instance quasiCoherent_inclusion_preservesFiniteColimits (X : Scheme.{u}) :
    PreservesFiniteColimits (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι :=
  (quasiCoherent_inducedAbelianClosure X).2.2.2.2.2

end AlgebraicGeometry.Scheme.Modules
