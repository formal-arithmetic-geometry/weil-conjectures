/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor



/-! # BoundedConstructibleHomSingle

The remaining local internal-Hom calculation on constructible sheaves in degree zero.
-/

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open scoped CategoryTheory.Obj
open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] {k : Type u} [Field k]
variable (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom]

/-- Internal Hom of two constructible sheaves placed in single degrees is bounded
constructible.

Source: Bhatt--Scholze, Proposition 6.8.11(3), Remark 6.8.15; blueprint
`lem-sfb-dc-hom-preserves`. For integral coefficients, the integral comparison identifies
constructible sheaves with locally derived-complete finite scalar local models. Reduction
modulo a uniformizer commutes with internal Hom by its perfect two-term resolution.
Finite-field internal-Hom finiteness bounds this reduction and makes its homology
constructible. The target is locally derived complete: tensor-Hom adjunction turns Hom
from each inverted-ideal localization into Hom with zero target. Apply the integral
cohomological criterion, and convert scalar models back to local finite presentations.
For rational coefficients take integral representatives and use constructible internal-Hom
continuity for the uniformly bounded-below localization tower. The evaluation-normalized
scalar adjunction identifies this localization with rational internal Hom. For algebraic
closure coefficients descend both inputs to one finite extension and use finite-free
scalar extension and filtered internal-Hom continuity. A supplied unit-ball coefficient is
identified with its integral realization. Single shifts change only the cohomological
bounds. Zero sheaves and empty schemes give zero Hom, and rank-zero presentations apply.
(blueprint: lem-sfb-dc-hom-single) -/
theorem boundedConstructible_hom_single
    {ℓ : ℕ} [IsEllAdicFinitenessCoefficient ℓ Λ] [Fact (ringChar k ≠ ℓ)]
    (n : ℤ) (F G : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left))
    (hF : IsConstructibleModuleObject (condensedRingObj Λ X.left) F)
    (hG : IsConstructibleModuleObject (condensedRingObj Λ X.left) G) :
    boundedConstructible (condensedRingObj Λ X.left)
      ((ihom ((DerivedCategory.singleFunctor _ n).obj F)).obj
        ((DerivedCategory.singleFunctor _ 0).obj G)) := by
  sorry


end AlgebraicGeometry.ProEtale.CondensedRing
