/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Sheaf.CategoryTheory.SiteCechComplex

/-!
# Cocycle lifting with coefficients large enough for morphisms and cover indices

Source: Stacks Project, Cohomology on Sites, Tags 03FC, 03AS, 03F5 and 03AT.
-/

@[expose] public section

universe u v w

namespace CategoryTheory

/-- A positive cocycle in an injective module presheaf has a primitive when its
coefficient universe contains the hom and index universes. No topology is required.
Source: Stacks Project, Cohomology on Sites, proof of Tag 03FC after Tag 03FB,
using Tags 03AS, 03F5 and 03AT.
(blueprint: lem-weil-pbc-injective-presheaf-module-cech-cocycle-lift-max)

Proof: Put a = max v w. Form the free R-module presheaf K_n on the disjoint union
of Hom(X,W(n,t)) over (n+1)-tuples t. Lift the hom sets to universe a before taking
free modules; both those hom sets and the tuples are a-small. The deletion maps
and alternating signs give a chain complex. At X, partition its basis by the
composite X -> U. Each fibre is the tuple complex on the set of lifts of that
composite to the family. Empty lift sets give zero. Inserting a chosen lift in
nonempty lift sets contracts this complex in positive degrees. Direct sums are
exact, and exactness in module presheaves is objectwise, so K is exact at q+1.
Free Yoneda identifies Hom(K_n,M) with the specified cochains, with boundary
precomposition corresponding to differentialValue. A cocycle gives a map
K_(q+1) -> M killing the incoming boundary; exactness factors this map through
the image in K_q. Injectivity extends it along the image inclusion to K_q.
Yoneda takes this extension to the desired primitive. All free values lie in a,
so no injectivity across different coefficient universes is assumed. This treats
q=0, the empty family, empty lift fibres, and the zero ring or zero module. -/
theorem injective_presheaf_module_cech_cocycle_lift_max
    {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ RingCat.{max v w})
    (M : PresheafOfModules.{max v w} R) [Injective M]
    {T : Type (max v w)} {U : C} (f : T → C) (hom : ∀ t, f t ⟶ U)
    (S : SiteCechComplex f hom) (q : ℕ)
    (c : S.cochains M.presheaf (q + 1))
    (hc : S.differentialValue M.presheaf (q + 1) c = 0) :
    ∃ b : S.cochains M.presheaf q, S.differentialValue M.presheaf q b = c := by sorry

end CategoryTheory
