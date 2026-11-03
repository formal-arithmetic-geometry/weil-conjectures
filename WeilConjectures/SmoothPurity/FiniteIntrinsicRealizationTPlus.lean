/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap

/-!
# Bounded-below intrinsic finite realization

Source: blueprint `thm-pur-finite-reduction-of-purity.proof.md`, Step 4:
normalized finite counit paragraph (blueprint: lem-route-finite-intrinsic-realization-tplus).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures

/-- The inverse intrinsic realization of a finite bounded constructible finite-Tor object is
bounded below. This is the bounded-below branch required by the published exceptional counit.
Source: blueprint `thm-pur-finite-reduction-of-purity.proof.md`, Step 4:
normalized finite counit paragraph (blueprint: lem-route-finite-intrinsic-realization-tplus).
Proof. Step 1: by def-weil-finite-tor-amplitude, `K^i = I_Y K` satisfies
`intrinsicFiniteTorsionConstructible` (def-weil-finite-torsion-constructibility), whose first
clause says that the set of degrees `i` with `H^i(K^i) ≠ 0` is finite, hence bounded below by
some `a` (also when it is empty); so `H^i(K^i) = 0` for `i < a`, i.e. `K^i ∈ D^{≥a}`
(def-sbc-standard-tstructure-derived-category, `DerivedCategory.isGE_iff`; Stacks Tag 05RV).
Step 2: `sfIntrinsicDerivedEquivalence Y A` is
`(sfIntrinsicModuleEquivalence Y A).mapDerivedCategory`,
whose inverse is `G.mapDerivedCategory` for the exact inverse abelian equivalence `G`; by
lem-weil-pbc-exact-functor-bounded-below (`Functor.isGE_mapDerivedCategory_obj`),
`L = E_Y^{-1}(K^i) ∈ D^{≥a}`. Step 3: `DerivedCategory.TStructure.t.plus L` is the existence
of an integer `a` with `L ∈ D^{≥a}` (def-weil-pbc-bounded-derived-subcategories); supply `a`.
The zero object and the empty scheme are covered by the same argument.
-/
theorem finiteIntrinsicRealization_tplus
    (P : PurityFiniteSetting.{u}) {Y : Scheme.{u}}
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [IsSeparated (Y ↘ Spec (.of P.field.k))]
    (K : finiteTorConstructibleCategory P.coefficients.l P.extension P.level
      P.level_pos Y) :
    DerivedCategory.TStructure.t.plus
      ((Scheme.sfIntrinsicDerivedEquivalence Y P.Ring).inverse.obj
        ((finiteTorConstructible P.coefficients.l P.extension P.level P.level_pos Y).ι.obj K)) := by
  classical
  obtain ⟨a, ha⟩ := K.property.1.1.bddBelow
  have hK : K.obj.IsGE a := (DerivedCategory.isGE_iff K.obj a).2 (by
    intro i hi
    by_contra hn
    exact (not_lt_of_ge (ha hn)) hi)
  refine ⟨a, ?_⟩
  exact (Scheme.sfIntrinsicModuleEquivalence Y P.Ring).inverse.isGE_mapDerivedCategory_obj
    K.obj a

end WeilConjectures
