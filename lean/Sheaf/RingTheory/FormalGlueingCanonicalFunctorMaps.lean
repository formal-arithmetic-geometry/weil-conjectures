/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RingTheory.FormalGlueingData
import Sheaf.Paper.FormalGlueingCanonicalMaps

@[expose] public section

universe u v w

open CategoryTheory
namespace FormalGlueing

/-- Given canonical glueing objects, construct their canonical morphism assignment.
This constructs maps; it does not identify maps of an arbitrary functor.
Source: Stacks Project, More on Algebra, Remark 05EL, construction of `Can` on maps.
(blueprint: lem-weil-pbc-formal-glueing-canonical-functor-maps).
Proof: transport extendMap φ h.hom and localMap (f i) h.hom along the given
prime and chart module equalities. For charts, restriction to R agrees with the
localized R-action by algebraMap_smul. The prime compatibility equation sends
(s tensor m)/f_i^a to s tensor (h(m)/f_i^a) on both sides, by compare_properties
and the fraction formula for localization maps. Tensor and localization induction
prove equality on all elements. The chart compatibility equation sends
(m/f_i^a)/f_j^b to (h(m)/f_j^b)/f_i^a on both sides, by swap_properties.
These equations construct a Hom for every h. Tensor base change and localization
preserve identities and composition (LinearMap.baseChange_id,
LinearMap.baseChange_comp and LocalizedModule.away_map_functorial). Hence the
constructed Homs preserve them componentwise. Hom has only prime and chart data;
its other fields are proofs, so componentwise equality proves both laws.
Transport along the fixed object equalities respects these laws. Empty chart
families and zero localizations cause no exception to these calculations. -/
theorem canonical_functor_maps {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R)
    (obj : ModuleCat.{max u v w} R → Data.{u, v, max u v w} φ f)
    (hobj : ∀ M : ModuleCat.{max u v w} R,
      (obj M).M' = extend φ M ∧
      (∀ i : Fin t, (obj M).M i =
        ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
      (∀ i : Fin t, HEq ((obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
      (∀ i j : Fin t,
        HEq ((obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))) :
    ∃ map : ∀ {M N : ModuleCat.{max u v w} R}, (M ⟶ N) → (obj M ⟶ obj N),
      (∀ M, map (𝟙 M) = 𝟙 (obj M)) ∧
      (∀ {M N P} (h : M ⟶ N) (k : N ⟶ P), map (h ≫ k) = map h ≫ map k) ∧
      (∀ (M N : ModuleCat.{max u v w} R) (h : M ⟶ N),
        HEq (map h).prime (extendMap φ h.hom) ∧
        ∀ i : Fin t, HEq ((map h).chart i) (localMap (f i) h.hom)) := by
  sorry

end FormalGlueing
