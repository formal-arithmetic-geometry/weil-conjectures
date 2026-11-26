/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.FormalGlueingData
import WeilConjectures.RingTheory.FormalGlueingCanonicalFunctorObjects
import WeilConjectures.RingTheory.FormalGlueingCanonicalFunctorMaps

/-!
# Construction of the canonical formal glueing functor

We assemble the canonical formal glueing objects and maps into the canonical functor from
`R`-modules to formal glueing data, without any flatness or quotient hypothesis.

## References

* [Stacks, Tag 05EL]
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace FormalGlueing

/-- The prescribed objects and maps form the canonical functor, without any flatness
or quotient hypothesis: it sends `M` to `S ⊗_R M` with charts `M_{f i}`, glued by the
comparison and swap maps, and sends a linear map to its base change and localizations. -/
theorem exists_canonical_functor {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S) (t : ℕ) (f : Fin t → R) :
    ∃ Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f,
      (∀ M : ModuleCat.{max u v w} R,
        (Can.obj M).M' = extend φ M ∧
        (∀ i : Fin t, (Can.obj M).M i =
          ModuleCat.of (Localization.Away (f i)) (LocalizedModule.Away (f i) M)) ∧
        (∀ i : Fin t, HEq ((Can.obj M).alpha i).toLinearMap (compare φ (f i) M)) ∧
        (∀ i j : Fin t,
          HEq ((Can.obj M).alpha_overlap i j).toLinearMap (swap (f i) (f j) M))) ∧
      (∀ (M N : ModuleCat.{max u v w} R) (h : M ⟶ N),
        HEq (Can.map h).prime (extendMap φ h.hom) ∧
        ∀ i : Fin t, HEq ((Can.map h).chart i) (localMap (f i) h.hom)) := by
  classical
  let obj := fun M : ModuleCat.{max u v w} R ↦
    (exists_canonical_functor_objects φ t f M).choose
  have hobj := fun M : ModuleCat.{max u v w} R ↦
    (exists_canonical_functor_objects φ t f M).choose_spec
  obtain ⟨map, hid, hcomp, hmap⟩ := canonical_functor_maps φ t f obj hobj
  let Can : ModuleCat.{max u v w} R ⥤ Data.{u, v, max u v w} φ f :=
    { obj := obj
      map := map
      map_id := hid
      map_comp := hcomp }
  exact ⟨Can, hobj, hmap⟩

end FormalGlueing
