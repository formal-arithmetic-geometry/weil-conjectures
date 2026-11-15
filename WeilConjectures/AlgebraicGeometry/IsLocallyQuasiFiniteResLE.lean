/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.AlgebraicGeometry.IsolatedFiberPointQuasiFiniteAffinePairs
import WeilConjectures.AlgebraicGeometry.LocallyOfFiniteTypeOfIsLocallyQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated

/-!
# Restriction of locally quasi-finite morphisms to open subschemes

## References

* Stacks Project, Morphisms of Schemes, Tags 01TD and 01TH, as invoked in Tag 03JA.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- Restricting a locally quasi-finite morphism to open subschemes preserves local
quasi-finiteness in the Stacks sense, including the finite-type requirement.
(Stacks, Tags 01TD, 01TH, 03JA)

The open immersions are `U.ι` and `V.ι`; the canonical restriction `f.resLE V U e`
satisfies `f.resLE V U e ≫ V.ι = U.ι ≫ f`. -/
theorem isLocallyQuasiFinite_resLE {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (hf : IsLocallyQuasiFinite f) (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    IsLocallyQuasiFinite (f.resLE V U e) := by
  have : AlgebraicGeometry.LocallyOfFiniteType f :=
    locallyOfFiniteType_of_isLocallyQuasiFinite f hf
  intro x
  have hx : f.QuasiFiniteAt (U.ι x) :=
    quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr
      (quasiFiniteAtPoint_isolated_in_fiber f (U.ι x) (hf (U.ι x))).1
  have hx' : (f.resLE V U e).QuasiFiniteAt x := by
    rwa [← quasiFiniteAt_comp_iff (g := V.ι), resLE_comp_ι,
      quasiFiniteAt_comp_iff_of_isOpenImmersion]
  have hisolated : IsOpen ({(f.resLE V U e).asFiber x} :
      Set ((f.resLE V U e).fiber ((f.resLE V U e) x))) :=
    quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hx'
  obtain ⟨V', hV', hyV', _⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (X := V) (x := (f.resLE V U e) x) (U := ⊤) (by trivial)
  obtain ⟨U', hU', hxU', hUV'⟩ := AlgebraicGeometry.exists_isAffineOpen_mem_and_subset
    (X := U) (x := x) (U := (f.resLE V U e) ⁻¹ᵁ V') hyV'
  exact ⟨U', hxU', hU', V', hV', hUV',
    isQuasiFiniteAtPrime_of_isOpen_singleton_asFiber (f.resLE V U e) x hisolated
      U' V' hU' hV' hxU' hUV'⟩

end AlgebraicGeometry.Scheme.Hom
