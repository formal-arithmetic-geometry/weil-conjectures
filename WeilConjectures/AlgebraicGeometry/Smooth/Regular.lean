/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.RingTheory.Smooth.Regular

/-!
# Smooth schemes over a field have regular local rings

A scheme smooth over a field has regular local rings at every point.  This is one of the two
inputs of miracle flatness for the multiplication-by-`n` isogeny of an abelian variety.

## Main results

* `AlgebraicGeometry.Smooth.isRegularLocalRing_stalk`: if `f : X ⟶ Spec k` is smooth for a
  field `k`, then `𝒪_{X, x}` is a regular local ring for every `x : X`.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

/-- **The local rings of a smooth scheme over a field are regular.**

A smooth morphism is standard smooth on a neighbourhood of every point, a standard smooth algebra
over a regular ring is a regular ring, and the stalk is a localisation of the sections over an
affine neighbourhood. -/
theorem Smooth.isRegularLocalRing_stalk {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hxV, e, hss⟩ := Smooth.exists_isStandardSmooth f x
  -- `Spec k` has a single point, so the affine open `U` is the whole of `Spec k`
  obtain rfl : U = ⊤ := by
    ext y
    simpa using Subsingleton.elim y (f.base x) ▸ e hxV
  -- the sections over `V` form a standard smooth algebra over `k`
  let : Algebra Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) := (f.appLE ⊤ V e).hom.toAlgebra
  have : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of k), ⊤) Γ(X, V) := hss
  have : IsRegularRing Γ(Spec (CommRingCat.of k), ⊤) :=
    IsRegularRing.of_ringEquiv (R := k)
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  have : IsRegularRing Γ(X, V) :=
    Algebra.IsStandardSmooth.isRegularRing (R := Γ(Spec (CommRingCat.of k), ⊤))
  -- and the stalk is a localisation of these sections at a prime
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (U := V) ⟨x, hxV⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
      (Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal)
      (X.presheaf.stalk x)).toRingEquiv

end AlgebraicGeometry
