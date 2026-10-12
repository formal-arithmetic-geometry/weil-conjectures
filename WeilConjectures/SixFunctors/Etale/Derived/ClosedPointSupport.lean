/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
public import WeilConjectures.SixFunctors.Etale.Derived.Point
public import WeilConjectures.ConstructibleSheaf.StalkZeroLocus

/-!
# Complexes supported on closed points

A morphism of bounded constructible complexes on a scheme of finite type over an algebraically
closed field which is an isomorphism on the geometric stalks at the nonclosed points and after
`Ra_*` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **Detection on closed points and global sections.** Let `X` be of finite type over an
algebraically closed field `k`, with structure morphism `a`, and let `f : K ⟶ L` be a morphism
of bounded constructible complexes on `X_ét` whose geometric stalks are isomorphisms at every
nonclosed point. Then the cone of `f` is supported on finitely many closed points, and `f` is an
isomorphism as soon as `Ra_* f` is. -/
theorem isIso_of_isIso_rightDerivedLowerStar_map_of_not_isClosed {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [LocallyOfFiniteType a]
    [QuasiCompact a]
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hL : boundedConstructible (ModuleCat.{u + 1} Λ) X L) (f : K ⟶ L)
    (hf : ∀ (x : X), ¬ IsClosed ({x} : Set X) → ∀ q : ℤ,
      IsIso ((X.uliftPointSmallEtale x).sheafFiber.map
        ((_root_.DerivedCategory.homologyFunctor _ q).map f)))
    (ha : IsIso ((R((a)_*[ModuleCat.{u + 1} Λ])).map f)) :
    IsIso f :=
  sorry

end Etale

end AlgebraicGeometry
