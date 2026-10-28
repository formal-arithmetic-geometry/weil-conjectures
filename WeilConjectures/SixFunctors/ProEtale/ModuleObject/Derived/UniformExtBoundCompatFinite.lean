/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing

/-!
# Compatibility: the finite-coefficient `Ext` vanishing

The vanishing step of blueprint `det-ctf-finite-compact-proetale`, resting on Deligne's generic
finiteness (blueprint `lem-asd-smooth-generic-direct-image`, for `thm-fin-deligne-generic-open`;
`AlgebraicGeometry.Etale.smoothGenericDirectImage`), stated in the form used by the uniform
`Ext` bound for `𝒪_E` (blueprint `sk-lem-int-ext` (2)).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl _root_.DerivedCategory.TStructure

namespace DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k]
  {X : Scheme.{u}} (hk : Etale.HasFiniteCohomologicalDimension Λ (Spec (.of k)))
  (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX] [QuasiSeparated aX]
  [HasInvertibleExponent Λ X]

include hk aX in
/-- Compatibility from blueprint `det-ctf-finite-compact-proetale` (vanishing step), resting on
`lem-asd-smooth-generic-direct-image` / `thm-fin-deligne-generic-open`: for `C` in
`Dctf(X, Λ)` there is `N` with `Hom(C, L) = 0` for every pro-étale complex `L` with cohomology
sheaves of étale origin in degrees `≤ N`. -/
lemma uniformExtBoundCompat_constructibleFiniteTor
    {C : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    (hC : DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X C) :
    ∃ N : ℤ, ∀ L, etaleOriginHomology Λ X L → L.IsLE N → ∀ f : C ⟶ L, f = 0 :=
  exists_forall_eq_zero_of_constructibleFiniteTor hk aX hC

end DerivedCategory

end AlgebraicGeometry.ProEtale
