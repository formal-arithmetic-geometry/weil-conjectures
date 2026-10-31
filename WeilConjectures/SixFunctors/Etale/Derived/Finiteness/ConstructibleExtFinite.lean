/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleHomFinite

/-!
# Morphisms between bounded constructible complexes form a finite set

Let `k` be a separably closed field, `Λ` a finite ring whose exponent is invertible in `k`, and
`X` a separated scheme of finite type over `k`. For bounded constructible complexes `K`, `L` of
étale sheaves of `Λ`-modules on `X`, the set of morphisms `K ⟶ L` in the derived category is finite
(`AlgebraicGeometry.Etale.finite_hom_of_boundedConstructible`).

The case of sheaves in degrees `0` and `n` (`AlgebraicGeometry.Etale.finite_ext_of_isConstructibleSheaf`,
finiteness of `Extⁿ(F, G)`) is proved by induction on `n` for all constructible `F` at once: `F` is a
quotient of a finite sum of extensions by zero `v_! Λ` along affine étale maps, with constructible
kernel `F'`, and in the long exact sequence
`Extⁿ⁻¹(F', G) ⟶ Extⁿ(F, G) ⟶ Extⁿ(⊕ v_! Λ, G)` the right term is `⊕ Hⁿ(V, G)`, finite by the
finiteness of cohomology. The general case follows by induction on the amplitudes, along the
truncation triangles.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- **Finiteness of `Extⁿ` between constructible sheaves**: over a separated scheme of finite type
over a separably closed field, with coefficients a finite ring with invertible exponent. -/
theorem finite_ext_of_isConstructibleSheaf {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p] (n : ℤ)
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    [IsConstructibleSheaf G] :
    Finite ((_root_.DerivedCategory.singleFunctor _ 0).obj F ⟶
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G)⟦n⟧) :=
  sorry

/-- **Morphisms between bounded constructible complexes form a finite set**, over a separated
scheme of finite type over a separably closed field, with coefficients a finite ring with
invertible exponent. -/
theorem finite_hom_of_boundedConstructible {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    {K L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X K)
    (hL : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X L) :
    Finite (K ⟶ L) :=
  sorry

end Etale

end AlgebraicGeometry
