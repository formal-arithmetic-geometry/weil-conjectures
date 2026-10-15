/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FiniteCancellation

/-!
# Constant coefficients under a finite modification

Let `f : X ⟶ S` be proper, and let `ν : Y ⟶ X` be finite, surjective, and an isomorphism over
the complement `U` of a closed subscheme `i : Z ⟶ X` on which `f` is finite. For a finite
`Λ`-module `M`, the higher direct images of the constant sheaf `M` along `f` and along `ν ≫ f`
are compared (`lem-finrepair-constant-finite-comparison`): the cokernel of the unit
`M_X ⟶ ν_* ν^* M_X` is supported on `Z`, whose direct images along `f` are concentrated in
degree `0`.

The constant sheaf on `Y` is written `ν^* M_X`; it is identified with `M_Y` by
`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- The comparison map `Rf_*(M_X) ⟶ R(ν ≫ f)_*(ν^* M_X)` for a finite `ν : Y ⟶ X`: the direct
image along `f` of the unit `M_X ⟶ ν_* ν^* M_X`, followed by the identification
`Rf_*(ν_* G) = R(ν ≫ f)_* G` of `AlgebraicGeometry.Etale.rightDerivedLowerStarSingleLowerStarIso`.
It is defined for any sheaf `F` in place of `M_X`. -/
noncomputable def rightDerivedLowerStarUnitComparison {X Y S : Scheme.{u}} (f : X ⟶ S)
    (ν : Y ⟶ X) [IsFinite ν] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj F) ⟶
      (R((ν ≫ f)_*[ModuleCat.{u + 1} Λ])).obj
        ((singleFunctor _ 0).obj ((ν)^*[ModuleCat.{u + 1} Λ].obj F)) :=
  (R((f)_*[ModuleCat.{u + 1} Λ])).map ((singleFunctor _ 0).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) ν).unit.app F)) ≫
    (rightDerivedLowerStarSingleLowerStarIso ν f _).hom

/-- Blueprint `lem-finrepair-constant-finite-comparison`: Constant coefficients under a finite
normalization comparison.

Let `f : X ⟶ S` be proper with `S` of finite type over a field `k`, and let `ν : Y ⟶ X` be finite
and surjective. Suppose `ν` is an isomorphism over the open `j : U ⟶ X` complementary to a
closed immersion `i : Z ⟶ X` for which `i ≫ f` is finite. Put `v = ν ≫ f` and let `M` be a finite
`Λ`-module, with constant sheaf `M_X` on `X` (and `ν^* M_X = M_Y` on `Y`). If all `Rᵠv_*(M_Y)`
are constructible, then so are all `Rᵠf_*(M_X)`, and the natural map
`Rᵠf_*(M_X) ⟶ Rᵠv_*(M_Y)` (`AlgebraicGeometry.Etale.rightDerivedLowerStarUnitComparison`) is an
isomorphism for every `q ≥ 2`. The blueprint takes `Z` reduced; this is not needed. -/
theorem constructible_and_isIso_rightDerivedLowerStarUnitComparison {k : Type u} [Field k]
    {X Y Z U S : Scheme.{u}} (aS : S ⟶ Spec (.of k)) [LocallyOfFiniteType aS] [QuasiCompact aS]
    (f : X ⟶ S) [IsProper f] (ν : Y ⟶ X) [IsFinite ν] [Surjective ν]
    (i : Z ⟶ X) [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) (hν : IsIso (pullback.snd ν j))
    [IsFinite (i ≫ f)] (M : ModuleCat.{u + 1} Λ) [Module.Finite Λ M]
    (hv : ∀ q : ℤ, IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((ν ≫ f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((ν)^*[ModuleCat.{u + 1} Λ].obj ((constantSheaf X.smallEtaleTopology _).obj M)))))) :
    (∀ q : ℤ, IsConstructibleSheaf ((homologyFunctor _ q).obj
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj ((singleFunctor _ 0).obj
        ((constantSheaf X.smallEtaleTopology _).obj M))))) ∧
    ∀ q : ℤ, 2 ≤ q → IsIso ((homologyFunctor _ q).map
      (rightDerivedLowerStarUnitComparison f ν ((constantSheaf X.smallEtaleTopology _).obj M))) :=
  sorry

end Etale

end AlgebraicGeometry
