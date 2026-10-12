/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.ModulePointFunctions
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Finite models of finite constant sheaves

Let `Λ` be a commutative ring and `F` a constant sheaf of `Λ`-modules on the small étale site of
a scheme `X`, `F ≅ M_X`. If the geometric stalks of `F` are finitely generated, then `F` is the
constant sheaf at a finitely generated `Λ`-module: if `X` is nonempty, the stalk of `M_X` at a
geometric point is `M` itself; if `X` is empty every sheaf is zero, hence constant at `0`.

## Main results

- `AlgebraicGeometry.Scheme.exists_finite_constant_model`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]

/-- **Finite models of finite constant sheaves**: a constant sheaf of `Λ`-modules on the small
étale site of `X` with finitely generated geometric stalks is isomorphic to the constant sheaf
`M_X` at a finitely generated `Λ`-module `M`. This includes the empty scheme.
(blueprint: `lem-weil-pbc-finite-constant-model`) -/
theorem exists_finite_constant_model (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [F.IsConstant X.smallEtaleTopology] [IsFiniteSheaf F] :
    ∃ M : ModuleCat.{u + 1} Λ, Module.Finite Λ M ∧
      Nonempty (F ≅ (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) := by
  obtain ⟨M, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant X.smallEtaleTopology F
  by_cases hX : IsEmpty X
  · exact ⟨ModuleCat.of Λ PUnit, inferInstance,
      ⟨(Etale.isZero_sheaf_of_isEmpty F).iso (Etale.isZero_sheaf_of_isEmpty _)⟩⟩
  obtain ⟨x⟩ := not_isEmpty_iff.1 hX
  refine ⟨M, ?_, ⟨e.symm⟩⟩
  let Φ := X.uliftPointSmallEtale x
  have h : ConcreteCategory.IsFinitelyGenerated
      ((Φ.sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) :=
    (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (F := F) _ (X.algClosurePoint x)).of_iso
      (((pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso.{u + 1}
        (ModuleCat.{u + 1} Λ)).app F).symm
  exact (ModuleCat.isFinitelyGenerated_iff _).1
    (h.of_iso (Φ.sheafFiber.mapIso e.symm ≪≫ Φ.sheafFiberConstantSheafIso M))

end AlgebraicGeometry.Scheme
