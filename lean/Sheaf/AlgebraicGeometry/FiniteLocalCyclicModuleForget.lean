/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.Data.ZMod.Basic
import Sheaf.AlgebraicGeometry.ConstantSheafGeometricStalk
import Sheaf.Paper.SheavesKilledByNZmodModules
import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Finite constant values for cyclic module sheaves

Source: Stacks Project, Tags 03RU and 03RW(2),(3), with cyclic coefficients.
(blueprint: lem-weil-pbc-finite-local-cyclic-module-forget).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- For cyclic coefficients, finite abelian local systems are exactly the module sheaves
admitting trivializations with finite constant values.
Source: Stacks Project, Definitions 03RU and 03RW(2),(3); the constant-stalk argument in
lem-weil-pbc-constructible-torsion-modules-agree, proof steps 4--6.
(blueprint: lem-weil-pbc-finite-local-cyclic-module-forget)

Proof: In the forward direction forget every finite module trivialization. Constants commute
with forgetting. Lift any geometric point through the etale cover and identify its stalk
with the finite constant value; this gives finite abelian stalks. Conversely discard empty
members of an abelian trivializing cover. The constant abelian value on a remaining member
is its stalk at a geometric point, hence finite and annihilated by n. Give it its canonical
Z/n-action and lift the scalars to ULift (ZMod n). Constants commute with forgetting, and
additive maps between cyclic modules are linear, so the abelian trivialization lifts to a
module trivialization. These lifts supply both the LocallyConstantDatum and its finite
values. Empty cover members must be discarded: constancy on an empty scheme implies
neither finiteness nor annihilation of the chosen constant value. For n = 1 all modules are
zero and the same argument applies; the empty base uses the empty cover.
-/
theorem finite_local_cyclic_module_forget_iff {Y : Scheme.{u}}
    (n : ℕ) [NeZero n]
    (M : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) :
    let G := (sheafCompose Y.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1})).obj M
    (IsLocallyConstantSheaf G ∧
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ Y),
        Finite (((pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G)) ↔
    ∃ d : LocallyConstantDatum M, ∀ i : d.cover.I₀,
      ∃ A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)), Finite A ∧
        Nonempty ((M.over (d.cover.etalePrecoverageToEtale i)) ≅
          (constantSheaf (Y.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))).obj A) := by
  sorry

end AlgebraicGeometry.Scheme
