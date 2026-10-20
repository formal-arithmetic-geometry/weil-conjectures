/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
import all Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus

/-! The complementary component of the varying-ring clopen projection is zero.
Source: the complementary-component calculation in the proof of

`lem-sp-varying-ring-proper-open-pasting`
(blueprint: new-lem-sp-varying-ring-module-pi-complement-zero).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)

set_option backward.isDefEq.respectTransparency false in
private theorem disjoint_direct {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s]
    (hc : Disjoint (Set.range s) (Set.range c)) (N : Modules R φ C) :
    IsZero ((pull R φ s).obj ((push R φ c).obj N)) := by
  let L := (pull R φ s).obj ((push R φ c).obj N)
  have hz (n : ℕ) : IsZero ((eval R φ U n).obj L) := by
    let e := (moduleEvalG R φ s n).app ((push R φ c).obj N) ≪≫
      (StrictTower.modulePullback (R n) s).mapIso ((moduleEvalP R φ c n).app N)
    exact (StrictTower.module_disjoint_direct (R n) s c hc
      ((eval R φ C n).obj N)).of_iso e
  apply (IsZero.iff_id_eq_zero _).2
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := (hz V.unop.1).eq_of_src (𝟙 _) 0
  exact congrArg (fun f ↦ (f.val.app (op V.unop.2)) x) h

set_option backward.isDefEq.respectTransparency false in
private theorem disjoint_extension {U X C : Scheme.{u}}
    (s : U ⟶ X) (c : C ⟶ X) [IsOpenImmersion s]
    (hc : Disjoint (Set.range s) (Set.range c)) (N : Modules R φ U) :
    IsZero ((pull R φ c).obj ((extension R φ s).obj N)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply ((moduleAdj R φ c).homEquiv _ _).injective
  apply ((moduleJAdj R φ s).homEquiv _ _).injective
  exact (disjoint_direct R φ s c hc _).eq_of_tgt _ _

/-- Restriction of the clopen projection to the complementary open vanishes.
Source: Stacks 09AE and the complementary-component part of the clopen projection
calculation in `lem-sp-varying-ring-proper-open-pasting`.
Proof: pull a module back to the complementary open.  The image of the clopen
projection is supported on the disjoint image open, so its restriction is zero.
The assertion is checked on pro-etale test objects, where the two disjoint opens
have empty pullback; the sheaf terminal-section property then identifies every
section with zero.  The same calculation is compatible with all semilinear
transitions.
(blueprint: new-lem-sp-varying-ring-module-pi-complement-zero). -/
theorem modulePi_complement_zero {U X C : Scheme.{u}} (s : U ⟶ X) (c : C ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion c]
    (hc : Set.range c = (Set.range s)ᶜ) (M : Modules R φ X) :
    (pull R φ c).map ((modulePi R φ s).app M) = 0 := by
  have hd : Disjoint (Set.range s) (Set.range c) := by
    rw [hc]
    exact disjoint_compl_right
  exact (disjoint_extension R φ s c hd ((pull R φ s).obj M)).eq_of_tgt _ _

end AlgebraicGeometry.ProEtale.VaryingRing
