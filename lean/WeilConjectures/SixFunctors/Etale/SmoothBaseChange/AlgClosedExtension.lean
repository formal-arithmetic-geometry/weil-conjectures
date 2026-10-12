/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

import Sheaf.AlgebraicGeometry.AlgClosedExtensionModuleSections
import Sheaf.AlgebraicGeometry.AlgClosedExtensionInjectiveAcyclic
import Sheaf.AlgebraicGeometry.ModuleAcyclicCohomologyComparisonZero
import Sheaf.AlgebraicGeometry.ModuleAcyclicEffacementLadder
import Sheaf.AlgebraicGeometry.KilledSheafModuleLift
import Mathlib.Algebra.FiveLemma
import Sheaf.AlgebraicGeometry.Curve.ConstantInvariance
import Sheaf.AlgebraicGeometry.CurveCohomologyConnectedReduction

/-!
# Invariance of cohomology under extension of algebraically closed fields

For an extension `k ⊆ k'` of algebraically closed fields, a quasi-compact quasi-separated
`k`-scheme `X` and `n` prime to the characteristic, the pullback map
`H^q(X_ét, ℤ/n) ⟶ H^q((X_{k'})_ét, ℤ/n)` is bijective.

## Main statements

- `AlgebraicGeometry.bijective_cohomologyMap_constantZMod`: the invariance statement.
- `AlgebraicGeometry.bijective_cohomologyMap_constantZMod_of_smoothOfRelativeDimension`: the
  invariance statement for a smooth separated curve.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

private theorem bijective_cohomologyMap_of_acyclic_modules
    {X Y : Scheme.{u}} (i : Y ⟶ X) (n : ℕ)
    (hzero : ∀ G : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))),
      IsIso (Etale.globalSectionsUpperStarMap
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) i G))
    (hacyclic : ∀ (J : Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) [Injective J]
        (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
          AddCommGrpCat.{u + 1})).obj
            ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) i).obj J)) q))
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap i
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))
        AddCommGrpCat.{u + 1})).obj M) q) := by
  induction q generalizing M with
  | zero =>
    exact Etale.bijective_cohomologyMap_of_module_acyclic_zero i n hzero M
  | succ q ih =>
    let U := sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n))) AddCommGrpCat.{u + 1})
    let V := (Etale.upperStar AddCommGrpCat.{u + 1} i)
    obtain ⟨J, Q, g, δX, δY, hX, hY, hsX, hsY, hδ⟩ :=
      Etale.exists_module_acyclic_effacement_ladder i n hacyclic M q
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      (Sheaf.H.map (U.map g) q) δX (Sheaf.H.map (V.map (U.map g)) q) δY
      (Etale.cohomologyMap i (U.obj J) q) (Etale.cohomologyMap i (U.obj Q) q)
      (Etale.cohomologyMap i (U.obj M) (q + 1))
      (AddMonoidHom.ext fun x ↦ (Etale.cohomologyMap_map i q (U.map g) x).symm)
      hδ hX hY (ih J).2 (ih Q) hsX hsY

/-- **Invariance under extension of algebraically closed fields.** Let `k ⊆ k'` be an
extension of algebraically closed fields, let `X` be a quasi-compact quasi-separated scheme
over `k` and let `n ≥ 1` be prime to `char k`. Form the base change

```
  X ×_{Spec k} Spec k' ──pullback.fst──▶ X
          │                             │
    pullback.snd                        f
          ▼                             ▼
       Spec k' ──Spec.map (algebraMap k k')──▶ Spec k
```

Then for every `q ≥ 0` the pullback map along the first projection

`ρ^q : H^q(X_ét, ℤ/n) ⟶ H^q((X_{k'})_ét, ℤ/n)`

is bijective. Its target is the cohomology of the pullback of the constant sheaf `ℤ/n`.
(blueprint: `sk-prop-ext-invariance`) -/
theorem bijective_cohomologyMap_constantZMod {k : Type u} [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    {k' : Type u} [Field k'] [IsAlgClosed k'] [Algebra k k'] (n : ℕ) (hn : (n : k) ≠ 0)
    (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) (X.constantZMod n) q) := by
  let i := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  have hkill : n • 𝟙 (X.constantZMod n) = 0 := by
    let C := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
    have h : n • 𝟙 (AddCommGrpCat.of (ULift.{u + 1} (ZMod n))) = 0 := by
      ext x
      simp [nsmul_eq_mul]
    change n • 𝟙 (C.obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))) = 0
    rw [← C.map_id, ← C.map_nsmul, h, C.map_zero]
  obtain ⟨M, ⟨e⟩⟩ := exists_module_sheaf_of_nsmul_id_eq_zero X n (X.constantZMod n) hkill
  have hM := bijective_cohomologyMap_of_acyclic_modules i n
    (Etale.isIso_globalSectionsUpperStarMap_algClosed_extension f n)
    (fun J _ q hq ↦
      Etale.subsingleton_cohomology_upperStar_injective_algClosed_extension f n hn J q hq)
    M q
  let eX := (Sheaf.functorH X.smallEtaleTopology q).mapIso e
  let eY := (Sheaf.functorH (pullback f
    (Spec.map (CommRingCat.ofHom (algebraMap k k')))).smallEtaleTopology q).mapIso
      (((Etale.upperStar AddCommGrpCat.{u + 1} i)).mapIso e)
  have hX : Function.Bijective (Sheaf.H.map e.hom q) :=
    ConcreteCategory.bijective_of_isIso eX.hom
  have hY : Function.Bijective
      (Sheaf.H.map (((Etale.upperStar AddCommGrpCat.{u + 1} i)).map e.hom) q) :=
    ConcreteCategory.bijective_of_isIso eY.hom
  refine ⟨?_, ?_⟩
  · intro x y hxy
    obtain ⟨x', rfl⟩ := hX.2 x
    obtain ⟨y', rfl⟩ := hX.2 y
    apply congrArg (Sheaf.H.map e.hom q)
    apply hM.1
    apply hY.1
    simpa only [← Etale.cohomologyMap_map] using hxy
  · intro y
    obtain ⟨y', rfl⟩ := hY.2 y
    obtain ⟨x', hx'⟩ := hM.2 y'
    refine ⟨Sheaf.H.map e.hom q x', ?_⟩
    rw [Etale.cohomologyMap_map, hx']

/-- Blueprint `sbc-thm-algebraically-closed-invariance`: Invariance under extension of
algebraically closed fields.

Let `k ⊆ k'` be algebraically closed fields, let `C` be a smooth separated curve over `k` and
let `d ≥ 1` be prime to `char k`. For every `q ≥ 0` the pullback map
`H^q(C_ét, ℤ/d) ⟶ H^q((C_{k'})_ét, ℤ/d)` along the projection `C_{k'} ⟶ C` is bijective.

This is the case of a curve of `AlgebraicGeometry.bijective_cohomologyMap_constantZMod`
(blueprint `sk-prop-ext-invariance`). -/
@[stacks 0A5E]
theorem bijective_cohomologyMap_constantZMod_of_smoothOfRelativeDimension {k : Type u}
    [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f] {k' : Type u} [Field k']
    [IsAlgClosed k'] [Algebra k k'] (d : ℕ) (hd : (d : k) ≠ 0) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) (C.constantZMod d) q) := by
  have : NeZero d := ⟨fun h ↦ hd (by rw [h]; simp)⟩
  apply bijective_curve_cohomologyMap_of_connected f d q
  intro D g _ _
  obtain ⟨c, hc, hsm, hfin, hclosed⟩ :=
    IsConnectedCurve.exists_smooth_properCompactification g
  have : IsConnectedCurve c.g := hc
  have : Smooth c.g := hsm
  obtain ⟨r, hr, hbij, _⟩ :=
    IsConnectedCurve.constant_cohomology_baseChange_compatible (K := k') g c hfin hclosed d hd
  let i := pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  let e := ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} i).app
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod d))))
  have he : Function.Bijective (Sheaf.H.map e.hom q) :=
    ConcreteCategory.bijective_of_isIso ((Sheaf.functorH _ q).mapIso e).hom
  have hb : Function.Bijective
      ((Sheaf.H.map e.hom q).comp (Etale.cohomologyMap i (D.constantZMod d) q)) := by
    simpa only [hr q] using hbij q
  refine ⟨fun x y h ↦ hb.1 (congrArg (Sheaf.H.map e.hom q) h), ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hb.2 (Sheaf.H.map e.hom q y)
  exact ⟨x, he.1 hx⟩

end AlgebraicGeometry
