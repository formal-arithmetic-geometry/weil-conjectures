/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.RelativeFlatModuleStalk
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.RelativeFlatOfStalks
import WeilConjectures.AlgebraicGeometry.PullbackStalkRelativeFlatExtension

/-! # Relative flatness of a module after base change

## References

* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 051D](https://stacks.math.columbia.edu/tag/051D)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Tensor pullback in a scheme base change preserves flatness over the base. -/
theorem relativelyFlat_module_pullback
    {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    (hflat : F.IsFlatOver f) :
    (Scheme.Modules.tensorPullbackObj (pullback.fst f p) F).IsFlatOver
      (pullback.snd f p) := by
  let a := pullback.fst f p
  let b := pullback.snd f p
  let e := (Scheme.Modules.nonempty_tensorPullbackAdjunction a).some.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction a)
  have : (Scheme.Modules.tensorPullbackObj a F).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (pullback f p).ringCatSheaf).prop_of_iso
      (e.app F).symm
      (inferInstanceAs (((Scheme.Modules.pullback a).obj F).IsQuasicoherent))
  apply relative_flat_of_stalks b
  intro z
  let M := (RingedSpace.moduleStalkFunctor X.toRingedSpace (a z)).obj F
  have hM : Module.Flat (S.presheaf.stalk (f (a z)))
      ((ModuleCat.restrictScalars (f.stalkMap (a z)).hom).obj M) := by
    let := (f.stalkMap (a z)).hom.toAlgebra
    exact relative_flat_module_stalk f F hflat (a z) rfl
  have hE := pullback_stalk_relative_flat_extension f p z M hM
  obtain ⟨d, _⟩ := Scheme.Modules.exists_tensorPullback_stalk_iso a z
  let k := (ModuleCat.restrictScalars (b.stalkMap z).hom).mapIso (d.app F)
  exact @Module.Flat.of_linearEquiv _ _ _ _ _ _ _ _ hE k.toLinearEquiv

end AlgebraicGeometry
