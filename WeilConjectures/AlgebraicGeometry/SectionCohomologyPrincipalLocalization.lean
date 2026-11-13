/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Module.LocalizedModule.Away
import WeilConjectures.AlgebraicGeometry.SectionCohomologyPrincipalDenominators
import WeilConjectures.AlgebraicGeometry.SectionCohomologyPrincipalTorsion

/-! # Principal localization of the cohomology presheaf

## References

* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 01E4](https://stacks.math.columbia.edu/tag/01E4)
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The cohomology presheaf of a pushed-forward injective resolution localizes on
principal opens of an affine base open. -/
theorem sectionCohomologyPresheaf_isLocalized_away {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) [QuasiCompact f] [QuasiSeparated f]
    [F.IsQuasicoherent] (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (hW : IsAffineOpen W) (a : Γ(T, W)) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let : Module Γ(T, W) (P.obj (op (T.basicOpen a))) :=
      Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
    IsLocalizedModule.Away a (P.map (homOfLE (T.basicOpen_le a)).op).hom := by
  dsimp only
  let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let P := sectionCohomologyPresheaf K q
  let : Module Γ(T, W) (P.obj (op (T.basicOpen a))) :=
    Module.compHom _ (T.presheaf.map (homOfLE (T.basicOpen_le a)).op).hom
  apply IsLocalizedModule.Away.mk_of_addCommGroup
  · apply (Module.End.isUnit_iff _).mpr
    change Function.Bijective (fun x : P.obj (op (T.basicOpen a)) ↦
      (T.presheaf.map (homOfLE (T.basicOpen_le a)).op a) • x)
    exact (T.toRingedSpace.isUnit_res_basicOpen a).smul_bijective
  · exact sectionCohomologyPresheaf_pow_lifts f F I q W hW a
  · exact sectionCohomologyPresheaf_pow_annihilates f F I q W hW a

end AlgebraicGeometry.Scheme.Modules
