/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.AlgebraicGeometry.KFlatStalkResidueCohomology
import Sheaf.AlgebraicGeometry.Modules.TensorPullbackStalk
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.CategoryTheory.Adjunction.Additive
import Sheaf.AlgebraicGeometry.DerivedPullback
import Sheaf.AlgebraicGeometry.TensorPullback

/-! # Scalar extension of derived fibre cohomology

Source: Stacks Project, Tag 0BDI, base-change paragraph; Tag 06YJ.
(blueprint: lem-sc-derived-fiber-cohomology-base-change).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The cohomology vector space of a derived fibre after pullback is the scalar
extension of the original fibre cohomology. No pseudo-coherence or finiteness is needed.

Source: Stacks Project, Tag 0BDI, base-change paragraph; Tag 06YJ.
(blueprint: lem-sc-derived-fiber-cohomology-base-change).

Proof: Put x = g(y), k = kappa(x), and l = kappa(y). The residue-field square
Spec l -> Y -> X = Spec l -> Spec k -> X commutes, by the residue-field map identity.
Represent E by a K-flat resolution. Pullback preserves K-flatness, so the
recorded derived-pullback counits compute both composites termwise. The ordinary
tensor-pullback composition isomorphism and the residue-field square identify the
fibre over y with the derived extension of the fibre over x along k -> l.
Since k is a field, l is flat over k, so extension of scalars is exact and commutes
with cohomology in every degree, including unbounded complexes. Evaluation on the
one-point spectra and transport of scalars along GammaSpecIso identify this
cohomology comparison with the displayed ModuleCat isomorphism. For the zero or
infinite-dimensional cohomology vector space the same argument applies. -/
theorem derivedFiberCohomology_baseChange_iso (X Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ x : X, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (X.residueField x)).toRingedSpace))]
    [∀ y : Y, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (Y.residueField y)).toRingedSpace))]
    (E : schemeDerivedCategory X) (g : Y ⟶ X) (i : ℤ) (y : Y) :
    Nonempty (derivedFiberCohomology Y ((derivedPullback g).obj E) i y ≅
      (ModuleCat.extendScalars (g.residueFieldMap y).hom).obj
        (derivedFiberCohomology X E i (g y))) := by
  classical
  let G := Modules.tensorPullback g
  have : G.Additive :=
    (Classical.choice (Modules.nonempty_tensorPullbackAdjunction g)).left_adjoint_additive
  let P₀ := DerivedCategory.Q.objPreimage E
  obtain ⟨P, s, hP, _, hs, _⟩ :=
    CochainComplex.exists_isKFlatResolution (R := X.sheaf) P₀
  have : QuasiIso s := hs
  let eP : DerivedCategory.Q.obj P ≅ E :=
    asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  let Pg := (G.mapHomologicalComplex (.up ℤ)).obj P
  have hPg : CochainComplex.IsKFlat (R := Y.sheaf) Pg := by
    convert CochainComplex.isKFlat_pullback g.base Y.sheaf X.sheaf ⟨g.c⟩ P hP using 1
    rfl
  obtain ⟨_, _, _, _, _, _, _, F, hF, hmap, hAdd, ε, _, _, hcompute⟩ :=
    Classical.choose_spec (exists_derivedPullback g)
  have hF' : F = G := CategoryTheory.Functor.ext hF (fun M N a ↦ hmap a)
  subst F
  let A := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let B := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  have : IsIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) := hcompute P hP
  let c : (derivedPullback g).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj Pg :=
    (derivedPullback g).mapIso ((DerivedCategory.quotientCompQhIso A).symm.app P) ≪≫
      asIso (ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P)) ≪≫
      DerivedCategory.Qh.mapIso ((G.mapHomotopyCategoryFactors (.up ℤ)).app P) ≪≫
      (DerivedCategory.quotientCompQhIso B).app Pg
  let ePg := c.symm ≪≫ (derivedPullback g).mapIso eP
  obtain ⟨ey⟩ := nonempty_kFlat_stalk_residueCohomology_linearEquiv Y
    ((derivedPullback g).obj E) y Pg hPg ePg i
  obtain ⟨ex⟩ := nonempty_kFlat_stalk_residueCohomology_linearEquiv X E (g y) P hP eP i
  let Sx := RingedSpace.moduleStalkFunctor X.toRingedSpace (g y)
  let Sy := RingedSpace.moduleStalkFunctor Y.toRingedSpace y
  have : Sx.PreservesZeroMorphisms :=
    RingedSpace.moduleStalkFunctor_preservesZeroMorphisms X.toRingedSpace (g y)
  have : Sy.PreservesZeroMorphisms :=
    RingedSpace.moduleStalkFunctor_preservesZeroMorphisms Y.toRingedSpace y
  let rx := IsLocalRing.residue (X.presheaf.stalk (g y))
  let ry := IsLocalRing.residue (Y.presheaf.stalk y)
  let t := (g.stalkMap y).hom
  let l := (g.residueFieldMap y).hom
  have : (ModuleCat.extendScalars.{u, u, u} rx).Additive :=
    (ModuleCat.extendRestrictScalarsAdj rx).left_adjoint_additive
  have : (ModuleCat.extendScalars.{u, u, u} ry).Additive :=
    (ModuleCat.extendRestrictScalarsAdj ry).left_adjoint_additive
  have : (ModuleCat.extendScalars.{u, u, u} t).Additive :=
    (ModuleCat.extendRestrictScalarsAdj t).left_adjoint_additive
  have : (ModuleCat.extendScalars.{u, u, u} l).Additive :=
    (ModuleCat.extendRestrictScalarsAdj l).left_adjoint_additive
  have hring : ry.comp t = l.comp rx := by
    exact congrArg CommRingCat.Hom.hom (residue_residueFieldMap g y).symm
  obtain ⟨d, _⟩ := Modules.exists_tensorPullback_stalk_iso g y
  let e : (G ⋙ Sy) ⋙ ModuleCat.extendScalars.{u, u, u} ry ≅
      (Sx ⋙ ModuleCat.extendScalars.{u, u, u} rx) ⋙ ModuleCat.extendScalars.{u, u, u} l :=
    Functor.isoWhiskerRight d (ModuleCat.extendScalars.{u, u, u} ry) ≪≫
      Functor.associator Sx (ModuleCat.extendScalars.{u, u, u} t)
        (ModuleCat.extendScalars.{u, u, u} ry) ≪≫
      Functor.isoWhiskerLeft Sx ((ModuleCat.extendScalarsComp t ry).symm ≪≫
        eqToIso (congrArg ModuleCat.extendScalars.{u, u, u} hring) ≪≫
        ModuleCat.extendScalarsComp rx l) ≪≫
      (Functor.associator Sx (ModuleCat.extendScalars.{u, u, u} rx)
        (ModuleCat.extendScalars.{u, u, u} l)).symm
  let ec := (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  let eh := (HomologicalComplex.homologyFunctor (ModuleCat.{u} (Y.residueField y))
    (.up ℤ) i).mapIso ec
  have : CategoryTheory.Limits.PreservesFiniteLimits (ModuleCat.extendScalars.{u, u, u} l) :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.Flat.of_isField (Field.toIsField _) l)
  let K := ((ModuleCat.extendScalars.{u, u, u} rx).mapHomologicalComplex (.up ℤ)).obj
    ((Sx.mapHomologicalComplex (.up ℤ)).obj P)
  let hc := (K.sc i).mapHomologyIso (ModuleCat.extendScalars.{u, u, u} l)
  exact ⟨ey.toModuleIso ≪≫ eh ≪≫ hc ≪≫
    (ModuleCat.extendScalars.{u, u, u} l).mapIso ex.toModuleIso.symm⟩

end AlgebraicGeometry.Scheme
