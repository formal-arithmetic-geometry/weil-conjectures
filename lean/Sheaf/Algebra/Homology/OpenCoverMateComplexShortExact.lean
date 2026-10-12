/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S3
-/
module

public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # The complex-level open-cover sequence with its canonical mate maps

Source: Stacks Project, Tag 08BU, proof, and Tag 08BW.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace SheafOfModules

/-- The termwise open-cover short exact sequence, before localization.

Source: Stacks Project, Tag 08BU, proof, and Tag 08BW (nested restriction maps).
(blueprint: lem-sc-open-cover-mate-complex-short-exact).

Proof: First use the actual extension-by-zero functors, namely the direct-sum
extension presheaf followed by module sheafification. For W contained in U, the
extension map from W to U is the unique map whose composite with the U counit is
the W counit. On sections its transpose is restriction to W of the U unit,
conjugated by `overFunctorMap`. These maps are natural in the module, hence commute
with the differentials of K and give complex maps. Take their difference into the
biproduct; the second map is the pair of counits. Their composite is zero since
both component composites are the W counit. At a point in U intersection V the
stalk sequence is diagonal difference followed by addition; in U minus V or V
minus U it is the identity sequence with zero at one end. The cover excludes a
fourth case. These sequences are short exact, so stalkwise reflection of exactness
and of monomorphisms and epimorphisms proves short exactness in every degree.
Degreewise short exactness is short exactness of complexes. Finally transport
along the unique compatible isomorphisms from any chosen left adjoints to these
extension-by-zero functors. These isomorphisms commute with units and counits,
so they preserve the displayed mate formulas and the short exact sequence. Empty
opens and equal opens satisfy the same stalk calculation. No derived objects or
distinguished triangles occur in this statement. -/
theorem open_cover_mate_complex_shortExact (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    [(overFunctor.{u} R U).Additive] [(overFunctor.{u} R V).Additive]
    [(overFunctor.{u} R (U ⊓ V)).Additive]
    (SU : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R)
    (SV : SheafOfModules.{u} (R.over V) ⥤ SheafOfModules.{u} R)
    (SW : SheafOfModules.{u} (R.over (U ⊓ V)) ⥤ SheafOfModules.{u} R)
    [SU.Additive] [SV.Additive] [SW.Additive]
    (aU : SU ⊣ overFunctor.{u} R U) (aV : SV ⊣ overFunctor.{u} R V)
    (aW : SW ⊣ overFunctor.{u} R (U ⊓ V))
    (K : CochainComplex (SheafOfModules.{u} R) ℤ) :
    let KU := (SU.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((overFunctor.{u} R U).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    let KV := (SV.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((overFunctor.{u} R V).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    let KW := (SW.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((overFunctor.{u} R (U ⊓ V)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    let εU := (aU.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K
    let εV := (aV.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K
    let cU := overFunctorMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)
    let cV := overFunctorMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)
    ∃ (f : KW ⟶ KU ⊞ KV),
      (∀ n, (f ≫ biprod.fst).f n = (aW.homEquiv _ _).symm
        (cU.inv.app (K.X n) ≫
          (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).map
            (aU.unit.app ((overFunctor.{u} R U).obj (K.X n))) ≫
          cU.hom.app (SU.obj ((overFunctor.{u} R U).obj (K.X n))))) ∧
      (∀ n, (-(f ≫ biprod.snd)).f n = (aW.homEquiv _ _).symm
        (cV.inv.app (K.X n) ≫
          (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).map
            (aV.unit.app ((overFunctor.{u} R V).obj (K.X n))) ≫
          cV.hom.app (SV.obj ((overFunctor.{u} R V).obj (K.X n))))) ∧
      ∃ hz : f ≫ biprod.desc εU εV = 0,
        (ShortComplex.mk f (biprod.desc εU εV) hz).ShortExact := by sorry

end SheafOfModules
