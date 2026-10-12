module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Geometry.RingedSpace.Basic

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace SheafOfModules
/-- Given the two canonical counit compatibility equations, the open-cover mate
sequence is short exact. The proof uses the extension-by-zero stalk calculation,
then reflects exactness, monicity and epimorphicity through module stalks.
Source: Stacks Project, Tag 08BU and Tag 00A7.
(blueprint: lem-sc-open-cover-mate-module-short-exact-core). -/
theorem open_cover_mate_module_shortExact_core (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (_hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (U V : Opens X) (_hcover : U ⊔ V = ⊤)
    [(overFunctor.{u} R U).Additive] [(overFunctor.{u} R V).Additive]
    [(overFunctor.{u} R (U ⊓ V)).Additive]
    (SU : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R)
    (SV : SheafOfModules.{u} (R.over V) ⥤ SheafOfModules.{u} R)
    (SW : SheafOfModules.{u} (R.over (U ⊓ V)) ⥤ SheafOfModules.{u} R)
    [SU.Additive] [SV.Additive] [SW.Additive]
    (aU : SU ⊣ overFunctor.{u} R U) (aV : SV ⊣ overFunctor.{u} R V)
    (aW : SW ⊣ overFunctor.{u} R (U ⊓ V))
    (F : SheafOfModules.{u} R)
    (iU iV : (SW.obj ((overFunctor.{u} R (U ⊓ V)).obj F)) ⟶ _)
    (hU : iU ≫ aU.counit.app F = aW.counit.app F)
    (hV : iV ≫ aV.counit.app F = aW.counit.app F)
    (hz : biprod.lift iU (-iV) ≫
      biprod.desc (aU.counit.app F) (aV.counit.app F) = 0) :
    (ShortComplex.mk (biprod.lift iU (-iV))
      (biprod.desc (aU.counit.app F) (aV.counit.app F)) hz).ShortExact := by
  sorry
/-- Compatibility of nested mates with counits.
Source: Stacks Project, Tag 08BU.
(blueprint: lem-sc-open-cover-mate-module-counit-compatibility). -/
theorem open_cover_mate_module_counit_compatibility (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (_hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (U V : Opens X) (_hcover : U ⊔ V = ⊤)
    [(overFunctor.{u} R U).Additive] [(overFunctor.{u} R V).Additive]
    [(overFunctor.{u} R (U ⊓ V)).Additive]
    (SU : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R)
    (SV : SheafOfModules.{u} (R.over V) ⥤ SheafOfModules.{u} R)
    (SW : SheafOfModules.{u} (R.over (U ⊓ V)) ⥤ SheafOfModules.{u} R)
    [SU.Additive] [SV.Additive] [SW.Additive]
    (aU : SU ⊣ overFunctor.{u} R U) (aV : SV ⊣ overFunctor.{u} R V)
    (aW : SW ⊣ overFunctor.{u} R (U ⊓ V)) (F : SheafOfModules.{u} R) :
    let cU := overFunctorMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)
    let cV := overFunctorMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)
    let iU := (aW.homEquiv _ _).symm (cU.inv.app F ≫
      (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).map
        (aU.unit.app ((overFunctor.{u} R U).obj F)) ≫ cU.hom.app
          (SU.obj ((overFunctor.{u} R U).obj F)))
    let iV := (aW.homEquiv _ _).symm (cV.inv.app F ≫
      (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).map
        (aV.unit.app ((overFunctor.{u} R V).obj F)) ≫ cV.hom.app
          (SV.obj ((overFunctor.{u} R V).obj F)))
    iU ≫ aU.counit.app F = aW.counit.app F ∧
      iV ≫ aV.counit.app F = aW.counit.app F := by
  dsimp
  constructor
  · apply (aW.homEquiv _ _).injective
    rw [CategoryTheory.Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply]
    rw [CategoryTheory.Adjunction.homEquiv_unit, aW.right_triangle_components]
    simp only [Category.assoc]
    rw [← (overFunctorMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).hom.naturality]
    simp only [Functor.comp_map, ← Functor.map_comp_assoc]
    rw [aU.right_triangle_components]
    simp
  · apply (aW.homEquiv _ _).injective
    rw [CategoryTheory.Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply]
    rw [CategoryTheory.Adjunction.homEquiv_unit, aW.right_triangle_components]
    simp only [Category.assoc]
    rw [← (overFunctorMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).hom.naturality]
    simp only [Functor.comp_map, ← Functor.map_comp_assoc]
    rw [aV.right_triangle_components]
    simp

end SheafOfModules
