module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings
namespace SheafOfModules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The tensor comparison and its pure-tensor normalization, isolated from the
outer ring and module-adjunction construction.
Source: Stacks Project, Modules on Sites, Tag 03EL.
(blueprint: lem-weil-pbc-ringed-topoi-module-pullback-tensor-tail)

The statement is the final tensor-comparison step of the parent theorem.  It
is left as an intermediate obligation so that the outer construction can use
it independently of the ring and module operation bookkeeping.
-/
theorem module_pullback_tensor_iso_tail
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (A : Sheaf K CommRingCat.{u})
    (c : A ⟶ S)
    (I : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ⥤
      ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat.{u}
      RingCat.{u})).obj A))
    (eI : I ⋙ (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
      sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})) ≅
      (toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})) ⋙ L)
    (T : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ⥤
      ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S))
    (hT : ∀ M, T.obj M = changeOfRings c (I.obj M))
    (q : ∀ M, ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
      sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶
      ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (T.obj M)))
    (hq : ∀ (M : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) (W : Dᵒᵖ) (m : (I.obj M).val.obj W),
      (q M).hom.app W m =
        (eqToHom (hT M).symm).val.app W
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S).obj)).unit.app
              (changeOfRingsPresheaf.{u, u, u} c (I.obj M))).app W
                ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W,(c.hom.app W).hom] m))) :
    ∃ (e : ∀ M N : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj R),
      T.obj ((monoidalCategory R).tensorObj (M) (N)) ≅
        ((monoidalCategory S).tensorObj (T.obj M) (T.obj N))),
      (∀ (M M' N N' : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
        CommRingCat.{u} RingCat.{u})).obj R)) (f : M ⟶ M') (g : N ⟶ N'),
        T.map ((monoidalCategory R).tensorHom f g) ≫ (e M' N').hom =
          (e M N).hom ≫ (monoidalCategory S).tensorHom (T.map f) (T.map g)) ∧
      ∀ (M N : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
        CommRingCat.{u} RingCat.{u})).obj R)) (Z : Sheaf J (Type u))
        (x : Z ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (M)))
        (y : Z ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (N)))
        (z : Z ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
            (((monoidalCategory R).tensorObj (M) (N))))),
        (∀ (W : Cᵒᵖ) (t : Z.obj.obj W), z.hom.app W t =
          (tensorObjIsoSheafification (M) (N)).inv.val.app W
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R).obj)).unit.app
                ((M).val ⊗ (N).val)).app W
              (x.hom.app W t ⊗ₜ[R.obj.obj W] y.hom.app W t))) →
        ∀ (W : Dᵒᵖ) (t : (L.obj Z).obj.obj W),
          (L.map z ≫ (eI.inv.app (((monoidalCategory R).tensorObj (M) (N))) ≫ q
            (((monoidalCategory R).tensorObj (M) (N)))) ≫
            (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
              sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).map
                (e M N).hom).hom.app W t =
          (tensorObjIsoSheafification (T.obj M) (T.obj N)).inv.val.app W
            (((PresheafOfModules.sheafificationAdjunction
              (𝟙 ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S).obj)).unit.app
                ((T.obj M).val ⊗ (T.obj N).val)).app W
              ((L.map x ≫ (eI.inv.app M ≫ q M)).hom.app W t ⊗ₜ[S.obj.obj W]
                (L.map y ≫ (eI.inv.app N ≫ q N)).hom.app W t)) := by
  sorry

end SheafOfModules
