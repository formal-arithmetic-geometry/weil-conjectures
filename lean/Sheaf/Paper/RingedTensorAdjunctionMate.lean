/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Functor
import Sheaf.Paper.RingedTopoiInverseImageTensorComparison
import Sheaf.Paper.RingedTopoiScalarTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # The tensor comparison is the specified adjunction mate

Source: Stacks Project, Modules on Sites, Tags 03D7 and 03EL.
(blueprint: lem-pd-ringed-tensor-adjunction-mate).
-/

@[expose] public section

universe u uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ChangeOfRings

/-- The actual oplax mate equals every normalized ringed tensor comparison, and its
scalar and unit maps have the stated inverse formulas.
Source: Stacks Project, Modules on Sites, Tags 03D7 and 03EL;
the identification of the specified mates is the agent expansion of these tags.
(blueprint: lem-pd-ringed-tensor-adjunction-mate).

Proof:
1. Compose the normalized inverse-image tensor isomorphism of
   lem-weil-pbc-algebraic-inverse-image-tensor-comparison with the normalized
   scalar-extension tensor isomorphism of
   lem-weil-pbc-scalar-extension-tensor-comparison. Naturality of scalar insertion
   gives the generalized pure equation of the canonical comparison.
2. Under the specified adjunction, the adjunct of f is unit followed by P(f).
   By lem-sfb-adjunction-oplax-mate, the adjunct of its tensor map is the tensor
   of the two units followed by the stipulated lax pairing.
3. Test the canonical comparison on the product of the two underlying source
   sheaves. Naturality of the geometric unit identifies its adjunct on every
   local pure tensor with this lax pairing. The sheaf tensor bilinear universal
   property makes the adjuncts equal, without asserting that all sheaf tensor
   sections are pure. Injectivity of the adjunction identifies the actual mates.
4. Scalar linearity gives s tensor (m tensor n) mapped to
   (s tensor m) tensor (1 tensor n). The reverse formula multiplies the scalars.
   It is balanced in both RI variables and over S, and commutes with restrictions.
   Extend through both sheafifications using the bilinear-extension universal
   property. The two composites are identities on generators and hence on sheaves.
5. Transport I(R) to RI by the algebraic inverse-image identifications. Scalar
   multiplication s tensor r mapped to s alpha(r) has adjunct c, so it is the
   actual unit mate. Its inverse sends s to s tensor 1; the two inverse equations
   follow by balancing and sheafification uniqueness, also for the zero ring. -/
theorem ringedTensor_adjunction_mate
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (v : C ⥤ D) [v.IsContinuous JC JD]
    (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uAdj : uInv ⊣ v.sheafPushforwardContinuous (Type u) JC JD)
    [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (α : RI ⟶ S)
    (φ : ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⟶
      (v.sheafPushforwardContinuous RingCat.{u} JC JD).obj ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S))
    (hφ : (sheafCompose JC (CategoryTheory.forget RingCat.{u})).map φ =
      uAdj.homEquiv _ _ (I.ringUnderlying.hom ≫
        (sheafCompose JD (CategoryTheory.forget CommRingCat.{u})).map α))
    (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R),
      L.obj M = changeOfRings.{vD, uD, u} α (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)} (f : M ⟶ N),
      L.map f = eqToHom (hobj M) ≫
        changeOfRingsHom.{vD, uD, u} α (I.modules.obj M) (I.modules.map f) ≫
          eqToHom (hobj N).symm)
    (am : L ⊣ (pushforward.{u} φ))
    (hunit : ∀ (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) (U : Cᵒᵖ) (m : M.val.obj U),
      (am.unit.app M).val.app U m =
        (eqToHom (hobj M).symm).val.app (v.op.obj U)
          (ringedComparisonScalarSection α (I.modules.obj M) (v.op.obj U) 1
            ((I.moduleUnderlying.inv.app M).hom.app (v.op.obj U)
              ((uAdj.unit.app ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ⋙ sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{u})).obj
      M)).hom.app U m))))
    [(pushforward.{u} φ).LaxMonoidal]
    (hlax : ∀ (H K : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) (U : Cᵒᵖ)
      (m : ((pushforward.{u} φ).obj H).val.obj U) (n : ((pushforward.{u} φ).obj K).val.obj U),
      (Functor.LaxMonoidal.μ (pushforward.{u} φ) H K).val.app U
        (ringedComparisonPure R _ _ U m n) =
          ringedComparisonPure S H K (v.op.obj U) m n)
    (hlaxUnit : ∀ (U : Cᵒᵖ) (r : R.obj.obj U),
      (Functor.LaxMonoidal.ε (pushforward.{u} φ)).val.app U r = φ.hom.app U r) :
    ∃ (k : CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I α L hobj)
      (a : ∀ M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R),
        I.modules.obj ((monoidalCategory R).tensorObj M N) ≅
          (monoidalCategory RI).tensorObj (I.modules.obj M) (I.modules.obj N))
      (j : I.modules.obj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ≅ (SheafOfModules.unit ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj RI)))
      (e₀ : L.obj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ≅ SheafOfModules.unit ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)),
      (∀ {M M' N N' : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)} (f : M ⟶ M') (g : N ⟶ N'),
        I.modules.map ((monoidalCategory R).tensorHom f g) ≫ (a M' N').hom =
          (a M N).hom ≫ (monoidalCategory RI).tensorHom
            (I.modules.map f) (I.modules.map g)) ∧
      (∀ (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) (Z : Sheaf JC (Type u))
        (x : Z ⟶ (toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{u})).obj M) (y : Z ⟶ (toSheaf
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj N)
        (z : Z ⟶ (toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{u})).obj ((monoidalCategory
      R).tensorObj M N)),
        (∀ (U : Cᵒᵖ) (t : Z.obj.obj U), z.hom.app U t =
          ringedComparisonPure R M N U (x.hom.app U t) (y.hom.app U t)) →
        ∀ (W : Dᵒᵖ) (t : (uInv.obj Z).obj.obj W),
          (a M N).hom.val.app W
            ((uInv.map z ≫ I.moduleUnderlying.inv.app
              ((monoidalCategory R).tensorObj M N)).hom.app W t) =
          ringedComparisonPure RI (I.modules.obj M) (I.modules.obj N) W
            ((uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t)
            ((uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)) ∧
      (∀ (W : Dᵒᵖ) (r : (I.modules.obj (SheafOfModules.unit ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R))).val.obj W),
        j.hom.val.app W r = I.ringUnderlying.hom.hom.app W
          ((I.moduleUnderlying.hom.app (SheafOfModules.unit ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R))).hom.app W r)) ∧
      (∀ (k' : CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I α L hobj)
        (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)),
        am.leftAdjointOplaxMonoidal.δ M N = (k'.mu M N).hom) ∧
      (∀ M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      IsIso (am.leftAdjointOplaxMonoidal.δ M N)) ∧
      (∀ (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) (W : Dᵒᵖ) (s : S.obj.obj W)
        (m : (I.modules.obj M).val.obj W) (n : (I.modules.obj N).val.obj W),
        (am.leftAdjointOplaxMonoidal.δ M N).val.app W
          ((eqToHom (hobj ((monoidalCategory R).tensorObj M N)).symm).val.app W
            (ringedComparisonScalarSection α _ W s
              ((a M N).inv.val.app W (ringedComparisonPure RI _ _ W m n)))) =
        ringedComparisonPure S _ _ W
          ((eqToHom (hobj M).symm).val.app W
            (ringedComparisonScalarSection α _ W s m))
          ((eqToHom (hobj N).symm).val.app W
            (ringedComparisonScalarSection α _ W 1 n))) ∧
      (∀ (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) (W : Dᵒᵖ) (s t : S.obj.obj W)
        (m : (I.modules.obj M).val.obj W) (n : (I.modules.obj N).val.obj W),
        (k.mu M N).inv.val.app W
          (ringedComparisonPure S _ _ W
            ((eqToHom (hobj M).symm).val.app W
              (ringedComparisonScalarSection α _ W s m))
            ((eqToHom (hobj N).symm).val.app W
              (ringedComparisonScalarSection α _ W t n))) =
        (eqToHom (hobj ((monoidalCategory R).tensorObj M N)).symm).val.app W
          (ringedComparisonScalarSection α _ W (s * t)
            ((a M N).inv.val.app W (ringedComparisonPure RI _ _ W m n)))) ∧
      e₀.hom = am.leftAdjointOplaxMonoidal.η ∧
      (∀ (W : Dᵒᵖ) (s : S.obj.obj W) (r : RI.obj.obj W),
        e₀.hom.val.app W
          ((eqToHom (hobj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R))).symm).val.app W
            (ringedComparisonScalarSection α _ W s (j.inv.val.app W r))) =
        s * α.hom.app W r) ∧
      (∀ (W : Dᵒᵖ) (s : S.obj.obj W),
        e₀.inv.val.app W s =
          (eqToHom (hobj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R))).symm).val.app W
            (ringedComparisonScalarSection α _ W s
              (j.inv.val.app W
                ((1 : RI.obj.obj W) :
                  (SheafOfModules.unit
                    ((sheafCompose JD
                      (forget₂ CommRingCat.{u} RingCat.{u})).obj RI)).val.obj W)))) := by
  sorry

end SheafOfModules
