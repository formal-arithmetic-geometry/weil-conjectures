module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.AlgebraicInverseImageOfTransport
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction

/-! # Tensor comparison from explicit inverse-image module operations

Source: Stacks Project, Modules on Sites, Tag 03EL.
(blueprint: lem-weil-pbc-ringed-topoi-module-pullback-tensor-tail)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings
namespace SheafOfModules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 800000 in
-- Elaborate the explicit scalar-extension casts and the normalized tensor-comparison data.
/-- The tensor comparison and its generalized pure-tensor normalization for the
specified inverse-image and scalar-extension module functors.
Source: Stacks Project, Modules on Sites, Tag 03EL, lemma-tensor-product-pullback;
Tags 03D2, 03D7 and 03CZ for transport, adjunction and sheafification.
(blueprint: lem-weil-pbc-ringed-topoi-module-pullback-tensor-tail)

The equations hI identify addition and scalar multiplication under eI and eR.

Proof:
Recover the full `AlgebraicInverseImage` presentation from hI. The module graph
conditions follow directly from product comparisons. Ring compatibility follows by
testing the module conditions on the regular R-module: the inverse image of its
section 1 is a faithful scalar generator, so its additive and scalar equations
recover ring addition and multiplication, and hence zero and one.

Apply `canonicalRingedTensorComparison_nonempty` to this presentation. Its existing
bilinear universal-property construction gives the tensor isomorphisms, simultaneous
naturality, and generalized pure-tensor normalization. The map equation hTmap gives
the construction's functoriality equation after cancelling the objectwise casts.
Its insertion maps coincide with the specified q because both satisfy hq. Substituting
these equalities gives exactly the normalization in the conclusion.
-/
theorem module_pullback_tensor_iso_tail
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (_adj : L ⊣ V) [PreservesFiniteLimits L]
    (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u})
    (A : Sheaf K CommRingCat.{u})
    (eR : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ≅
      L.obj ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R))
    (c : A ⟶ S)
    (I : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ⥤
      ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat.{u}
      RingCat.{u})).obj A))
    (eI : I ⋙ (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
      sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})) ≅
      (toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})) ⋙ L)
    (hI : ∀ M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
          ∃ (addM : ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
            sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
            (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂
            CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
            AddCommGrpCat.{u})).obj M))
            (muM : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj M))
            (addI : ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
              sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (I.obj M)))
            (muI : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (I.obj M))),
      (∀ (W : Cᵒᵖ) (x : (((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose
        J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
        AddCommGrpCat.{u})).obj M)).obj.obj W),
        addM.hom.app W x = @Add.add (M.val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
          M)).hom.app W x) : M.val.obj W) (((prod.snd : ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M) ⨯ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶
          ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M)).hom.app W x) : M.val.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
        (CategoryTheory.forget AddCommGrpCat.{u})).obj M)).obj.obj W),
        muM.hom.app W x = @SMul.smul (R.obj.obj W) (M.val.obj W) inferInstance (((prod.fst :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) : R.obj.obj W) (((prod.snd :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ⟶ ((toSheaf ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj M)).hom.app W x) : M.val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf
        ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).obj.obj W),
        addI.hom.app W x = @Add.add ((I.obj M).val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (I.obj M))).hom.app W x) : (I.obj M).val.obj W) (((prod.snd : ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M)) ⨯ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (I.obj M)) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
          sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).hom.app W x) :
          (I.obj M).val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯
        ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M))).obj.obj W),
        muI.hom.app W x = @SMul.smul (A.obj.obj W) ((I.obj M).val.obj W) inferInstance (((prod.fst :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj A)).hom.app W x) : A.obj.obj W) (((prod.snd :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf ((sheafCompose K
          (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (I.obj M))).hom.app W x) : (I.obj M).val.obj W)) ∧
          L.map addM = prodComparison L ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
            RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M)
            ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose
            J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
            prod.map (eI.inv.app M) (eI.inv.app M) ≫ addI ≫ eI.hom.app M ∧
          L.map muM = prodComparison L ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
            R) ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
            sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M) ≫
            prod.map eR.inv (eI.inv.app M) ≫ muI ≫ eI.hom.app M)
    (T : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ⥤
      ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S))
    (hT : ∀ M, T.obj M = changeOfRings c (I.obj M))
    (hTmap : ∀ {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
            R)} (f : M ⟶ N),
            T.map f ≫ eqToHom (hT N) =
              eqToHom (hT M) ≫ changeOfRingsHom c (I.obj M) (I.map f))
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
                ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W,(c.hom.app W).hom] m)))
    (P : ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S) ⥤
      ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
        RingCat.{u})).obj R))
    (eP : P ⋙ (toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})) ≅
      (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})) ⋙ V)
    (hP : ∀ H : SheafOfModules.{u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S),
          ∃ (addH : ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
            sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf
            ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
            (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K (forget₂
            CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
            AddCommGrpCat.{u})).obj H))
            (muH : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K
              (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj H))
            (addP : ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
              sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (P.obj H)))
            (muP : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (P.obj H)))
            (k : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ V.obj (((sheafCompose K
              (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf ((sheafCompose K (forget₂
              CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
              AddCommGrpCat.{u})).obj H))),
      (∀ (W : Dᵒᵖ) (x : (((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
        sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf ((sheafCompose
        K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
        AddCommGrpCat.{u})).obj H)).obj.obj W),
        addH.hom.app W x = @Add.add (H.val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf ((sheafCompose K (forget₂
          CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj
          H)).hom.app W x) : H.val.obj W) (((prod.snd : ((toSheaf ((sheafCompose K (forget₂
          CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj H) ⨯ ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
          RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶
          ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H)).hom.app W x) : H.val.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯
        ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
        (CategoryTheory.forget AddCommGrpCat.{u})).obj H)).obj.obj W),
        muH.hom.app W x = @SMul.smul (S.obj.obj W) (H.val.obj W) inferInstance (((prod.fst :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj S)).hom.app W x) : S.obj.obj W) (((prod.snd :
          ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯ ((toSheaf
          ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
          (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K (forget₂
          CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
          AddCommGrpCat.{u})).obj H)).hom.app W x) : H.val.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H))).obj.obj W),
        addP.hom.app W x = @Add.add ((P.obj H).val.obj W) inferInstance (((prod.fst : ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (P.obj H))).hom.app W x) : (P.obj H).val.obj W) (((prod.snd : ((toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (P.obj H)) ⨯ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
          (P.obj H)) ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
          sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H))).hom.app W x) :
          (P.obj H).val.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
        (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H))).obj.obj W),
        muP.hom.app W x = @SMul.smul (R.obj.obj W) ((P.obj H).val.obj W) inferInstance (((prod.fst :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) : R.obj.obj W) (((prod.snd :
          ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
          (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})).obj (P.obj H))).hom.app W x) : (P.obj H).val.obj W)) ∧
          V.map addH = prodComparison V ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u}
            RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H)
            ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose
            K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ≫
            prod.map (eP.inv.app H) (eP.inv.app H) ≫ addP ≫ eP.hom.app H ∧
          k ≫ V.map (prod.fst : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯
            ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose
            K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((sheafCompose K
            (CategoryTheory.forget CommRingCat.{u})).obj S)) =
            (prod.fst : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((sheafCompose J
              (CategoryTheory.forget CommRingCat.{u})).obj R)) ≫
              _adj.homEquiv ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)
                ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S)
                (eR.inv ≫ (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).map c) ∧
          k ≫ V.map (prod.snd : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj S) ⨯
            ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose
            K (CategoryTheory.forget AddCommGrpCat.{u})).obj H) ⟶ ((toSheaf ((sheafCompose K
            (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K (CategoryTheory.forget
            AddCommGrpCat.{u})).obj H)) =
            (prod.snd : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((toSheaf
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (P.obj H)) ⟶ ((toSheaf ((sheafCompose J
              (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
              AddCommGrpCat.{u})).obj (P.obj H))) ≫ eP.hom.app H ∧
          muP ≫ eP.hom.app H = k ≫ V.map muH)
    (am : T ⊣ P)
    (hAdj : ∀ (M : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj R))
      (H : ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂
        CommRingCat.{u} RingCat.{u})).obj S)) (f : T.obj M ⟶ H),
      (toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
        sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).map
          (am.homEquiv M H f) ≫ eP.hom.app H =
        _adj.homEquiv
          ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
            sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M)
          ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
            sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj H)
          (eI.inv.app M ≫ q M ≫
            (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙
              sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).map f)) :
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
  classical
  have _ := hP
  obtain ⟨AI, rfl, hring, hunderlying⟩ :=
    algebraicInverseImage_of_module_transport J K L R A eR I eI hI
  have hmap' : ∀ {M N : SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (f : M ⟶ N),
      T.map f = eqToHom (hT M) ≫ changeOfRingsHom c (AI.modules.obj M) (AI.modules.map f) ≫
        eqToHom (hT N).symm := by
    intro M N f
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using
      congrArg (fun g ↦ g ≫ eqToHom (hT N).symm) (hTmap f)
  have hu : AI.moduleUnderlying = eI := eq_of_heq hunderlying
  cases hu
  have hT' : ∀ M, T.obj M = changeOfRings c (AI.modules.obj M) := hT
  obtain ⟨k⟩ := canonicalRingedTensorComparison_nonempty
    R S A L AI c T hT' V _adj hmap'
  rcases k with ⟨q', hq', e, he, hp⟩
  have hqq : q' = q := by
    funext M
    ext W m
    exact (hq' M W m).trans (hq M W m).symm
  subst q'
  refine ⟨e, fun M M' N N' f g ↦ he f g, ?_⟩
  -- Expose the normalization formula before specializing generalized sections.
  unfold ringedComparisonPureCondition ringedComparisonPure at hp
  intro M N Z x y z hz W t
  simpa only [Category.assoc] using hp M N Z x y z hz W t

end SheafOfModules
