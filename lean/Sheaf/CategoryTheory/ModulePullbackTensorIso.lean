/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NG
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Grp.FilteredColimits
import Sheaf.CategoryTheory.ModulePullbackTensorIsoE
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction

/-! # Tensor pullback on arbitrary ringed topoi

Source: Stacks Project, Modules on Sites, Tag 03EL, lemma-tensor-product-pullback
(blueprint: lem-weil-pbc-ringed-topoi-module-pullback-tensor).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings

namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 800000 in
-- Elaborating the explicit ring, module, scalar-extension and pure-tensor identifications.
/-- Pullback of module sheaves preserves tensor products, canonically and naturally.
Source: Stacks Project, Modules on Sites, Tag 03EL, lemma-tensor-product-pullback
(blueprint: lem-weil-pbc-ringed-topoi-module-pullback-tensor).

The existential ring A, module functor I and underlying-sheaf identifications explicitly
specify inverse image under L: addition, multiplication and scalar actions are transported
through its product comparisons. The functor T is the recorded sheafified change of rings
along c on I, on both objects and maps; q is insertion of 1 into that tensor product.
The family e has the required orientation and its first equation is simultaneous naturality.
The final equation characterizes the canonical comparison on all generalized pure tensors:
it sends the inverse image of m tensor n to (1 tensor m) tensor (1 tensor n).
This avoids assuming any extra geometric or module functor data.

Proof:
1. Use lem-weil-pbc-ringed-topoi-module-adjunction and the tensor universal property
   lem-pc-sites-sheaf-tensor-bilinear-universal to identify Hom(T(M tensor N),H)
   with R-bilinear maps (M,N) into the specified direct image of H.
2. Transpose by the set-sheaf adjunction. Preservation of binary and triple products
   identifies the transposes of both additivity equations and both scalar equations.
   Zero uses the terminal comparison. The ring and group operations are supplied by
   lem-weil-pbc-adjunction-lifts-group-ring-objects. The triangle identity identifies
   the transposed scalar action with restriction along c.
3. Extend an A-bilinear beta uniquely by (s tensor x,t tensor y) maps to st beta(x,y).
   The two balancing relations follow from A-bilinearity; commutativity of S lets the
   two scalars commute. Restriction compatibility gives a map of presheaves. Module
   sheafification and finite-product preservation of set sheafification extend this
   uniquely to sheaves (def-weil-presheaf-modules-sheafification,
   def-weil-pbc-sheafification, lem-weil-pbc-sheafification-sets-exact).
4. Apply the tensor universal property again to obtain Hom(T(M) tensor T(N),H).
   The bijections are natural in H. Evaluate them and their inverse on identities;
   naturality gives mutually inverse maps, with e oriented from T(M tensor N).
5. Each bijection commutes with precomposition in M and N, yielding the displayed
   simultaneous naturality. On pure tensors the construction inserts 1 in each
   scalar factor, yielding the generalized-element normalization below.
No flatness, stalks, enough points or nonzero-ring hypothesis is used. -/
theorem module_pullback_tensor_iso
                  {C D : Type u} [Category.{u} C] [Category.{u} D]
                  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
                  (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
                  (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
                  (_adj : L ⊣ V) [PreservesFiniteLimits L]
                  (R : Sheaf J CommRingCat.{u}) (S : Sheaf K CommRingCat.{u}) :
                  ∃ (A : Sheaf K CommRingCat.{u}) (eR : ((sheafCompose K (CategoryTheory.forget
      CommRingCat.{u})).obj A) ≅ L.obj ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
      R))
      (addR mulR : ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((sheafCompose
        J (CategoryTheory.forget CommRingCat.{u})).obj R) ⟶ ((sheafCompose J (CategoryTheory.forget
        CommRingCat.{u})).obj R))
      (addA mulA : ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((sheafCompose
        K (CategoryTheory.forget CommRingCat.{u})).obj A) ⟶ ((sheafCompose K (CategoryTheory.forget
        CommRingCat.{u})).obj A)),
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).obj.obj W),
        addR.hom.app W x = @Add.add (R.obj.obj W) inferInstance (((prod.fst : ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R)).hom.app W x) : R.obj.obj W) (((prod.snd : ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) :
          R.obj.obj W)) ∧
      (∀ (W : Cᵒᵖ) (x : (((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).obj.obj W),
        mulR.hom.app W x = @Mul.mul (R.obj.obj W) inferInstance (((prod.fst : ((sheafCompose J
          (CategoryTheory.forget CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R)).hom.app W x) : R.obj.obj W) (((prod.snd : ((sheafCompose J (CategoryTheory.forget
          CommRingCat.{u})).obj R) ⨯ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj
          R) ⟶ ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)).hom.app W x) :
          R.obj.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).obj.obj W),
        addA.hom.app W x = @Add.add (A.obj.obj W) inferInstance (((prod.fst : ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A)).hom.app W x) : A.obj.obj W) (((prod.snd : ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).hom.app W x) :
          A.obj.obj W)) ∧
      (∀ (W : Dᵒᵖ) (x : (((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯
        ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).obj.obj W),
        mulA.hom.app W x = @Mul.mul (A.obj.obj W) inferInstance (((prod.fst : ((sheafCompose K
          (CategoryTheory.forget CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A)).hom.app W x) : A.obj.obj W) (((prod.snd : ((sheafCompose K (CategoryTheory.forget
          CommRingCat.{u})).obj A) ⨯ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
          A) ⟶ ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj A)).hom.app W x) :
          A.obj.obj W)) ∧
      L.map addR = prodComparison L ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ≫
        prod.map eR.inv eR.inv ≫ addA ≫ eR.hom ∧
      L.map mulR = prodComparison L ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R)
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj R) ≫
        prod.map eR.inv eR.inv ≫ mulA ≫ eR.hom ∧
      ∀ c : A ⟶ S,
      ∃ (I : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
        RingCat.{u})).obj R) ⥤
        ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj
          A))
        (eI : I ⋙ (toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
          sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})) ≅ (toSheaf ((sheafCompose J
          (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose J (CategoryTheory.forget
          AddCommGrpCat.{u})) ⋙ L),
        (∀ M : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R),
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
            prod.map eR.inv (eI.inv.app M) ≫ muI ≫ eI.hom.app M) ∧
        ∃ (T : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).obj R) ⥤
          ringedSiteModules.{u, u, u, u} ((sheafCompose K (forget₂ CommRingCat.{u}
            RingCat.{u})).obj S))
          (hT : ∀ M, T.obj M = changeOfRings c (I.obj M)),
          (∀ {M N : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
            RingCat.{u})).obj
            R)} (f : M ⟶ N),
            T.map f ≫ eqToHom (hT N) =
              eqToHom (hT M) ≫ changeOfRingsHom c (I.obj M) (I.map f)) ∧
          ∃ (q : ∀ M, ((toSheaf ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj A) ⋙
              sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).obj (I.obj M)) ⟶ ((toSheaf
              ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S) ⋙ sheafCompose K
              (CategoryTheory.forget AddCommGrpCat.{u})).obj (T.obj M))),
            (∀ (M : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
              RingCat.{u})).obj
              R)) (W : Dᵒᵖ)
                (m : (I.obj M).val.obj W),
              (q M).hom.app W m =
                (eqToHom (hT M).symm).val.app W
                  (((PresheafOfModules.sheafificationAdjunction
                    (𝟙 ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S).obj)).unit.app
                      (changeOfRingsPresheaf.{u, u, u} c (I.obj M))).app W
                        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m))) ∧
          ∃ (e : ∀ M N : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
            RingCat.{u})).obj R),
            T.obj ((monoidalCategory R).tensorObj (M) (N)) ≅ ((monoidalCategory S).tensorObj (T.obj
              M) (T.obj N))),
            (∀ (M M' N N' : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂
              CommRingCat.{u} RingCat.{u})).obj R)) (f : M ⟶ M') (g : N ⟶ N'),
              T.map ((monoidalCategory R).tensorHom f g) ≫ (e M' N').hom =
                (e M N).hom ≫ (monoidalCategory S).tensorHom (T.map f) (T.map g)) ∧
            ∀ (M N : ringedSiteModules.{u, u, u, u} ((sheafCompose J (forget₂ CommRingCat.{u}
              RingCat.{u})).obj R)) (Z : Sheaf J (Type u))
              (x : Z ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
                sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (M))) (y : Z ⟶
                ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
                sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (N)))
              (z : Z ⟶ ((toSheaf ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
                sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj (((monoidalCategory
                R).tensorObj (M) (N))))),
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
                    sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).map (e M
                    N).hom).hom.app W t =
                (tensorObjIsoSheafification (T.obj M) (T.obj N)).inv.val.app W
                  (((PresheafOfModules.sheafificationAdjunction
                  (𝟙 ((sheafCompose K (forget₂ CommRingCat.{u} RingCat.{u})).obj S).obj)).unit.app
                    ((T.obj M).val ⊗ (T.obj N).val)).app W
                  ((L.map x ≫ (eI.inv.app (M) ≫ q (M))).hom.app W t ⊗ₜ[S.obj.obj W] (L.map y ≫
                    (eI.inv.app (N) ≫ q (N))).hom.app W t)) := by
  classical
  obtain ⟨A, eR, addR, mulR, addA, mulA, h⟩ :=
    module_pullback_pushforward_adjunction J K L V _adj R S
  rcases h with ⟨haddR, hmulR, haddA, hmulA, hmapadd, hmapmul, hc⟩
  refine ⟨A, eR, addR, mulR, addA, mulA, haddR, hmulR, haddA, hmulA,
    hmapadd, hmapmul, ?_⟩
  intro c
  rcases hc c with ⟨I, P, eI, eP, hI, hP, hTdata⟩
  rcases hTdata with ⟨T, hT, hTmap, hamq⟩
  rcases hamq with ⟨am, q, hq, ham⟩
  refine ⟨I, eI, hI, T, hT, hTmap, q, hq, ?_⟩
  exact module_pullback_tensor_iso_tail J K L V _adj R S A eR c I eI hI T hT hTmap
    q hq P eP hP am ham


end SheafOfModules
