module

public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings
namespace SheafOfModules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- The tensor comparison and its generalized pure-tensor normalization for the
specified inverse-image and scalar-extension module functors.
Source: Stacks Project, Modules on Sites, Tag 03EL, lemma-tensor-product-pullback;
Tags 03D2, 03D7 and 03CZ for transport, adjunction and sheafification.
(blueprint: lem-weil-pbc-ringed-topoi-module-pullback-tensor-tail)

The equations hI identify addition and scalar multiplication under eI and eR.
The equations hP identify the direct-image module action with the adjunct of c.
These operation equations are essential: an underlying-sheaf comparison and a
compatible module adjunction alone can also describe nongeometric scalar actions.

Proof:
For an S-module H, the adjunction am and the sheaf tensor universal property
identify Hom(T(M tensor_R N), H) with R-bilinear sheaf maps from M times N to P(H).
Transpose such a map through _adj, using the inverse of the product comparison
for L and eI in the two source factors and eP in the target. The addition equations
in hI and hP identify the two additivity diagrams with their transposes. For the
scalar equations, use the product comparison on the three factors R, M and N.
The two projections specifying k in hP identify its ring component with the
adjunct of eR.inv followed by c and its module component with eP. Its last equation
therefore identifies the transposed scalar action with restriction of the H-action
along c. The scalar equations in hI identify the source actions through eR.
Injectivity of the adjunction hom equivalence proves both directions. We obtain
exactly the A-bilinear sheaf maps I(M) times I(N) to H restricted along c.

Extend such a map beta sectionwise by
(s tensor x, t tensor y) mapping to (s * t) times beta(x, y).
A-bilinearity gives the two tensor balancing relations. Commutativity of S gives
S-linearity in each variable. The restriction maps agree on pure tensors, hence
on all tensors by tensor induction. Sheafification extends the two variables
uniquely: finite-product preservation of set sheafification transports the
bilinear equations, and the sheaf tensor universal property gives an S-linear
map T(M) tensor_S T(N) to H. Conversely, precompose with q in both variables.
The equation hq and linearity show that these constructions are inverse, first
on pure tensors and then on their sheafifications. This gives a Hom equivalence
natural in H. Applying it and its inverse to identities gives the two comparison
maps; naturality shows their composites are identities. Take the orientation
from T(M tensor_R N) to T(M) tensor_S T(N).

The constructions commute with precomposition in M and N; the functorial
identification hTmap gives the displayed simultaneous naturality. Finally hAdj
identifies the mate of a map out of T with its composite after eI.inv and q.
Thus the Hom equivalence applied to the identity of T(M) tensor_S T(N) sends
the inverse image of the source pure-tensor map to the tensor of the two maps
obtained by q. This equality of sheaf morphisms can be precomposed by any Z
and evaluated at every W and t, giving exactly the stated normalization.
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
  sorry

end SheafOfModules
