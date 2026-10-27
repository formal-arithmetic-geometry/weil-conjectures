/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.ZariskiEtaleTensorSections
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.TensorPullbackQuasiCoherent
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.EtaleQuasiCoherentDescent
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsMapNaturality
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction
import Sheaf.AlgebraicGeometry.EtaleTensorSectionsAdjunctionExtension
import Sheaf.AlgebraicGeometry.EtaleTensorSectionsOpenDetermination

/-!
# Tensor extension, affine free presentations and Hom comparison

Source: Stacks Project, Descent, Tags 03FH, 03DV (2), and 0GN7
(blueprint: lem-trf-etale-extension-free-presentations-hom).

## Main declarations

- `etaleExtensionAssociator`: the canonical reassociation of three étale arrows.
- `etaleExtension_free_presentations_hom`: tensor extension, free presentations and Hom.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Reassociation of three étale arrows, with identity underlying scheme map.
Source: Stacks Project, Descent, Tag 03FH (2)
(blueprint: lem-trf-etale-extension-free-presentations-hom). -/
def etaleExtensionAssociator {T : Scheme.{u}} (U : T.Etale) (A : U.left.Etale)
    (B : A.left.Etale) :
    Scheme.Etale.mk ((B.hom ≫ A.hom) ≫ U.hom) ≅
      Scheme.Etale.mk (B.hom ≫ (A.hom ≫ U.hom)) :=
  MorphismProperty.Over.isoMk (Iso.refl B.left)
    ((Category.id_comp _).trans (Category.assoc B.hom A.hom U.hom))

/-- Tensor extension is left adjoint to open restriction, preserves arbitrary small
colimits, sends the unit ring module to the étale ring module, and identifies on
quasi-coherent modules with the actual tensor-section sheaf. The comparison is linear,
natural in module maps, and identifies the unit on every open with the identity.
Localization is expressed on the underlying additive presheaves via the existing
slice equivalence; its components are linear by the displayed tensor-composition
normalization. The final equations give map naturality and the three-arrow cocycle.
Affine presentations are cokernel coforks between small free module sheaves; their
images are again cokernels, with the images of both free terms free. The localization
comparison identifies their target with the restriction of the original extension.

Source: Stacks Project, Descent, Tags 03FH, 03DV (2), and 0GN7
(blueprint: lem-trf-etale-extension-free-presentations-hom).

Proof, following the eight DAG steps:
1. Apply the ringed-module adjunction to epsilon. Its right adjoint evaluates on
   opens, so its tensor left adjoint preserves all small colimits. This uses
   lem-weil-pbc-ringed-topoi-module-adjunction, lem-trf-zariski-etale-tensor-sections,
   and lem-weil-pbc-left-adjoint-preserves-colimits.
2. Quasi-coherent étale descent says the tensor-section presheaf is already a sheaf.
   Remove sheafification from zariskiEtale_tensorSections by its universal property.
   This retains the scalar action and the pullback action on module maps, using
   lem-sc-etale-qcoherent-descent and def-weil-presheaf-modules-sheafification.
3. The slice equivalence identifies T_et/U with U_et. Tensor pullback preserves
   quasi-coherence. On a:A to U the localized comparison is the normalized
   composition comparison c_(a,u). Map naturality and the normalized adjunction
   units prove naturality and the cocycle for three successive arrows. The nodes are
   lem-weil-pbc-etale-site-localization-open, lem-weil-pbc-module-pullback-quasi-coherent,
   lem-sc-etale-qcoherent-presheaf-functorial and lem-sc-etale-tensor-sections-map-naturality.
4. Pullback of the unit ring module is the unit ring module: multiplication of
   tensors has inverse b mapped to b tensor 1. The rank-one affine tilde calculation
   proves Zariski quasi-coherence of the unit. Step 2 identifies its extension, using
   lem-weil-pbc-spec-tilde-free-module.
5. On an affine cover write F as tilde M. Present M by the free module on its
   underlying set, with relations the underlying set of the kernel. The tilde/Gamma
   adjunction preserves these coproducts and cokernels; tilde A is the unit module.
   These are pqf-def-coherent and lem-weil-pbc-affine-tilde-gamma-adjunction.
6. Apply extension to these presentations. Steps 1 and 4 make the images free
   presentations. Step 3 identifies their target with the restricted extension.
   Apply the same argument to v^*F for every étale object v, proving the site-local
   quasi-coherence condition on every object, including objects over the empty scheme:
   def-trf-space-quasi-coherent-module. For open restriction use
   lem-weil-pbc-open-immersion-module-pullback-restriction.
7. Restrict a tensor-section map to opens and precompose with the unit-compatible
   open-pullback comparison. The adjunction-extension theorem and open-determination
   theorem make this the adjunction Hom bijection. Consequently its unit is exactly
   the identity after the open-section identification, including the empty open. Use
   lem-trf-etale-tensor-sections-adjunction-extension and
   lem-trf-etale-tensor-sections-open-determination.
8. Adjunction identifies Hom(LF,LH) with Hom(F,RLH). Step 7 makes the unit of H an
   isomorphism. Its naturality identifies this bijection with h mapped to L(h). -/
theorem etaleExtension_free_presentations_hom :
    ∃ c : ∀ T : Scheme.{u}, ZariskiEtaleModuleContext T,
      (∀ T : Scheme.{u}, PreservesColimitsOfSize.{v, w} (c T).extension) ∧
      (∀ T : Scheme.{u}, Nonempty
        ((c T).extension.obj (SheafOfModules.unit T.ringCatSheaf) ≅
          SheafOfModules.unit (smallEtaleModuleRing T))) ∧
      (∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent],
        ((c T).extension.obj F).IsQuasicoherent) ∧
      (∀ (T : Scheme.{u}) (F H : T.Modules) [F.IsQuasicoherent] [H.IsQuasicoherent],
        Function.Bijective (fun h : F ⟶ H ↦ (c T).extension.map h)) ∧
      ∃ e : ∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent],
          (SheafOfModules.toSheaf (smallEtaleModuleRing T)).obj ((c T).extension.obj F) ≅
            etaleTensorSectionsSheaf F,
        (∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent]
            (V : T.Etale) (r : Γ(V.left, ⊤))
            (s : ((c T).extension.obj F).val.obj (op V)),
          (e T F).hom.hom.app (op V) (r • s) =
            r • (@id (Γ((tensorPullback V.hom).obj F, ⊤))
              ((e T F).hom.hom.app (op V) s))) ∧
        (∀ (T : Scheme.{u}) (F H : T.Modules) [F.IsQuasicoherent] [H.IsQuasicoherent]
            (h : F ⟶ H) (V : T.Etale),
          ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
            ((c T).extension.map h)).hom.app (op V) ≫
              (e T H).hom.hom.app (op V) =
            (e T F).hom.hom.app (op V) ≫ ((tensorPullback V.hom).map h).app ⊤) ∧
        (∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent] (W : T.Opens),
          ((c T).adjunction.unit.app F).app W ≫
              (e T F).hom.hom.app (op ((AlgebraicGeometry.gabberOpenEtale T).obj W)) ≫
                (tensorOpenSectionIso T F W).hom = 𝟙 _) ∧
        ∃ k : ∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent] (U : T.Etale),
            (Scheme.Etale.etaleToOver U ⋙ Over.forget U).op ⋙
                ((c T).extension.obj F).val.presheaf ≅
              ((c U.left).extension.obj ((tensorPullback U.hom).obj F)).val.presheaf,
          (∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent]
              (U : T.Etale) (A : U.left.Etale),
            (k T F U).hom.app (op A) ≫
                (e U.left ((tensorPullback U.hom).obj F)).hom.hom.app (op A) ≫
                ((tensorSectionsComp A.hom U.hom).hom.app F).app ⊤ =
              (e T F).hom.hom.app (op (Scheme.Etale.mk (A.hom ≫ U.hom)))) ∧
          (∀ (T : Scheme.{u}) (F H : T.Modules) [F.IsQuasicoherent] [H.IsQuasicoherent]
              (h : F ⟶ H) (U : T.Etale) (A : U.left.Etale),
            ((SheafOfModules.toSheaf (smallEtaleModuleRing T)).map
            ((c T).extension.map h)).hom.app
                (op (Scheme.Etale.mk (A.hom ≫ U.hom))) ≫ (k T H U).hom.app (op A) =
              (k T F U).hom.app (op A) ≫
                ((SheafOfModules.toSheaf (smallEtaleModuleRing U.left)).map
                  ((c U.left).extension.map ((tensorPullback U.hom).map h))).hom.app
                  (op A)) ∧
          (∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent]
              (U : T.Etale) (A : U.left.Etale) (B : A.left.Etale),
            (k T F U).hom.app (op (Scheme.Etale.mk (B.hom ≫ A.hom))) ≫
                (k U.left ((tensorPullback U.hom).obj F) A).hom.app (op B) ≫
                ((SheafOfModules.toSheaf (smallEtaleModuleRing A.left)).map
                  ((c A.left).extension.map
                    ((tensorSectionsComp A.hom U.hom).hom.app F))).hom.app (op B) =
              ((c T).extension.obj F).val.presheaf.map
                  (etaleExtensionAssociator U A B).inv.op ≫
                (k T F (Scheme.Etale.mk (A.hom ≫ U.hom))).hom.app (op B)) ∧
          ∀ (T : Scheme.{u}) (F : T.Modules) [F.IsQuasicoherent],
            ∃ (ι : Type u) (W : ι → T.Opens),
              (∀ x : T, ∃ i : ι, x ∈ W i) ∧ (∀ i : ι, IsAffineOpen (W i)) ∧
              ∀ i : ι, ∃ (I J : Type u)
                (f : SheafOfModules.free (R := (W i).toScheme.ringCatSheaf) I ⟶
                  SheafOfModules.free J)
                (g : SheafOfModules.free J ⟶ (tensorPullback (W i).ι).obj F)
                (z : f ≫ g = 0),
                Nonempty (IsColimit (CokernelCofork.ofπ g z)) ∧
                Nonempty ((c (W i).toScheme).extension.obj (SheafOfModules.free I) ≅
                  SheafOfModules.free (R := smallEtaleModuleRing (W i).toScheme) I) ∧
                Nonempty ((c (W i).toScheme).extension.obj (SheafOfModules.free J) ≅
                  SheafOfModules.free (R := smallEtaleModuleRing (W i).toScheme) J) ∧
                ∃ z' : (c (W i).toScheme).extension.map f ≫
                    (c (W i).toScheme).extension.map g = 0,
                  Nonempty (IsColimit (CokernelCofork.ofπ
                    ((c (W i).toScheme).extension.map g) z')) := by
  sorry

end
end AlgebraicGeometry.Scheme.Modules
