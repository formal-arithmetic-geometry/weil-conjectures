/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.CommAlgebraSheaf
public import Sheaf.AlgebraicGeometry.ModulePullbackTensor
public import Sheaf.AlgebraicGeometry.TensorPullbackStructureSheaf
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapAlgebra

/-! # Transport of the structure algebra through an invertible base-change map

Source: Stacks Project, Constructions, Section 01LQ; Cohomology, Remark 08HY.
This isolates steps 2--3 of the relative-Spec base-change argument
(blueprint: lem-weil-pbc-structure-algebra-pullback-transport).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def algebraModuleMap {S : Scheme.{u}}
    {A B : S.CommAlgebraSheaf} (f : A ⟶ B) :
    (A.toModule : S.Modules) ⟶ (B.toModule : S.Modules) where
  val := {
    app := fun V ↦ ModuleCat.ofHom (X := A.toModule.val.obj V)
      (Y := B.toModule.val.obj V) {
      toFun := f.right.hom.app V
      map_add' := (f.right.hom.app V).hom.map_add
      map_smul' := by
        intro r a
        change A.right.obj.obj V at a
        change f.right.hom.app V (A.hom.hom.app V r * a) =
          B.hom.hom.app V r * f.right.hom.app V a
        rw [(f.right.hom.app V).hom.map_mul]
        have h := congrArg (fun t ↦ t.hom.app V) f.w
        exact congrArg (fun t ↦ t * f.right.hom.app V a)
          (ConcreteCategory.congr_hom h r) }
    naturality := by
      intro U V i
      ext a
      exact ConcreteCategory.congr_hom (f.right.hom.naturality i) a }

private noncomputable def algebraModuleIso {S : Scheme.{u}}
    {A B : S.CommAlgebraSheaf} (a : A ≅ B) :
    (A.toModule : S.Modules) ≅ (B.toModule : S.Modules) where
  hom := algebraModuleMap a.hom
  inv := algebraModuleMap a.inv
  hom_inv_id := by
    apply hom_ext
    intro W
    ext x
    exact congrArg (fun t ↦ t.right.hom.app (op W)
      (show A.right.obj.obj (op W) from x)) a.hom_inv_id
  inv_hom_id := by
    apply hom_ext
    intro W
    ext x
    exact congrArg (fun t ↦ t.right.hom.app (op W)
      (show B.right.obj.obj (op W) from x)) a.inv_hom_id

private theorem tensor_hom_ext {S : Scheme.{u}} {M N P : S.Modules}
    (f h : M ⊗ N ⟶ P)
    (ht : ∀ (W : S.Opens) (s : Γ(M, W)) (t : Γ(N, W)),
      f.app W (tmulSection s t) = h.app W (tmulSection s t)) : f = h := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (PresheafOfModules.sheafificationAdjunction (𝟙 S.ringCatSheaf.obj)).homEquiv _ P
    |>.injective
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro s t
  exact ht (unop W) s t

set_option maxHeartbeats 600000 in
-- The algebra-to-module comparison and tensor naturality require dependent sheaf elaboration.
/-- For a commuting square whose canonical structure-module comparison is invertible,
transport an algebra identification on the old base to the actual structure algebra on
its new base. No affineness, cartesianness or quasi-coherence is assumed or concluded.
Source: Stacks Project, Constructions, Section 01LQ; Cohomology, Remark 08HY;
Modules, Tag 01CD; the transport calculation in steps 2--3 of the parent node
(blueprint: lem-weil-pbc-structure-algebra-pullback-transport).
Proof: Let B = pi_* O_X, B' = pi'_* O_X', and let delta be the displayed canonical
invertible module comparison. The algebra isomorphism alpha induces an O_S-module
isomorphism a: A.toModule ≅ B: its section maps are alpha's ring maps and their inverses,
linear because alpha commutes with the structure maps. Set hA' to the inverse of
the composite (g^* a) followed by delta. Choose mu' to be the actual multiplication on B' and e' to
be pi'-sharp. The tensor universal property specifies mu' by products of pure section
tensors; e' has the asserted formula by construction. On the old base the same property
and hmu identify multiplication on B with a^{-1} tensor a^{-1} followed by mu and a;
he similarly identifies its unit. Apply g^* to these identities. Naturality of the
comparison in module_pullback_tensor moves g^*(a tensor a) through that comparison.
The multiplication and unit identities of moduleBaseChangeMap_algebra for delta now
give the two displayed transport equations, cancelling the inverse isomorphisms.
For the section formula, unit naturality gives
(g^*a)(eta_A(a)) = eta_B(alpha(a)). The adjoint identity for delta in
moduleBaseChangeMap_algebra evaluates delta(eta_B(b)) as g'-sharp(b) on each inverse
image open, after the canonical pushforward-composition identifications. Substitute
b = alpha(a). This proves the final formula, without any assumption of flatness or
nonemptiness; all equalities are sheaf-morphism equalities and also apply on empty opens.
-/
theorem structure_algebra_pullback_transport
    (S S' : Scheme.{u}) (g : S' ⟶ S)
    (A : S.CommAlgebraSheaf)
    (μ : (SheafOfModules.monoidalCategory S.sheaf).tensorObj A.toModule A.toModule ⟶
      A.toModule)
    (e : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ⟶ (A.toModule : S.Modules))
    (hμ : ∀ (V : S.Opens) (a b : A.right.obj.obj (op V)),
      μ.val.app (op V) (tmulSection (M := A.toModule) (N := A.toModule) (U := V) a b) = a * b)
    (he : ∀ (V : S.Opens) (r : Γ(S, V)), e.val.app (op V) r = A.hom.hom.app (op V) r)
    (X : Scheme.{u}) (π : X ⟶ S)
    (α : A ≅ Under.mk (⟨π.c⟩ : Scheme.sheaf _ ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} π.base).obj (Scheme.sheaf _)))
    (X' : Scheme.{u}) (π' : X' ⟶ S') (g' : X' ⟶ X)
    (w : g' ≫ π = π' ≫ g)
    [IsIso (moduleBaseChangeMap π π' g g' w (SheafOfModules.unit X.ringCatSheaf) ≫
      (pushforward π').map (tensorPullbackObjUnitToUnit g'))] :
    let A' : S'.CommAlgebraSheaf := Under.mk (⟨π'.c⟩ : Scheme.sheaf _ ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} π'.base).obj (Scheme.sheaf _))
    ∃
      (hA' : (A'.toModule : S'.Modules) ≅ (tensorPullback g).obj (A.toModule : S.Modules))
      (μ' : (SheafOfModules.monoidalCategory S'.sheaf).tensorObj A'.toModule A'.toModule ⟶
        A'.toModule)
      (e' : (SheafOfModules.unit S'.ringCatSheaf : S'.Modules) ⟶ (A'.toModule : S'.Modules)),
      (∀ (W : S'.Opens) (a b : A'.right.obj.obj (op W)),
        μ'.val.app (op W)
          (tmulSection (M := A'.toModule) (N := A'.toModule) (U := W) a b) = a * b) ∧
      (∀ (W : S'.Opens) (r : Γ(S', W)), e'.val.app (op W) r = A'.hom.hom.app (op W) r) ∧
      (tensorPullback g).map μ =
        (Classical.choose (module_pullback_tensor g)
          (A.toModule : S.Modules) (A.toModule : S.Modules)).hom ≫
          (SheafOfModules.monoidalCategory S'.sheaf).tensorHom hA'.inv hA'.inv ≫ μ' ≫ hA'.hom ∧
      (tensorPullback g).map e ≫ hA'.inv = tensorPullbackObjUnitToUnit g ≫ e' ∧
      (∀ (V : S.Opens) (a : A.right.obj.obj (op V)),
        hA'.inv.val.app (op (g ⁻¹ᵁ V))
            (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
              (A.toModule : S.Modules)).val.app (op V) a) =
          g'.appLE (π ⁻¹ᵁ V) (π' ⁻¹ᵁ (g ⁻¹ᵁ V))
            (by rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w])
            (α.hom.right.hom.app (op V) a))  := by
  classical
  let := SheafOfModules.monoidalCategory S.sheaf
  let := SheafOfModules.monoidalCategory S'.sheaf
  let a : (A.toModule : S.Modules) ≅
      (pushforward π).obj (SheafOfModules.unit X.ringCatSheaf) := algebraModuleIso α
  let δ := moduleBaseChangeMap π π' g g' w (SheafOfModules.unit X.ringCatSheaf) ≫
    (pushforward π').map (tensorPullbackObjUnitToUnit g')
  let c : (tensorPullback g).obj (A.toModule : S.Modules) ≅
      (pushforward π').obj (SheafOfModules.unit X'.ringCatSheaf) :=
    (tensorPullback g).mapIso a ≪≫ asIso δ
  obtain ⟨m, m', hm, hm', hadj, hmul, hunit⟩ := moduleBaseChangeMap_algebra π π' g g' w
  have hma : μ ≫ a.hom =
      (SheafOfModules.monoidalCategory S.sheaf).tensorHom a.hom a.hom ≫ m := by
    apply tensor_hom_ext
    intro W s t
    change a.hom.val.app (op W) (μ.val.app (op W) (tmulSection s t)) =
      m.app W ((SheafOfModules.monoidalCategory S.sheaf).tensorHom
        a.hom a.hom |>.val.app (op W) (tmulSection s t))
    erw [tensorHom_app_tmulSection (X := S) a.hom a.hom s t, hm]
    change α.hom.right.hom.app (op W) (μ.val.app (op W) (tmulSection s t)) = _
    rw [hμ]
    exact (α.hom.right.hom.app (op W)).hom.map_mul s t
  have hea : e ≫ a.hom =
      SheafOfModules.unitToPushforwardObjUnit π.toRingCatSheafHom := by
    apply hom_ext
    intro W
    ext r
    change α.hom.right.hom.app (op W) (e.val.app (op W) r) = π.app W r
    rw [he]
    exact congrArg (fun t ↦ t.hom.app (op W) r) α.hom.w
  let e' := SheafOfModules.unitToPushforwardObjUnit π'.toRingCatSheafHom
  refine ⟨c.symm, m', e', hm', ?_, ?_, ?_, ?_⟩
  · intro W r
    rfl
  · apply (cancel_mono c.hom).mp
    simp only [Iso.symm_hom, Iso.symm_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    change (tensorPullback g).map μ ≫ (tensorPullback g).map a.hom ≫ δ = _
    rw [← Functor.map_comp_assoc, hma, Functor.map_comp, Category.assoc, hmul]
    have hn := (Classical.choose_spec (module_pullback_tensor g)).1
      (A.toModule : S.Modules) (A.toModule : S.Modules)
      ((pushforward π).obj (SheafOfModules.unit X.ringCatSheaf))
      ((pushforward π).obj (SheafOfModules.unit X.ringCatSheaf)) a.hom a.hom
    rw [← Category.assoc]
    erw [hn]
    rw [Category.assoc]
    simp only [c, Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
    have ht := tensorHom_comp_tensorHom (C := S'.Modules)
      ((tensorPullback g).map a.hom) ((tensorPullback g).map a.hom) δ δ
    simpa only [Category.assoc] using congrArg
      (fun t ↦ (Classical.choose (module_pullback_tensor g)
        (A.toModule : S.Modules) (A.toModule : S.Modules)).hom ≫ t ≫ m') ht
  · change (tensorPullback g).map e ≫ (tensorPullback g).map a.hom ≫ δ = _
    rw [← Functor.map_comp_assoc, hea]
    exact hunit
  · intro V s
    change δ.app (g ⁻¹ᵁ V)
      (((tensorPullback g).map a.hom).val.app (op (g ⁻¹ᵁ V))
        (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
          (A.toModule : S.Modules)).val.app (op V) s)) = _
    have hn := congrArg (fun t ↦ t.val.app (op V) s)
      ((Classical.choose (exists_tensorPullbackAdjunction g)).unit_naturality a.hom)
    change ((tensorPullback g).map a.hom).val.app (op (g ⁻¹ᵁ V))
        (((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
          (A.toModule : S.Modules)).val.app (op V) s) =
      ((Classical.choose (exists_tensorPullbackAdjunction g)).unit.app
        ((pushforward π).obj (SheafOfModules.unit X.ringCatSheaf))).val.app (op V)
          (α.hom.right.hom.app (op V) s) at hn
    rw [hn]
    have hv := congrArg (fun t ↦ t.app V
      (α.hom.right.hom.app (op V) s)) hadj
    simp only [Hom.comp_app, ConcreteCategory.comp_apply, pushforward_map_app,
      pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
      pushforwardCongr_hom_app_app] at hv
    exact hv

end AlgebraicGeometry
