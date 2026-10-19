/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.AlgebraicGeometry.LocalDirectImageStalkClassMap

/-! # Scalar compatibility of the local direct-image class map

Source: Stacks Project, Tags 02OD and 01E4.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives

set_option maxHeartbeats 800000 in
-- Elaborating the nested derived, forgetful and evaluation comparisons needs a larger limit.
private theorem resolution_top_smul {Z S : Scheme.{u}} (h : Z ⟶ S)
    {G : Z.Modules} (K : InjectiveResolution G) (p : ℕ)
    (t : S.presheaf.obj (op ⊤))
    (x : (RingedSpace.moduleCohomology Z.toRingedSpace p).obj G) :
    Scheme.Modules.resolutionSectionClass K
        (((Scheme.Modules.pushforward h).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj K.cocomplex) ⊤ (Iso.refl _) p (h.appTop.hom t • x) =
      t • (show ((((Scheme.Modules.pushforward h).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K.cocomplex).homology p).val.obj (op ⊤) from
          Scheme.Modules.resolutionSectionClass K
            (((Scheme.Modules.pushforward h).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj K.cocomplex) ⊤ (Iso.refl _) p x) := by
  let := RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
  let A := RingedSpace.globalSectionsComplex K
  let L := ((Scheme.Modules.pushforward h).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K.cocomplex
  let B := ((SheafOfModules.forget S.ringCatSheaf).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj L
  let U := forget₂ (ModuleCat.{u} (Z.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u}
  let E := PresheafOfModules.toPresheaf S.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation S.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let τ : E ⟶ E := {
    app := fun M ↦ (M.obj (op ⊤)).smul t
    naturality := fun M N q ↦ by
      ext z
      exact ((q.app (op ⊤)).hom.map_smul t z).symm }
  let cA := (A.sc p).mapHomologyIso U
  let cB := (B.sc p).mapHomologyIso E
  have hscalar : (A.sc p).mapNatTrans
      (ModuleCat.smulNatTrans (Z.ringCatSheaf.obj.obj (op ⊤)) (h.appTop.hom t)) =
      (B.sc p).mapNatTrans τ := by
    ext m <;> rfl
  have hm := congrArg (fun q ↦ ShortComplex.homologyMap q) hscalar
  rw [ShortComplex.homologyMap_mapNatTrans,
    ShortComplex.homologyMap_mapNatTrans] at hm
  have hm' := congrArg (fun q ↦ cA.inv ≫ q ≫ cB.hom) hm
  have hc : (A.sc p).homology.smul (h.appTop.hom t) ≫ cA.inv ≫ cB.hom =
      cA.inv ≫ cB.hom ≫ τ.app (B.sc p).homology := by
    simpa [cA, cB, U, Category.assoc, ModuleCat.smulNatTrans] using hm'
  have hc' (z : (A.sc p).homology) :
      cB.hom (cA.inv (h.appTop.hom t • z)) =
        t • (show (B.sc p).homology.obj (op ⊤) from cB.hom (cA.inv z)) := by
    exact congrArg (fun q ↦ q z) hc
  let e := (K.isoRightDerivedObj (RingedSpace.globalSectionsFunctor Z.toRingedSpace) p).hom
  let θ := (Scheme.Modules.sectionCohomologyTheta L p).app (op ⊤)
  dsimp only [Scheme.Modules.resolutionSectionClass]
  simp only [Iso.refl_hom]
  erw [CategoryTheory.Functor.map_id]
  erw [Category.id_comp]
  change θ (cB.hom (cA.inv (e (h.appTop.hom t • x)))) =
    t • (show (L.homology p).val.obj (op ⊤) from θ (cB.hom (cA.inv (e x))))
  rw [e.hom.map_smul, hc', θ.hom.map_smul]

private theorem local_germ_smul {Y : Scheme.{u}} (y : Y)
    (G : (Spec (CommRingCat.of (Y.presheaf.stalk y))).Modules)
    (r : Y.presheaf.stalk y) (s : G.val.obj (op ⊤)) :
    TopCat.Presheaf.germ ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj G).presheaf
        ⊤ y (by trivial) (((Scheme.ΓSpecIso (CommRingCat.of
          (Y.presheaf.stalk y))).inv.hom r) • s) =
      r • (show (RingedSpace.moduleStalkFunctor Y.toRingedSpace y).obj
        ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj G) from
        TopCat.Presheaf.germ
          ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj G).presheaf
          ⊤ y (by trivial) s) := by
  obtain ⟨V, hy, a, rfl⟩ := Y.presheaf.exists_germ_eq r
  let c := Y.fromSpecStalk y
  let M := (Scheme.Modules.pushforward c).obj G
  have hr : (c.app V).hom a =
      ((Spec (CommRingCat.of (Y.presheaf.stalk y))).presheaf.map
        (homOfLE (le_top (a := c ⁻¹ᵁ V))).op).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom
          (Y.presheaf.germ V y hy a)) := by
    rw [Scheme.fromSpecStalk_app hy]
    rfl
  rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE le_top) y hy,
    ← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE le_top) y hy]
  change TopCat.Presheaf.germ M.presheaf V y hy
      (G.val.map (homOfLE (le_top (a := c ⁻¹ᵁ V))).op (_ • s)) = _
  rw [G.val.map_smul]
  change TopCat.Presheaf.germ M.presheaf V y hy
      (((Spec (CommRingCat.of (Y.presheaf.stalk y))).presheaf.map
        (homOfLE (le_top (a := c ⁻¹ᵁ V))).op).hom
          ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom
            (Y.presheaf.germ V y hy a)) •
            (show G.val.obj (op (c ⁻¹ᵁ V)) from
              G.val.map (homOfLE (le_top (a := c ⁻¹ᵁ V))).op s)) = _
  rw [← hr]
  exact PresheafOfModules.germ_smul (R := Y.presheaf) M.val y V hy a _

/-- Scalar compatibility of the specified additive cohomology-to-stalk map.
Source: Stacks Project, Tag 01E4, Lemma 20.7.3, the section-complex comparison;
Tag 02OD, Lemma 30.20.7, the displayed local-stalk/global-cohomology equality.
(blueprint: lem-weil-pbc-local-direct-image-stalk-class-smul)

Proof: Put A = O_{Y,y}, c = fromSpecStalk y, f' = pullback.fst c f, and
F' = (tensorPullback (pullback.snd c f)).obj F. Represent r by a structure-sheaf
section a on a neighborhood V of y. The inverse image c^{-1}V is the entire
local spectrum. The germ/stalk-map square for c, followed by the canonical
closed-point ring isomorphism, identifies c.app V a with Gamma-Spec.inv r,
after transporting the inverse-image open to top. Thus multiplication by r
on the source cohomology is multiplication by f'.appTop (Gamma-Spec.inv r)
on the global section complex of the fixed injective resolution of F'.
The resolution-to-derived isomorphism is a morphism of global-section modules.
The forgetful homology comparison and the identity of the two section complexes
respect the indicated scalar actions as follows. For a fixed base section t,
multiplication by its pullback is a chain endomorphism, since every differential
is linear. Naturality of each mapHomologyIso with respect to this endomorphism
identifies the induced map on homology with multiplication by t. This applies
both to forgetting module scalars and to evaluating presheaf modules on top;
the identity of the section complexes intertwines the same endomorphisms. Evaluation of presheaf
homology is linear over the ring of sections on top. The sheafification comparison
and its adjoint theta are morphisms of presheaves of modules, hence their component
on top is linear. The higher-direct-image resolution comparison is a morphism of
module sheaves and therefore linear on sections. Finally restrict its top section
to V. The inverse image is still top, and the restriction is the identity under
this identification. The module germ identity sends a times this section to
r times its germ. Composing these identities proves the displayed equation for
the actual localDirectImage_stalk_class construction, not an arbitrarily chosen
comparison. The argument works in degree zero, for the zero module, and for an
empty local base change, since it uses only linear maps and their induced homology.
-/
theorem localDirectImage_stalk_class_smul {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (p : ℕ) (r : Y.presheaf.stalk y)
    (x : (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
          (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
      ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)) :
    localDirectImage_stalk_class f y F p (r • x) =
      r • localDirectImage_stalk_class f y F p x := by
  let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
  let K := injectiveResolution F'
  let x' : (RingedSpace.moduleCohomology
    (pullback (Y.fromSpecStalk y) f).toRingedSpace p).obj F' := x
  let h := pullback.fst (Y.fromSpecStalk y) f
  let L := ((Scheme.Modules.pushforward h).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K.cocomplex
  let t := (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom r
  let b := Scheme.Modules.resolutionSectionClass K L ⊤ (Iso.refl _) p
  let j := (K.isoRightDerivedObj (Scheme.Modules.pushforward h) p).inv
  change TopCat.Presheaf.germ
      ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
        (((Scheme.Modules.pushforward h).rightDerived p).obj F')).presheaf
      ⊤ y (by trivial) (Scheme.Modules.Hom.app j ⊤ (b (h.appTop.hom t • x'))) = _
  have hb := resolution_top_smul h K p t x'
  change b (h.appTop.hom t • x') =
    t • (show (L.homology p).val.obj (op ⊤) from b x') at hb
  rw [hb, Scheme.Modules.Hom.app_smul]
  exact local_germ_smul y (((Scheme.Modules.pushforward h).rightDerived p).obj F') r
    (Scheme.Modules.Hom.app j ⊤ (b x'))

end AlgebraicGeometry
