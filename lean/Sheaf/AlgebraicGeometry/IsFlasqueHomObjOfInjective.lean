/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Sheaves.Flasque
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroHomFormula

/-! # Flasqueness of internal Hom into an injective module

Source: Stacks Project, Cohomology, Tag 01EA, the extension-by-zero argument applied
 to the restricted source module (blueprint: lem-sc-ext-coherent-hom-injective-flasque).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
open Classical in
private noncomputable def extensionToSource {C : Type u} [SmallCategory C]
    {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (F : SheafOfModules.{u} R)
    (U : C) :
    (SheafOfModules.extensionByZeroPresheaf R U).obj
        ((SheafOfModules.overFunctor R U).obj F) ⟶ F.val where
  app W := ModuleCat.ofHom (DirectSum.toModule _ _ _ (fun _ ↦ LinearMap.id))
  naturality {W W'} f := by
    ext s
    induction s using DirectSum.induction_on with
    | zero => simp
    | of h s =>
      change (DirectSum.toModule (R.obj.obj W') (W'.unop ⟶ U)
          (F.val.obj W') (fun _ ↦ LinearMap.id))
          (SheafOfModules.extensionByZeroPresheafRestrictAdd R U
            ((SheafOfModules.overFunctor R U).obj F) f
            (DirectSum.of _ h s)) =
        F.val.map f ((DirectSum.toModule (R.obj.obj W) (W.unop ⟶ U)
          (F.val.obj W) (fun _ ↦ LinearMap.id))
          (DirectSum.of _ h s))
      unfold SheafOfModules.extensionByZeroPresheafRestrictAdd
      erw [DirectSum.toAddMonoid_of]
      dsimp only [AddMonoidHom.comp_apply]
      erw [DirectSum.toModule_lof, DirectSum.toModule_lof]
      rfl
    | add s t hs ht => simpa only [map_add] using congrArg₂ (· + ·) hs ht

private theorem extensionToSource_of {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (F : SheafOfModules.{u} R)
    (U : C) (W : Cᵒᵖ) [DecidableEq (W.unop ⟶ U)]
    (h : W.unop ⟶ U) (s : F.val.obj W) :
    (extensionToSource R F U).app W (DirectSum.of _ h s) = s := by
  classical
  change (DirectSum.toModule (R.obj.obj W) (W.unop ⟶ U)
    (F.val.obj W) (fun _ ↦ LinearMap.id)) (DirectSum.of _ h s) = s
  erw [DirectSum.toModule_lof]
  rfl

private theorem sumIdentity_injective (A : Type u) [Ring A] (M : Type u)
    [AddCommGroup M] [Module A M] (ι : Type u) [Subsingleton ι] [DecidableEq ι] :
    Function.Injective (DirectSum.toModule A ι M (fun _ ↦ LinearMap.id)) := by
  by_cases h : Nonempty ι
  · obtain ⟨h⟩ := h
    have hinv (s : DirectSum ι (fun _ ↦ M)) :
        DirectSum.of (fun _ ↦ M) h
          (DirectSum.toModule A ι M (fun _ ↦ LinearMap.id) s) = s := by
      induction s using DirectSum.induction_on with
      | zero => simp
      | of h' s =>
        have : h' = h := Subsingleton.elim _ _
        subst h'
        erw [DirectSum.toModule_lof]
        rfl
      | add s t hs ht => simpa only [map_add] using congrArg₂ (· + ·) hs ht
    exact fun s t he ↦ (hinv s).symm.trans ((congrArg (DirectSum.of _ h) he).trans (hinv t))
  · have : IsEmpty ι := not_nonempty_iff.mp h
    intro s t _
    exact Subsingleton.elim s t

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem extensionToSource_mono {C : Type u} [SmallCategory C] [Quiver.IsThin C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) (F : SheafOfModules.{u} R)
    (U : C) : Mono (extensionToSource R F U) := by
  classical
  apply PresheafOfModules.mono_of_injective
  intro W
  let : DecidableEq (W.unop ⟶ U) := Classical.decEq _
  change Function.Injective (DirectSum.toModule (R.obj.obj W) (W.unop ⟶ U)
    (F.val.obj W) (fun _ ↦ LinearMap.id))
  exact sumIdentity_injective (R.obj.obj W) (F.val.obj W) (W.unop ⟶ U)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem extendsToSource {C : Type u} [SmallCategory C] [Quiver.IsThin C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
    (F I : SheafOfModules.{u} R) [Injective I] (U : C)
    (adj : (SheafOfModules.extensionByZeroPresheaf R U ⋙
      PresheafOfModules.sheafification (𝟙 R.obj)) ⊣ SheafOfModules.overFunctor R U)
    (hformula : ∀ (G : SheafOfModules.{u} R)
      (ψ : (SheafOfModules.extensionByZeroPresheaf R U ⋙
        PresheafOfModules.sheafification (𝟙 R.obj)).obj
          ((SheafOfModules.overFunctor R U).obj F) ⟶ G)
      (W : C) (h : W ⟶ U) (s : F.val.obj (op W)),
      ((adj.homEquiv _ G ψ).val.app (op (Over.mk h))) s =
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) ψ).app (op W)
          (DirectSum.of _ h s))
    (t : (SheafOfModules.overFunctor R U).obj F ⟶
      (SheafOfModules.overFunctor R U).obj I) :
    ∃ g : F ⟶ I, (SheafOfModules.overFunctor R U).map g = t := by
  classical
  let FU := (SheafOfModules.overFunctor R U).obj F
  let P := (SheafOfModules.extensionByZeroPresheaf R U).obj FU
  let S := PresheafOfModules.sheafification (𝟙 R.obj)
  let e : P ⟶ F.val := extensionToSource R F U
  have : Mono e := extensionToSource_mono R F U
  let a := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  let c : S.obj P ⟶ F := (a.homEquiv P F).symm e
  have : Mono c := by
    dsimp only [c]
    rw [a.homEquiv_counit]
    infer_instance
  let ψ := (adj.homEquiv FU I).symm t
  let g : F ⟶ I := Injective.factorThru ψ c
  refine ⟨g, ?_⟩
  have hc : PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) c = e :=
    (a.homEquiv P F).apply_symm_apply e
  have hg := Injective.comp_factorThru ψ c
  have hr := adj.homEquiv_naturality_right c g
  have hcid : adj.homEquiv FU F c = 𝟙 FU := by
    ext W x
    have h := hformula F c W.unop.left W.unop.hom x
    rw [hc] at h
    exact h.trans (extensionToSource_of R F U (op W.unop.left) W.unop.hom x)
  rw [hcid, Category.id_comp, hg, Equiv.apply_symm_apply] at hr
  exact hr.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- On a Noetherian scheme, internal Hom from a coherent module into an injective module
has flasque underlying abelian sheaf. Source: Stacks Project, Cohomology, Tag 01EA,
with the same extension-by-zero argument for Hom
(blueprint: lem-sc-ext-coherent-hom-injective-flasque).

Proof:
1. For an open `V`, sections of internal Hom are maps `F|_V ⟶ I|_V`
   (`def-pur-sheaf-hom`). The extension-by-zero adjunction identifies these with
   maps `j_{V!}(F|_V) ⟶ I` (`lem-weil-pbc-module-extension-by-zero-adjunction`, clause 2).
2. For `U' ⊆ U`, the canonical map `j_{U'!}(F|_{U'}) ⟶ j_{U!}(F|_U)` is the identity
   at stalks in `U'` and has zero source elsewhere (the stalk clause of the same node).
   It is monic by the stalkwise exactness criterion
   (`lem-weil-pbc-module-stalk-exact`, clause 5, applied to the complex starting with zero).
3. Injectivity of `I` (`def-sp-injective-resolutions`) makes precomposition with this
   monomorphism surjective. Under the adjunction bijections, this is restriction of
   Hom sections: on `U'` the canonical map is the identity on the restricted `F`.
4. All restriction maps are therefore surjective, which is flasqueness
   (`def-sc-zariski-flasque`). -/
theorem isFlasque_homObj_of_coherent_injective (X : Scheme.{u})
    [IsNoetherian X]
    (F I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (hF : RingedSpace.IsCoherent X.toRingedSpace F) [Injective I] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj
        (SheafOfModules.homObj (R := X.sheaf) F I)) := by
  classical
  have _ := hF
  constructor
  intro U V i
  refine (AddCommGrpCat.epi_iff_surjective _).mpr fun s ↦ ?_
  obtain ⟨adj, hformula⟩ := Scheme.Modules.module_extensionByZero_hom_formula X V.unop
  let t : (SheafOfModules.overFunctor X.ringCatSheaf V.unop).obj F ⟶
      (SheafOfModules.overFunctor X.ringCatSheaf V.unop).obj I := ⟨s⟩
  obtain ⟨g, hg⟩ := extendsToSource X.ringCatSheaf F I V.unop adj
    (fun G ψ W h x ↦ hformula _ G ψ W h x) t
  refine ⟨(PresheafOfModules.restrictOver X.sheaf.obj U.unop).map g.val, ?_⟩
  change PresheafOfModules.restrictOverMap i.unop
      ((PresheafOfModules.restrictOver X.sheaf.obj U.unop).map g.val) = s
  rw [PresheafOfModules.restrictOverMap_restrictOver_map]
  exact congrArg SheafOfModules.Hom.val hg

end AlgebraicGeometry
