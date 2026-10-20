/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.SecSmoothPurity.CochainCoefficientArrows
import Sheaf.SecSmoothPurity.ModuleTensorGenerators

/-! # Scalar-extension tensor square for module coefficient change

Source: Stacks Project, sites-modules.tex, Tag 03EL, and
sites-cohomology.tex, Tag 07A4.
(blueprint: lem-pur-module-tensor-extension-equation)
-/

@[expose] public section

universe w uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace CategoryTheory.CochainPullback
set_option autoImplicit false
set_option Elab.async false
set_option linter.checkUnivs false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}} {S : Sheaf K CommRingCat.{w}}


open SheafOfModules
attribute [local instance] monoidalCategory symmetricCategory
open scoped TensorProduct ChangeOfRings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] scalarAssociation SheafOfModules.monoidalCategory
attribute [local irreducible] extensionComparison extensionAdjunction
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification

set_option maxHeartbeats 80000 in
-- Keep dependent scalar-extension presentations explicit during elaboration.
private theorem scalarTensor_hom_ext₂
    {A B : Sheaf J CommRingCat.{w}} (c : A ⟶ B)
    (M N : Modules A) (H : Modules B)
    {f g : (changeOfRings c M ⊗ changeOfRings c N) ⟶ H}
    (h : ∀ W m n, f.val.app W (moduleTmul _ _ W
        (extensionTmul c M W 1 m) (extensionTmul c N W 1 n)) =
      g.val.app W (moduleTmul _ _ W
        (extensionTmul c M W 1 m) (extensionTmul c N W 1 n))) : f = g := by
  let RB := (sheafCompose J (forget₂ CommRingCat RingCat)).obj B
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 RB.obj)
  let S := PresheafOfModules.sheafification (𝟙 RB.obj)
  let E := changeOfRingsPresheaf c M
  let F := changeOfRingsPresheaf c N
  let ηE := adj.unit.app E
  let ηF := adj.unit.app F
  let E2 := (S.obj E).val ⊗ (S.obj F).val
  have hη (V : PresheafOfModules.{w} RB.obj) :
      (J.W.inverseImage (PresheafOfModules.toPresheaf RB.obj))
        (adj.unit.app V) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 RB.obj)]
    change IsIso (S.map (adj.unit.app V))
    dsimp only [S, adj]
    infer_instance
  have hηη := (J.W.inverseImage (PresheafOfModules.toPresheaf RB.obj)).tensorHom_mem
    ηE ηF (hη E) (hη F)
  have hi : IsIso (S.map (ηE ⊗ₘ ηF)) := by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 RB.obj)] at hηη
    exact hηη
  let q := S.map (ηE ⊗ₘ ηF) ≫
    (tensorObjIsoSheafification (S.obj E) (S.obj F)).inv
  have : IsIso q := by
    dsimp only [q]
    infer_instance
  apply ((asIso q).symm.homFromEquiv).injective
  apply (adj.homEquiv (E ⊗ F) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro W
  let : CommRing (RB.obj.obj W) := inferInstanceAs (CommRing (B.obj.obj W))
  let a : (E.obj W) ⊗[RB.obj.obj W] (F.obj W) →ₗ[RB.obj.obj W] H.val.obj W :=
    ((adj.unit.app (E ⊗ F) ≫
      (SheafOfModules.forget RB ⋙ PresheafOfModules.restrictScalars (𝟙 RB.obj)).map
        (q ≫ f)).app W).hom
  let b : (E.obj W) ⊗[RB.obj.obj W] (F.obj W) →ₗ[RB.obj.obj W] H.val.obj W :=
    ((adj.unit.app (E ⊗ F) ≫
      (SheafOfModules.forget RB ⋙ PresheafOfModules.restrictScalars (𝟙 RB.obj)).map
        (q ≫ g)).app W).hom
  apply ModuleCat.hom_ext
  change a = b
  have hh : ModuleCat.ofHom (X := E.obj W)
      (Y := ModuleCat.of (RB.obj.obj W) ((F.obj W) →ₗ[RB.obj.obj W] H.val.obj W))
      (TensorProduct.curry a) =
      ModuleCat.ofHom (X := E.obj W)
        (Y := ModuleCat.of (RB.obj.obj W) ((F.obj W) →ₗ[RB.obj.obj W] H.val.obj W))
        (TensorProduct.curry b) := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change TensorProduct.curry a _ = TensorProduct.curry b _
    have hm : ModuleCat.ofHom (X := F.obj W) (Y := ModuleCat.of (RB.obj.obj W)
        (H.val.obj W)) (TensorProduct.curry a
          ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) =
        ModuleCat.ofHom (X := F.obj W) (Y := ModuleCat.of (RB.obj.obj W)
          (H.val.obj W)) (TensorProduct.curry b
            ((1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) := by
      apply ModuleCat.ExtendScalars.hom_ext
      intro n
      change TensorProduct.curry a _ _ = TensorProduct.curry b _ _
      let m' := (1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m
      let n' := (1 : B.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n
      have he := congrArg (fun k ↦ k.app W (m' ⊗ₜ[B.obj.obj W] n'))
        (adj.unit.naturality (ηE ⊗ₘ ηF))
      change (adj.unit.app E2).app W (ηE.app W m' ⊗ₜ[B.obj.obj W] ηF.app W n') =
        (S.map (ηE ⊗ₘ ηF)).val.app W
          ((adj.unit.app (E ⊗ F)).app W (m' ⊗ₜ[B.obj.obj W] n')) at he
      change f.val.app W ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W
          ((S.map (ηE ⊗ₘ ηF)).val.app W
            ((adj.unit.app (E ⊗ F)).app W (m' ⊗ₜ[B.obj.obj W] n')))) =
        g.val.app W ((tensorObjIsoSheafification (S.obj E) (S.obj F)).inv.val.app W
          ((S.map (ηE ⊗ₘ ηF)).val.app W
            ((adj.unit.app (E ⊗ F)).app W (m' ⊗ₜ[B.obj.obj W] n'))))
      rw [← he]
      rw [← moduleTmul]
      dsimp only [S, E, F, ηE, ηF, adj, RB, m', n']
      simpa only [extensionTmul, extensionFunctor, SheafOfModules.changeOfRings] using h W m n
    exact congrArg ModuleCat.Hom.hom hm
  exact TensorProduct.curry_injective (congrArg ModuleCat.Hom.hom hh)

private theorem productElements {A : Type uE} [Category.{vE} A] [HasBinaryProducts A]
    (F : A ⥤ Type w) (X Y : A) [PreservesLimit (pair X Y) F]
    (x : F.obj X) (y : F.obj Y) :
    ∃ t : F.obj (X ⨯ Y), F.map prod.fst t = x ∧ F.map prod.snd t = y := by
  let e := asIso (prodComparison F X Y) ≪≫ Types.binaryProductIso (F.obj X) (F.obj Y)
  have hf : e.hom ≫ ↾_root_.Prod.fst = F.map prod.fst := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, Types.binaryProductIso_hom_comp_fst, prodComparison_fst]
  have hs : e.hom ≫ ↾_root_.Prod.snd = F.map prod.snd := by
    dsimp only [e, Iso.trans_hom, asIso_hom]
    rw [Category.assoc, Types.binaryProductIso_hom_comp_snd, prodComparison_snd]
  refine ⟨e.inv (x, y), ?_, ?_⟩
  · rw [← hf]
    change (e.hom (e.inv (x, y))).1 = x
    rw [Iso.inv_hom_id_apply]
  · rw [← hs]
    change (e.hom (e.inv (x, y))).2 = y
    rw [Iso.inv_hom_id_apply]

set_option maxHeartbeats 80000 in
-- Keep dependent scalar-extension presentations explicit during elaboration.
private theorem pair_hom_ext (f : RingedPullback R S) (k : Comparison f)
    (M N : Modules R) (H : Modules S)
    {a b : f.L.obj M ⊗ f.L.obj N ⟶ H}
    (h : ∀ (W : Dᵒᵖ) (m : (f.I.modules.obj M).val.obj W)
      (n : (f.I.modules.obj N).val.obj W),
      a.val.app W (moduleTmul _ _ W ((k.q M).hom.app W m) ((k.q N).hom.app W n)) =
      b.val.app W (moduleTmul _ _ W ((k.q M).hom.app W m) ((k.q N).hom.app W n))) :
    a = b := by
  let eM := eqToIso (f.hobj M).symm
  let eN := eqToIso (f.hobj N).symm
  apply (cancel_epi (eM.hom ⊗ₘ eN.hom)).mp
  apply scalarTensor_hom_ext₂ f.coefficient (f.I.modules.obj M) (f.I.modules.obj N) H
  intro W m n
  change a.val.app W ((eM.hom ⊗ₘ eN.hom).val.app W _) =
    b.val.app W ((eM.hom ⊗ₘ eN.hom).val.app W _)
  rw [moduleTmul_map]
  have hM : eM.hom.val.app W
      (extensionTmul f.coefficient (f.I.modules.obj M) W 1 m) =
        (k.q M).hom.app W m := (k.q_one M W m).symm
  have hN : eN.hom.val.app W
      (extensionTmul f.coefficient (f.I.modules.obj N) W 1 n) =
        (k.q N).hom.app W n := (k.q_one N W n).symm
  rw [hM, hN]
  exact h W m n

private theorem generator_pair_elements (f : RingedPullback R S) (k : Comparison f)
    (M N : Modules R) (W : Dᵒᵖ) (m : (f.I.modules.obj M).val.obj W)
    (n : (f.I.modules.obj N).val.obj W) :
    ∃ (Z : Sheaf J (Type w)) (x : Z ⟶ (underlying R).obj M)
      (y : Z ⟶ (underlying R).obj N) (t : (f.uInv.obj Z).obj.obj W),
      (generator f k x).hom.app W t = (k.q M).hom.app W m ∧
      (generator f k y).hom.app W t = (k.q N).hom.app W n := by
  let := f.finiteLimits
  let F := f.uInv ⋙ sheafToPresheaf K (Type w) ⋙ (evaluation Dᵒᵖ (Type w)).obj W
  let X := (underlying R).obj M
  let Y := (underlying R).obj N
  let m' := (f.I.moduleUnderlying.hom.app M).hom.app W m
  let n' := (f.I.moduleUnderlying.hom.app N).hom.app W n
  obtain ⟨t, ht₁, ht₂⟩ := productElements F X Y m' n'
  refine ⟨X ⨯ Y, prod.fst, prod.snd, t, ?_, ?_⟩
  · change (k.q M).hom.app W ((f.I.moduleUnderlying.inv.app M).hom.app W
      ((F.map prod.fst) t)) = _
    rw [ht₁]
    have hi := congrArg (fun v ↦ v.hom.app W m) (f.I.moduleUnderlying.hom_inv_id_app M)
    exact congrArg ((k.q M).hom.app W) hi
  · change (k.q N).hom.app W ((f.I.moduleUnderlying.inv.app N).hom.app W
      ((F.map prod.snd) t)) = _
    rw [ht₂]
    have hi := congrArg (fun v ↦ v.hom.app W n) (f.I.moduleUnderlying.hom_inv_id_app N)
    exact congrArg ((k.q N).hom.app W) hi

private theorem extension_generator {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {M : Modules A} {Z : Sheaf J (Type w)} (x : Z ⟶ (underlying A).obj M) :
    generator (extensionPullback a) (extensionComparison a) x = x ≫ insertion a M := by
  apply Sheaf.hom_ext
  ext U t
  have hq := (extensionComparison a).q_one M U (x.hom.app U t)
  have hu := (Classical.choose_spec (extensionAdjunction_existsUnique a)).1
    M U (x.hom.app U t)
  change ((extensionComparison a).q M).hom.app U (x.hom.app U t) =
    ((extensionAdjunction a).unit.app M).val.app U (x.hom.app U t)
  have hq' : ((extensionComparison a).q M).hom.app U (x.hom.app U t) =
      extensionTmul a M U 1 (x.hom.app U t) := by
    simpa only [extensionPullback, identityAlgebraicInverseImage, Functor.id_obj,
      eqToHom_refl, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply, extensionTmul, extensionFunctor] using hq
  exact hq'.trans (by simpa only [extensionAdjunction] using hu.symm)

private theorem insertion_tensorPair {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {M N : Modules A} {Z : Sheaf J (Type w)}
    (x : Z ⟶ (underlying A).obj M) (y : Z ⟶ (underlying A).obj N) :
    moduleTensorPair x y ≫ insertion a (M ⊗ N) ≫
        (underlying B).map ((extensionComparison a).mu M N).hom =
      moduleTensorPair (x ≫ insertion a M) (y ≫ insertion a N) := by
  have h := generator_tensorPair (extensionPullback a) (extensionComparison a) x y
  rw [extension_generator, extension_generator, extension_generator] at h
  dsimp only [extensionPullback, Functor.id_obj] at h
  simpa only [Category.assoc] using h

private theorem tensorPair_map {A : Sheaf J CommRingCat.{w}}
    {M N M' N' : Modules A} {Z : Sheaf J (Type w)}
    (x : Z ⟶ (underlying A).obj M) (y : Z ⟶ (underlying A).obj N)
    (a : M ⟶ M') (b : N ⟶ N') :
    moduleTensorPair x y ≫ (underlying A).map (a ⊗ₘ b) =
      moduleTensorPair (x ≫ (underlying A).map a) (y ≫ (underlying A).map b) := by
  apply Sheaf.hom_ext
  ext U t
  exact moduleTmul_map a b U _ _

attribute [local irreducible] moduleTensorPair generator moduleTmul extensionTmul
attribute [local irreducible] extensionFunctor
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option maxHeartbeats 80000 in
-- Normalize the dependent coefficient sources before rewriting the generator equations.
private theorem coefficient_generators (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d))
    (M N : Modules R) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying R).obj M) (y : Z ⟶ (underlying R).obj N) :
    generator (changed f d) k' (moduleTensorPair x y ≫ insertion d.sourceMap (M ⊗ N)) ≫
        (underlying d.S').map
          ((changed f d).L.map ((extensionComparison d.sourceMap).mu M N).hom ≫
            (k'.mu ((extensionFunctor d.sourceMap).obj M)
              ((extensionFunctor d.sourceMap).obj N)).hom ≫
            ((scalarAssociation f k d k').hom.app M ⊗ₘ
              (scalarAssociation f k d k').hom.app N)) =
      moduleTensorPair (generator f k x ≫ insertion d.targetMap (f.L.obj M))
        (generator f k y ≫ insertion d.targetMap (f.L.obj N)) := by
  have hb : IsScalarAssociation f k d k' (scalarAssociation f k d k') := by
    unfold scalarAssociation
    exact (Classical.choose_spec (scalarAssociation_existsUnique f k d k')).1
  let x' := x ≫ insertion d.sourceMap M
  let y' := y ≫ insertion d.sourceMap N
  let a : (extensionFunctor d.sourceMap).obj (M ⊗ N) ⟶
      (extensionFunctor d.sourceMap).obj M ⊗ (extensionFunctor d.sourceMap).obj N :=
    ((extensionComparison d.sourceMap).mu M N).hom
  have hi : (moduleTensorPair x y ≫ insertion d.sourceMap (M ⊗ N)) ≫
      (underlying d.R').map a = moduleTensorPair x' y' := by
    exact insertion_tensorPair d.sourceMap x y
  have hn := generator_naturality (changed f d) k' a
    (moduleTensorPair x y ≫ insertion d.sourceMap (M ⊗ N))
  have ht := generator_tensorPair (changed f d) k' x' y'
  have hm := tensorPair_map (generator (changed f d) k' x')
    (generator (changed f d) k' y')
    ((scalarAssociation f k d k').hom.app M)
    ((scalarAssociation f k d k').hom.app N)
  change generator (changed f d) k'
      (moduleTensorPair x y ≫ insertion d.sourceMap (M ⊗ N)) ≫
      (underlying d.S').map ((changed f d).L.map a ≫
        (k'.mu ((extensionFunctor d.sourceMap).obj M)
          ((extensionFunctor d.sourceMap).obj N)).hom ≫
        ((scalarAssociation f k d k').hom.app M ⊗ₘ
          (scalarAssociation f k d k').hom.app N)) = _
  simp only [Functor.map_comp, ← Category.assoc]
  erw [← hn, hi, ht, hm]
  erw [hb M Z x, hb N Z y]
  rfl

private theorem insertion_naturality {A B : Sheaf J CommRingCat.{w}} (c : A ⟶ B)
    {M N : Modules A} (a : M ⟶ N) :
    (underlying A).map a ≫ insertion c N =
      insertion c M ≫ (underlying B).map ((extensionFunctor c).map a) := by
  apply Sheaf.hom_ext
  ext U x
  exact congrArg (fun z ↦ z.val.app U x) ((extensionAdjunction c).unit.naturality a)

set_option maxHeartbeats 80000 in
-- Control conversions through scalar-extension and sheafification presentations.
/-- The scalar-association tensor square for ordinary coefficient extension.
Source: Stacks 03EL, scalar association in tensor pullback.
(blueprint: lem-pur-module-tensor-extension-equation).

Proof: cancel inverse scalar association, take adjuncts under target scalar
extension/restriction, and cancel the inverse original tensor comparison. To
prove equality on the resulting pair tensor, sheafify the tensor of the two
presheafification units and cancel its invertible sheafification. The
sheafification adjunction and sectionwise currying reduce to scalar-extension
unit insertions in both factors. Transport these insertions by hobj and q_one.
Finite-product preservation represents the pair of inverse-image sections by
one generalized element. On that element generator naturality and the pure
comparison equation identify insertion followed by tensor comparison with the
pairing of insertions. IsScalarAssociation identifies both coefficient routes.
Its normalization also cancels inverse scalar association in the adjunct,
leaving exactly this equality. No points or extra generation assumption are
used; zero rings and modules and noninvertible coefficient maps are allowed. -/
theorem cochainModuleTensorExtensionCoefficient (f : RingedPullback R S) (k : Comparison f)
    (d : CoefficientSquare f) (k' : Comparison (changed f d)) :
    ∀ M N : Modules R,
      (changed f d).L.map ((extensionComparison d.sourceMap).mu M N).hom ≫
          (k'.mu ((extensionFunctor d.sourceMap).obj M)
            ((extensionFunctor d.sourceMap).obj N)).hom ≫
          ((scalarAssociation f k d k').hom.app M ⊗ₘ
            (scalarAssociation f k d k').hom.app N) =
        (scalarAssociation f k d k').hom.app (M ⊗ N) ≫
          (extensionFunctor d.targetMap).map (k.mu M N).hom ≫
          ((extensionComparison d.targetMap).mu (f.L.obj M) (f.L.obj N)).hom := by
  intro M N
  let b := scalarAssociation f k d k'
  let eR : (extensionFunctor d.sourceMap).obj (M ⊗ N) ⟶
      (extensionFunctor d.sourceMap).obj M ⊗ (extensionFunctor d.sourceMap).obj N :=
    ((extensionComparison d.sourceMap).mu M N).hom
  let eS : (extensionFunctor d.targetMap).obj (f.L.obj M ⊗ f.L.obj N) ⟶
      (extensionFunctor d.targetMap).obj (f.L.obj M) ⊗
        (extensionFunctor d.targetMap).obj (f.L.obj N) :=
    ((extensionComparison d.targetMap).mu (f.L.obj M) (f.L.obj N)).hom
  let lhs : (changed f d).L.obj ((extensionFunctor d.sourceMap).obj (M ⊗ N)) ⟶
      (extensionFunctor d.targetMap).obj (f.L.obj M) ⊗
        (extensionFunctor d.targetMap).obj (f.L.obj N) :=
    (changed f d).L.map eR ≫
      (k'.mu ((extensionFunctor d.sourceMap).obj M)
        ((extensionFunctor d.sourceMap).obj N)).hom ≫ (b.hom.app M ⊗ₘ b.hom.app N)
  let rhs := b.hom.app (M ⊗ N) ≫
    (extensionFunctor d.targetMap).map (k.mu M N).hom ≫ eS
  change lhs = rhs
  have hb : IsScalarAssociation f k d k' b := by
    dsimp only [b]
    unfold scalarAssociation
    exact (Classical.choose_spec (scalarAssociation_existsUnique f k d k')).1
  have hg (Z : Sheaf J (Type w))
      (x : Z ⟶ (underlying R).obj M) (y : Z ⟶ (underlying R).obj N) :
      generator (changed f d) k'
          (moduleTensorPair x y ≫ insertion d.sourceMap (M ⊗ N)) ≫
          (underlying d.S').map lhs =
        generator (changed f d) k'
          (moduleTensorPair x y ≫ insertion d.sourceMap (M ⊗ N)) ≫
          (underlying d.S').map rhs := by
    have h₀ := coefficient_generators f k d k' M N Z x y
    have h₁ := congrArg (fun z ↦ z ≫
      (underlying d.S').map ((extensionFunctor d.targetMap).map (k.mu M N).hom) ≫
      (underlying d.S').map eS) (hb (M ⊗ N) Z (moduleTensorPair x y))
    have h₂ := congrArg (fun z ↦ generator f k (moduleTensorPair x y) ≫ z ≫
      (underlying d.S').map eS) (insertion_naturality d.targetMap (k.mu M N).hom)
    have h₃ := congrArg (fun z ↦ z ≫ insertion d.targetMap (f.L.obj M ⊗ f.L.obj N) ≫
      (underlying d.S').map eS) (generator_tensorPair f k x y)
    have h₄ : moduleTensorPair (generator f k x) (generator f k y) ≫
        insertion d.targetMap (f.L.obj M ⊗ f.L.obj N) ≫ (underlying d.S').map eS =
      moduleTensorPair (generator f k x ≫ insertion d.targetMap (f.L.obj M))
        (generator f k y ≫ insertion d.targetMap (f.L.obj N)) := by
      exact insertion_tensorPair d.targetMap (generator f k x) (generator f k y)
    have h₁' : generator (changed f d) k'
        (moduleTensorPair x y ≫ insertion d.sourceMap (M ⊗ N)) ≫
        (underlying d.S').map rhs =
      generator f k (moduleTensorPair x y) ≫
        insertion d.targetMap (f.L.obj (M ⊗ N)) ≫
        (underlying d.S').map ((extensionFunctor d.targetMap).map (k.mu M N).hom) ≫
        (underlying d.S').map eS := by
      have h := h₁.trans (Category.assoc (generator f k (moduleTensorPair x y))
        (insertion d.targetMap (f.L.obj (M ⊗ N)))
        ((underlying d.S').map ((extensionFunctor d.targetMap).map (k.mu M N).hom) ≫
          (underlying d.S').map eS))
      simpa only [rhs, Functor.map_comp, Category.assoc] using h
    have h₂' : generator f k (moduleTensorPair x y) ≫
        (underlying S).map (k.mu M N).hom ≫
        insertion d.targetMap (f.L.obj M ⊗ f.L.obj N) ≫ (underlying d.S').map eS =
      generator f k (moduleTensorPair x y) ≫
        insertion d.targetMap (f.L.obj (M ⊗ N)) ≫
        (underlying d.S').map ((extensionFunctor d.targetMap).map (k.mu M N).hom) ≫
        (underlying d.S').map eS := by
      simpa only [Category.assoc] using h₂
    have h₃' : generator f k (moduleTensorPair x y) ≫
        (underlying S).map (k.mu M N).hom ≫
        insertion d.targetMap (f.L.obj M ⊗ f.L.obj N) ≫ (underlying d.S').map eS =
      moduleTensorPair (generator f k x) (generator f k y) ≫
        insertion d.targetMap (f.L.obj M ⊗ f.L.obj N) ≫ (underlying d.S').map eS := by
      simpa only [Category.assoc] using h₃
    exact h₀.trans (h₄.symm.trans (h₃'.symm.trans (h₂'.trans h₁'.symm)))
  apply (cancel_epi (b.inv.app (M ⊗ N))).mp
  apply ((extensionAdjunction d.targetMap).homEquiv _ _).injective
  apply (cancel_epi (k.mu M N).inv).mp
  apply pair_hom_ext f k M N
  intro W m n
  obtain ⟨Z, x, y, t, hx, hy⟩ := generator_pair_elements f k M N W m n
  have hs : moduleTensorPair (generator f k x) (generator f k y) ≫
      (underlying S).map ((k.mu M N).inv ≫
        (extensionAdjunction d.targetMap).homEquiv _ _ (b.inv.app (M ⊗ N) ≫ lhs)) =
      moduleTensorPair (generator f k x) (generator f k y) ≫
      (underlying S).map ((k.mu M N).inv ≫
        (extensionAdjunction d.targetMap).homEquiv _ _ (b.inv.app (M ⊗ N) ≫ rhs)) := by
    erw [← generator_tensorPair f k x y]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_assoc]
    simp only [Adjunction.homEquiv_unit, Functor.map_comp]
    change generator f k (moduleTensorPair x y) ≫ insertion d.targetMap (f.L.obj (M ⊗ N)) ≫
        (underlying d.S').map (b.inv.app (M ⊗ N)) ≫ (underlying d.S').map lhs =
      generator f k (moduleTensorPair x y) ≫ insertion d.targetMap (f.L.obj (M ⊗ N)) ≫
        (underlying d.S').map (b.inv.app (M ⊗ N)) ≫ (underlying d.S').map rhs
    have hi' : generator (changed f d) k'
        (moduleTensorPair x y ≫ insertion d.sourceMap (M ⊗ N)) =
      (generator f k (moduleTensorPair x y) ≫
        insertion d.targetMap (f.L.obj (M ⊗ N))) ≫
        (underlying d.S').map (b.inv.app (M ⊗ N)) := by
      exact (((underlying d.S').mapIso (b.app (M ⊗ N))).eq_comp_inv).2
        (hb (M ⊗ N) Z (moduleTensorPair x y))
    have h := hg Z x y
    erw [hi'] at h
    dsimp only [changed] at h ⊢
    simpa only [Category.assoc] using h
  have hv := congrArg (fun z ↦ z.hom.app W t) hs
  unfold moduleTensorPair at hv
  change (((k.mu M N).inv ≫
      (extensionAdjunction d.targetMap).homEquiv _ _ (b.inv.app (M ⊗ N) ≫ lhs)).val.app W)
      (moduleTmul _ _ W ((generator f k x).hom.app W t)
        ((generator f k y).hom.app W t)) =
    (((k.mu M N).inv ≫
      (extensionAdjunction d.targetMap).homEquiv _ _ (b.inv.app (M ⊗ N) ≫ rhs)).val.app W)
      (moduleTmul _ _ W ((generator f k x).hom.app W t)
        ((generator f k y).hom.app W t)) at hv
  simpa only [hx, hy] using hv

end CategoryTheory.CochainPullback
