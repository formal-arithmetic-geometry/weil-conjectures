/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Specified evaluation and inverse tensor pair for a sheaf line

Source: Stacks Project, Modules on Sites, Tags 0B8Q and 0B8N.
(blueprint: lem-pur-sheaf-line-evaluation-inverse-pair)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe uC vC r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace SheafOfModules.LineEvaluation

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{max uC vC r} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{max uC vC r} RingCat.{max uC vC r})]
  (R : Sheaf J CommRingCat.{max uC vC r})

/-- The module category already defined on the given ringed site.
Source: Stacks 03DD (blueprint: lem-pur-sheaf-line-evaluation-inverse-pair). -/
abbrev Modules := ringedSiteModules.{max uC vC r}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)

/-- The existing internal Hom dual to the coefficient unit.
Source: Stacks 0B8Q (blueprint: lem-pur-sheaf-line-evaluation-inverse-pair). -/
abbrev dual (P : Modules.{uC, vC, r} R) : Modules.{uC, vC, r} R :=
  homObj (R := R) P (𝟙_ (Modules.{uC, vC, r} R))

/-- The image of a pure tensor under the sheafification unit and tensor comparison.
Source: Stacks 03EK (blueprint: lem-pur-sheaf-line-evaluation-inverse-pair). -/
def pureTensor (M N : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) : (M ⊗ N).val.obj U :=
  (tensorObjIsoSheafification M N).inv.val.app U
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).unit.app
        (M.val ⊗ N.val)).app U (x ⊗ₜ[R.obj.obj U] y))

/-- Reassociation, evaluation of the last two factors, and the right unitor.
Source: Stacks 0B8N (blueprint: lem-pur-sheaf-line-evaluation-inverse-pair). -/
def cancellation (P Q : Modules.{uC, vC, r} R) (e : P ⊗ Q ≅ 𝟙_ (Modules.{uC, vC, r} R)) :
    tensorRight P ⋙ tensorRight Q ≅ 𝟭 (Modules.{uC, vC, r} R) :=
  (tensorRightTensor P Q).symm ≪≫ (tensoringRight (Modules.{uC, vC, r} R)).mapIso e ≪≫
    rightUnitorNatIso (Modules.{uC, vC, r} R)

/-- Global ring sections, acting componentwise on module morphisms.
Source: Stacks 04TT (blueprint: lem-pur-sheaf-line-evaluation-inverse-pair). -/
abbrev scalars := RingCat.sectionsSubring (R.obj ⋙ forget₂ CommRingCat RingCat)

/-- The existing sectionwise scalar action, with no chosen linear structure.
Source: Stacks 04TT (blueprint: lem-pur-sheaf-line-evaluation-inverse-pair). -/
instance coefficientLinear : Linear (scalars.{uC, vC, r} R) (Modules.{uC, vC, r} R) :=
  homLinear R.obj ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).property

set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance 2000] cochainModulesMonoidal

private abbrev ringSheaf :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

private abbrev unitDual (P : Modules.{uC, vC, r} R) : Modules.{uC, vC, r} R :=
  homObj (R := R) P (unit (ringSheaf.{uC, vC, r} R))

private noncomputable def adj :
    PresheafOfModules.sheafification (𝟙 (ringSheaf.{uC, vC, r} R).obj) ⊣
      forget (ringSheaf.{uC, vC, r} R) :=
  PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf.{uC, vC, r} R).obj)

@[instance_reducible]
private noncomputable def forgetLax : (forget (ringSheaf.{uC, vC, r} R)).LaxMonoidal :=
  (adj.{uC, vC, r} R).rightAdjointLaxMonoidal

private theorem forget_mu (M N : Modules.{uC, vC, r} R) :
    let := forgetLax.{uC, vC, r} R
    Functor.LaxMonoidal.μ (forget (ringSheaf.{uC, vC, r} R)) M N =
      (adj.{uC, vC, r} R).unit.app (M.val ⊗ N.val) ≫ (tensorObjIsoSheafification M N).inv.val := by
  let := forgetLax.{uC, vC, r} R
  change (adj.{uC, vC, r} R).unit.app (M.val ⊗ N.val) ≫
    (forget (ringSheaf.{uC, vC, r} R)).map
      (Functor.OplaxMonoidal.δ
        (PresheafOfModules.sheafification (𝟙 (ringSheaf.{uC, vC, r} R).obj)) M.val N.val ≫
        ((adj.{uC, vC, r} R).counit.app M ⊗ₘ (adj.{uC, vC, r} R).counit.app N)) = _
  simp only [tensorObjIsoSheafification, Iso.trans_inv, Iso.symm_inv,
    Functor.Monoidal.μIso_inv, tensorIso_hom, Iso.app_hom, asIso_hom]
  dsimp only [forget, Functor.map_comp, adj, ringSheaf]

attribute [local irreducible] tensorObjIsoSheafification

private noncomputable def pureBilin (M N : Modules.{uC, vC, r} R) (U : Cᵒᵖ) :
    M.val.obj U →ₗ[R.obj.obj U] N.val.obj U →ₗ[R.obj.obj U] (M ⊗ N).val.obj U :=
  TensorProduct.curry (((adj.{uC, vC, r} R).unit.app (M.val ⊗ N.val) ≫
    (tensorObjIsoSheafification M N).inv.val).app U).hom

private theorem forget_epsilon :
    letI := forgetLax.{uC, vC, r} R
    Functor.LaxMonoidal.ε (forget (ringSheaf.{uC, vC, r} R)) = 𝟙 _ := by
  let := forgetLax.{uC, vC, r} R
  change (adj.{uC, vC, r} R).unit.app _ ≫
    (forget (ringSheaf.{uC, vC, r} R)).map
      ((adj.{uC, vC, r} R).counit.app (unit (ringSheaf.{uC, vC, r} R))) = 𝟙 _
  exact (adj.{uC, vC, r} R).right_triangle_components (unit (ringSheaf.{uC, vC, r} R))

attribute [local irreducible] PresheafOfModules.sheafificationAdjunction

private theorem pure_smul_left (M N : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (a : R.obj.obj U) (x : M.val.obj U) (y : N.val.obj U) :
    pureTensor.{uC, vC, r} R M N U (a • x) y = a • pureTensor.{uC, vC, r} R M N U x y := by
  exact (pureBilin.{uC, vC, r} R M N U).map_smul₂ a x y

private theorem pure_smul_right (M N : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (a : R.obj.obj U) (x : M.val.obj U) (y : N.val.obj U) :
    pureTensor.{uC, vC, r} R M N U x (a • y) = a • pureTensor.{uC, vC, r} R M N U x y := by
  exact (pureBilin.{uC, vC, r} R M N U x).map_smul a y

private theorem pure_hom_ext (M N H : Modules.{uC, vC, r} R)
    {f g : M ⊗ N ⟶ H}
    (h : ∀ U x y, f.val.app U (pureTensor.{uC, vC, r} R M N U x y) =
      g.val.app U (pureTensor.{uC, vC, r} R M N U x y)) : f = g := by
  apply (cancel_epi (tensorObjIsoSheafification M N).inv).mp
  apply ((adj.{uC, vC, r} R).homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

private theorem pure_map {M M' N N' : Modules.{uC, vC, r} R}
    (f : M ⟶ M') (g : N ⟶ N') (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (f ⊗ₘ g).val.app U (pureTensor.{uC, vC, r} R M N U x y) =
      pureTensor.{uC, vC, r} R M' N' U (f.val.app U x) (g.val.app U y) := by
  exact CategoryTheory.CochainPullback.moduleTmul_map f g U x y

private theorem pure_assoc (M N H : Modules.{uC, vC, r} R)
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) (z : H.val.obj U) :
    (α_ M N H).hom.val.app U
      (pureTensor.{uC, vC, r} R (M ⊗ N) H U (pureTensor.{uC, vC, r} R M N U x y) z) =
        pureTensor.{uC, vC, r} R M (N ⊗ H) U x (pureTensor.{uC, vC, r} R N H U y z) := by
  exact CategoryTheory.CochainPullback.moduleTmul_associator M N H U x y z

private theorem pure_right_unitor (M : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (x : M.val.obj U) (a : R.obj.obj U) :
    (ρ_ M).hom.val.app U (pureTensor.{uC, vC, r} R M (unit (ringSheaf.{uC, vC, r} R)) U x a) =
      a • x := by
  let := forgetLax.{uC, vC, r} R
  have h := Functor.LaxMonoidal.right_unitality (forget (ringSheaf.{uC, vC, r} R)) M
  rw [forget_epsilon.{uC, vC, r}, whiskerLeft_id, Category.id_comp, forget_mu.{uC, vC, r}] at h
  exact (congrArg (fun k ↦ k.app U (x ⊗ₜ[R.obj.obj U] a)) h).symm

private theorem pure_braiding (M N : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) :
    (β_ M N).hom.val.app U (pureTensor.{uC, vC, r} R M N U x y) =
      pureTensor.{uC, vC, r} R N M U y x := by
  exact CategoryTheory.CochainPullback.moduleTmul_braiding M N U x y

private noncomputable def evalLinear (P : Modules.{uC, vC, r} R) (U : Cᵒᵖ) :
    (unitDual.{uC, vC, r} R P).val.obj U →ₗ[R.obj.obj U]
      P.val.obj U →ₗ[R.obj.obj U] R.obj.obj U where
  toFun phi := (phi.app (op (Over.mk (𝟙 U.unop)))).hom
  map_add' _ _ := rfl
  map_smul' a phi := by
    ext x
    change R.obj.map (𝟙 U.unop).op a •
      (phi.app (op (Over.mk (𝟙 U.unop))) x) = a • _
    rw [op_id, R.obj.map_id]
    rfl

omit [EssentiallySmall.{max uC vC r} C] in
private theorem eval_restrict (P : Modules.{uC, vC, r} R) {U V : Cᵒᵖ}
    (f : U ⟶ V) (phi : (unitDual.{uC, vC, r} R P).val.obj U) (x : P.val.obj U) :
    evalLinear.{uC, vC, r} R P V ((unitDual.{uC, vC, r} R P).val.map f phi) (P.val.map f x) =
      R.obj.map f (evalLinear.{uC, vC, r} R P U phi x) := by
  change phi.app (op (Over.mk (𝟙 V.unop ≫ f.unop))) (P.val.map f x) = _
  refine (PresheafOfModules.restrictOver_hom_app_congr phi (Category.id_comp _) _).trans ?_
  exact PresheafOfModules.naturality_apply phi
    (Over.homMk f.unop : Over.mk f.unop ⟶ Over.mk (𝟙 U.unop)).op x

private noncomputable def evalPresheaf (P : Modules.{uC, vC, r} R) :
    P.val ⊗ (unitDual.{uC, vC, r} R P).val ⟶ (unit (ringSheaf.{uC, vC, r} R)).val where
  app U := ModuleCat.ofHom (X := (P.val ⊗ (unitDual.{uC, vC, r} R P).val).obj U)
    (Y := (unit (ringSheaf.{uC, vC, r} R)).val.obj U)
    (TensorProduct.lift (evalLinear.{uC, vC, r} R P U).flip)
  naturality {U V} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x phi
    exact eval_restrict.{uC, vC, r} R P f phi x

private noncomputable def evaluation (P : Modules.{uC, vC, r} R) :
    P ⊗ unitDual.{uC, vC, r} R P ⟶ unit (ringSheaf.{uC, vC, r} R) :=
  (tensorObjIsoSheafification P (unitDual.{uC, vC, r} R P)).hom ≫
    ((adj.{uC, vC, r} R).homEquiv
    (P.val ⊗ (unitDual.{uC, vC, r} R P).val) (unit (ringSheaf.{uC, vC, r} R))).symm
      (evalPresheaf.{uC, vC, r} R P)

private theorem evaluation_pure (P : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (x : P.val.obj U) (phi : (unitDual.{uC, vC, r} R P).val.obj U) :
    (evaluation.{uC, vC, r} R P).val.app U
      (pureTensor.{uC, vC, r} R P (unitDual.{uC, vC, r} R P) U x phi) =
        phi.app (op (Over.mk (𝟙 U.unop))) x := by
  let A := P.val ⊗ (unitDual.{uC, vC, r} R P).val
  let H := unit (ringSheaf.{uC, vC, r} R)
  let k := ((adj.{uC, vC, r} R).homEquiv A H).symm (evalPresheaf.{uC, vC, r} R P)
  let t := ((adj.{uC, vC, r} R).unit.app A).app U (x ⊗ₜ[R.obj.obj U] phi)
  let e := tensorObjIsoSheafification P (unitDual.{uC, vC, r} R P)
  have h := ((adj.{uC, vC, r} R).homEquiv A H).apply_symm_apply
    (evalPresheaf.{uC, vC, r} R P)
  rw [Adjunction.homEquiv_unit] at h
  have hh := congrArg (fun m ↦ m.app U (x ⊗ₜ[R.obj.obj U] phi)) h
  have hi := congrArg (fun m ↦ m.val.app U t) e.inv_hom_id
  change e.hom.val.app U (e.inv.val.app U t) = t at hi
  change k.val.app U (e.hom.val.app U (e.inv.val.app U t)) = _
  rw [hi]
  exact hh

attribute [local irreducible] evaluation pureTensor

omit [EssentiallySmall.{max uC vC r} C] in
private theorem basis_eval_bijective (P : Modules.{uC, vC, r} R) {W : C}
    (p : P.val.obj (op W)) (phi : (unitDual.{uC, vC, r} R P).val.obj (op W))
    (hphi : phi.app (op (Over.mk (𝟙 W))) p = (1 : R.obj.obj (op W)))
    (hgen : ∀ (V : Over W) (x : P.val.obj (op V.left)),
      ∃ a : R.obj.obj (op V.left), x = a • (show P.val.obj (op V.left) from P.val.map V.hom.op p)) :
    Function.Bijective (fun q : (unitDual.{uC, vC, r} R P).val.obj (op W) ↦
      q.app (op (Over.mk (𝟙 W))) p) := by
  change Function.Bijective (fun q ↦ evalLinear.{uC, vC, r} R P (op W) q p)
  refine ⟨?_, fun a ↦ ⟨a • phi, ?_⟩⟩
  · intro q q' hq
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨a, rfl⟩ := hgen V.unop x
    have h0 : q.app V (P.val.map V.unop.hom.op p) =
        q'.app V (P.val.map V.unop.hom.op p) := by
      have hqV := PresheafOfModules.naturality_apply q
        (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 W)).op p
      have hqV' := PresheafOfModules.naturality_apply q'
        (Over.homMk V.unop.hom : V.unop ⟶ Over.mk (𝟙 W)).op p
      exact hqV.trans ((congrArg ((unit (ringSheaf.{uC, vC, r} R)).val.map
        V.unop.hom.op) hq).trans hqV'.symm)
    change q.app V (a • _) = q'.app V (a • _)
    rw [map_smul, map_smul, h0]
  · change evalLinear.{uC, vC, r} R P (op W) (a • phi) p = a
    erw [map_smul, LinearMap.smul_apply]
    change a • (phi.app (op (Over.mk (𝟙 W))) p) = a
    rw [hphi]
    exact mul_one a

omit [EssentiallySmall.{max uC vC r} C] in
private theorem eval_bijective (P : Modules.{uC, vC, r} R) {W : C}
    (p : P.val.obj (op W)) (phi : (unitDual.{uC, vC, r} R P).val.obj (op W))
    (hphi : phi.app (op (Over.mk (𝟙 W))) p = (1 : R.obj.obj (op W)))
    (hgen : ∀ (V : Over W) (x : P.val.obj (op V.left)),
      ∃ a : R.obj.obj (op V.left), x = a • (show P.val.obj (op V.left) from P.val.map V.hom.op p)) :
    Function.Bijective ((evalPresheaf.{uC, vC, r} R P).app (op W)) := by
  refine TensorProduct.lift_bijective_of_forall_eq_smul
    (evalLinear.{uC, vC, r} R P (op W)).flip p (fun x ↦ ?_)
    (basis_eval_bijective.{uC, vC, r} R P p phi hphi hgen)
  obtain ⟨a, ha⟩ := hgen (Over.mk (𝟙 W)) x
  refine ⟨a, ?_⟩
  change x = a • (show P.val.obj (op W) from P.val.map (𝟙 W).op p) at ha
  simpa only [op_id, PresheafOfModules.map_id, ModuleCat.restrictScalarsId'_inv_app,
    ModuleCat.restrictScalarsId'App_inv_apply] using ha

private noncomputable def dualChartMap (P : Modules.{uC, vC, r} R) (W : C)
    (e : P.over W ≅ unit ((ringSheaf.{uC, vC, r} R).over W)) :
    (unitDual.{uC, vC, r} R P).over W ⟶ unit ((ringSheaf.{uC, vC, r} R).over W) where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        (X := ((unitDual.{uC, vC, r} R P).over W).val.obj V)
        (Y := (unit ((ringSheaf.{uC, vC, r} R).over W)).val.obj V)
        ((evalLinear.{uC, vC, r} R P (op V.unop.left)).flip
          (e.inv.val.app V (1 : R.obj.obj (op V.unop.left))))
      naturality := by
        intro V V' f
        ext phi
        let p := e.inv.val.app V (1 : R.obj.obj (op V.unop.left))
        have hp : P.val.map f.unop.left.op p =
            e.inv.val.app V' (1 : R.obj.obj (op V'.unop.left)) := by
          have h := PresheafOfModules.naturality_apply e.inv.val f
            (1 : R.obj.obj (op V.unop.left))
          exact h.symm.trans (congrArg (e.inv.val.app V')
            (R.obj.map f.unop.left.op).hom.map_one)
        change evalLinear.{uC, vC, r} R P (op V'.unop.left)
            ((unitDual.{uC, vC, r} R P).val.map f.unop.left.op phi)
            (e.inv.val.app V' (1 : R.obj.obj (op V'.unop.left))) = _
        rw [← hp]
        exact eval_restrict.{uC, vC, r} R P f.unop.left.op phi p }

attribute [local irreducible] dualChartMap

attribute [local irreducible] cancellation

private theorem tensor_linear (P : Modules.{uC, vC, r} R) :
    (tensorRight P).Linear (scalars.{uC, vC, r} R) := by
  constructor
  intro M N f a
  apply pure_hom_ext.{uC, vC, r} R M P (N ⊗ P)
  intro U x p
  have hm := pure_map.{uC, vC, r} R (a • f) (𝟙 P) U x p
  have hn := pure_map.{uC, vC, r} R f (𝟙 P) U x p
  rw [tensorHom_id] at hm hn
  change ((tensorRight P).map (a • f)).val.app U (pureTensor.{uC, vC, r} R M P U x p) = _ at hm
  erw [hm]
  change pureTensor.{uC, vC, r} R N P U (a.1 U • f.val.app U x) p =
    a.1 U • ((f ▷ P).val.app U (pureTensor.{uC, vC, r} R M P U x p))
  rw [hn, pure_smul_left.{uC, vC, r}]
  rfl

private theorem pure_restrict (M N : Modules.{uC, vC, r} R) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : M.val.obj U) (y : N.val.obj U) :
    (M ⊗ N).val.map f (pureTensor.{uC, vC, r} R M N U x y) =
      pureTensor.{uC, vC, r} R M N V (M.val.map f x) (N.val.map f y) := by
  let z := x ⊗ₜ[R.obj.obj U] y
  have hi := PresheafOfModules.naturality_apply
    (tensorObjIsoSheafification M N).inv.val f
      (((adj.{uC, vC, r} R).unit.app (M.val ⊗ N.val)).app U z)
  have hu := PresheafOfModules.naturality_apply
    ((adj.{uC, vC, r} R).unit.app (M.val ⊗ N.val)) f z
  unfold pureTensor
  exact hi.symm.trans (congrArg ((tensorObjIsoSheafification M N).inv.val.app V) hu.symm)

omit [EssentiallySmall.{max uC vC r} C] in
private theorem section_ext (M : Modules.{uC, vC, r} R) {U : Cᵒᵖ} (x y : M.val.obj U)
    (s : Sieve U.unop) (hs : s ∈ J U.unop)
    (h : ∀ V (f : V ⟶ U.unop), s f → M.val.map f.op x = M.val.map f.op y) : x = y := by
  have hM := Presheaf.isSheaf_comp_of_isSheaf J _ (CategoryTheory.forget AddCommGrpCat) M.isSheaf
  exact (((isSheaf_iff_isSheaf_of_type J _).mp hM).isSeparated _ hs).ext h

private noncomputable def siteRightIso (P : Modules.{uC, vC, r} R) :
    tensorRight P ≅ siteSheafTensorRight P :=
  (siteSheafTensorRightIso R P).symm

private theorem eval_scaled (P : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (p : P.val.obj U) (phi : (unitDual.{uC, vC, r} R P).val.obj U)
    (hp : phi.app (op (Over.mk (𝟙 U.unop))) p = (1 : R.obj.obj U))
    (a b : R.obj.obj U) :
    (evaluation.{uC, vC, r} R P).val.app U
      (pureTensor.{uC, vC, r} R P (unitDual.{uC, vC, r} R P) U (a • p) (b • phi)) = a * b := by
  rw [evaluation_pure.{uC, vC, r}]
  change evalLinear.{uC, vC, r} R P U (b • phi) (a • p) = _
  rw [(evalLinear.{uC, vC, r} R P U (b • phi)).map_smul]
  erw [(evalLinear.{uC, vC, r} R P U).map_smul, LinearMap.smul_apply]
  change a * (b * evalLinear.{uC, vC, r} R P U phi p) = _
  rw [show evalLinear.{uC, vC, r} R P U phi p = 1 from hp, mul_one]

private theorem pure_units (M N : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) (u : (R.obj.obj U)ˣ) :
    pureTensor.{uC, vC, r} R M N U ((u : R.obj.obj U) • x)
        ((↑(u⁻¹) : R.obj.obj U) • y) = pureTensor.{uC, vC, r} R M N U x y := by
  rw [pure_smul_left.{uC, vC, r}, pure_smul_right.{uC, vC, r}, smul_smul, Units.mul_inv, one_smul]

private theorem pure_units_nested (M N H : Modules.{uC, vC, r} R) (U : Cᵒᵖ)
    (x : M.val.obj U) (y : N.val.obj U) (z : H.val.obj U) (u : (R.obj.obj U)ˣ) :
    pureTensor.{uC, vC, r} R (M ⊗ N) H U
        (pureTensor.{uC, vC, r} R M N U x ((u : R.obj.obj U) • y))
        ((↑(u⁻¹) : R.obj.obj U) • z) =
      pureTensor.{uC, vC, r} R (M ⊗ N) H U (pureTensor.{uC, vC, r} R M N U x y) z := by
  rw [pure_smul_right.{uC, vC, r} R M N U, pure_units.{uC, vC, r}]

end SheafOfModules.LineEvaluation
