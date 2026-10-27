/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.CategoryTheory.ConstantFiniteFreePresentationExtension
public import Sheaf.CategoryTheory.SiteConstantModuleHom
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Finiteness.Projective
import Sheaf.Paper.ScalarExtensionBinaryCoherence

/-! # The finite-projective inverse to normalized scalar dual evaluation

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, final finite-free/direct-summand
reduction; algebra.tex, Tags 05CE and 05CF.
(blueprint: lem-sfb-scalar-dual-evaluation-inverse).

The scalar-extension objects and constant-module functor are the existing constructions
of `ConstantFiniteFreePresentationExtension`. Only the section formula is introduced here.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Opposite
open CategoryTheory.ConstantFiniteFreePresentationExtension

namespace CategoryTheory.ScalarDualEvaluation

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type (max u v)) [CommRing R] (B : Sheaf J CommRingCat.{max u v})
  (α : (constantSheaf J CommRingCat.{max u v}).obj (CommRingCat.of R) ⟶ B)

/-- The existing scalar tensor sheafification unit, applied to a constant module section.
Source: Stacks 03CY and 03EK (blueprint: lem-sfb-scalar-dual-evaluation-inverse).
This is the actual element b tensor v, not a chosen representative of an arbitrary section. -/
def pureTensor (V : ModuleCat.{max u v} R) (U : Cᵒᵖ) (b : B.obj.obj U) (x : V) :
    (extension J R B α V).val.obj U :=
  SheafOfModules.scalarExtensionRingIsoTmul α ((constantModuleHomFunctor J R).obj V) U
    ((constantModuleHomUnit J R V).app U x) b

/-- The finite dual-generator inverse formula, before asserting linearity or naturality.
The functional h is a morphism on the entire slice; its component at the identity of U
is evaluated on the constant generator p(e_j).
Source: Stacks 08JJ, final finite-free/direct-summand reduction
(blueprint: lem-sfb-scalar-dual-evaluation-inverse). -/
def inverseSection (V : ModuleCat.{max u v} R) {N : ℕ}
    (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V) (U : Cᵒᵖ)
    (h : (SheafOfModules.homObj (R := B) (extension J R B α V)
      (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))).val.obj U) :
    (extension J R B α (ModuleCat.of R (Module.Dual R V))).val.obj U :=
  ∑ j : Fin N, pureTensor J R B α (ModuleCat.of R (Module.Dual R V)) U
    (h.app (op (Over.mk (𝟙 U.unop)))
      (pureTensor J R B α V U 1 (p (Pi.single j 1)))) ((LinearMap.proj j).comp i)

set_option backward.isDefEq.respectTransparency.types false in
private lemma splitting_expansion.{w} (S : Type w) [CommRing S] (V : ModuleCat.{w} S) {N : ℕ}
    (i : V →ₗ[S] (Fin N → S)) (p : (Fin N → S) →ₗ[S] V)
    (h : p.comp i = LinearMap.id) (x : V) :
    x = ∑ j : Fin N, (i x j) • p (Pi.single j 1) := by
  have hx := LinearMap.congr_fun h x
  change p (i x) = x at hx
  calc
    x = p (i x) := hx.symm
    _ = p (∑ j : Fin N, (i x j) • Pi.single j 1) :=
      congrArg p (pi_eq_sum_univ' (i x))
    _ = _ := by
      rw [map_sum]
      simp only [map_smul]

set_option backward.isDefEq.respectTransparency.types false in
private lemma dual_expansion.{w} (S : Type w) [CommRing S] (V : ModuleCat.{w} S) {N : ℕ}
    (i : V →ₗ[S] (Fin N → S)) (p : (Fin N → S) →ₗ[S] V)
    (h : p.comp i = LinearMap.id) (φ : Module.Dual S V) :
    φ = ∑ j : Fin N, φ (p (Pi.single j 1)) • ((LinearMap.proj j).comp i) := by
  ext x
  have hx := congrArg φ (splitting_expansion S V i p h x)
  simpa [map_sum, map_smul, mul_comm] using hx

private abbrev scalar (U : Cᵒᵖ) : R →+* B.obj.obj U :=
  (α.hom.app U).hom.comp
    ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app U).hom

set_option backward.isDefEq.respectTransparency.types false in
private lemma ringUnit_compat (U : Cᵒᵖ) (r : R) :
    (constantModuleHomRingIso J R).hom.hom.app U
      ((toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U r) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app U r := by
  let : J.PreservesSheafification
      (forget₂ CommRingCat.{max u v} RingCat.{max u v}) :=
    GrothendieckTopology.instPreservesSheafification J
      (forget₂ CommRingCat.{max u v} RingCat.{max u v})
      (FD := fun A B : CommRingCat.{max u v} ↦ A →+* B)
      (CD := fun A : CommRingCat.{max u v} ↦ A)
      (FE := fun A B : RingCat.{max u v} ↦ A →+* B)
      (CE := fun A : RingCat.{max u v} ↦ A)
  exact ConcreteCategory.congr_hom
    (congr_app (sheafComposeIso_hom_fac J (forget₂ CommRingCat RingCat)
      ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))) U) r

set_option backward.isDefEq.respectTransparency.types false in
private lemma pure_smul (V : ModuleCat.{max u v} R) (U : Cᵒᵖ)
    (a b : B.obj.obj U) (x : V) :
    a • pureTensor J R B α V U b x = pureTensor J R B α V U (a * b) x :=
  SheafOfModules.scalarExtensionSection_smul α _ U a b _

set_option backward.isDefEq.respectTransparency.types false in
private lemma pure_base_smul (V : ModuleCat.{max u v} R) (U : Cᵒᵖ)
    (b : B.obj.obj U) (r : R) (x : V) :
    pureTensor J R B α V U b (r • x) =
      pureTensor J R B α V U (b * scalar J R B α U r) x := by
  let a := (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R))).app U r
  have hi := congrArg (fun f ↦ f.hom.app U a) (constantModuleHomRingIso J R).hom_inv_id
  have hu : (constantModuleHomUnit J R V).app U (r • x) =
      (constantModuleHomRingIso J R).hom.hom.app U a •
        (constantModuleHomUnit J R V).app U x := by
    change (constantModuleHomRingIso J R).inv.hom.app U
      ((constantModuleHomRingIso J R).hom.hom.app U a) = a at hi
    change (constantModuleHomUnit J R V).app U (r • x) =
      (constantModuleHomRingIso J R).inv.hom.app U
        ((constantModuleHomRingIso J R).hom.hom.app U a) •
          (show ((siteConstantModuleFunctorGeneral J R).obj V).val.obj U from
            (constantModuleHomUnit J R V).app U x)
    rw [hi]
    exact (((PresheafOfModules.sheafificationAdjunction
      (toSheafify J ((Functor.const Cᵒᵖ).obj (RingCat.of R)))).unit.app
        ((siteConstantModulePresheafGeneral (C := C) R).obj V)).app U).hom.map_smul r x
  unfold pureTensor
  erw [hu]
  exact (SheafOfModules.scalarExtensionSection_base_smul α _ U b _ _).trans
    (congrArg (fun c ↦ SheafOfModules.scalarExtensionRingIsoTmul α _ U
      ((constantModuleHomUnit J R V).app U x) (b * α.hom.app U c))
        (ringUnit_compat J R U r))

set_option backward.isDefEq.respectTransparency.types false in
private lemma pure_sum (V : ModuleCat.{max u v} R) (U : Cᵒᵖ)
    (b : B.obj.obj U) {ι : Type*} (s : Finset ι) (f : ι → V) :
    pureTensor J R B α V U b (∑ j ∈ s, f j) =
      ∑ j ∈ s, pureTensor J R B α V U b (f j) := by
  unfold pureTensor
  rw [map_sum]
  dsimp only [SheafOfModules.scalarExtensionRingIsoTmul]
  rw [TensorProduct.tmul_sum, map_sum]

set_option backward.isDefEq.respectTransparency.types false in
private lemma extension_map_pure {V W : ModuleCat.{max u v} R} (f : V ⟶ W)
    (U : Cᵒᵖ) (b : B.obj.obj U) (x : V) :
    (extensionMap J R B α f).val.app U (pureTensor J R B α V U b x) =
      pureTensor J R B α W U b (f x) := by
  unfold pureTensor
  refine (SheafOfModules.scalarExtension_map_tmul α
    ((constantModuleHomFunctor J R).map f) U b
    ((constantModuleHomUnit J R V).app U x)).trans ?_
  apply congrArg (fun z ↦ SheafOfModules.scalarExtensionRingIsoTmul α _ U z b)
  have h := toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map
    ((siteConstantModulePresheafGeneral (C := C) R).map f))
  exact (ConcreteCategory.congr_hom (congr_app h U) x).symm

set_option backward.isDefEq.respectTransparency.types false in
private lemma extension_map_comp {V W T : ModuleCat.{max u v} R}
    (f : V ⟶ W) (g : W ⟶ T) :
    extensionMap J R B α (f ≫ g) =
      extensionMap J R B α f ≫ extensionMap J R B α g := by
  unfold extensionMap
  rw [Functor.map_comp]
  exact SheafOfModules.scalarExtension_map_comp α _ _

set_option backward.isDefEq.respectTransparency.types false in
private lemma extension_map_id (V : ModuleCat.{max u v} R) :
    extensionMap J R B α (𝟙 V) = 𝟙 _ := by
  unfold extensionMap
  rw [Functor.map_id]
  exact SheafOfModules.scalarExtension_map_id α _

set_option backward.isDefEq.respectTransparency.types false in
private lemma section_expansion (V : ModuleCat.{max u v} R) {N : ℕ}
    (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V)
    (h : p.comp i = LinearMap.id) (U : Cᵒᵖ) (x : (extension J R B α V).val.obj U) :
    ∃ a : Fin N → B.obj.obj U,
      x = ∑ j : Fin N, pureTensor J R B α V U (a j) (p (Pi.single j 1)) := by
  obtain ⟨_, _, e, _, _, he, _, _⟩ := constantFiniteFreePresentationExtension J R B α
  let y := (e N).hom.val.app U ((extensionMap J R B α (ModuleCat.ofHom i)).val.app U x)
  refine ⟨fun j ↦ commCoordinate J B N U y j, ?_⟩
  have hid : extensionMap J R B α (ModuleCat.ofHom i) ≫
      extensionMap J R B α (ModuleCat.ofHom p) = 𝟙 _ := by
    rw [← extension_map_comp]
    have hp : (ModuleCat.ofHom i : V ⟶ ModuleCat.of R (Fin N → R)) ≫
        ModuleCat.ofHom p = 𝟙 V := ModuleCat.hom_ext h
    rw [hp, extension_map_id]
  have hy : (e N).inv.val.app U y =
      (extensionMap J R B α (ModuleCat.ofHom i)).val.app U x :=
    congrArg (fun f ↦ f.val.app U
      ((extensionMap J R B α (ModuleCat.ofHom i)).val.app U x)) (e N).hom_inv_id
  have hx := congrArg (fun f ↦ f.val.app U x) hid
  change (extensionMap J R B α (ModuleCat.ofHom p)).val.app U
    ((extensionMap J R B α (ModuleCat.ofHom i)).val.app U x) = x at hx
  calc
    x = (extensionMap J R B α (ModuleCat.ofHom p)).val.app U
        ((extensionMap J R B α (ModuleCat.ofHom i)).val.app U x) := hx.symm
    _ = (extensionMap J R B α (ModuleCat.ofHom p)).val.app U
        ((e N).inv.val.app U y) := congrArg _ hy.symm
    _ = _ := by
      rw [he, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact extension_map_pure J R B α (ModuleCat.ofHom p) U _ _

private abbrev dualSheaf (V : ModuleCat.{max u v} R) :=
  SheafOfModules.homObj (R := B) (extension J R B α V)
    (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))

set_option backward.isDefEq.respectTransparency.types false in
private lemma pure_naturality (V : ModuleCat.{max u v} R) {U T : Cᵒᵖ}
    (f : U ⟶ T) (b : B.obj.obj U) (x : V) :
    (extension J R B α V).val.map f (pureTensor J R B α V U b x) =
      pureTensor J R B α V T (B.obj.map f b) x := by
  unfold pureTensor
  refine (SheafOfModules.scalarExtensionSection_naturality α
    ((constantModuleHomFunctor J R).obj V) f b
    ((constantModuleHomUnit J R V).app U x)).trans ?_
  apply congrArg (fun z ↦ SheafOfModules.scalarExtensionRingIsoTmul α _ T z
    (B.obj.map f b))
  exact (NatTrans.naturality_apply (constantModuleHomUnit J R V) f x).symm

set_option backward.isDefEq.respectTransparency.types false in
private def evaluateGenerator (V : ModuleCat.{max u v} R) (U : Cᵒᵖ) (x : V) :
    (dualSheaf J R B α V).val.obj U →ₗ[B.obj.obj U] B.obj.obj U where
  toFun h := h.app (op (Over.mk (𝟙 U.unop))) (pureTensor J R B α V U 1 x)
  map_add' _ _ := rfl
  map_smul' r h := by
    change B.obj.map (𝟙 U.unop).op r * _ = r * _
    simp
    rfl

set_option backward.isDefEq.respectTransparency.types false in
private def inverseLinear (V : ModuleCat.{max u v} R) {N : ℕ}
    (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V) (U : Cᵒᵖ) :
    (dualSheaf J R B α V).val.obj U →ₗ[B.obj.obj U]
      (extension J R B α (ModuleCat.of R (Module.Dual R V))).val.obj U :=
  ∑ j : Fin N, (evaluateGenerator J R B α V U (p (Pi.single j 1))).smulRight
    (pureTensor J R B α (ModuleCat.of R (Module.Dual R V)) U 1
      ((LinearMap.proj j).comp i))

set_option backward.isDefEq.respectTransparency.types false in
private lemma inverseLinear_apply (V : ModuleCat.{max u v} R) {N : ℕ}
    (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V) (U : Cᵒᵖ)
    (h : (dualSheaf J R B α V).val.obj U) :
    inverseLinear J R B α V i p U h = inverseSection J R B α V i p U h := by
  simp only [inverseLinear, LinearMap.sum_apply, LinearMap.smulRight_apply,
    evaluateGenerator, LinearMap.coe_mk, AddHom.coe_mk, inverseSection]
  apply Finset.sum_congr rfl
  intro j _
  exact (pure_smul J R B α _ U _ 1 _).trans (by rw [mul_one])

set_option backward.isDefEq.respectTransparency.types false in
private lemma localized_evaluation (V : ModuleCat.{max u v} R) (U : Cᵒᵖ)
    (h : (dualSheaf J R B α V).val.obj U) (W : (Over U.unop)ᵒᵖ) (x : V) :
    B.obj.map W.unop.hom.op
      (h.app (op (Over.mk (𝟙 U.unop))) (pureTensor J R B α V U 1 x)) =
      h.app W (pureTensor J R B α V (op W.unop.left) 1 x) := by
  have hn := PresheafOfModules.naturality_apply h
    (Over.homMk W.unop.hom : W.unop ⟶ Over.mk (𝟙 U.unop)).op
      (pureTensor J R B α V U 1 x)
  change h.app W ((extension J R B α V).val.map W.unop.hom.op
    (pureTensor J R B α V U 1 x)) = _ at hn
  rw [pure_naturality, map_one] at hn
  exact hn.symm

set_option backward.isDefEq.respectTransparency.types false in
private lemma dual_section_expansion (V : ModuleCat.{max u v} R) {N : ℕ}
    (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V)
    (h : p.comp i = LinearMap.id) (U : Cᵒᵖ)
    (x : (extension J R B α (ModuleCat.of R (Module.Dual R V))).val.obj U) :
    ∃ a : Fin N → B.obj.obj U,
      x = ∑ j : Fin N, pureTensor J R B α (ModuleCat.of R (Module.Dual R V)) U
        (a j) ((LinearMap.proj j).comp i) := by
  let t : Module.Dual R V →ₗ[R] (Fin N → R) :=
    LinearMap.pi (fun j ↦ Module.Dual.eval R V (p (Pi.single j 1)))
  let q : (Fin N → R) →ₗ[R] Module.Dual R V :=
    ∑ j : Fin N, (LinearMap.proj j).smulRight ((LinearMap.proj j).comp i)
  have hq (j : Fin N) : q (Pi.single j 1) = (LinearMap.proj j).comp i := by
    simp [q, Pi.single_apply]
  have hqt : q.comp t = LinearMap.id := by
    ext φ x
    have hd := LinearMap.congr_fun (dual_expansion.{max u v} R V i p h φ) x
    simpa [q, t] using hd.symm
  obtain ⟨a, ha⟩ := section_expansion J R B α
    (ModuleCat.of R (Module.Dual R V)) t q hqt U x
  exact ⟨a, by simpa only [hq] using ha⟩

private abbrev Normalized (V : ModuleCat.{max u v} R)
    (β : extension J R B α (ModuleCat.of R (Module.Dual R V)) ⟶ dualSheaf J R B α V) :=
  ∀ (U : Cᵒᵖ) (b : B.obj.obj U) (φ : Module.Dual R V)
    (W : (Over U.unop)ᵒᵖ) (b' : B.obj.obj (op W.unop.left)) (x : V),
    (β.val.app U (pureTensor J R B α _ U b φ)).app W
      (pureTensor J R B α V (op W.unop.left) b' x) =
      B.obj.map W.unop.hom.op b * b' * scalar J R B α (op W.unop.left) (φ x)

set_option backward.isDefEq.respectTransparency.types false in
private lemma inverse_beta_pure (V : ModuleCat.{max u v} R) {N : ℕ}
    (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V)
    (hp : p.comp i = LinearMap.id)
    (β : extension J R B α (ModuleCat.of R (Module.Dual R V)) ⟶ dualSheaf J R B α V)
    (hβ : Normalized J R B α V β) (U : Cᵒᵖ) (b : B.obj.obj U) (φ : Module.Dual R V) :
    inverseLinear J R B α V i p U (β.val.app U (pureTensor J R B α _ U b φ)) =
      pureTensor J R B α _ U b φ := by
  rw [inverseLinear_apply, inverseSection]
  have hφ := congrArg (pureTensor J R B α (ModuleCat.of R (Module.Dual R V)) U b)
    (dual_expansion.{max u v} R V i p hp φ)
  rw [pure_sum] at hφ
  conv_rhs => rw [hφ]
  apply Finset.sum_congr rfl
  intro j _
  rw [pure_base_smul]
  congr 1
  simpa using hβ U b φ (op (Over.mk (𝟙 U.unop))) 1 (p (Pi.single j 1))

set_option backward.isDefEq.respectTransparency.types false in
private lemma inverse_beta (V : ModuleCat.{max u v} R) {N : ℕ}
    (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V)
    (hp : p.comp i = LinearMap.id)
    (β : extension J R B α (ModuleCat.of R (Module.Dual R V)) ⟶ dualSheaf J R B α V)
    (hβ : Normalized J R B α V β) (U : Cᵒᵖ)
    (x : (extension J R B α (ModuleCat.of R (Module.Dual R V))).val.obj U) :
    inverseLinear J R B α V i p U (β.val.app U x) = x := by
  obtain ⟨a, hx⟩ := dual_section_expansion J R B α V i p hp U x
  rw [hx, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact inverse_beta_pure J R B α V i p hp β hβ U _ _

set_option backward.isDefEq.respectTransparency.types false in
private def evalAt (V : ModuleCat.{max u v} R) (U : Cᵒᵖ) (W : (Over U.unop)ᵒᵖ)
    (x : (extension J R B α V).val.obj (op W.unop.left)) :
    (dualSheaf J R B α V).val.obj U →+ B.obj.obj (op W.unop.left) where
  toFun h := h.app W x
  map_zero' := rfl
  map_add' _ _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
private lemma beta_inverse_pure (V : ModuleCat.{max u v} R) {N : ℕ}
    (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V)
    (hp : p.comp i = LinearMap.id)
    (β : extension J R B α (ModuleCat.of R (Module.Dual R V)) ⟶ dualSheaf J R B α V)
    (hβ : Normalized J R B α V β) (U : Cᵒᵖ)
    (h : (dualSheaf J R B α V).val.obj U) (W : (Over U.unop)ᵒᵖ)
    (b : B.obj.obj (op W.unop.left)) (x : V) :
    (β.val.app U (inverseLinear J R B α V i p U h)).app W
      (pureTensor J R B α V (op W.unop.left) b x) =
      h.app W (pureTensor J R B α V (op W.unop.left) b x) := by
  rw [inverseLinear_apply, inverseSection, map_sum]
  change evalAt J R B α V U W _ (∑ j : Fin N, _) = _
  rw [map_sum]
  have hx := congrArg (pureTensor J R B α V (op W.unop.left) b)
    (splitting_expansion.{max u v} R V i p hp x)
  rw [pure_sum] at hx
  conv_rhs => rw [hx, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (β.val.app U (pureTensor J R B α _ U
    (h.app (op (Over.mk (𝟙 U.unop)))
      (pureTensor J R B α V U 1 (p (Pi.single j 1))))
    ((LinearMap.proj j).comp i))).app W _ = _
  rw [hβ, localized_evaluation, pure_base_smul]
  rw [← mul_one (b * scalar J R B α (op W.unop.left) (i x j)), ← pure_smul]
  rw [map_smul]
  change _ = (b * scalar J R B α (op W.unop.left) (i x j)) * _
  simp only [LinearMap.comp_apply, LinearMap.proj_apply]
  ac_rfl

set_option backward.isDefEq.respectTransparency.types false in
private lemma beta_inverse (V : ModuleCat.{max u v} R) {N : ℕ}
    (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V)
    (hp : p.comp i = LinearMap.id)
    (β : extension J R B α (ModuleCat.of R (Module.Dual R V)) ⟶ dualSheaf J R B α V)
    (hβ : Normalized J R B α V β) (U : Cᵒᵖ)
    (h : (dualSheaf J R B α V).val.obj U) :
    β.val.app U (inverseLinear J R B α V i p U h) = h := by
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, hx⟩ := section_expansion J R B α V i p hp (op W.unop.left) x
  change (β.val.app U (inverseLinear J R B α V i p U h)).app W x = h.app W x
  rw [hx, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact beta_inverse_pure J R B α V i p hp β hβ U h W _ _

set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private def inverseMorphism (V : ModuleCat.{max u v} R) {N : ℕ}
    (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V)
    (hp : p.comp i = LinearMap.id)
    (β : extension J R B α (ModuleCat.of R (Module.Dual R V)) ⟶ dualSheaf J R B α V)
    (hβ : Normalized J R B α V β) :
    dualSheaf J R B α V ⟶ extension J R B α (ModuleCat.of R (Module.Dual R V)) :=
  ⟨{ app := fun U ↦ ModuleCat.ofHom
        (X := (dualSheaf J R B α V).val.obj U)
        (Y := (extension J R B α (ModuleCat.of R (Module.Dual R V))).val.obj U)
        (inverseLinear J R B α V i p U)
     naturality := by
      intro U T f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro h
      apply (Function.LeftInverse.injective (inverse_beta J R B α V i p hp β hβ T))
      change β.val.app T (inverseLinear J R B α V i p T
        ((dualSheaf J R B α V).val.map f h)) =
        β.val.app T ((extension J R B α _).val.map f
          (inverseLinear J R B α V i p U h))
      rw [beta_inverse J R B α V i p hp β hβ,
        PresheafOfModules.naturality_apply β.val,
        beta_inverse J R B α V i p hp β hβ] }⟩

set_option backward.isDefEq.respectTransparency.types false in
private lemma inverseMorphism_apply (V : ModuleCat.{max u v} R) {N : ℕ}
    (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V)
    (hp : p.comp i = LinearMap.id)
    (β : extension J R B α (ModuleCat.of R (Module.Dual R V)) ⟶ dualSheaf J R B α V)
    (hβ : Normalized J R B α V β) (U : Cᵒᵖ)
    (h : (dualSheaf J R B α V).val.obj U) :
    (inverseMorphism J R B α V i p hp β hβ).val.app U h =
      inverseLinear J R B α V i p U h := by
  unfold inverseMorphism
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Any scalar-dual comparison normalized on localized pure tensors has the displayed
finite dual-generator inverse, for every finite free splitting.

Source: Stacks Project, sites-cohomology.tex, Tag 08JJ, final finite-free/direct-summand
reduction, and algebra.tex, Tags 05CE and 05CF
(blueprint: lem-sfb-scalar-dual-evaluation-inverse).

Proof plan, following the six steps of the node:
1. Finite generation gives a surjection p from a finite free module. Projectivity lifts
id_V to i, giving p i = id. The empty family is allowed when V = 0.
2. Expand i(v) in the standard basis and apply p: v = sum lambda_j(v) v_j. Apply a
functional to obtain phi = sum phi(v_j) lambda_j. Thus V and its dual are split retracts
of the same finite free module.
3. Apply constant module sheafification and scalar extension to both retractions.
The unconditional finite-power clause of lem-sfb-constant-finite-free-presentation-extension
identifies the middle object with B^N, with inverse sum b_j tensor e_j. Consequently EVERY
section of either retract has a finite expansion in the indicated constant generators;
no assertion that every tensor section is pure and no flatness are needed.
4. Define inverseSection by the stated finite sum. Evaluation is additive and B(U)-linear.
Naturality of each slice morphism h, together with restriction of constant generators,
shows that the sum commutes with every restriction. These maps form gamma.
5. The normalization hypothesis and v = sum lambda_j(v) v_j show beta gamma = id on
constant generators on every slice. Step 3 extends the equality to every local section,
so the slice maps, and hence the sheaf morphisms, are equal.
6. On b tensor phi the other composite is sum b alpha(phi(v_j)) tensor lambda_j,
which is b tensor phi by the dual identity and balancing. Step 3 extends it to every
section. An inverse is unique, proving independence of every other splitting. Empty sums
handle N = 0; the same argument includes V = 0 with N positive, the zero ring, the zero
coefficient sheaf, empty covering sieves, and non-flat coefficients. -/
theorem scalarDualEvaluationInverse (V : ModuleCat.{max u v} R)
    [Module.Finite R V] [Module.Projective R V]
    (β : extension J R B α (ModuleCat.of R (Module.Dual R V)) ⟶
      SheafOfModules.homObj (R := B) (extension J R B α V)
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)))
    (hβ : ∀ (U : Cᵒᵖ) (b : B.obj.obj U) (φ : Module.Dual R V)
      (W : (Over U.unop)ᵒᵖ) (b' : B.obj.obj (op W.unop.left)) (x : V),
      (β.val.app U (pureTensor J R B α _ U b φ)).app W
          (pureTensor J R B α V (op W.unop.left) b' x) =
        B.obj.map W.unop.hom.op b * b' *
          α.hom.app (op W.unop.left)
            ((toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of R))).app
              (op W.unop.left) (φ x))) :
    (∃ (N : ℕ) (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V),
      p.comp i = LinearMap.id) ∧
    ∀ (N : ℕ) (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V),
      p.comp i = LinearMap.id →
      (∀ x : V, x = ∑ j : Fin N, (i x j) • p (Pi.single j 1)) ∧
      (∀ φ : Module.Dual R V,
        φ = ∑ j : Fin N, φ (p (Pi.single j 1)) • ((LinearMap.proj j).comp i)) ∧
      ∃ γ : SheafOfModules.homObj (R := B) (extension J R B α V)
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ⟶
            extension J R B α (ModuleCat.of R (Module.Dual R V)),
        (∀ (U : Cᵒᵖ) (h : (SheafOfModules.homObj (R := B) (extension J R B α V)
          (SheafOfModules.unit
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))).val.obj U),
          γ.val.app U h = inverseSection J R B α V i p U h) ∧
        γ ≫ β = 𝟙 _ ∧ β ≫ γ = 𝟙 _ ∧ IsIso β ∧
        ∀ (N' : ℕ) (i' : V →ₗ[R] (Fin N' → R)) (p' : (Fin N' → R) →ₗ[R] V),
          p'.comp i' = LinearMap.id →
          ∀ (U : Cᵒᵖ) (h : (SheafOfModules.homObj (R := B) (extension J R B α V)
            (SheafOfModules.unit
              ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))).val.obj U),
            inverseSection J R B α V i' p' U h = γ.val.app U h := by
  classical
  have hex : ∃ (N : ℕ) (i : V →ₗ[R] (Fin N → R)) (p : (Fin N → R) →ₗ[R] V),
      p.comp i = LinearMap.id := by
    obtain ⟨N, p, i, _, _, hp⟩ := Module.Finite.exists_comp_eq_id_of_projective R V
    exact ⟨N, i, p, hp⟩
  refine ⟨hex, ?_⟩
  intro N i p hp
  refine ⟨splitting_expansion.{max u v} R V i p hp, dual_expansion.{max u v} R V i p hp, ?_⟩
  let γ := inverseMorphism J R B α V i p hp β hβ
  have hγ : ∀ (U : Cᵒᵖ) (h : (dualSheaf J R B α V).val.obj U),
      γ.val.app U h = inverseSection J R B α V i p U h :=
      by
    intro U h
    exact (inverseMorphism_apply J R B α V i p hp β hβ U h).trans
      (inverseLinear_apply J R B α V i p U h)
  have hγβ : γ ≫ β = 𝟙 _ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    change β.val.app U (γ.val.app U h) = h
    rw [hγ, ← inverseLinear_apply]
    exact beta_inverse J R B α V i p hp β hβ U h
  have hβγ : β ≫ γ = 𝟙 _ := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change γ.val.app U (β.val.app U x) = x
    rw [hγ, ← inverseLinear_apply]
    exact inverse_beta J R B α V i p hp β hβ U x
  refine ⟨γ, hγ, hγβ, hβγ, ⟨⟨γ, hβγ, hγβ⟩⟩, ?_⟩
  intro N' i' p' hp' U h
  apply Function.LeftInverse.injective (inverse_beta J R B α V i p hp β hβ U)
  change β.val.app U (inverseSection J R B α V i' p' U h) =
    β.val.app U (γ.val.app U h)
  rw [hγ, ← inverseLinear_apply, ← inverseLinear_apply, beta_inverse J R B α V i' p' hp' β hβ,
    beta_inverse J R B α V i p hp β hβ]

end CategoryTheory.ScalarDualEvaluation
