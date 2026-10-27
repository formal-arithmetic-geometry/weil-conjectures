/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q66
-/
module

public import Sheaf.SixFunctors.SemilinearProperOpenCore

import Mathlib.Util.AliasIn
import all Sheaf.SixFunctors.SemilinearProperOpenCore
import Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.AlgebraicGeometry.SemilinearScalarDerivedComparison
import Sheaf.AlgebraicGeometry.SemilinearScalarAdjunctions
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import all Sheaf.AlgebraicGeometry.VaryingRingOperations
import all Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows

/-! # Existing scalar constructions for semilinear proper/open mates

This part of the intrinsic coefficient API is separated to keep each file within
the compilation limit. The original constructions and their properties are retained.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option synthInstance.maxSize 32
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open WeilConjectures.SemilinearSections
section ProofEnvironment
attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf Functor.mapDerivedCategoryNatIso
  Functor.mapDerivedCategoryCompIso HasDerivedCategory.standard DerivedCategory.Q
  Functor.mapDerivedCategoryFactors
namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen
variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
attribute [local irreducible] SemilinearSections.systemRing
  coefficientMap VaryingRing.ringMap alpha gamma

section ScalarRestriction
attribute [local implicit_reducible]
  VaryingRing.coefficientTransition VaryingRing.ordinaryScalarMap
  StrictTower.G StrictTower.R P R

variable (B : Type (u + 1)) [CommRing B]
  (φ : ∀ n : ℕ, B →+* C n)
  (hφ : ∀ n : ℕ, (τ n).hom.comp (φ (n + 1)) = φ n)

/-- The actual level scalar restriction along the supplied B -> C_n.
Source: Stacks 03CZ; ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev levelRestriction (X : Scheme.{u}) (n : ℕ) :=
  SemilinearSections.res.{u + 1, u, u + 1}
    ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map (CommRingCat.ofHom (φ n)))



set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 400000 in
-- Constructing the entire scalar-restriction functor requires sectionwise transports.
/-- Termwise scalar restriction to ordinary constant-B towers, uniquely characterized
on objects, transitions, and morphisms. Source: Stacks 03CZ; Zheng 4.1
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: keep the component sheaves and restrict their scalar actions along phi_n.
The equation hphi makes each horizontal restriction B-linear. Functor identities
and composition are those of the system presheaf. The evaluated functor equations
fix all objects and morphisms, and the section formula fixes every transition;
thus this is a unique actual functor, rather than an arbitrary comparison map. -/
theorem rhoOrdinary_existsUnique (X : Scheme.{u})
    (compatible : ∀ n : ℕ, (τ n).hom.comp (φ (n + 1)) = φ n) :
    ∃! F : Modules C τ X ⥤ StrictTower.Towers B X,
      (∀ n : ℕ, F ⋙ (CategoryTheory.evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) =
        SemilinearSections.evaluation.{u + 1, u, u + 1} (ProEt.topology X) (coefficients C X)
          (transition C τ X) n ⋙ levelRestriction C B φ X n) ∧
      (∀ (M : Modules C τ X) (n m : ℕ) (h : n ≤ m) (U : X.ProEt),
        HEq (fun x ↦ ((((F.obj M).map (homOfLE h).op).val.app (op U)) x))
          (fun x : M.val.obj (op (m, U)) ↦
            M.val.map (Prod.mkHom (homOfLE h) (𝟙 U)).op x)) := by
  apply ordinary_restriction_existsUnique (ProEt.topology X)
    (coefficients C X) (transition C τ X) (StrictTower.coefficients B X)
    (fun n ↦ (constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (φ n)))
  intro n
  rw [← Functor.map_comp]
  exact congrArg ((constantSheaf (ProEt.topology X) CommRingCat.{u + 1}).map)
    (CommRingCat.hom_ext (compatible n))


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The unique ordinary restriction functor with the prescribed section formulas.
Source: Stacks 03CZ (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def rhoOrdinary (X : Scheme.{u}) :=
  (rhoOrdinary_existsUnique C τ B φ X hφ).choose
attribute [local irreducible] rhoOrdinary



set_option synthInstance.maxSize 64 in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem rho_section_type (X : Scheme.{u}) (M : Modules C τ X)
    (n : ℕ) (U : X.ProEt) :
    ((((rhoOrdinary C τ B φ hφ X).obj M).obj (op n)).val.obj (op U) : Type (u + 1)) =
      (M.val.obj (op (n, U)) : Type (u + 1))  := by
  have e : rhoOrdinary C τ B φ hφ X ⋙
      (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) =
      SemilinearSections.evaluation (ProEt.topology X) (coefficients C X)
        (transition C τ X) n ⋙ levelRestriction C B φ X n := by
    unfold rhoOrdinary
    exact (rhoOrdinary_existsUnique C τ B φ X hφ).choose_spec.1.1 n
  exact congrArg (fun N : StrictTower.Modules B X ↦ (N.val.obj (op U) : Type (u + 1)))
    (Functor.congr_obj e M)


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem rho_transition (X : Scheme.{u}) (M : Modules C τ X)
    (n m : ℕ) (h : n ≤ m) (U : X.ProEt) :
    HEq (fun x ↦ ((((rhoOrdinary C τ B φ hφ X).obj M).map
      (homOfLE h).op).val.app (op U)) x)
      (fun x : M.val.obj (op (m, U)) ↦
        M.val.map (Prod.mkHom (homOfLE h) (𝟙 U)).op x) := by
  unfold rhoOrdinary
  exact (rhoOrdinary_existsUnique C τ B φ X hφ).choose_spec.1.2 M n m h U
section OrdinaryScalarProof
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem transition_transport
    {A B D E M N : Type u} (hD : D = M) (hE : E = N)
    (a : A → B) (b : B → E) (c : A → D) (d : D → E)
    (l : B → N) (m : A → M) (t : M → N)
    (hb : HEq b l) (hc : HEq c m) (hd : HEq d t)
    (ht : ∀ x, l (a x) = t (m x)) : ∀ x, b (a x) = d (c x) := by
  subst D E
  rw [eq_of_heq hb, eq_of_heq hc, eq_of_heq hd]
  exact ht

private theorem post_eq_sections
    {A B : Type*} [Category A] [Category B] {J : GrothendieckTopology B}
    {S : Sheaf J RingCat} {F G H : A ⥤ SheafOfModules.{u + 1} S}
    (e : F ≅ G) (h : G = H) (M : A) (U : Bᵒᵖ) :
    HEq (fun x ↦ ((e ≪≫ eqToIso h).hom.app M).val.app U x)
      (fun x ↦ (e.hom.app M).val.app U x) := by
  subst H
  rfl


private theorem normalized_inverse {A B : Type u} (f : A → B) (g : B → A)
    (h : ∀ x, f (g x) = x) (hf : ∀ x, HEq (f x) x) (x : B) : HEq (g x) x :=
  (hf (g x)).symm.trans (heq_of_eq (h x))
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem normalized_apply {A B D : Type u} (hA : A = D) (hB : B = D)
    (f : A → B) (hf : HEq f (fun x : D ↦ x)) (x : A) : HEq (f x) x := by
  subst A B
  exact heq_of_eq (congrFun (eq_of_heq hf) x)

private theorem post_eq_section
    {A D : Type*} [Category A] [Category D] {J : GrothendieckTopology D}
    {S : Sheaf J RingCat} {F G H : A ⥤ SheafOfModules.{u + 1} S}
    (e : F ≅ G) (h : G = H) (M : A) (U : Dᵒᵖ) (x : (F.obj M).val.obj U) :
    HEq (((e ≪≫ eqToIso h).hom.app M).val.app U x)
      ((e.hom.app M).val.app U x) := by
  subst H
  rfl


private theorem restriction_rho_iso
    (D : VaryingRing.OrdinaryScalarRestriction C τ B (fun n ↦ CommRingCat.ofHom (φ n)))
    (X : Scheme.{u}) : ∃ e : D.rho X ≅ rhoOrdinary C τ B φ hφ X,
      ∀ (M : Modules C τ X) (n : ℕ) (H : X.ProEtᵒᵖ)
        (x : (((D.rho X).obj M).obj (op n)).val.obj H),
        HEq (((e.hom.app M).app (op n)).val.app H x) x := by
  have he (n : ℕ) : rhoOrdinary C τ B φ hφ X ⋙
      (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) =
      SemilinearSections.evaluation (ProEt.topology X) (coefficients C X)
        (transition C τ X) n ⋙ levelRestriction C B φ X n := by
    unfold rhoOrdinary
    exact (rhoOrdinary_existsUnique C τ B φ X hφ).choose_spec.1.1 n
  let e (n : ℕ) :
      D.rho X ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) ≅
      rhoOrdinary C τ B φ hφ X ⋙
        (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) :=
    D.level X n ≪≫ eqToIso (he n).symm
  let t (M : VaryingRing.Modules C τ X) : (D.rho X).obj M ⟶
      (rhoOrdinary C τ B φ hφ X).obj M :=
    NatTrans.ofOpSequence (fun n ↦ (e n).hom.app M) (by
      intro n
      ext U x
      exact transition_transport
        (A := (((D.rho X).obj M).obj (op (n + 1))).val.obj U)
        (B := (((D.rho X).obj M).obj (op n)).val.obj U)
        (rho_section_type C τ B φ hφ X M (n + 1) U.unop)
        (rho_section_type C τ B φ hφ X M n U.unop)
        _ _ _ _ _ _ _
        (post_eq_sections (D.level X n) (he n).symm M U)
        (post_eq_sections (D.level X (n + 1)) (he (n + 1)).symm M U)
        (rho_transition C τ B φ hφ X M n (n + 1) (Nat.le_succ n) U.unop)
        (D.transitions X M n U) x)
  let eM (M : VaryingRing.Modules C τ X) : (D.rho X).obj M ≅
      (rhoOrdinary C τ B φ hφ X).obj M :=
    NatIso.ofComponents (fun n ↦ (e n.unop).app M)
      (fun f ↦ (t M).naturality f)
  refine ⟨NatIso.ofComponents eM (by
    intro M N f
    apply NatTrans.ext
    funext n
    exact (e n.unop).hom.naturality f), ?_⟩
  intro M n H x
  have ht := post_eq_section (D.level X n) (he n).symm M H x
  apply HEq.trans ht
  exact D.level_sections X n M H x


end OrdinaryScalarProof


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Scalar restriction is exact without coefficient flatness.
Source: Stacks 03CZ (blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: the ordinary functor leaves underlying additive sheaves and all transition
maps unchanged. Kernels and sheafified cokernels therefore have the same restricted
actions. Componentwise exactness gives additivity and both preservation assertions. -/
theorem rhoOrdinary_exact (X : Scheme.{u}) :
    (rhoOrdinary C τ B φ hφ X).Additive ∧
      PreservesFiniteLimits (rhoOrdinary C τ B φ hφ X) ∧
        PreservesFiniteColimits (rhoOrdinary C τ B φ hφ X)  := by
  have hψ : ∀ n, CommRingCat.ofHom (φ (n + 1)) ≫ τ n = CommRingCat.ofHom (φ n) :=
    fun n ↦ CommRingCat.hom_ext (hφ n)
  obtain ⟨D⟩ := VaryingRing.ordinaryScalarRestriction C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ
  obtain ⟨e, _⟩ := restriction_rho_iso C τ B φ hφ D X
  let dAX : (D.rho X).Additive := D.additive X
  let dLX : PreservesFiniteLimits (D.rho X) := D.limits X
  let dCX : PreservesFiniteColimits (D.rho X) := D.colimits X
  exact ⟨Functor.additive_of_iso (F := D.rho X) e,
    preservesFiniteLimits_of_natIso (F := D.rho X) e,
    preservesFiniteColimits_of_natIso (F := D.rho X) e⟩

/-- Additivity of scalar restriction. Source: Stacks 03CZ
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
instance rho_additive (X : Scheme.{u}) : (rhoOrdinary C τ B φ hφ X).Additive :=
  (rhoOrdinary_exact C τ B φ hφ X).1

/-- Left exactness of scalar restriction. Source: Stacks 03CZ
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
instance rho_limits (X : Scheme.{u}) :
    PreservesFiniteLimits (rhoOrdinary C τ B φ hφ X) :=
  (rhoOrdinary_exact C τ B φ hφ X).2.1

/-- Right exactness of scalar restriction. Source: Stacks 03CZ
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
instance rho_colimits (X : Scheme.{u}) :
    PreservesFiniteColimits (rhoOrdinary C τ B φ hφ X) :=
  (rhoOrdinary_exact C τ B φ hφ X).2.2

/-- Exact scalar restriction on ordinary derived systems.
Source: Stacks 03CZ (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
abbrev rho (X : Scheme.{u}) := (rhoOrdinary C τ B φ hφ X).mapDerivedCategory



/-- Direct image and scalar restriction commute by the identity on component sections.
Source: the ring-sheaf change adjunction; Stacks 03CZ and 03D7
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: both composites evaluate to M_n(U ×_Y X), with the B action through phi_n.
The identity is linear, natural in U, n and M, and invertible. Its components on
all sections uniquely determine the comparison. -/
theorem rhoPushOrdinary_existsUnique {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃! e : rhoOrdinary C τ B φ hφ X ⋙ StrictTower.towerDirectImage B f ≅
      push C τ f ⋙ rhoOrdinary C τ B φ hφ Y,
      ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
        HEq (fun x ↦ ((((e.hom.app M).app (op n)).val.app (op U)) x))
          (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x) := by
  have hψ : ∀ n, CommRingCat.ofHom (φ (n + 1)) ≫ τ n = CommRingCat.ofHom (φ n) :=
    fun n ↦ CommRingCat.hom_ext (hφ n)
  obtain ⟨D⟩ := VaryingRing.ordinaryScalarRestriction C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ
  obtain ⟨G⟩ := VaryingRing.ordinaryScalarAdjunctions C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ D
  obtain ⟨aX, haX⟩ := restriction_rho_iso C τ B φ hφ D X
  obtain ⟨aY, haY⟩ := restriction_rho_iso C τ B φ hφ D Y
  let d := Functor.isoWhiskerRight aX.symm (StrictTower.towerDirectImage B f) ≪≫
    (G.d f).symm ≪≫ Functor.isoWhiskerLeft (VaryingRing.push C τ f) aY
  have hd : ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ (((d.hom.app M).app (op n)).val.app (op U)) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x) := by
    intro M n U
    apply normalized_function
      (rho_section_type C τ B φ hφ X M n ((proEtaleBaseChange f).obj U))
      (rho_section_type C τ B φ hφ Y ((VaryingRing.push C τ f).obj M) n U)
    intro x
    let y := (((aX.inv.app M).app (op n)).val.app
      (op ((proEtaleBaseChange f).obj U))) x
    let z := ((((G.d f).inv.app M).app (op n)).val.app (op U)) y
    have hy : HEq y x := normalized_inverse
      (fun q ↦ (((aX.hom.app M).app (op n)).val.app
        (op ((proEtaleBaseChange f).obj U))) q)
      (fun q ↦ (((aX.inv.app M).app (op n)).val.app
        (op ((proEtaleBaseChange f).obj U))) q)
      (fun q ↦ congrArg (fun v ↦ (v.app (op n)).val.app
        (op ((proEtaleBaseChange f).obj U)) q) (aX.inv_hom_id_app M))
      (haX M n (op ((proEtaleBaseChange f).obj U))) x
    have hz : HEq z y := normalized_inverse
      (fun q ↦ ((((G.d f).hom.app M).app (op n)).val.app (op U)) q)
      (fun q ↦ ((((G.d f).inv.app M).app (op n)).val.app (op U)) q)
      (fun q ↦ congrArg (fun v ↦ (v.app (op n)).val.app (op U) q)
        ((G.d f).inv_hom_id_app M)) (G.d_sections f M n (op U)) y
    exact (haY ((VaryingRing.push C τ f).obj M) n (op U) z).trans
      (hz.trans hy)
  obtain ⟨e, he⟩ := tower_normalized_transport
    (congrArg (fun F : Modules C τ X ⥤ Modules C τ Y ↦
      F ⋙ rhoOrdinary C τ B φ hφ Y) (push_eq C τ f).symm) d
    (fun M n U ↦ M.val.obj (op (n.unop, (proEtaleBaseChange f).obj U)))
    (fun M n U ↦ hd M n.unop U)
  refine ⟨e, (fun M n U ↦ he M (op n) U), ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply NatTrans.ext
  funext n
  ext U x
  exact congrFun (eq_of_heq ((he' M n.unop U.unop).trans
    (he M n U.unop).symm)) x

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem restriction_pull_mate_normalization_canonical
    (D : VaryingRing.OrdinaryScalarRestriction C τ B (fun n ↦ CommRingCat.ofHom (φ n)))
    (G : VaryingRing.OrdinaryScalarAdjunctions C τ B (fun n ↦ CommRingCat.ofHom (φ n)) D)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : rhoOrdinary C τ B φ hφ X ⋙ StrictTower.towerDirectImage B f ≅
      VaryingRing.push C τ f ⋙ rhoOrdinary C τ B φ hφ Y)
    (he : ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op n)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) :
    ∃ (aX : D.rho X ≅ rhoOrdinary C τ B φ hφ X)
      (aY : D.rho Y ≅ rhoOrdinary C τ B φ hφ Y),
      HEq ((mateEquiv (VaryingRing.moduleAdj C τ f)
        (VaryingRing.scalarTowerAdj B f)).symm e.inv).natTrans
        (Functor.whiskerRight aY.inv (StrictTower.towerPullback B f) ≫
          (G.b f).inv ≫ Functor.whiskerLeft (VaryingRing.pull C τ f) aX.hom) := by
  obtain ⟨aX, haX⟩ := restriction_rho_iso C τ B φ hφ D X
  obtain ⟨aY, haY⟩ := restriction_rho_iso C τ B φ hφ D Y
  let d := Functor.isoWhiskerLeft (VaryingRing.push C τ f) aY.symm ≪≫
    G.d f ≪≫ Functor.isoWhiskerRight aX (StrictTower.towerDirectImage B f)
  have hd : d.hom = e.inv := by
    apply (cancel_mono e.hom).mp
    erw [e.inv_hom_id]
    apply NatTrans.ext
    funext M
    apply NatTrans.ext
    funext n
    ext U x
    let y := (((aY.inv.app ((VaryingRing.push C τ f).obj M)).app n).val.app U) x
    let z := ((((G.d f).hom.app M).app n).val.app U) y
    let t := (((aX.hom.app M).app n).val.app
      ((proEtaleBaseChange f).op.obj U)) z
    have hy : HEq y x := normalized_inverse
      (fun q ↦ (((aY.hom.app ((VaryingRing.push C τ f).obj M)).app n).val.app U) q)
      (fun q ↦ (((aY.inv.app ((VaryingRing.push C τ f).obj M)).app n).val.app U) q)
      (fun q ↦ congrArg (fun v ↦ (v.app n).val.app U q)
        (aY.inv_hom_id_app ((VaryingRing.push C τ f).obj M)))
      (haY ((VaryingRing.push C τ f).obj M) n.unop U) x
    have hz := G.d_sections f M n.unop U y
    have ht := haX M n.unop ((proEtaleBaseChange f).op.obj U) z
    have hh := normalized_apply
      (rho_section_type C τ B φ hφ X M n.unop ((proEtaleBaseChange f).obj U.unop))
      (rho_section_type C τ B φ hφ Y ((VaryingRing.push C τ f).obj M) n.unop U.unop)
      _ (he M n.unop U.unop) t
    exact eq_of_heq (hh.trans (ht.trans (hz.trans hy)))
  let w := ((TwoSquare.mk _ _ _ _ (G.b f).inv).whiskerTop aY.inv).whiskerBottom aX.hom
  have hw : mateEquiv (VaryingRing.moduleAdj C τ f)
      (VaryingRing.scalarTowerAdj B f) w = TwoSquare.mk _ _ _ _ d.hom := by
    dsimp only [w]
    erw [mateEquiv_whiskerTop_whiskerBottom]
    apply TwoSquare.ext
    intro N
    change aY.inv.app ((VaryingRing.push C τ f).obj N) ≫
      (mateEquiv (VaryingRing.moduleAdj C τ f) (VaryingRing.scalarTowerAdj B f)
        (G.b f).inv).natTrans.app N ≫
        (StrictTower.towerDirectImage B f).map (aX.hom.app N) = d.hom.app N
    rw [G.mate]
    rfl
  refine ⟨aX, aY, ?_⟩
  rw [← hd]
  change HEq ((mateEquiv (VaryingRing.moduleAdj C τ f)
    (VaryingRing.scalarTowerAdj B f)).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans _
  rw [← hw, Equiv.symm_apply_apply]
  exact HEq.rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem restriction_pull_mate_normalization
    (D : VaryingRing.OrdinaryScalarRestriction C τ B (fun n ↦ CommRingCat.ofHom (φ n)))
    (G : VaryingRing.OrdinaryScalarAdjunctions C τ B (fun n ↦ CommRingCat.ofHom (φ n)) D)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules C τ X ⥤ Modules C τ Y) [F.IsRightAdjoint]
    (hF : F = VaryingRing.push C τ f)
    (e : rhoOrdinary C τ B φ hφ X ⋙ StrictTower.towerDirectImage B f ≅
      F ⋙ rhoOrdinary C τ B φ hφ Y)
    (he : ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op n)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) :
    ∃ (aX : D.rho X ≅ rhoOrdinary C τ B φ hφ X)
      (aY : D.rho Y ≅ rhoOrdinary C τ B φ hφ Y),
      HEq ((mateEquiv (Adjunction.ofIsRightAdjoint F)
        (VaryingRing.scalarTowerAdj B f)).symm e.inv).natTrans
        (Functor.whiskerRight aY.inv (StrictTower.towerPullback B f) ≫
          (G.b f).inv ≫ Functor.whiskerLeft (VaryingRing.pull C τ f) aX.hom) := by
  subst F
  exact restriction_pull_mate_normalization_canonical C τ B φ hφ D G f e he

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_pull_mate_normalization {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules C τ X ⥤ Modules C τ Y) [F.IsRightAdjoint]
    (hF : F = VaryingRing.push C τ f)
    (e : rhoOrdinary C τ B φ hφ X ⋙ StrictTower.towerDirectImage B f ≅
      F ⋙ rhoOrdinary C τ B φ hφ Y)
    (he : ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op n)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x)) :
    ∃ (D : VaryingRing.OrdinaryScalarComparison C τ B (fun n ↦ CommRingCat.ofHom (φ n)))
      (aX : D.rho X ≅ rhoOrdinary C τ B φ hφ X)
      (aY : D.rho Y ≅ rhoOrdinary C τ B φ hφ Y),
      HEq ((mateEquiv (Adjunction.ofIsRightAdjoint F)
        (VaryingRing.scalarTowerAdj B f)).symm e.inv).natTrans
        (Functor.whiskerRight aY.inv (StrictTower.towerPullback B f) ≫
          (D.b f).inv ≫ Functor.whiskerLeft (VaryingRing.pull C τ f) aX.hom) := by
  have hψ : ∀ n, CommRingCat.ofHom (φ (n + 1)) ≫ τ n = CommRingCat.ofHom (φ n) :=
    fun n ↦ CommRingCat.hom_ext (hφ n)
  obtain ⟨D⟩ := VaryingRing.ordinaryScalarComparison C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ
  let E : VaryingRing.OrdinaryScalarRestriction C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)) :=
    { rho := D.rho
      additive := D.additive
      limits := D.limits
      colimits := D.colimits
      level := D.level
      level_sections := D.level_sections
      transitions := D.transitions }
  let G : VaryingRing.OrdinaryScalarAdjunctions C τ B
      (fun n ↦ CommRingCat.ofHom (φ n)) E :=
    { b := D.b
      d := D.d
      d_sections := D.d_sections
      mate := D.mate
      a := D.a
      open_unit := D.open_unit }
  obtain ⟨aX, aY, h⟩ := restriction_pull_mate_normalization C τ B φ hφ E G f F hF e he
  exact ⟨D, aX, aY, h⟩

/-- The ordinary inverse-image scalar comparison is the transpose of the uniquely
section-normalized direct-image comparison. Source: the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def rhoPullInv {X Y : Scheme.{u}} (f : X ⟶ Y) :
    rhoOrdinary C τ B φ hφ Y ⋙ StrictTower.towerPullback B f ⟶
      pull C τ f ⋙ rhoOrdinary C τ B φ hφ X :=
  (mateEquiv (ordinaryAdj C τ f)
    ((proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
      (StrictTower.coefficients B X) (StrictTower.constantRingIso B f)).whiskerRight ℕᵒᵖ)).symm
    (rhoPushOrdinary_existsUnique C τ B φ hφ f).choose.inv


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The identified-coefficient inverse-image scalar comparison is invertible.
Source: the ring-sheaf change adjunction; Stacks 03EK
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: on underlying inverse-image additive sheaves this transpose is the identity.
The scalar action is restricted along the identified constant maps, so the identity
has an inverse, simultaneously in the coefficient index. -/
theorem rhoPullInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (rhoPullInv C τ B φ hφ f) := by
  have hψ : ∀ n, CommRingCat.ofHom (φ (n + 1)) ≫ τ n = CommRingCat.ofHom (φ n) :=
    fun n ↦ CommRingCat.hom_ext (hφ n)
  obtain ⟨D⟩ := VaryingRing.ordinaryScalarRestriction C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ
  obtain ⟨G⟩ := VaryingRing.ordinaryScalarAdjunctions C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ D
  obtain ⟨aX, aY, h⟩ := restriction_pull_mate_normalization C τ B φ hφ D G f
    (push C τ f) (push_eq C τ f)
    (rhoPushOrdinary_existsUnique C τ B φ hφ f).choose
    (rhoPushOrdinary_existsUnique C τ B φ hφ f).choose_spec.1
  let b := Functor.isoWhiskerRight aY.symm (StrictTower.towerPullback B f) ≪≫
    (G.b f).symm ≪≫ Functor.isoWhiskerLeft (VaryingRing.pull C τ f) aX
  let g := b.hom
  have hg : IsIso g := b.isIso_hom
  exact @isIso_of_heq _ _ _ _ _ _ _
    (congrArg (fun F ↦ F ⋙ rhoOrdinary C τ B φ hφ X) (pull_eq C τ f))
    (rhoPullInv C τ B φ hφ f) g h hg


/-- The canonical scalar-restriction inverse-image comparison after exact localization.
Source: the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def rhoP {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P C τ f ⋙ rho C τ B φ hφ X ≅ rho C τ B φ hφ Y ⋙ StrictTower.G B f :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
  Functor.mapDerivedCategoryNatIso
    (@asIso _ _ _ _ (rhoPullInv C τ B φ hφ f) (rhoPullInv_isIso C τ B φ hφ f)).symm ≪≫
  Functor.mapDerivedCategoryCompIso _ _

/-- The direct-image comparison is the actual derived mate of rhoP inverse.
Source: the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def rhoR {X Y : Scheme.{u}} (f : X ⟶ Y) :
    R C τ f ⋙ rho C τ B φ hφ Y ⟶ rho C τ B φ hφ X ⋙ StrictTower.R B f :=
  mateEquiv (adj C τ f) (StrictTower.adj B f) (rhoP C τ B φ hφ f).inv

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_derived_mate_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Modules C τ X ⥤ Modules C τ Y) [F.IsRightAdjoint] [F.Additive]
    [F.leftAdjoint.Additive] [PreservesFiniteLimits F.leftAdjoint]
    [PreservesFiniteColimits F.leftAdjoint]
    (hF : F = VaryingRing.push C τ f)
    (e : rhoOrdinary C τ B φ hφ X ⋙ StrictTower.towerDirectImage B f ≅
      F ⋙ rhoOrdinary C τ B φ hφ Y)
    (he : ∀ (M : Modules C τ X) (n : ℕ) (U : Y.ProEt),
      HEq (fun x ↦ ((e.hom.app M).app (op n)).val.app (op U) x)
        (fun x : M.val.obj (op (n, (proEtaleBaseChange f).obj U)) ↦ x))
    (s : rhoOrdinary C τ B φ hφ Y ⋙ StrictTower.towerPullback B f ≅
      F.leftAdjoint ⋙ rhoOrdinary C τ B φ hφ X)
    (hs : s.hom = ((mateEquiv (Adjunction.ofIsRightAdjoint F)
      (VaryingRing.scalarTowerAdj B f)).symm e.inv).natTrans) :
    IsIso (mateEquiv (Adjunction.ofIsRightAdjoint F).mapDerivedCategoryRightDerivedAdjunction
      (StrictTower.adj B f) (Functor.mapDerivedCategorySquareIso s).hom).natTrans := by
  subst F
  obtain ⟨D, aX, aY, h⟩ := scalar_pull_mate_normalization C τ B φ hφ f
    (VaryingRing.push C τ f) rfl e he
  let q : rhoOrdinary C τ B φ hφ Y ⋙ StrictTower.towerPullback B f ≅
      VaryingRing.pull C τ f ⋙ rhoOrdinary C τ B φ hφ X :=
    Functor.isoWhiskerRight aY.symm (StrictTower.towerPullback B f) ≪≫
      (D.b f).symm ≪≫ Functor.isoWhiskerLeft (VaryingRing.pull C τ f) aX
  have hq : s = q := by
    apply Iso.ext
    rw [hs]
    exact eq_of_heq h
  rw [hq]
  let rAX : (rhoOrdinary C τ B φ hφ X).Additive := rho_additive C τ B φ hφ X
  let rAY : (rhoOrdinary C τ B φ hφ Y).Additive := rho_additive C τ B φ hφ Y
  let rLX : PreservesFiniteLimits (rhoOrdinary C τ B φ hφ X) := rho_limits C τ B φ hφ X
  let rLY : PreservesFiniteLimits (rhoOrdinary C τ B φ hφ Y) := rho_limits C τ B φ hφ Y
  let rCX : PreservesFiniteColimits (rhoOrdinary C τ B φ hφ X) := rho_colimits C τ B φ hφ X
  let rCY : PreservesFiniteColimits (rhoOrdinary C τ B φ hφ Y) := rho_colimits C τ B φ hφ Y
  let pA : (VaryingRing.pull C τ f).Additive := VaryingRing.pullAdditive C τ f
  let pL : PreservesFiniteLimits (VaryingRing.pull C τ f) := VaryingRing.pullLimits C τ f
  let pC : PreservesFiniteColimits (VaryingRing.pull C τ f) := VaryingRing.pullColimits C τ f
  let dAX : (D.rho X).Additive := D.additive X
  let dAY : (D.rho Y).Additive := D.additive Y
  let dLX : PreservesFiniteLimits (D.rho X) := D.limits X
  let dLY : PreservesFiniteLimits (D.rho Y) := D.limits Y
  let dCX : PreservesFiniteColimits (D.rho X) := D.colimits X
  let dCY : PreservesFiniteColimits (D.rho Y) := D.colimits Y
  let AX := Functor.mapDerivedCategoryNatIso aX
  let AY := Functor.mapDerivedCategoryNatIso aY
  have hloc : (Functor.mapDerivedCategorySquareIso q).hom =
      Functor.whiskerRight AY.inv (StrictTower.G B f) ≫
        (VaryingRing.scalarB D f).inv ≫
          Functor.whiskerLeft (VaryingRing.G C τ f) AX.hom := by
    have ht := derived_square_conjugate aY.symm (D.b f).symm aX
    simp only [Functor.square_symm_hom, Functor.mapDerivedCategoryNatIso_symm,
      ] at ht
    exact ht
  let w := ((TwoSquare.mk _ _ _ _ (VaryingRing.scalarB D f).inv).whiskerTop
    AY.inv).whiskerBottom AX.hom
  have hw : (Functor.mapDerivedCategorySquareIso q).hom = w.natTrans := by
    simpa only [w, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      TwoSquare.mk, TwoSquare.natTrans, Category.assoc] using hloc
  rw [hw]
  change IsIso (mateEquiv (VaryingRing.adj C τ f) (StrictTower.adj B f) w).natTrans
  dsimp only [w]
  rw [mateEquiv_whiskerTop_whiskerBottom]
  have hψ : ∀ n, CommRingCat.ofHom (φ (n + 1)) ≫ τ n = CommRingCat.ofHom (φ n) :=
    fun n ↦ CommRingCat.hom_ext (hφ n)
  have := VaryingRing.scalarD_isIso D hψ f
  dsimp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.mk,
    TwoSquare.natTrans]
  change IsIso ((Functor.whiskerLeft (VaryingRing.P C τ f) AY.inv ≫
    VaryingRing.scalarD D f) ≫ Functor.whiskerRight AX.hom (StrictTower.R B f))
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The specified derived direct-image mate is invertible.
Source: the ring-sheaf change adjunction; Zheng 4.10
(blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: evaluation of this mate is the canonical scalar-restriction direct-image
comparison of the ring-sheaf adjunction, by its adjunct clause. Each is invertible.
Levelwise detection of quasi-isomorphisms then gives invertibility on towers.
This uses detection of isomorphisms and never faithfulness on morphisms. -/
theorem rhoR_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (rhoR C τ B φ hφ f) := by
  have h := scalar_derived_mate_isIso C τ B φ hφ f (push C τ f) (push_eq C τ f)
    (rhoPushOrdinary_existsUnique C τ B φ hφ f).choose
    (rhoPushOrdinary_existsUnique C τ B φ hφ f).choose_spec.1
    (@asIso _ _ _ _ (rhoPullInv C τ B φ hφ f) (rhoPullInv_isIso C τ B φ hφ f)) rfl
  change IsIso (mateEquiv (adj C τ f) (StrictTower.adj B f)
    (Functor.mapDerivedCategorySquareIso
      (@asIso _ _ _ _ (rhoPullInv C τ B φ hφ f)
        (rhoPullInv_isIso C τ B φ hφ f))).hom).natTrans at h
  change IsIso (mateEquiv (adj C τ f) (StrictTower.adj B f)
    (rhoP C τ B φ hφ f).inv).natTrans
  have he : (rhoP C τ B φ hφ f).inv =
      (Functor.mapDerivedCategorySquareIso
        (@asIso _ _ _ _ (rhoPullInv C τ B φ hφ f)
          (rhoPullInv_isIso C τ B φ hφ f))).hom := by
    unfold rhoP
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_inv, Iso.trans_hom,
      Iso.symm_inv, Iso.symm_hom, derived_iso_symm_inv, Category.assoc]
  rw [he]
  exact h

/-- The open scalar comparison is fixed by the open-adjunction transpose of rhoP.
Source: Stacks 03DI and the ring-sheaf change adjunction
(blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def rhoJInv {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    rho C τ B φ hφ U ⋙ StrictTower.J B j ⟶ J C τ j ⋙ rho C τ B φ hφ X :=
  (mateEquiv (jAdj C τ j) (StrictTower.jAdj B j)).symm (rhoP C τ B φ hφ j).hom

section ScalarOpenComparison

private theorem inverse_mate_support_isIso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {R : B ⥤ A} {l : D ⥤ E} {r : E ⥤ D}
    (a : L ⊣ R) (b : l ⊣ r) (F : A ⥤ D) (G : B ⥤ E)
    (e : R ⋙ F ≅ G ⋙ r) [IsIso a.unit]
    (hc : ∀ M, IsIso (b.counit.app (G.obj (L.obj M)))) :
    IsIso ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ e.hom)).natTrans := by
  have hi (M : A) : IsIso
      (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ e.hom)).natTrans.app M) := by
    have := hc M
    dsimp only [mateEquiv, Equiv.symm, Equiv.coe_fn_mk, TwoSquare.mk,
      TwoSquare.natTrans, NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.whiskerRight_app, Functor.comp_map, Functor.associator_inv_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app]
    dsimp only [Functor.comp_obj]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    have : IsIso (a.unit.app M) := inferInstance
    have h₁ : IsIso (l.map (F.map (a.unit.app M))) := inferInstance
    have h₂ : IsIso (l.map (e.hom.app (L.obj M))) := inferInstance
    have h₃ : IsIso (b.counit.app (G.obj (L.obj M))) := hc M
    erw [Category.comp_id]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem scalar_open_existsIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    Nonempty (J C τ j ⋙ rho C τ B φ hφ X ≅
      rho C τ B φ hφ U ⋙ StrictTower.J B j) := by
  have hψ : ∀ n, CommRingCat.ofHom (φ (n + 1)) ≫ τ n = CommRingCat.ofHom (φ n) := by
    intro n
    exact CommRingCat.hom_ext (hφ n)
  obtain ⟨D⟩ := VaryingRing.ordinaryScalarRestriction C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ
  obtain ⟨G⟩ := VaryingRing.ordinaryScalarAdjunctions C τ B
    (fun n ↦ CommRingCat.ofHom (φ n)) hψ D
  obtain ⟨aX, _⟩ := restriction_rho_iso C τ B φ hφ D X
  obtain ⟨aU, _⟩ := restriction_rho_iso C τ B φ hφ D U
  let e : extension C τ j ⋙ rhoOrdinary C τ B φ hφ X ≅
      rhoOrdinary C τ B φ hφ U ⋙ StrictTower.towerJ B j :=
    eqToIso (congrArg (fun F ↦ F ⋙ rhoOrdinary C τ B φ hφ X) (extension_eq C τ j)) ≪≫
      Functor.isoWhiskerLeft (VaryingRing.extension C τ j) aX.symm ≪≫
      G.a j ≪≫ Functor.isoWhiskerRight aU (StrictTower.towerJ B j)
  exact ⟨(Functor.mapDerivedCategoryCompIso
      (extension C τ j) (rhoOrdinary C τ B φ hφ X)).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫
      Functor.mapDerivedCategoryCompIso (rhoOrdinary C τ B φ hφ U) (StrictTower.towerJ B j)⟩

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Open extension commutes with scalar restriction under its ordinary section units.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-proper-open-mate-pasting).
Proof: localized extension is the same module on the open and zero on its complement.
Scalar restriction keeps both pieces, and its open-adjunction transpose is the
identity on the original sections. Exact localization preserves this comparison. -/
theorem rhoJInv_isIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (rhoJInv C τ B φ hφ j) := by
  have := jAdj_unit_isIso C τ j
  have := StrictTower.jAdj_unit_isIso B j
  let ff := (StrictTower.jAdj B j).fullyFaithfulLOfIsIsoUnit
  have := ff.full
  have := ff.faithful
  obtain ⟨e⟩ := scalar_open_existsIso C τ B φ hφ j
  have hc (M : Derived C τ U) :
      IsIso ((StrictTower.jAdj B j).counit.app
        ((rho C τ B φ hφ X).obj ((J C τ j).obj M))) :=
    (StrictTower.jAdj B j).isIso_counit_app_of_iso (e.app M)
  unfold rhoJInv
  exact inverse_mate_support_isIso
    (L := J C τ j) (R := P C τ j)
    (l := StrictTower.J B j) (r := StrictTower.G B j)
    (jAdj C τ j) (StrictTower.jAdj B j)
    (rho C τ B φ hφ U) (rho C τ B φ hφ X) (rhoP C τ B φ hφ j) hc

end ScalarOpenComparison

/-- The invertible, open-unit-normalized scalar-restriction comparison.
Source: Stacks 03DI (blueprint: lem-sf-semilinear-proper-open-mate-pasting). -/
def rhoJ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    J C τ j ⋙ rho C τ B φ hφ X ≅ rho C τ B φ hφ U ⋙ StrictTower.J B j :=
  (@asIso _ _ _ _ (rhoJInv C τ B φ hφ j) (rhoJInv_isIso C τ B φ hφ j)).symm

end ScalarRestriction

end AlgebraicGeometry.ProEtale.SemilinearProperOpen

namespace SemilinearProperOpenScalarAliases
private alias normalized_apply :=
  AlgebraicGeometry.ProEtale.SemilinearProperOpen.normalized_apply
end SemilinearProperOpenScalarAliases

end ProofEnvironment
