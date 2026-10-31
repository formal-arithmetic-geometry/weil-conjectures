/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.StrictCoefficient.NormalizedCoefficientDiagramSupplement
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement

/-! # Normalized coefficient transition formulas

Source: Stacks Project, Modules on Sites, Tags 03CY, 03D2 and 03EL.
(blueprint: lem-pur-normalized-kappa-transition-calculus).

The scalar-extension associator multiplies coefficients. The normalized kappa
comparison transports arbitrary generalized inverse-image sections, and its
inverse contracts the coefficient through the recorded ring square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] SheafOfModules.monoidalCategory
universe w uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open SheafOfModules
open scoped TensorProduct ChangeOfRings
namespace CategoryTheory.CochainPullback.StrictCoefficient.KappaCalculation

attribute [local irreducible] scalarComp scalarUnit extensionAdjunction
attribute [local irreducible] generator
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
set_option Elab.async false

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Auxiliary map or section predicate for the normalized kappa calculation.
Source: Stacks 03EL, strict totalization step 5
(blueprint: lem-pur-normalized-kappa-transition-calculus). -/
def semilinearSectionMap {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {P : Complex A} {Q : Complex B} (f : (extend a).obj P ⟶ Q) (p : ℤ) :
    (underlying A).obj (P.X p) ⟶ (underlying B).obj (Q.X p) :=
  insertion a (P.X p) ≫ (underlying B).map (f.f p)

/-- Auxiliary map or section predicate for the normalized kappa calculation.
Source: Stacks 03EL, strict totalization step 5
(blueprint: lem-pur-normalized-kappa-transition-calculus). -/
def inverseSectionMap (d : Diagram (J := J) (K := K)) {i j : Index} (a : i ⟶ j)
    {P : Complex (d.R.obj i)} {Q : Complex (d.R.obj j)}
    (f : (extend (d.R.map a)).obj P ⟶ Q) (p : ℤ) :
    (underlying (d.RI.obj i)).obj ((d.algebraic i).modules.obj (P.X p)) ⟶
      (underlying (d.RI.obj j)).obj ((d.algebraic j).modules.obj (Q.X p)) :=
  (d.algebraic i).moduleUnderlying.hom.app (P.X p) ≫
    d.inverse.map (semilinearSectionMap (d.R.map a) f p) ≫
      (d.algebraic j).moduleUnderlying.inv.app (Q.X p)

/-- Auxiliary map or section predicate for the normalized kappa calculation.
Source: Stacks 03EL, strict totalization step 5
(blueprint: lem-pur-normalized-kappa-transition-calculus). -/
def diagramInsertion (d : Diagram (J := J) (K := K)) {i j : Index} (a : i ⟶ j)
    (M : Modules (d.R.obj i)) :
    (underlying (d.RI.obj i)).obj ((d.algebraic i).modules.obj M) ⟶
      (underlying (d.RI.obj j)).obj
        ((d.algebraic j).modules.obj ((extensionFunctor (d.R.map a)).obj M)) :=
  (d.algebraic i).moduleUnderlying.hom.app M ≫
    d.inverse.map (insertion (d.R.map a) M) ≫
      (d.algebraic j).moduleUnderlying.inv.app ((extensionFunctor (d.R.map a)).obj M)

/-- Auxiliary map or section predicate for the normalized kappa calculation.
Source: Stacks 03EL, strict totalization step 5
(blueprint: lem-pur-normalized-kappa-transition-calculus). -/
def diagramPullSection (d : Diagram (J := J) (K := K)) (i : Index)
    (M : Modules (d.R.obj i)) (U : Dᵒᵖ) (b : (d.S.obj i).obj.obj U)
    (x : ((d.algebraic i).modules.obj M).val.obj U) : ((d.L i).obj M).val.obj U :=
  (eqToHom (d.hobj i M).symm).val.app U
    (extensionTmul (d.phi.app i) ((d.algebraic i).modules.obj M) U b x)

/-- Auxiliary map or section predicate for the normalized kappa calculation.
Source: Stacks 03EL, strict totalization step 5
(blueprint: lem-pur-normalized-kappa-transition-calculus). -/
def kappaTransitionForward {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l)
    (r : i ⟶ k) (s : j ⟶ l) (h : a ≫ s = r ≫ b)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj k))
    (f : (extend (d.R.map r)).obj P ⟶ Q) :=
  (extend (d.S.map s)).map (e.kappaC a P).hom ≫
    e.pullArrow s ((extend (d.R.map a)).obj P) ((extend (d.R.map b)).obj Q)
      (squareArrow d.R a b r s h P Q f)

/-- Auxiliary map or section predicate for the normalized kappa calculation.
Source: Stacks 03EL, strict totalization step 5
(blueprint: lem-pur-normalized-kappa-transition-calculus). -/
def kappaTransitionInverse {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l)
    (r : i ⟶ k) (s : j ⟶ l) (h : a ≫ s = r ≫ b)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj k))
    (f : (extend (d.R.map r)).obj P ⟶ Q) :=
  (extend (d.S.map s)).map (e.kappaC a P).inv ≫
    squareArrow d.S a b r s h ((pull (d.ringed i)).obj P)
      ((pull (d.ringed k)).obj Q) (e.pullArrow r P Q f)

/-- Auxiliary map or section predicate for the normalized kappa calculation.
Source: Stacks 03EL, strict totalization step 5
(blueprint: lem-pur-normalized-kappa-transition-calculus). -/
def KappaTransitionValues {d : Diagram (J := J) (K := K)}
    (e : Comparisons d) : Prop :=
  ∀ {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj k))
    (f : (extend (d.R.map r)).obj P ⟶ Q) (p : ℤ) (U : Dᵒᵖ)
    (v : (d.S.obj j).obj.obj U) (z : (d.S.obj i).obj.obj U)
    (x : ((d.algebraic i).modules.obj (P.X p)).val.obj U),
    ((((kappaTransitionForward e a b r s h P Q f).f p).val.app U
      (extensionTmul (d.S.map s) (((extend (d.S.map a)).obj
          ((pull (d.ringed i)).obj P)).X p) U 1
        (extensionTmul (d.S.map a) ((d.L i).obj (P.X p)) U v
          (diagramPullSection d i (P.X p) U z x)))) =
      diagramPullSection d l ((extensionFunctor (d.R.map b)).obj (Q.X p)) U
        ((d.S.map s).hom.app U v *
          (d.S.map b).hom.app U ((d.S.map r).hom.app U z))
        ((diagramInsertion d b (Q.X p)).hom.app U
          ((inverseSectionMap d r f p).hom.app U x))) ∧
    (∀ z' : (d.RI.obj j).obj.obj U,
      (((kappaTransitionInverse e a b r s h P Q f).f p).val.app U
        (extensionTmul (d.S.map s)
          ((d.L j).obj ((extensionFunctor (d.R.map a)).obj (P.X p))) U 1
          (diagramPullSection d j ((extensionFunctor (d.R.map a)).obj (P.X p)) U v
            (z' • (@id (((d.algebraic j).modules.obj
              ((extensionFunctor (d.R.map a)).obj (P.X p))).val.obj U)
                ((diagramInsertion d a (P.X p)).hom.app U x)))))) =
        extensionTmul (d.S.map b) ((d.L k).obj (Q.X p)) U
          ((d.S.map s).hom.app U v *
            (d.phi.app l).hom.app U ((d.RI.map s).hom.app U z'))
          (diagramPullSection d k (Q.X p) U 1
            ((inverseSectionMap d r f p).hom.app U x)))

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem extension_unit {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (M : Modules A) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((extensionAdjunction a).unit.app M).val.app U x = extensionTmul a M U 1 x := by
  unfold extensionAdjunction
  exact (Classical.choose_spec (extensionAdjunction_existsUnique a)).1 M U x

private theorem extension_smul {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (M : Modules A) (U : Cᵒᵖ) (b : B.obj.obj U) (x : M.val.obj U) :
    extensionTmul a M U b x = b • extensionTmul a M U 1 x := by
  let t := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app
      (changeOfRingsPresheaf a M)).app U
  have h := t.hom.map_smul b ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)
  change t ((b * 1) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x) =
    b • t ((1 : B.obj.obj U) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x) at h
  simpa only [mul_one, extensionTmul, extensionFunctor, SheafOfModules.changeOfRings] using h

private theorem extension_map {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {M N : Modules A} (f : M ⟶ N) (U : Cᵒᵖ) (b : B.obj.obj U) (x : M.val.obj U) :
    ((extensionFunctor a).map f).val.app U (extensionTmul a M U b x) =
      extensionTmul a N U b (f.val.app U x) := by
  have h := congrArg (fun z ↦ z.val.app U x) ((extensionAdjunction a).unit.naturality f)
  change ((extensionAdjunction a).unit.app N).val.app U (f.val.app U x) =
    ((extensionFunctor a).map f).val.app U
      (((extensionAdjunction a).unit.app M).val.app U x) at h
  rw [extension_unit, extension_unit] at h
  rw [extension_smul a M, extension_smul a N, map_smul, h]

private theorem extension_hom_ext {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (M : Modules A) (N : Modules B) {f g : (extensionFunctor a).obj M ⟶ N}
    (h : ∀ U x, f.val.app U (extensionTmul a M U 1 x) =
      g.val.app U (extensionTmul a M U 1 x)) : f = g := by
  apply ((extensionAdjunction a).homEquiv M N).injective
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  change f.val.app U (((extensionAdjunction a).unit.app M).val.app U x) =
    g.val.app U (((extensionAdjunction a).unit.app M).val.app U x)
  simpa only [extension_unit] using h U x


private theorem extension_smul_arg {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    (M : Modules A) (U : Cᵒᵖ) (b : B.obj.obj U) (r : A.obj.obj U)
    (x : M.val.obj U) :
    extensionTmul a M U b (r • x) =
      (a.hom.app U r) • extensionTmul a M U b x := by
  let t := ((PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj)).unit.app
      (changeOfRingsPresheaf a M)).app U
  change t (b ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] (r • x)) = _
  rw [← TensorProduct.smul_tmul]
  change t (((a.hom.app U r) * b) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x) = _
  have ht := t.hom.map_smul (a.hom.app U r)
    (b ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x)
  change t (((a.hom.app U r) * b) ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x) =
    (a.hom.app U r) • t (b ⊗ₜ[A.obj.obj U, (a.hom.app U).hom] x) at ht
  exact ht

private theorem insertion_extension_map {A B : Sheaf J CommRingCat.{w}} (a : A ⟶ B)
    {M N : Modules A} (f : M ⟶ N) :
    insertion a M ≫ (underlying B).map ((extensionFunctor a).map f) =
      (underlying A).map f ≫ insertion a N := by
  exact (insertion_naturality a f).symm

private theorem pull_generator_hom_ext {R : Sheaf J CommRingCat.{w}}
    {S : Sheaf K CommRingCat.{w}} (f : RingedPullback R S) (c : Comparison f)
    (M : Modules R) (N : Modules S) {a b : f.L.obj M ⟶ N}
    (h : ∀ (Z : Sheaf J (Type w)) (x : Z ⟶ (underlying R).obj M),
      generator f c x ≫ (underlying S).map a =
        generator f c x ≫ (underlying S).map b) : a = b := by
  apply (cancel_epi ((presentationIso f).inv.app M)).1
  apply extension_hom_ext f.coefficient (f.I.modules.obj M) N
  intro U x
  have ht := congrArg (fun z ↦ z.hom.app U
    ((f.I.moduleUnderlying.hom.app M).hom.app U x))
    (h ((underlying R).obj M) (𝟙 _))
  have hq := c.q_one M U x
  simp only [generator, Functor.map_id, Category.id_comp, Category.assoc] at ht
  have hi := congrArg (fun z ↦ z.hom.app U x) (f.I.moduleUnderlying.hom_inv_id_app M)
  change (f.I.moduleUnderlying.inv.app M).hom.app U
    ((f.I.moduleUnderlying.hom.app M).hom.app U x) = x at hi
  change a.val.app U ((c.q M).hom.app U
    ((f.I.moduleUnderlying.inv.app M).hom.app U
      ((f.I.moduleUnderlying.hom.app M).hom.app U x))) =
    b.val.app U ((c.q M).hom.app U
      ((f.I.moduleUnderlying.inv.app M).hom.app U
        ((f.I.moduleUnderlying.hom.app M).hom.app U x))) at ht
  rw [hi, hq] at ht
  exact ht

private theorem kappa_generator (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) {i j : Index} (a : i ⟶ j)
    (M : Modules (d.R.obj i)) (Z : Sheaf J (Type w))
    (x : Z ⟶ (underlying (d.R.obj i)).obj M) :
    generator (d.ringed i) (c i) x ≫ insertion (d.S.map a) ((d.L i).obj M) ≫
      (underlying (d.S.obj j)).map ((e.kappa a).hom.app M) =
    generator (d.ringed j) (c j) (x ≫ insertion (d.R.map a) M) := by
  have h := hn a M Z x
  change generator (d.ringed j) (c j) (x ≫ insertion (d.R.map a) M) ≫
    (underlying (d.S.obj j)).map ((e.kappa a).inv.app M) =
      generator (d.ringed i) (c i) x ≫ insertion (d.S.map a) ((d.L i).obj M) at h
  have ht := congrArg (fun z ↦ z ≫
    (underlying (d.S.obj j)).map ((e.kappa a).hom.app M)) h
  rw [Category.assoc, ← Functor.map_comp, (e.kappa a).inv_hom_id_app] at ht
  erw [Functor.map_id, Category.comp_id] at ht
  exact ht.symm

private theorem pullArrow_generator (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) {i j : Index} (a : i ⟶ j)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj j))
    (f : (extend (d.R.map a)).obj P ⟶ Q) (p : ℤ)
    (Z : Sheaf J (Type w)) (x : Z ⟶ (underlying (d.R.obj i)).obj (P.X p))
    (U : Dᵒᵖ) (v : (d.inverse.obj Z).obj.obj U) :
    ((e.pullArrow a P Q f).f p).val.app U
      (extensionTmul (d.S.map a) ((d.L i).obj (P.X p)) U 1
        ((generator (d.ringed i) (c i) x).hom.app U v)) =
      (generator (d.ringed j) (c j)
        (x ≫ semilinearSectionMap (d.R.map a) f p)).hom.app U v := by
  have h := congrArg (fun z ↦ z.hom.app U v)
    (kappa_generator d c e hn a (P.X p) Z x)
  change ((e.kappa a).hom.app (P.X p)).val.app U
    (((extensionAdjunction (d.S.map a)).unit.app ((d.L i).obj (P.X p))).val.app U
      ((generator (d.ringed i) (c i) x).hom.app U v)) = _ at h
  rw [extension_unit] at h
  have ht := congrArg (fun z ↦ z.hom.app U v)
    (CategoryTheory.CochainPullback.generator_naturality
      (d.ringed j) (c j) (f.f p) (x ≫ insertion (d.R.map a) (P.X p)))
  change ((d.L j).map (f.f p)).val.app U
    (((e.kappa a).hom.app (P.X p)).val.app U _) = _
  rw [h]
  exact ht.symm

private theorem diagramPullSection_eq (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (i : Index)
    (M : Modules (d.R.obj i)) (U : Dᵒᵖ) (b : (d.S.obj i).obj.obj U)
    (x : ((d.algebraic i).modules.obj M).val.obj U) :
    diagramPullSection d i M U b x =
      b • (@id (((d.L i).obj M).val.obj U) (((c i).q M).hom.app U x)) := by
  dsimp only [diagramPullSection]
  rw [extension_smul, map_smul]
  exact congrArg (fun z : ((d.L i).obj M).val.obj U ↦ b • z)
    ((c i).q_one M U x).symm

private theorem diagramPullSection_generator (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (i : Index)
    (M : Modules (d.R.obj i)) (U : Dᵒᵖ)
    (x : ((d.algebraic i).modules.obj M).val.obj U) :
    ((c i).q M).hom.app U x =
      (generator (d.ringed i) (c i) (𝟙 ((underlying (d.R.obj i)).obj M))).hom.app U
        (((d.algebraic i).moduleUnderlying.hom.app M).hom.app U x) := by
  simp only [generator, Functor.map_id, Category.id_comp]
  change _ = ((c i).q M).hom.app U
    (((d.algebraic i).moduleUnderlying.inv.app M).hom.app U
      (((d.algebraic i).moduleUnderlying.hom.app M).hom.app U x))
  have h := congrArg (fun z ↦ z.hom.app U x)
    ((d.algebraic i).moduleUnderlying.hom_inv_id_app M)
  exact (congrArg (fun z ↦ ((c i).q M).hom.app U z) h).symm

private theorem pullArrow_section (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) {i j : Index} (a : i ⟶ j)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj j))
    (f : (extend (d.R.map a)).obj P ⟶ Q) (p : ℤ) (U : Dᵒᵖ)
    (b : (d.S.obj j).obj.obj U) (b' : (d.S.obj i).obj.obj U)
    (x : ((d.algebraic i).modules.obj (P.X p)).val.obj U) :
    ((e.pullArrow a P Q f).f p).val.app U
      (extensionTmul (d.S.map a) ((d.L i).obj (P.X p)) U b
        (diagramPullSection d i (P.X p) U b' x)) =
    diagramPullSection d j (Q.X p) U (b * (d.S.map a).hom.app U b')
      ((inverseSectionMap d a f p).hom.app U x) := by
  rw [diagramPullSection_eq d c]
  have h := pullArrow_generator d c e hn a P Q f p
    ((underlying (d.R.obj i)).obj (P.X p)) (𝟙 _) U
      (((d.algebraic i).moduleUnderlying.hom.app (P.X p)).hom.app U x)
  rw [← diagramPullSection_generator d c i (P.X p) U x] at h
  dsimp only [id]
  rw [extension_smul_arg, extension_smul, map_smul, map_smul, h,
    diagramPullSection_eq d c, smul_smul, mul_comm ((d.S.map a).hom.app U b') b]
  congr 1
  simp only [inverseSectionMap, generator, Category.id_comp, id]
  rfl

private theorem kappa_section (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) {i j : Index} (a : i ⟶ j)
    (M : Modules (d.R.obj i)) (U : Dᵒᵖ)
    (b : (d.S.obj j).obj.obj U) (b' : (d.S.obj i).obj.obj U)
    (x : ((d.algebraic i).modules.obj M).val.obj U) :
    ((e.kappa a).hom.app M).val.app U
      (extensionTmul (d.S.map a) ((d.L i).obj M) U b
        (diagramPullSection d i M U b' x)) =
    diagramPullSection d j ((extensionFunctor (d.R.map a)).obj M) U
      (b * (d.S.map a).hom.app U b') ((diagramInsertion d a M).hom.app U x) := by
  have h := congrArg (fun z ↦ z.hom.app U
    (((d.algebraic i).moduleUnderlying.hom.app M).hom.app U x))
    (kappa_generator d c e hn a M ((underlying (d.R.obj i)).obj M) (𝟙 _))
  change ((e.kappa a).hom.app M).val.app U
    (((extensionAdjunction (d.S.map a)).unit.app ((d.L i).obj M)).val.app U
      ((generator (d.ringed i) (c i) (𝟙 _)).hom.app U _)) = _ at h
  rw [extension_unit (d.S.map a) ((d.L i).obj M),
    ← diagramPullSection_generator d c i M U x] at h
  rw [diagramPullSection_eq d c]
  dsimp only [id]
  rw [extension_smul_arg, extension_smul,
    map_smul, map_smul, h, diagramPullSection_eq d c, smul_smul,
    mul_comm ((d.S.map a).hom.app U b') b]
  congr 1
  simp only [diagramInsertion, generator, Category.id_comp, id]
  rfl

private theorem q_smul (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (i : Index)
    (M : Modules (d.R.obj i)) (U : Dᵒᵖ) (r : (d.RI.obj i).obj.obj U)
    (x : ((d.algebraic i).modules.obj M).val.obj U) :
    ((c i).q M).hom.app U (r • x) = (d.phi.app i).hom.app U r •
      (@id (((d.L i).obj M).val.obj U) (((c i).q M).hom.app U x)) := by
  have h := (c i).q_one M U (r • x)
  change ((c i).q M).hom.app U (r • x) =
    (eqToHom (d.hobj i M).symm).val.app U
      (extensionTmul (d.phi.app i) ((d.algebraic i).modules.obj M) U 1 (r • x)) at h
  rw [h, extension_smul_arg, map_smul]
  exact congrArg (fun z : ((d.L i).obj M).val.obj U ↦ (d.phi.app i).hom.app U r • z)
    ((c i).q_one M U x).symm

private theorem kappa_inv_section (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) {i j : Index} (a : i ⟶ j)
    (M : Modules (d.R.obj i)) (U : Dᵒᵖ)
    (b : (d.S.obj j).obj.obj U) (r : (d.RI.obj j).obj.obj U)
    (x : ((d.algebraic i).modules.obj M).val.obj U) :
    ((e.kappa a).inv.app M).val.app U
      (diagramPullSection d j ((extensionFunctor (d.R.map a)).obj M) U b
        (r • (@id (((d.algebraic j).modules.obj
          ((extensionFunctor (d.R.map a)).obj M)).val.obj U)
          ((diagramInsertion d a M).hom.app U x)))) =
    extensionTmul (d.S.map a) ((d.L i).obj M) U
      (b * (d.phi.app j).hom.app U r) (diagramPullSection d i M U 1 x) := by
  have h := congrArg (fun z ↦ z.hom.app U
    (((d.algebraic i).moduleUnderlying.hom.app M).hom.app U x)) (hn a M
      ((underlying (d.R.obj i)).obj M) (𝟙 _))
  change ((e.kappa a).inv.app M).val.app U
    ((generator (d.ringed j) (c j) (𝟙 _ ≫ insertion (d.R.map a) M)).hom.app U _) =
    (((extensionAdjunction (d.S.map a)).unit.app ((d.L i).obj M)).val.app U
      ((generator (d.ringed i) (c i) (𝟙 _)).hom.app U _)) at h
  have hx : (generator (d.ringed j) (c j)
      (𝟙 ((underlying (d.R.obj i)).obj M) ≫ insertion (d.R.map a) M)).hom.app U
      (((d.algebraic i).moduleUnderlying.hom.app M).hom.app U x) =
      ((c j).q ((extensionFunctor (d.R.map a)).obj M)).hom.app U
        ((diagramInsertion d a M).hom.app U x) := by
    simp only [generator, Category.id_comp, diagramInsertion]
    rfl
  rw [hx, extension_unit (d.S.map a) ((d.L i).obj M),
    ← diagramPullSection_generator d c i M U x] at h
  rw [diagramPullSection_eq d c, q_smul, extension_smul]
  dsimp only [id]
  erw [map_smul, map_smul]
  rw [h, diagramPullSection_eq d c, one_smul]
  dsimp only [id]
  rw [extension_smul]
  rw [smul_smul, mul_comm]

private theorem scalarComp_unit {A B H : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (b : B ⟶ H) (c : A ⟶ H) (hc : c = a ≫ b)
    (P : Complex A) (p : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) :
    (((scalarComp a b c hc).hom.app P).f p).val.app U
      (extensionTmul b ((extensionFunctor a).obj (P.X p)) U 1
        (extensionTmul a (P.X p) U 1 x)) = extensionTmul c (P.X p) U 1 x := by
  have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
    (((extensionAdjunction a).comp (extensionAdjunction b)).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionComposition a b c hc))
    (extensionAdjunction c) (P.X p)
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at h
  have h' := congrArg (fun z ↦ z.val.app U x) h
  change (((extensionAdjunction a).homEquiv (P.X p) _
    ((extensionAdjunction b).homEquiv _ _
      ((Adjunction.leftAdjointUniq
        (((extensionAdjunction a).comp (extensionAdjunction b)).ofNatIsoRight
          (SheafOfModules.systemScalarRestrictionComposition a b c hc))
        (extensionAdjunction c)).hom.app (P.X p)))).val.app U x) =
    ((extensionAdjunction c).unit.app (P.X p)).val.app U x at h'
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit] at h'
  unfold scalarComp
  dsimp only [NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex]
  change ((Adjunction.leftAdjointUniq
    (((extensionAdjunction a).comp (extensionAdjunction b)).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionComposition a b c hc))
    (extensionAdjunction c)).hom.app (P.X p)).val.app U
    (((extensionAdjunction b).unit.app ((extensionFunctor a).obj (P.X p))).val.app U
      (((extensionAdjunction a).unit.app (P.X p)).val.app U x)) =
    ((extensionAdjunction c).unit.app (P.X p)).val.app U x at h'
  rw [extension_unit, extension_unit, extension_unit] at h'
  change ((Adjunction.leftAdjointUniq
    (((extensionAdjunction a).comp (extensionAdjunction b)).ofNatIsoRight
      (SheafOfModules.systemScalarRestrictionComposition a b c hc))
    (extensionAdjunction c)).hom.app (P.X p)).val.app U
      (extensionTmul b ((extensionFunctor a).obj (P.X p)) U 1
        (extensionTmul a (P.X p) U 1 x)) = extensionTmul c (P.X p) U 1 x
  exact h'


private theorem scalarComp_value {A B H : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (b : B ⟶ H) (c : A ⟶ H) (hc : c = a ≫ b)
    (P : Complex A) (p : ℤ) (U : Cᵒᵖ) (v : H.obj.obj U) (z : B.obj.obj U)
    (x : (P.X p).val.obj U) :
    (((scalarComp a b c hc).hom.app P).f p).val.app U
      (extensionTmul b ((extensionFunctor a).obj (P.X p)) U v
        (extensionTmul a (P.X p) U z x)) =
      extensionTmul c (P.X p) U (v * b.hom.app U z) x := by
  rw [extension_smul a, extension_smul_arg b, extension_smul b,
    map_smul, map_smul, scalarComp_unit, extension_smul]
  rw [one_smul, smul_smul, mul_comm (b.hom.app U z) v]
  exact (extension_smul c (P.X p) U _ x).symm

private theorem scalarComp_inv_value {A B H : Sheaf J CommRingCat.{w}}
    (a : A ⟶ B) (b : B ⟶ H) (c : A ⟶ H) (hc : c = a ≫ b)
    (P : Complex A) (p : ℤ) (U : Cᵒᵖ) (v : H.obj.obj U)
    (x : (P.X p).val.obj U) :
    (((scalarComp a b c hc).inv.app P).f p).val.app U
      (extensionTmul c (P.X p) U v x) =
      extensionTmul b ((extensionFunctor a).obj (P.X p)) U v
        (extensionTmul a (P.X p) U 1 x) := by
  have h := scalarComp_value a b c hc P p U v 1 x
  rw [map_one, mul_one] at h
  rw [← h]
  exact congrArg (fun z ↦ z.val.app U
    (extensionTmul b ((extensionFunctor a).obj (P.X p)) U v
      (extensionTmul a (P.X p) U 1 x)))
    (show ((scalarComp a b c hc).hom.app P).f p ≫
      ((scalarComp a b c hc).inv.app P).f p = 𝟙 _ from
      congrArg (fun z ↦ z.f p) ((scalarComp a b c hc).hom_inv_id_app P))

private theorem extension_eq_value {A B : Sheaf J CommRingCat.{w}}
    (a b : A ⟶ B) (h : a = b) (P : Complex A) (p : ℤ) (U : Cᵒᵖ)
    (v : B.obj.obj U) (x : (P.X p).val.obj U) :
    ((eqToHom (congrArg (fun t ↦ (extend t).obj P) h)).f p).val.app U
      (extensionTmul a (P.X p) U v x) = extensionTmul b (P.X p) U v x := by
  subst b
  rfl

private theorem squareArrow_value (B : Index ⥤ Sheaf J CommRingCat.{w})
    {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P : Complex (B.obj i)) (Q : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ Q) (p : ℤ) (U : Cᵒᵖ)
    (v : (B.obj l).obj.obj U) (z : (B.obj j).obj.obj U) (x : (P.X p).val.obj U) :
    ((squareArrow B a b r s h P Q f).f p).val.app U
      (extensionTmul (B.map s) ((extensionFunctor (B.map a)).obj (P.X p)) U v
        (extensionTmul (B.map a) (P.X p) U z x)) =
      extensionTmul (B.map b) (Q.X p) U (v * (B.map s).hom.app U z)
        ((semilinearSectionMap (B.map r) f p).hom.app U x) := by
  change ((extensionFunctor (B.map b)).map (f.f p)).val.app U
    ((((diagramComp B r b).inv.app P).f p).val.app U
      (((eqToHom (congrArg (fun t ↦ (extend (B.map t)).obj P) h)).f p).val.app U
        ((((diagramComp B a s).hom.app P).f p).val.app U _))) = _
  simp only [diagramComp]
  rw [scalarComp_value]
  rw [show congrArg (fun t ↦ (extend (B.map t)).obj P) h =
    congrArg (fun t ↦ (extend t).obj P) (congrArg B.map h) from rfl]
  rw [extension_eq_value _ _ (congrArg B.map h), scalarComp_inv_value]
  have ht := extension_map (B.map b) (f.f p) U
    (v * (B.map s).hom.app U z) (extensionTmul (B.map r) (P.X p) U 1 x)
  exact ht.trans (congrArg (extensionTmul (B.map b) (Q.X p) U _) (by
    change _ = (f.f p).val.app U
      (((extensionAdjunction (B.map r)).unit.app (P.X p)).val.app U x)
    rw [extension_unit]))

private theorem squareArrow_units (B : Index ⥤ Sheaf J CommRingCat.{w})
    {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P : Complex (B.obj i)) (Q : Complex (B.obj k))
    (f : (extend (B.map r)).obj P ⟶ Q) (p : ℤ) :
    insertion (B.map a) (P.X p) ≫
        semilinearSectionMap (B.map s) (squareArrow B a b r s h P Q f) p =
      semilinearSectionMap (B.map r) f p ≫ insertion (B.map b) (Q.X p) := by
  apply Sheaf.hom_ext
  ext U x
  change ((squareArrow B a b r s h P Q f).f p).val.app U
    (((extensionAdjunction (B.map s)).unit.app
      ((extensionFunctor (B.map a)).obj (P.X p))).val.app U
        (((extensionAdjunction (B.map a)).unit.app (P.X p)).val.app U x)) =
    (((extensionAdjunction (B.map b)).unit.app (Q.X p)).val.app U
      ((semilinearSectionMap (B.map r) f p).hom.app U x))
  rw [extension_unit, extension_unit, extension_unit]
  simpa only [map_one, mul_one] using squareArrow_value B a b r s h P Q f p U 1 1 x

private theorem inverseSectionMap_square (d : Diagram (J := J) (K := K))
    {i j k l : Index} (a : i ⟶ j) (b : k ⟶ l) (r : i ⟶ k) (s : j ⟶ l)
    (h : a ≫ s = r ≫ b) (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj k))
    (f : (extend (d.R.map r)).obj P ⟶ Q) (p : ℤ) :
    diagramInsertion d a (P.X p) ≫
        inverseSectionMap d s (squareArrow d.R a b r s h P Q f) p =
      inverseSectionMap d r f p ≫ diagramInsertion d b (Q.X p) := by
  let H := (d.algebraic i).moduleUnderlying.hom.app (P.X p)
  let T := (d.algebraic l).moduleUnderlying.inv.app
    ((extensionFunctor (d.R.map b)).obj (Q.X p))
  change H ≫ d.inverse.map (insertion (d.R.map a) (P.X p)) ≫
      (d.algebraic j).moduleUnderlying.inv.app
        ((extensionFunctor (d.R.map a)).obj (P.X p)) ≫
      (d.algebraic j).moduleUnderlying.hom.app
        ((extensionFunctor (d.R.map a)).obj (P.X p)) ≫
      d.inverse.map (semilinearSectionMap (d.R.map s)
        (squareArrow d.R a b r s h P Q f) p) ≫ T =
    H ≫ d.inverse.map (semilinearSectionMap (d.R.map r) f p) ≫
      (d.algebraic k).moduleUnderlying.inv.app (Q.X p) ≫
      (d.algebraic k).moduleUnderlying.hom.app (Q.X p) ≫
      d.inverse.map (insertion (d.R.map b) (Q.X p)) ≫ T
  simp only [Iso.inv_hom_id_app_assoc]
  have hh := congrArg (fun z ↦ H ≫ d.inverse.map z ≫ T)
    (squareArrow_units d.R a b r s h P Q f p)
  simpa only [Functor.map_comp, Category.assoc] using hh

private theorem semilinear_pullArrow_section (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) {i j : Index} (a : i ⟶ j)
    (P : Complex (d.R.obj i)) (Q : Complex (d.R.obj j))
    (f : (extend (d.R.map a)).obj P ⟶ Q) (p : ℤ) (U : Dᵒᵖ)
    (x : ((d.algebraic i).modules.obj (P.X p)).val.obj U) :
    (semilinearSectionMap (d.S.map a) (e.pullArrow a P Q f) p).hom.app U
      (diagramPullSection d i (P.X p) U 1 x) =
    diagramPullSection d j (Q.X p) U 1 ((inverseSectionMap d a f p).hom.app U x) := by
  change ((e.pullArrow a P Q f).f p).val.app U
    (((extensionAdjunction (d.S.map a)).unit.app ((d.L i).obj (P.X p))).val.app U _) = _
  rw [extension_unit]
  simpa only [map_one, mul_one] using pullArrow_section d c e hn a P Q f p U 1 1 x

attribute [local irreducible] extensionFunctor Comparisons.pullArrow squareArrow

private theorem kappaTransitionValues (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) : KappaTransitionValues e := by
  intro i j k l a b r s h P Q f p U v z x
  constructor
  · change ((e.pullArrow s ((extend (d.R.map a)).obj P)
        ((extend (d.R.map b)).obj Q) (squareArrow d.R a b r s h P Q f)).f p).val.app U
      (((extensionFunctor (d.S.map s)).map ((e.kappa a).hom.app (P.X p))).val.app U _) = _
    erw [extension_map, kappa_section d c e hn, pullArrow_section d c e hn]
    rw [map_mul]
    have hc := congrArg (fun t ↦ t.hom.app U z)
      ((d.S.map_comp a s).symm.trans
        ((congrArg d.S.map h).trans (d.S.map_comp r b)))
    change (d.S.map s).hom.app U ((d.S.map a).hom.app U z) =
      (d.S.map b).hom.app U ((d.S.map r).hom.app U z) at hc
    rw [hc]
    simp only [one_mul]
    congr 1
    exact congrArg (fun t ↦ t.hom.app U x) (inverseSectionMap_square d a b r s h P Q f p)
  · intro z'
    change ((squareArrow d.S a b r s h ((pull (d.ringed i)).obj P)
      ((pull (d.ringed k)).obj Q) (e.pullArrow r P Q f)).f p).val.app U
        (((extensionFunctor (d.S.map s)).map ((e.kappa a).inv.app (P.X p))).val.app U _) = _
    erw [extension_map, kappa_inv_section d c e hn, squareArrow_value,
      semilinear_pullArrow_section d c e hn]
    rw [map_mul, one_mul]
    congr 2
    exact congrArg (fun t ↦ t.hom.app U z') (d.phi.naturality s).symm

/-- The prescribed forward and inverse values of normalized kappa square transport.
Source: Stacks 03EL; original
strict-totalization proof step 5
(blueprint: lem-pur-normalized-kappa-transition-calculus).
Proof: test the two scalar extensions by their adjunctions and the inverse-image
presentation by generalized sections. Normalization gives the forward kappa
formula; cancellation gives its inverse. The scalar associator multiplies its
coefficients. The coefficient graph square and naturality of phi identify the
coefficients for both transports. No semilinear transition is inverted. -/
theorem normalizedKappaTransitionValues (d : Diagram (J := J) (K := K))
    (c : ∀ i : Index, Comparison (d.ringed i)) (e : Comparisons d)
    (hn : e.Normalized c) : KappaTransitionValues e := by
  exact kappaTransitionValues d c e hn

end CategoryTheory.CochainPullback.StrictCoefficient.KappaCalculation
