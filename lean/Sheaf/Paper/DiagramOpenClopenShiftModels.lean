/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q123
-/
module

public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.SixFunctors.OpenTensorNormalization
public import Mathlib.CategoryTheory.Shift.Adjunction
public import Sheaf.Paper.DiagramOpenClopenShiftCore
public import Sheaf.Paper.DiagramOpenClopenShiftOpenSupport
import all Sheaf.SixFunctors.SemilinearProperOpenMatePasting
import all Sheaf.Paper.DiagramOpenClopenShiftCore
import all Sheaf.Paper.DiagramOpenClopenShiftOpenSupport
import all Sheaf.AlgebraicGeometry.VaryingRingOperations
import all Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows
import all Sheaf.AlgebraicGeometry.VaryingRingModulePiComplementZero
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.CategoryTheory.ExactDerivedAdjunctionUnitShift
import Sheaf.CategoryTheory.DerivedCategory.DerivedMateComparison
import all Sheaf.AlgebraicGeometry.StrictTowerDirectImageCoherence
import all Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import all Sheaf.AlgebraicGeometry.SemilinearClopenUnitProjector
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift

/-! # Open and clopen shift models on whole semilinear systems

Source: Stacks Project, Tags 03DI, 03DJ, 04TQ--04TS, 015F, 070H and 07A6;
blueprint `fix-prop-coherence`, maps-used sentence
(blueprint: lem-pur-diagram-open-clopen-shift-models).

The maps are the existing proper/open calculus maps. Representatives are natural
transformations of whole systems, localized through the standard factorizations.
The right-derived shift is the existing K-injective shift, rather than a shift
transported along a clopen isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u a av aw b bv bw

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject

namespace AlgebraicGeometry.ProEtale.SemilinearProperOpen.DiagramShift

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  Functor.rightDerivedFunctor constantSheaf
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem pull_map_sections {U X : Scheme.{u}} (s : U ⟶ X)
    [IsOpenImmersion s] {M N : Modules C τ X} (f g : M ⟶ N)
    (h : (pull C τ s).map f = (pull C τ s).map g) (n : ℕ) (W : U.ProEt)
    (x : M.val.obj (Opposite.op (n, (VaryingRing.openMap s).obj W))) :
    (f.val.app (Opposite.op (n, (VaryingRing.openMap s).obj W))) x =
      (g.val.app (Opposite.op (n, (VaryingRing.openMap s).obj W))) x := by
  rw [pull_eq] at h
  have := VaryingRing.openRingTranspose_isIso C τ s
  have := VaryingRing.prodOpenContinuous s
  let e : VaryingRing.pull C τ s ≅
      SheafOfModules.pushforward.{u + 1}
        (F := (𝟭 ℕ).prod (VaryingRing.openMap s))
        (inv (VaryingRing.openRingTranspose C τ s)) :=
    (VaryingRing.moduleAdj C τ s).leftAdjointUniq (VaryingRing.openPullAdj C τ s)
  have he : (SheafOfModules.pushforward (inv (VaryingRing.openRingTranspose C τ s))).map f =
      (SheafOfModules.pushforward (inv (VaryingRing.openRingTranspose C τ s))).map g := by
    apply (cancel_epi (e.hom.app M)).mp
    exact (e.hom.naturality f).symm.trans
      ((congrArg (fun q ↦ q ≫ e.hom.app N) h).trans (e.hom.naturality g))
  exact congrArg (fun q ↦ (q.val.app (Opposite.op (n, W))) x) he

set_option maxHeartbeats 50000 in
-- Check sheaf gluing uniqueness on all coefficient sections.
private theorem clopen_pair_faithful {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion z]
    (hr : Set.range z = (Set.range s)ᶜ) : ((pull C τ s).prod' (pull C τ z)).Faithful := by
  classical
  let Y : Bool → Scheme.{u} := fun b ↦ cond b U Z
  let j : ∀ b, Y b ⟶ X := fun b ↦ Bool.rec z s b
  have hj (b : Bool) : IsOpenImmersion (j b) := by cases b <;> infer_instance
  have hd : Pairwise (fun b c ↦ Disjoint (Set.range (j b)) (Set.range (j c))) := by
    intro b c hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · change Disjoint (Set.range z) (Set.range s)
      rw [hr]
      exact disjoint_compl_left
    · change Disjoint (Set.range s) (Set.range z)
      rw [hr]
      exact disjoint_compl_right
    · exact (hbc rfl).elim
  have hc : ∀ x : X, ∃ b, x ∈ Set.range (j b) := by
    intro x
    by_cases hx : x ∈ Set.range s
    · exact ⟨true, hx⟩
    · refine ⟨false, ?_⟩
      change x ∈ Set.range z
      rw [hr]
      exact hx
  constructor
  intro M N f g h
  have hs : (pull C τ s).map f = (pull C τ s).map g := congrArg (fun q ↦ q.1) h
  have hz : (pull C τ z).map f = (pull C τ z).map g := congrArg (fun q ↦ q.2) h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hb := (@Scheme.ProEt.clopenSections_bijective.{u, u + 1, u + 1, 0}
    X Bool Y j hj hd hc
    ((sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      (coefficients C X V.unop.1))
    ((VaryingRing.eval C τ X V.unop.1).obj N) V.unop.2).injective
  apply hb
  funext b
  have hpiece : ∀ (b : Bool) (W : (Y b).ProEt)
      (x : M.val.obj (Opposite.op (V.unop.1, (@VaryingRing.openMap _ _ (j b) (hj b)).obj W))),
      (f.val.app (Opposite.op (V.unop.1, (@VaryingRing.openMap _ _ (j b) (hj b)).obj W))) x =
        (g.val.app (Opposite.op (V.unop.1, (@VaryingRing.openMap _ _ (j b) (hj b)).obj W))) x := by
    intro b W x
    cases b
    · exact pull_map_sections C τ z f g hz _ W x
    · exact pull_map_sections C τ s f g hs _ W x
  let i : (V.unop.1, (@VaryingRing.openMap _ _ (j b) (hj b)).obj
      (Scheme.ProEt.clopenTestPiece (j b) V.unop.2)) ⟶ V.unop :=
    ⟨𝟙 V.unop.1, @Scheme.ProEt.clopenTestInclusion _ _ (j b) (hj b) V.unop.2⟩
  have hh := hpiece b (Scheme.ProEt.clopenTestPiece (j b) V.unop.2)
    (M.val.map i.op x)
  have hf := congrArg (fun q ↦ q x) (f.val.naturality i.op)
  have hg := congrArg (fun q ↦ q x) (g.val.naturality i.op)
  exact hf.symm.trans (hh.trans hg)

private theorem clopen_pair_joint {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] [IsOpenImmersion z]
    (hr : Set.range z = (Set.range s)ᶜ) :
    JointlyReflectIsomorphisms (pairFunctor (pull C τ s) (pull C τ z)) := by
  have := clopen_pair_faithful C τ s z hr
  apply jointlyReflectIsomorphisms_pairFunctor
  intro M N f hs hz
  have := hs
  have := hz
  have hi : IsIso (((pull C τ s).prod' (pull C τ z)).map f) := by
    change IsIso (Prod.mkHom ((pull C τ s).map f) ((pull C τ z).map f))
    change IsIso ((asIso ((pull C τ s).map f)).prod
      (asIso ((pull C τ z).map f))).hom
    infer_instance
  have hm : Mono f := ((pull C τ s).prod' (pull C τ z)).mono_of_mono_map inferInstance
  have he : Epi f := ((pull C τ s).prod' (pull C τ z)).epi_of_epi_map inferInstance
  exact isIso_of_mono_of_epi f

private theorem disjoint_ordinary {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] (hr : Disjoint (Set.range s) (Set.range z))
    (N : Modules C τ U) : IsZero ((pull C τ z).obj ((extension C τ s).obj N)) := by
  rw [pull_eq, extension_eq]
  exact VaryingRing.disjoint_extension C τ s z hr N

private theorem disjoint_complex {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] (hr : Disjoint (Set.range s) (Set.range z))
    (N : CochainComplex (Modules C τ U) ℤ) :
    IsZero (((pull C τ z).mapHomologicalComplex (.up ℤ)).obj
      (((extension C τ s).mapHomologicalComplex (.up ℤ)).obj N)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.Hom.ext
  funext p
  exact (disjoint_ordinary C τ s z hr (N.X p)).eq_of_src _ _

private theorem disjoint_derived {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] (hr : Disjoint (Set.range s) (Set.range z))
    (N : Derived C τ U) : IsZero ((P C τ z).obj ((J C τ s).obj N)) := by
  let F := extension C τ s ⋙ pull C τ z
  have hz : IsZero (F.mapDerivedCategory.obj N) := by
    apply F.isZero_mapDerivedCategory_obj
    intro p
    exact disjoint_ordinary C τ s z hr _
  exact hz.of_iso ((Functor.mapDerivedCategoryCompIso
    (extension C τ s) (pull C τ z)).symm.app N)

section ProductFromOpenAdjunctions

universe x y
variable {A B D : Type x} [Category.{y} A] [Category.{y} B] [Category.{y} D]
    [Preadditive A] [Preadditive B] [Preadditive D]
    [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
    [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D]

private def gluingSum (L : B ⥤ A) (M : D ⥤ A) : B × D ⥤ A where
  obj X := L.obj X.1 ⊞ M.obj X.2
  map f := biprod.map (L.map f.1) (M.map f.2)
  map_id X := by apply biprod.hom_ext <;> simp
  map_comp f g := by apply biprod.hom_ext <;> simp [Category.assoc]

omit [HasZeroObject A] in
private theorem iso_desc_of_zero {W X Y : A} (f : W ⟶ Y) (g : X ⟶ Y)
    [IsIso f] (hz : IsZero X) : IsIso (biprod.desc f g) := by
  have he : biprod.desc f g = (isoBiprodZero hz).inv ≫ f := by
    apply biprod.hom_ext' <;> simp [hz.eq_of_src g 0]
  rw [he]
  infer_instance

omit [HasZeroObject A] [HasZeroObject B] in
private theorem iso_map_desc_of_zero (F : A ⥤ B) [F.Additive]
    [PreservesBinaryBiproducts F] {W X Y : A} (f : W ⟶ Y) (g : X ⟶ Y)
    [IsIso (F.map f)] (hz : IsZero (F.obj X)) : IsIso (F.map (biprod.desc f g)) := by
  rw [← biprod.mapBiprod_hom_desc]
  have := iso_desc_of_zero (F.map f) (F.map g) hz
  infer_instance

omit [HasZeroObject A] [HasZeroObject B] [HasBinaryBiproducts B] in
private theorem iso_map_desc_of_zero_left (F : A ⥤ B) [F.Additive]
    [PreservesBinaryBiproducts F] {W X Y : A} (f : W ⟶ Y) (g : X ⟶ Y)
    [IsIso (F.map g)] (hz : IsZero (F.obj W)) : IsIso (F.map (biprod.desc f g)) := by
  have he : biprod.desc (F.map f) (F.map g) =
      (isoZeroBiprod hz).inv ≫ F.map g := by
    apply biprod.hom_ext' <;> simp [hz.eq_of_src (F.map f) 0]
  rw [← biprod.mapBiprod_hom_desc, he]
  infer_instance

private def gluingSumCounit {L : B ⥤ A} {P : A ⥤ B} {M : D ⥤ A} {Q : A ⥤ D}
    (a : L ⊣ P) (b : M ⊣ Q) : P.prod' Q ⋙ gluingSum L M ⟶ 𝟭 A where
  app X := biprod.desc (a.counit.app X) (b.counit.app X)
  naturality {X Y} f := by
    apply biprod.hom_ext' <;>
      simp [gluingSum]

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts D] in
private theorem gluingSumCounit_isIso
    {L : B ⥤ A} {P : A ⥤ B} {M : D ⥤ A} {Q : A ⥤ D}
    [P.Additive] [Q.Additive] [PreservesBinaryBiproducts P] [PreservesBinaryBiproducts Q]
    (a : L ⊣ P) (b : M ⊣ Q) [IsIso a.unit] [IsIso b.unit]
    (hz : ∀ X, IsZero (P.obj (M.obj X))) (hw : ∀ X, IsZero (Q.obj (L.obj X)))
    (hjoint : ∀ {X Y : A} (f : X ⟶ Y), IsIso (P.map f) → IsIso (Q.map f) → IsIso f) :
    IsIso (gluingSumCounit a b) := by
  have (X : A) : IsIso ((gluingSumCounit a b).app X) := by
    have hp : IsIso (P.map (a.counit.app X)) := by
      have he : P.map (a.counit.app X) = inv (a.unit.app (P.obj X)) := by
        apply (cancel_epi (a.unit.app (P.obj X))).mp
        simp [a.right_triangle_components]
      rw [he]
      infer_instance
    have hq : IsIso (Q.map (b.counit.app X)) := by
      have he : Q.map (b.counit.app X) = inv (b.unit.app (Q.obj X)) := by
        apply (cancel_epi (b.unit.app (Q.obj X))).mp
        simp [b.right_triangle_components]
      rw [he]
      infer_instance
    exact hjoint _
      (iso_map_desc_of_zero P (a.counit.app X) (b.counit.app X) (hz _))
      (iso_map_desc_of_zero_left Q (a.counit.app X) (b.counit.app X) (hw _))
  exact NatIso.isIso_of_isIso_app _

omit [HasZeroObject A] [HasZeroObject B] [HasBinaryBiproducts B] in
private theorem iso_map_inl_of_zero (F : A ⥤ B) [F.Additive]
    [PreservesBinaryBiproducts F] (W X : A) (hz : IsZero (F.obj X)) :
    IsIso (F.map (biprod.inl : W ⟶ W ⊞ X)) := by
  have he : F.map (biprod.inl : W ⟶ W ⊞ X) =
      (isoBiprodZero hz).hom ≫ (F.mapBiprod W X).inv := by
    change F.map biprod.inl = biprod.inl ≫ (F.mapBiprod W X).inv
    rw [Functor.mapBiprod_inv, biprod.inl_desc]
  rw [he]
  infer_instance

omit [HasZeroObject A] [HasZeroObject B] [HasBinaryBiproducts B] in
private theorem iso_map_inr_of_zero (F : A ⥤ B) [F.Additive]
    [PreservesBinaryBiproducts F] (W X : A) (hz : IsZero (F.obj W)) :
    IsIso (F.map (biprod.inr : X ⟶ W ⊞ X)) := by
  have he : F.map (biprod.inr : X ⟶ W ⊞ X) =
      (isoZeroBiprod hz).hom ≫ (F.mapBiprod W X).inv := by
    change F.map biprod.inr = biprod.inr ≫ (F.mapBiprod W X).inv
    rw [Functor.mapBiprod_inv, biprod.inr_desc]
  rw [he]
  infer_instance

private def gluingSumUnit {L : B ⥤ A} {P : A ⥤ B} {M : D ⥤ A} {Q : A ⥤ D}
    (a : L ⊣ P) (b : M ⊣ Q) : 𝟭 (B × D) ⟶ gluingSum L M ⋙ P.prod' Q where
  app X := Prod.mkHom (a.unit.app X.1 ≫ P.map biprod.inl)
    (b.unit.app X.2 ≫ Q.map biprod.inr)
  naturality {X Y} f := by
    apply Prod.hom_ext
    · change f.1 ≫ (a.unit.app Y.1 ≫ P.map biprod.inl) =
        (a.unit.app X.1 ≫ P.map biprod.inl) ≫
          P.map (biprod.map (L.map f.1) (M.map f.2))
      rw [Category.assoc, ← P.map_comp, biprod.inl_map, P.map_comp, ← Category.assoc]
      simpa only [Functor.id_map, Functor.comp_map, Category.assoc] using
        congrArg (fun q ↦ q ≫ P.map (biprod.inl : L.obj Y.1 ⟶
          L.obj Y.1 ⊞ M.obj Y.2)) (a.unit.naturality f.1)
    · change f.2 ≫ (b.unit.app Y.2 ≫ Q.map biprod.inr) =
        (b.unit.app X.2 ≫ Q.map biprod.inr) ≫
          Q.map (biprod.map (L.map f.1) (M.map f.2))
      rw [Category.assoc, ← Q.map_comp, biprod.inr_map, Q.map_comp, ← Category.assoc]
      simpa only [Functor.id_map, Functor.comp_map, Category.assoc] using
        congrArg (fun q ↦ q ≫ Q.map (biprod.inr : M.obj Y.2 ⟶
          L.obj Y.1 ⊞ M.obj Y.2)) (b.unit.naturality f.2)

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
private theorem gluingSumUnit_isIso
    {L : B ⥤ A} {P : A ⥤ B} {M : D ⥤ A} {Q : A ⥤ D}
    [P.Additive] [Q.Additive] [PreservesBinaryBiproducts P] [PreservesBinaryBiproducts Q]
    (a : L ⊣ P) (b : M ⊣ Q) [IsIso a.unit] [IsIso b.unit]
    (hz : ∀ X, IsZero (P.obj (M.obj X))) (hw : ∀ X, IsZero (Q.obj (L.obj X))) :
    IsIso (gluingSumUnit a b) := by
  have (X : B × D) : IsIso ((gluingSumUnit a b).app X) := by
    have := iso_map_inl_of_zero P (L.obj X.1) (M.obj X.2) (hz _)
    have := iso_map_inr_of_zero Q (L.obj X.1) (M.obj X.2) (hw _)
    change IsIso ((asIso (a.unit.app X.1 ≫ P.map biprod.inl)).prod
      (asIso (b.unit.app X.2 ≫ Q.map biprod.inr))).hom
    infer_instance
  exact NatIso.isIso_of_isIso_app _

private def gluingSumEquivalence
    {L : B ⥤ A} {P : A ⥤ B} {M : D ⥤ A} {Q : A ⥤ D}
    [P.Additive] [Q.Additive] [PreservesBinaryBiproducts P] [PreservesBinaryBiproducts Q]
    (a : L ⊣ P) (b : M ⊣ Q) [IsIso a.unit] [IsIso b.unit]
    (hz : ∀ X, IsZero (P.obj (M.obj X))) (hw : ∀ X, IsZero (Q.obj (L.obj X)))
    (hjoint : ∀ {X Y : A} (f : X ⟶ Y), IsIso (P.map f) → IsIso (Q.map f) → IsIso f) :
    A ≌ B × D := by
  have := gluingSumCounit_isIso a b hz hw hjoint
  have := gluingSumUnit_isIso a b hz hw
  exact CategoryTheory.Equivalence.mk (P.prod' Q) (gluingSum L M)
    (asIso (gluingSumCounit a b)).symm (asIso (gluingSumUnit a b)).symm

omit [Preadditive A] [Preadditive B] [Preadditive D]
  [HasZeroObject A] [HasZeroObject B] [HasBinaryBiproducts A]
  [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
private def gluingInsertion
    {L : B ⥤ A} {P : A ⥤ B} {Q : A ⥤ D}
    (a : L ⊣ P) [IsIso a.unit] (hz : ∀ X, IsZero (Q.obj (L.obj X))) :
    L ⋙ P.prod' Q ≅ (𝟭 B).prod' ((Functor.const B).obj (0 : D)) :=
  NatIso.ofComponents (fun X ↦ (asIso (a.unit.app X)).symm.prod ((hz X).isoZero))
    (by
      intro X Y f
      apply Prod.hom_ext
      · change P.map (L.map f) ≫ inv (a.unit.app Y) = inv (a.unit.app X) ≫ f
        simpa only [Functor.comp_map, Functor.id_map, NatIso.isIso_inv_app] using
          (inv a.unit).naturality f
      · exact (isZero_zero D).eq_of_tgt _ _)

omit [Preadditive A] [Preadditive B] [Preadditive D]
  [HasZeroObject A] [HasZeroObject B] [HasBinaryBiproducts A]
  [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
private theorem gluingInsertion_unit
    {L : B ⥤ A} {P : A ⥤ B} {Q : A ⥤ D}
    (a : L ⊣ P) [IsIso a.unit] (hz : ∀ X, IsZero (Q.obj (L.obj X))) (X : B) :
    a.unit.app X ≫ ((gluingInsertion a hz).hom.app X).1 = 𝟙 X := by
  exact IsIso.hom_inv_id (a.unit.app X)

omit [Preadditive A] [Preadditive B] [HasZeroObject A] [HasZeroObject B]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
private theorem gluingInsertion_projection
    {L : B ⥤ A} {P : A ⥤ B} {Q : A ⥤ D}
    (a : L ⊣ P) [IsIso a.unit] (hz : ∀ X, IsZero (Q.obj (L.obj X)))
    (X : A) (f : X ⟶ L.obj (P.obj X)) (hf : P.map f = a.unit.app (P.obj X)) :
    (P.prod' Q).map f ≫ (gluingInsertion a hz).hom.app (P.obj X) =
      Prod.mkHom (𝟙 (P.obj X)) (0 : Q.obj X ⟶ 0) := by
  apply Prod.hom_ext
  · change P.map f ≫ inv (a.unit.app (P.obj X)) = 𝟙 _
    rw [hf, IsIso.hom_inv_id]
  · exact (isZero_zero D).eq_of_tgt _ _

end ProductFromOpenAdjunctions

private theorem homological_unit_isIso
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {L : A ⥤ B} {P : B ⥤ A} [L.Additive] [P.Additive]
    (a : L ⊣ P) [IsIso a.unit] :
    IsIso (a.mapHomologicalComplex (.up ℤ)).unit := by
  have (K : CochainComplex A ℤ) :
      IsIso ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
    have (p : ℤ) : IsIso (((a.mapHomologicalComplex (.up ℤ)).unit.app K).f p) := by
      change IsIso (a.unit.app (K.X p))
      infer_instance
    exact HomologicalComplex.Hom.isIso_of_components _
  exact NatIso.isIso_of_isIso_app _

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def ordinaryClopenEquivalence
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion z]
    (hr : Set.range z = (Set.range s)ᶜ) : Modules C τ X ≌ Modules C τ U × Modules C τ Z := by
  have hsz : Disjoint (Set.range s) (Set.range z) := by
    rw [hr]
    exact disjoint_compl_right
  have hzs := hsz.symm
  let a := ordinaryOpenAdj C τ s
  let b := ordinaryOpenAdj C τ z
  have hau : IsIso a.unit := ordinaryOpenUnitIso C τ s
  have hbu : IsIso b.unit := ordinaryOpenUnitIso C τ z
  let hz := disjoint_ordinary C τ z s hzs
  let hw := disjoint_ordinary C τ s z hsz
  let hj := clopen_pair_joint C τ s z hr
  exact gluingSumEquivalence a b hz hw (fun f hs hz ↦ hj.isIso_of_pairFunctor f hs hz)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def complexClopenEquivalence
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion z]
    (hr : Set.range z = (Set.range s)ᶜ) : CochainComplex (Modules C τ X) ℤ ≌
      CochainComplex (Modules C τ U) ℤ × CochainComplex (Modules C τ Z) ℤ := by
  have hsz : Disjoint (Set.range s) (Set.range z) := by
    rw [hr]
    exact disjoint_compl_right
  have hzs := hsz.symm
  let a := ordinaryOpenAdj C τ s
  let b := ordinaryOpenAdj C τ z
  have hau : IsIso a.unit := ordinaryOpenUnitIso C τ s
  have hbu : IsIso b.unit := ordinaryOpenUnitIso C τ z
  let hj := clopen_pair_joint C τ s z hr
  have haC : IsIso (a.mapHomologicalComplex (.up ℤ)).unit := homological_unit_isIso a
  have hbC : IsIso (b.mapHomologicalComplex (.up ℤ)).unit := homological_unit_isIso b
  exact gluingSumEquivalence (a.mapHomologicalComplex (.up ℤ))
    (b.mapHomologicalComplex (.up ℤ)) (disjoint_complex C τ z s hzs)
    (disjoint_complex C τ s z hsz) (fun {K L} f hs hz ↦ by
      have := hs
      have := hz
      have (p : ℤ) : IsIso (f.f p) :=
        hj.isIso_of_pairFunctor (f.f p)
          (inferInstanceAs (IsIso (((pull C τ s).mapHomologicalComplex (.up ℤ)).map f |>.f p)))
          (inferInstanceAs (IsIso (((pull C τ z).mapHomologicalComplex (.up ℤ)).map f |>.f p)))
      exact HomologicalComplex.Hom.isIso_of_components f)


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private def derivedClopenEquivalence
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion z]
    (hr : Set.range z = (Set.range s)ᶜ) : Derived C τ X ≌ Derived C τ U × Derived C τ Z := by
  have hsz : Disjoint (Set.range s) (Set.range z) := by
    rw [hr]
    exact disjoint_compl_right
  have hzs := hsz.symm
  have haD : IsIso (jAdj C τ s).unit := jAdj_unit_isIso C τ s
  have hbD : IsIso (jAdj C τ z).unit := jAdj_unit_isIso C τ z
  let hj := clopen_pair_joint C τ s z hr
  let hjD := Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory
    (pull C τ s) (pull C τ z) hj
  have hsA : (P C τ s).Additive :=
    inferInstanceAs ((pull C τ s).mapDerivedCategory.Additive)
  have hzA : (P C τ z).Additive :=
    inferInstanceAs ((pull C τ z).mapDerivedCategory.Additive)
  have hsB : PreservesBinaryBiproducts (P C τ s) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have hzB : PreservesBinaryBiproducts (P C τ z) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  exact gluingSumEquivalence (jAdj C τ s) (jAdj C τ z)
    (disjoint_derived C τ z s hzs) (disjoint_derived C τ s z hsz)
    (fun f hs hz ↦ hjD.isIso_of_pairFunctor f hs hz)


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem ordinaryClopenEquivalence_functor
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion z]
    (_hr : Set.range z = (Set.range s)ᶜ) :
    (ordinaryClopenEquivalence (C := C) (τ := τ) s z _hr).functor =
      (pull C τ s).prod' (pull C τ z) := by rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem complexClopenEquivalence_functor
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion z]
    (_hr : Set.range z = (Set.range s)ᶜ) :
    (complexClopenEquivalence (C := C) (τ := τ) s z _hr).functor =
      ((pull C τ s).mapHomologicalComplex (.up ℤ)).prod'
        ((pull C τ z).mapHomologicalComplex (.up ℤ)) := by rfl

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem derivedClopenEquivalence_functor
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion z]
    (_hr : Set.range z = (Set.range s)ᶜ) :
    (derivedClopenEquivalence (C := C) (τ := τ) s z _hr).functor =
      (P C τ s).prod' (P C τ z) := by rfl

attribute [local irreducible] ordinaryClopenEquivalence complexClopenEquivalence
  derivedClopenEquivalence

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem clopen_models
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)
    {U X Z : Scheme.{u}} (s : U ⟶ X) (z : Z ⟶ X)
    [IsOpenImmersion s] [IsClosedImmersion s] [IsOpenImmersion z]
    (hr : Set.range z = (Set.range s)ᶜ) :
    ∃ hpush : PreservesFiniteColimits (push C τ s), Nonempty (ClopenModels C τ s z hpush) := by
  have hpush : PreservesFiniteColimits (push C τ s) := by
    rw [push_eq]
    exact VaryingRing.semilinearClopen_push_colimits C τ s
  have := hpush
  have hsz : Disjoint (Set.range s) (Set.range z) := by
    rw [hr]
    exact disjoint_compl_right
  let a := ordinaryOpenAdj C τ s
  have hau : IsIso a.unit := ordinaryOpenUnitIso C τ s
  let hw := disjoint_ordinary C τ s z hsz
  let E : Modules C τ X ≌ Modules C τ U × Modules C τ Z :=
    ordinaryClopenEquivalence (C := C) (τ := τ) s z hr
  let EC : CochainComplex (Modules C τ X) ℤ ≌
      CochainComplex (Modules C τ U) ℤ × CochainComplex (Modules C τ Z) ℤ :=
    complexClopenEquivalence (C := C) (τ := τ) s z hr
  have haD : IsIso (jAdj C τ s).unit := jAdj_unit_isIso C τ s
  let ED : Derived C τ X ≌ Derived C τ U × Derived C τ Z :=
    derivedClopenEquivalence (C := C) (τ := τ) s z hr
  let eE : E.functor ≅ (pull C τ s).prod' (pull C τ z) :=
    eqToIso (ordinaryClopenEquivalence_functor (C := C) (τ := τ) s z hr)
  let eC : EC.functor ≅ ((pull C τ s).mapHomologicalComplex (.up ℤ)).prod'
      ((pull C τ z).mapHomologicalComplex (.up ℤ)) :=
    eqToIso (complexClopenEquivalence_functor (C := C) (τ := τ) s z hr)
  let eD : ED.functor ≅ (P C τ s).prod' (P C τ z) :=
    eqToIso (derivedClopenEquivalence_functor (C := C) (τ := τ) s z hr)
  refine ⟨hpush, ⟨{
    ordinary := E
    ordinaryRestriction := eE
    ordinaryInsertion := Functor.isoWhiskerLeft (extension C τ s) eE ≪≫ gluingInsertion a hw
    ordinaryInsertion_unit := ?_
    direct := ordinaryDirect C τ s
    direct_adjunct := ordinaryDirect_adjunct C τ s
    comparison := termwiseIsoModel (ordinaryDirect C τ s) _ (direct_localized C τ s)
    comparison_ordinary := ?_
    projection := projectionModel C τ s
    projection_unit := ordinaryPi_unit C τ s
    ordinary_projection := ?_
    complexes := EC
    complexRestriction := eC
    derived := ED
    derivedRestriction := eD
    derivedInsertion := Functor.isoWhiskerLeft (J C τ s) eD ≪≫
      gluingInsertion (jAdj C τ s) (disjoint_derived C τ s z hsz)
    derivedInsertion_unit := ?_
    derived_projection := ?_
    comparison_shift := openToS_shift C τ s
    projection_shift := pi_shift C τ s }⟩⟩
  · intro N
    change a.unit.app N ≫
      (eE.inv.app _ ≫ (eE.hom.app _ ≫ (gluingInsertion a hw).hom.app N)).1 = 𝟙 N
    rw [← Category.assoc, eE.inv_hom_id_app, Category.id_comp]
    exact gluingInsertion_unit a hw N
  · rfl
  · intro M
    change E.functor.map ((ordinaryPi C τ s).app M) ≫
      (eE.hom.app _ ≫ (gluingInsertion a hw).hom.app ((pull C τ s).obj M)) =
        eE.hom.app M ≫ _
    rw [← Category.assoc, eE.hom.naturality, Category.assoc]
    exact congrArg (fun q ↦ eE.hom.app M ≫ q)
      (gluingInsertion_projection a hw M ((ordinaryPi C τ s).app M)
        (ordinaryPi_component C τ s M))
  · intro N
    change (jAdj C τ s).unit.app N ≫
      (eD.inv.app _ ≫ (eD.hom.app _ ≫
        (gluingInsertion (jAdj C τ s) (disjoint_derived C τ s z hsz)).hom.app N)).1 = 𝟙 N
    rw [← Category.assoc, eD.inv_hom_id_app, Category.id_comp]
    exact gluingInsertion_unit (jAdj C τ s) (disjoint_derived C τ s z hsz) N
  · intro M
    change ED.functor.map ((pi C τ s).app M) ≫
      (eD.hom.app _ ≫ (gluingInsertion (jAdj C τ s)
        (disjoint_derived C τ s z hsz)).hom.app ((P C τ s).obj M)) = eD.hom.app M ≫ _
    rw [← Category.assoc, eD.hom.naturality, Category.assoc]
    exact congrArg (fun q ↦ eD.hom.app M ≫ q)
      (gluingInsertion_projection (jAdj C τ s) (disjoint_derived C τ s z hsz)
        M ((pi C τ s).app M) (pi_components C τ s z hr M).1)

/-- The canonical open/clopen comparisons admit simultaneous shift-compatible
section models on whole semilinear systems.
Source: Stacks 03DI, 03DJ, 04TQ--04TS, 015F, 070H and 07A6; blueprint
`fix-prop-coherence`, maps-used sentence
(blueprint: lem-pur-diagram-open-clopen-shift-models).

Proof:
Use the canonical ordinary open adjunctions and their left-adjoint compositor.
The mate comparison for localization identifies its termwise localization with
`jComp`, and identifies the ordinary open-unit restriction with `restrictionIso`.
The ordinary and localized adjunction units give the displayed normalization
identities. Disjoint restriction vanishes by the ordinary extension-by-zero API.

For complementary opens, the sheaf gluing uniqueness theorem makes the pair of
restrictions faithful on whole systems. Exactness then makes them jointly reflect
isomorphisms. The inverse equivalence is the biproduct of the two extensions;
its unit and counit are built from the open adjunctions. The same construction
works for complexes and derived categories, using componentwise isomorphism
reflection and its exact-derived counterpart. Thus no choice of an unspecified
gluing witness is made.

The canonical map from extension to direct image is the direct-image unit
followed by the inverse open unit. Full faithfulness makes it invertible in the
clopen case. Localizing its transpose identifies it with `openToS`. Localizing
the ordinary direct-image unit followed by this inverse identifies the ordinary
component projection with `pi`. Their restrictions are the identity and zero
components of the product model.

Termwise natural maps have the required degree formulas and complex shift
squares. Exact-derived adjunction units commute with the prescribed termwise
shifts, while the canonical right-derived adjunction commutes with its fixed
K-injective shift. The explicit unit words therefore give all four derived
shift squares. Compositor associativity and the inverse-image unit laws give
the extension compositor laws. These constructions also apply to identity and
empty opens, using only whole-system maps and localization identities.
-/
theorem diagramOpenClopenShiftModels : Nonempty (Models C τ) := by
  exact ⟨by
    refine {
      direct_adjunction_shift := ?_
      opens := ?_
      clopens := ?_
      composition_assoc := ?_
      composition_left_unit := ?_
      composition_right_unit := ?_ }
    · intro X Y v
      exact canonicalRightDerivedAdjunctionShift (ordinaryAdj C τ v)
    · intro U V X s b _ _
      exact Classical.choice (openModels_nonempty C τ s b)
    · exact clopen_models C τ
    · exact (compositor_associativity C τ).2.2
    · exact extension_left_unit C τ
    · exact extension_right_unit C τ
  ⟩

end AlgebraicGeometry.ProEtale.SemilinearProperOpen.DiagramShift
