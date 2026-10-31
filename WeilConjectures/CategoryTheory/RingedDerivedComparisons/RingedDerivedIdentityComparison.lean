/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedComparisonData
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory

/-! # Identity normalization

Source: Stacks Project, Modules on Sites and Cohomology on Sites,
Tags 03D7, 03D8, 0D6D, 0D6E and 07A6.
(blueprint: lem-sfb-ringed-derived-identity-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u w
open CategoryTheory CategoryTheory.Limits WeilConjectures SheafOfModules
namespace CategoryTheory.RingedDerivedComparisons

attribute [local irreducible] SheafOfModules.monoidalCategory

open CategoryTheory.MonoidalCategory in
private abbrev Site.ringSets (X : Site.{u, w}) :=
  (sheafCompose X.J (CategoryTheory.forget CommRingCat.{u})).obj X.A

open CategoryTheory.MonoidalCategory in
private def linearCombination {X : Site.{u, w}} (M : X.modules)
    {T : Sheaf X.J (Type u)} (a : T ⟶ X.ringSets) (x y : T ⟶ X.sets.obj M) :
    T ⟶ X.sets.obj M :=
  ⟨{ app := fun U ↦ ↾(fun t ↦ @Add.add (M.val.obj U) inferInstance
        (@SMul.smul (X.A.obj.obj U) (M.val.obj U) inferInstance
          (a.hom.app U t) (x.hom.app U t)) (y.hom.app U t))
     naturality := by
       intro U V i
       ext t
       symm
       change (M.val.map i)
         (@Add.add (M.val.obj U) inferInstance
           (@SMul.smul (X.A.obj.obj U) (M.val.obj U) inferInstance
             (a.hom.app U t) (x.hom.app U t)) (y.hom.app U t)) =
         @Add.add (M.val.obj V) inferInstance
           (@SMul.smul (X.A.obj.obj V) (M.val.obj V) inferInstance
             (a.hom.app V (T.obj.map i t)) (x.hom.app V (T.obj.map i t)))
           (y.hom.app V (T.obj.map i t))
       refine Eq.trans ((M.val.map i).hom.map_add _ _) ?_
       apply congrArg₂ (fun (x y : M.val.obj V) ↦ x + y)
       · refine (M.val.map_smul i _ _).trans ?_
         exact congrArg₂ (fun (r : X.A.obj.obj V) (z : M.val.obj V) ↦ r • z)
           (CategoryTheory.congr_fun (a.hom.naturality i) t).symm
           (CategoryTheory.congr_fun (x.hom.naturality i) t).symm
       · exact (CategoryTheory.congr_fun (y.hom.naturality i) t).symm }⟩

open CategoryTheory.MonoidalCategory in
private abbrev transpose {X Y : Site.{u, w}} (f : Morphism X Y)
    (M : X.modules) {T : Sheaf Y.J (Type u)} (x : T ⟶ Y.sets.obj (f.modules.obj M)) :=
  (f.adj.homEquiv T (X.sets.obj M)).symm (x ≫ f.underlying.hom.app M)

open CategoryTheory.MonoidalCategory in
private theorem transpose_injective {X Y : Site.{u, w}} (f : Morphism X Y)
    (M : X.modules) (T : Sheaf Y.J (Type u)) :
    Function.Injective (transpose f M (T := T)) := by
  intro x y h
  apply (cancel_mono (f.underlying.hom.app M)).mp
  exact (f.adj.homEquiv T (X.sets.obj M)).symm.injective h

open CategoryTheory.MonoidalCategory in
private theorem transpose_combination {X Y : Site.{u, w}} (f : Morphism X Y)
    (M : X.modules) {T : Sheaf Y.J (Type u)} (a : T ⟶ Y.ringSets)
    (x y : T ⟶ Y.sets.obj (f.modules.obj M)) :
    transpose f M (linearCombination (f.modules.obj M) a x y) =
      linearCombination M (f.inverse.map a ≫ f.ringMap)
        (transpose f M x) (transpose f M y) := by
  apply Sheaf.hom_ext
  ext U t
  exact f.module_linear M T a x y _ (fun _ _ ↦ rfl) U t

open CategoryTheory.MonoidalCategory in
private theorem homEquiv_conjugate
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R')
    (c : L ≅ L') (U : C) (E : D) (b : L.obj U ⟶ E) :
    a.homEquiv U E b ≫ (conjugateIsoEquiv a a' c.symm).hom.app E =
      a'.homEquiv U E (c.inv.app U ≫ b) := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  let κ := conjugateIsoEquiv a a' c.symm
  change (a.unit.app U ≫ R.map b) ≫ κ.hom.app E = _
  rw [Category.assoc, κ.hom.naturality, ← Category.assoc]
  change (a.unit.app U ≫ (conjugateEquiv a a' c.inv).app (L.obj U)) ≫ _ = _
  rw [unit_conjugateEquiv, Category.assoc, ← R'.map_comp]

open CategoryTheory.MonoidalCategory in
private def liftLinear {X : Site.{u, w}} {M N : X.modules}
    (q : X.sets.obj M ⟶ X.sets.obj N)
    (ha : ∀ U (x y : M.val.obj U), q.hom.app U (x + y) =
      @Add.add (N.val.obj U) inferInstance (q.hom.app U x) (q.hom.app U y))
    (hs : ∀ U (r : X.A.obj.obj U) (x : M.val.obj U),
      q.hom.app U (r • x) = r • (show N.val.obj U from q.hom.app U x)) : M ⟶ N where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := q.hom.app U
          map_add' := ha U
          map_smul' := hs U }
      naturality := by
        intro U V i
        ext x
        exact CategoryTheory.congr_fun (q.hom.naturality i) x }

open CategoryTheory.MonoidalCategory in
private theorem liftLinear_of_combination {X : Site.{u, w}} {M N : X.modules}
    (q : X.sets.obj M ⟶ X.sets.obj N)
    (h : ∀ (T : Sheaf X.J (Type u)) (a : T ⟶ X.ringSets)
      (x y : T ⟶ X.sets.obj M),
      linearCombination M a x y ≫ q = linearCombination N a (x ≫ q) (y ≫ q)) :
    ∃ v : M ⟶ N, X.sets.map v = q := by
  let one (T : Sheaf X.J (Type u)) : T ⟶ X.ringSets :=
    ⟨{ app := fun U ↦ ↾(fun _ ↦ (1 : X.A.obj.obj U))
       naturality := by intro U V i; ext t; exact (X.A.obj.map i).hom.map_one.symm }⟩
  let zero (T : Sheaf X.J (Type u)) : T ⟶ X.sets.obj M :=
    ⟨{ app := fun U ↦ ↾(fun _ ↦ (0 : M.val.obj U))
       naturality := by intro U V i; ext t; exact (M.val.map i).hom.map_zero.symm }⟩
  have ha U (x y : M.val.obj U) : q.hom.app U (x + y) =
      @Add.add (N.val.obj U) inferInstance (q.hom.app U x) (q.hom.app U y) := by
    let T := (X.sets.obj M) ⊗ (X.sets.obj M)
    have hh := congrArg (fun z ↦ z.hom.app U (x, y))
      (h T (one T) (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _))
    change q.hom.app U ((1 : X.A.obj.obj U) • x + y) =
      @Add.add (N.val.obj U) inferInstance
        ((1 : X.A.obj.obj U) • (show N.val.obj U from q.hom.app U x))
        (q.hom.app U y) at hh
    simpa only [one_smul] using hh
  have hz U : q.hom.app U (0 : M.val.obj U) = (0 : N.val.obj U) := by
    have hh := ha U 0 0
    change (q.hom.app U (0 + 0) : N.val.obj U) = _ at hh
    simp only [zero_add] at hh
    exact (@add_eq_left (N.val.obj U) inferInstance inferInstance _ _).mp hh.symm
  have hs U (r : X.A.obj.obj U) (x : M.val.obj U) :
      q.hom.app U (r • x) = r • (show N.val.obj U from q.hom.app U x) := by
    let T := X.ringSets ⊗ (X.sets.obj M)
    have hh := congrArg (fun z ↦ z.hom.app U (r, x))
      (h T (CartesianMonoidalCategory.fst _ _) (CartesianMonoidalCategory.snd _ _) (zero T))
    change q.hom.app U (r • x + (0 : M.val.obj U)) =
      @Add.add (N.val.obj U) inferInstance
        (r • (show N.val.obj U from q.hom.app U x)) (q.hom.app U (0 : M.val.obj U)) at hh
    rw [hz] at hh
    change q.hom.app U (r • x + (0 : M.val.obj U)) =
      (r • (show N.val.obj U from q.hom.app U x)) + (0 : N.val.obj U) at hh
    simpa only [add_zero] using hh
  exact ⟨liftLinear q ha hs, rfl⟩

open CategoryTheory.MonoidalCategory in
private theorem moduleIso_of_underlying {X : Site.{u, w}} {M N : X.modules}
    (q : X.sets.obj M ≅ X.sets.obj N)
    (h : ∀ (T : Sheaf X.J (Type u)) (a : T ⟶ X.ringSets)
      (x y : T ⟶ X.sets.obj M),
      linearCombination M a x y ≫ q.hom =
        linearCombination N a (x ≫ q.hom) (y ≫ q.hom)) :
    ∃ e : M ≅ N, X.sets.map e.hom = q.hom := by
  obtain ⟨v, hv⟩ := liftLinear_of_combination q.hom h
  have hi : ∀ (T : Sheaf X.J (Type u)) (a : T ⟶ X.ringSets)
      (x y : T ⟶ X.sets.obj N),
      linearCombination N a x y ≫ q.inv =
        linearCombination M a (x ≫ q.inv) (y ≫ q.inv) := by
    intro T a x y
    apply (cancel_mono q.hom).mp
    rw [Category.assoc, q.inv_hom_id, Category.comp_id, h]
    simp only [Category.assoc, q.inv_hom_id, Category.comp_id]
  obtain ⟨v', hv'⟩ := liftLinear_of_combination q.inv hi
  refine ⟨⟨v, v', ?_, ?_⟩, hv⟩
  · apply X.sets.map_injective
    rw [Functor.map_comp, hv, hv', q.hom_inv_id, Functor.map_id]
  · apply X.sets.map_injective
    rw [Functor.map_comp, hv, hv', q.inv_hom_id, Functor.map_id]

private def underlyingIdentity {X : Site.{u, w}} (f : Morphism X X)
    (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))) :
    f.modules ⋙ X.sets ≅ X.sets :=
  f.underlying ≪≫
    Functor.isoWhiskerLeft X.sets
      (conjugateIsoEquiv f.adj (Adjunction.id (C := Sheaf X.J (Type u))) θ.symm) ≪≫
    Functor.rightUnitor X.sets

private theorem underlyingIdentity_transpose {X : Site.{u, w}} (f : Morphism X X)
    (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))) (M : X.modules)
    {T : Sheaf X.J (Type u)} (x : T ⟶ X.sets.obj (f.modules.obj M)) :
    x ≫ (underlyingIdentity f θ).hom.app M = θ.inv.app T ≫ transpose f M x := by
  have hh := homEquiv_conjugate f.adj
    (Adjunction.id (C := Sheaf X.J (Type u))) θ T (X.sets.obj M) (transpose f M x)
  rw [Equiv.apply_symm_apply] at hh
  change x ≫ f.underlying.hom.app M ≫
    (conjugateIsoEquiv f.adj (Adjunction.id (C := Sheaf X.J (Type u)))
      θ.symm).hom.app (X.sets.obj M) = θ.inv.app T ≫ transpose f M x at hh
  dsimp only [underlyingIdentity, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app]
  erw [Category.comp_id]
  exact hh

private theorem underlyingIdentity_linear {X : Site.{u, w}} (f : Morphism X X)
    (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u)))
    (hθ : f.ringMap = θ.hom.app X.ringSets)
    (M : X.modules) (T : Sheaf X.J (Type u)) (a : T ⟶ X.ringSets)
    (x y : T ⟶ X.sets.obj (f.modules.obj M)) :
    linearCombination (f.modules.obj M) a x y ≫ (underlyingIdentity f θ).hom.app M =
      linearCombination M a (x ≫ (underlyingIdentity f θ).hom.app M)
        (y ≫ (underlyingIdentity f θ).hom.app M) := by
  rw [underlyingIdentity_transpose, transpose_combination,
    underlyingIdentity_transpose, underlyingIdentity_transpose]
  change linearCombination M
    (θ.inv.app T ≫ f.inverse.map a ≫ f.ringMap)
    (θ.inv.app T ≫ transpose f M x) (θ.inv.app T ≫ transpose f M y) = _
  congr 1
  rw [hθ, ← θ.inv.naturality_assoc a]
  simp

private theorem ordinaryIdentityRight_exists {X : Site.{u, w}} (f : Morphism X X)
    (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u)))
    (hθ : f.ringMap = θ.hom.app X.ringSets) :
    ∃ d : f.modules ≅ 𝟭 X.modules,
      ∀ M, X.sets.map (d.hom.app M) = (underlyingIdentity f θ).hom.app M := by
  classical
  have he (M : X.modules) : ∃ e : f.modules.obj M ≅ M,
      X.sets.map e.hom = (underlyingIdentity f θ).hom.app M :=
    moduleIso_of_underlying ((underlyingIdentity f θ).app M)
      (underlyingIdentity_linear f θ hθ M)
  let e (M : X.modules) := (he M).choose
  have heq (M : X.modules) :
      X.sets.map (e M).hom = (underlyingIdentity f θ).hom.app M := (he M).choose_spec
  refine ⟨NatIso.ofComponents e ?_, heq⟩
  intro M N b
  apply X.sets.map_injective
  change X.sets.map (f.modules.map b ≫ (e N).hom) =
    X.sets.map ((e M).hom ≫ b)
  rw [Functor.map_comp, Functor.map_comp, heq, heq]
  exact (underlyingIdentity f θ).hom.naturality b

private def normalizedAdj {X : Site.{u, w}} {f : Morphism X X} (l : Lift f) :
    l.edge.pullback ⊣ f.modules :=
  l.edge.moduleAdjunction.ofNatIsoRight (eqToIso l.pushforward_eq)

private theorem normalized_transpose {X : Site.{u, w}} {f : Morphism X X}
    (l : Lift f) (M N : X.modules) (b : l.edge.pullback.obj M ⟶ N) :
    transpose f N (X.sets.map ((normalizedAdj l).homEquiv M N b)) =
      l.insertion M ≫ X.sets.map b := by
  apply (f.adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  simpa only [normalizedAdj, Adjunction.homEquiv_ofNatIsoRight_apply,
    Functor.map_comp, eqToIso.hom, Functor.whiskerRight_app, Lift.insertion,
    Category.assoc] using l.ordinary_adjunction M N b

private theorem ordinaryIdentity_exists {X : Site.{u, w}} {f : Morphism X X}
    (l : Lift f) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u)))
    (hθ : f.ringMap = θ.hom.app X.ringSets) :
    ∃ e : l.edge.pullback ≅ 𝟭 X.modules,
      ∀ M, l.insertion M ≫ X.sets.map (e.hom.app M) = θ.hom.app (X.sets.obj M) := by
  obtain ⟨d, hd⟩ := ordinaryIdentityRight_exists f θ hθ
  let e := ((conjugateIsoEquiv (normalizedAdj l)
    (Adjunction.id (C := X.modules))).symm d).symm
  have he : conjugateIsoEquiv (normalizedAdj l)
      (Adjunction.id (C := X.modules)) e.symm = d := Equiv.apply_symm_apply _ d
  refine ⟨e, ?_⟩
  intro M
  have hm := homEquiv_conjugate (normalizedAdj l)
    (Adjunction.id (C := X.modules)) e M M (e.hom.app M)
  rw [he, Iso.inv_hom_id_app] at hm
  have hh := underlyingIdentity_transpose f θ M
    (X.sets.map ((normalizedAdj l).homEquiv M M (e.hom.app M)))
  rw [← hd, ← X.sets.map_comp, hm, normalized_transpose] at hh
  apply (cancel_epi (θ.inv.app (X.sets.obj M))).mp
  change X.sets.map (𝟙 M) = _ at hh
  change θ.inv.app (X.sets.obj M) ≫
    (l.insertion M ≫ X.sets.map (e.hom.app M)) =
      θ.inv.app (X.sets.obj M) ≫ θ.hom.app (X.sets.obj M)
  rw [Iso.inv_hom_id_app]
  dsimp only [Functor.id_obj] at *
  simpa only [Functor.map_id, Category.assoc] using hh.symm

open CategoryTheory.MonoidalCategory in
private theorem canonical_all {X Y : Site.{u, w}} {f : Morphism X Y} (l : Lift f)
    (P : CochainComplex Y.modules ℤ) (I : CochainComplex X.modules ℤ)
    (hp : Y.corner.mateFlat P)
    (b : P ⟶ (l.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj I) :
    (l.edge.derivedAdjunction.homEquiv (DerivedCategory.Q.obj P)
      (DerivedCategory.Q.obj I)).symm (DerivedCategory.Q.map b ≫ l.eta.app I) =
      l.alpha P ≫ DerivedCategory.Q.map
        (((l.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I).symm b) := by
  let := (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
    X.J X.A).1
  obtain ⟨J, hJ, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective I
  let := hj
  apply (cancel_mono (DerivedCategory.Q.map j)).mp
  rw [← l.edge.derivedAdjunction.homEquiv_naturality_right_symm, Category.assoc]
  have hn := l.eta.naturality j
  dsimp only [Functor.comp_map] at hn
  rw [← hn]
  rw [← Category.assoc, ← DerivedCategory.Q.map_comp]
  refine (l.canonical_adjunction P J hp hJ
    (b ≫ (l.edge.pushforward.mapHomologicalComplex (.up ℤ)).map j)).trans ?_
  have ht :=
    (l.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv_naturality_right_symm b j
  calc
    _ = l.alpha P ≫ DerivedCategory.Q.map
        ((((l.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I).symm b) ≫
          j) := congrArg
            (fun z : (l.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P ⟶ J ↦
              l.alpha P ≫ (DerivedCategory.Q (C := X.modules)).map z) ht
    _ = _ := by
      exact (congrArg (fun z ↦ l.alpha P ≫ z)
        ((DerivedCategory.Q (C := X.modules)).map_comp
          (((l.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I).symm b)
          j)).trans (Category.assoc _ _ _).symm


private instance identityPullback_additive {X : Site.{u, w}} {f : Morphism X X}
    (l : Lift f) : (show X.modules ⥤ X.modules from l.edge.pullback).Additive :=
  l.edge.additive

private instance identityPushforward_additive {X : Site.{u, w}} {f : Morphism X X}
    (l : Lift f) : (show X.modules ⥤ X.modules from l.edge.pushforward).Additive :=
  l.right_additive

private def complexIdentity {X : Site.{u, w}} {F : X.modules ⥤ X.modules}
    [F.PreservesZeroMorphisms] (e : F ≅ 𝟭 X.modules) :
    F.mapHomologicalComplex (.up ℤ) ≅ 𝟭 (CochainComplex X.modules ℤ) :=
  NatIso.ofComponents
    (fun P ↦ HomologicalComplex.Hom.isoOfComponents (fun n ↦ e.app (P.X n))
      (by intro i j hij; exact (e.hom.naturality (P.d i j)).symm))
    (by
      intro P Q b
      apply HomologicalComplex.hom_ext
      intro n
      exact e.hom.naturality (b.f n))

private theorem identity_mate {C : Type*} [Category C] {L R : C ⥤ C}
    (a : L ⊣ R) (e : L ≅ 𝟭 C) (M : C) :
    a.homEquiv M M (e.hom.app M) ≫
      (conjugateIsoEquiv a (Adjunction.id (C := C)) e.symm).hom.app M = 𝟙 M := by
  have h := homEquiv_conjugate a (Adjunction.id (C := C)) e M M (e.hom.app M)
  rw [Iso.inv_hom_id_app] at h
  refine h.trans ?_
  change (𝟙 M) ≫ (𝟙 M) = 𝟙 M
  exact Category.id_comp _

private theorem derivedIdentity_exists {X : Site.{u, w}} {f : Morphism X X}
    (l : Lift f) (e : l.edge.pullback ≅ 𝟭 X.modules) :
    ∃ c : l.edge.left ≅ 𝟭 X.D,
      (∀ P : CochainComplex X.modules ℤ, X.corner.mateFlat P →
        c.hom.app (DerivedCategory.Q.{w}.obj P) =
          l.alpha P ≫ DerivedCategory.Q.{w}.map ((complexIdentity (X := X) e).hom.app P)) ∧
      ∀ I : CochainComplex X.modules ℤ,
        l.eta.app I ≫ (conjugateIsoEquiv l.edge.derivedAdjunction
          (Adjunction.id (C := X.D)) c.symm).hom.app (DerivedCategory.Q.{w}.obj I) =
            DerivedCategory.Q.{w}.map ((complexIdentity (X := X)
              (conjugateIsoEquiv l.edge.moduleAdjunction
                (Adjunction.id (C := X.modules)) e.symm)).hom.app I) := by
  let d := conjugateIsoEquiv l.edge.moduleAdjunction
    (Adjunction.id (C := X.modules)) e.symm
  let β : l.edge.pushforward.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ≅
      DerivedCategory.Q.{w} ⋙ 𝟭 X.D :=
    Functor.isoWhiskerRight (complexIdentity (X := X) d) DerivedCategory.Q.{w} ≪≫
      Functor.leftUnitor DerivedCategory.Q.{w} ≪≫ (Functor.rightUnitor DerivedCategory.Q.{w}).symm
  let W := HomologicalComplex.quasiIso X.modules (.up ℤ)
  have : (DerivedCategory.Q.{w} (C := X.modules)).IsLocalization W := by
    dsimp only [W]
    infer_instance
  have : l.edge.right.IsRightDerivedFunctor l.eta W := l.isRightDerived
  have : (𝟭 X.D).IsRightDerivedFunctor β.hom W :=
    Functor.isRightDerivedFunctor_of_inverts W (𝟭 X.D) β.symm
  let r : l.edge.right ≅ 𝟭 X.D :=
    Functor.rightDerivedUnique l.edge.right (𝟭 X.D) l.eta β.hom W
  have hr (I : CochainComplex X.modules ℤ) :
      l.eta.app I ≫ r.hom.app (DerivedCategory.Q.{w}.obj I) =
        DerivedCategory.Q.{w}.map ((complexIdentity (X := X) d).hom.app I) := by
    simp [r, β]
  let c : l.edge.left ≅ 𝟭 X.D :=
    ((conjugateIsoEquiv l.edge.derivedAdjunction (Adjunction.id (C := X.D))).symm r).symm
  have hc : conjugateIsoEquiv l.edge.derivedAdjunction
      (Adjunction.id (C := X.D)) c.symm = r := Equiv.apply_symm_apply _ r
  refine ⟨c, ?_, ?_⟩
  · intro P hp
    let a := (complexIdentity (X := X) e).hom.app P
    let b := (l.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P P a
    have hb : b ≫ (complexIdentity (X := X) d).hom.app P = 𝟙 P := by
      apply HomologicalComplex.hom_ext
      intro n
      exact identity_mate l.edge.moduleAdjunction e (P.X n)
    have hh := identity_mate l.edge.derivedAdjunction c (DerivedCategory.Q.{w}.obj P)
    erw [hc] at hh
    have hb' : l.edge.derivedAdjunction.homEquiv _ _
        (l.alpha P ≫ DerivedCategory.Q.{w}.map a) ≫ r.hom.app (DerivedCategory.Q.{w}.obj P) =
          𝟙 (DerivedCategory.Q.{w}.obj P) := by
      have hcan := canonical_all l P P hp b
      rw [Equiv.symm_apply_apply] at hcan
      rw [← hcan]
      erw [Equiv.apply_symm_apply, Category.assoc, hr,
        ← DerivedCategory.Q.{w}.map_comp, hb, DerivedCategory.Q.{w}.map_id]
    exact (l.edge.derivedAdjunction.homEquiv _ _).injective
      ((cancel_mono (r.hom.app (DerivedCategory.Q.{w}.obj P))).mp (hh.trans hb'.symm))
  · intro I
    rw [hc]
    exact hr I

private def purePair {X : Site.{u, w}} (M N : X.modules)
    {T : Sheaf X.J (Type u)} (x : T ⟶ X.sets.obj M) (y : T ⟶ X.sets.obj N) :
    T ⟶ X.sets.obj ((monoidalCategory X.A).tensorObj M N) :=
  ⟨{ app := fun U ↦ ↾(fun t ↦ RingedTensor.pure X.A M N U
        (x.hom.app U t) (y.hom.app U t))
     naturality := by
       intro U V i
       ext t
       have hx := NatTrans.naturality_apply x.hom i t
       have hy := NatTrans.naturality_apply y.hom i t
       change RingedTensor.pure X.A M N V (x.hom.app V (T.obj.map i t))
         (y.hom.app V (T.obj.map i t)) =
           ((monoidalCategory X.A).tensorObj M N).val.map i
             (RingedTensor.pure X.A M N U (x.hom.app U t) (y.hom.app U t))
       rw [hx, hy]
       exact (RingedTensor.pure_restrict X.A M N i _ _).symm }⟩

open CategoryTheory.MonoidalCategory in
private theorem ordinaryIdentity_tensor {X : Site.{u, w}} {f : Morphism X X}
    (l : Lift f) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u)))
    (e : l.edge.pullback ≅ 𝟭 X.modules)
    (he : ∀ M, l.insertion M ≫ X.sets.map (e.hom.app M) = θ.hom.app (X.sets.obj M))
    (M N : X.modules) :
    (l.edge.ordinaryTensor.mu M N).hom ≫
        (monoidalCategory X.A).tensorHom (e.hom.app M) (e.hom.app N) =
      e.hom.app ((monoidalCategory X.A).tensorObj M N) := by
  let ζ : l.edge.inverse ≅ 𝟭 (Sheaf X.J (Type u)) := eqToIso l.inverse_eq ≪≫ θ
  have hζ (H : X.modules) :
      l.edge.insertion H ≫ X.sets.map (e.hom.app H) = ζ.hom.app (X.sets.obj H) := by
    apply (cancel_epi (eqToHom (congrArg (fun F ↦ F.obj (X.sets.obj H))
      l.inverse_eq.symm))).mp
    simpa only [Lift.insertion, Category.assoc, ζ, Iso.trans_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using he H
  let T := (monoidalCategory X.A).tensorObj M N
  let v := e.inv.app T ≫ (l.edge.ordinaryTensor.mu M N).hom ≫
    (monoidalCategory X.A).tensorHom (e.hom.app M) (e.hom.app N)
  have hv : v = 𝟙 T := by
    apply RingedTensor.pure_hom_ext X.A M N T
    intro U m n
    let Z := (X.sets.obj M) ⊗ (X.sets.obj N)
    let x : Z ⟶ X.sets.obj M := CartesianMonoidalCategory.fst _ _
    let y : Z ⟶ X.sets.obj N := CartesianMonoidalCategory.snd _ _
    let z := purePair M N x y
    let t := (ζ.inv.app Z).hom.app U (m, n)
    have hp := l.edge.ordinaryTensor.pure M N Z x y z (fun _ _ ↦ rfl) U t
    have heval (H : X.modules) (b : Z ⟶ X.sets.obj H) :
        (l.edge.inverse.map b ≫ l.edge.insertion H).hom.app U t =
          (X.sets.map (e.inv.app H)).hom.app U (b.hom.app U (m, n)) := by
      have hh : l.edge.inverse.map b ≫ l.edge.insertion H =
          ζ.hom.app Z ≫ b ≫ X.sets.map (e.inv.app H) := by
        apply (cancel_mono (X.sets.map (e.hom.app H))).mp
        rw [Category.assoc, hζ, ζ.hom.naturality]
        simp only [Category.assoc, ← X.sets.map_comp, Iso.inv_hom_id_app,
          ]
        rfl
      rw [hh]
      change (X.sets.map (e.inv.app H)).hom.app U
        (b.hom.app U ((ζ.hom.app Z).hom.app U ((ζ.inv.app Z).hom.app U (m, n)))) = _
      rw [show (ζ.hom.app Z).hom.app U ((ζ.inv.app Z).hom.app U (m, n)) = (m, n) from
        congrArg (fun a ↦ a.hom.app U (m, n)) (ζ.inv_hom_id_app Z)]
    change (l.edge.ordinaryTensor.mu M N).hom.val.app U
      ((l.edge.inverse.map z ≫ l.edge.insertion T).hom.app U t) =
        RingedTensor.pure X.A _ _ U
          ((l.edge.inverse.map x ≫ l.edge.insertion M).hom.app U t)
          ((l.edge.inverse.map y ≫ l.edge.insertion N).hom.app U t) at hp
    rw [heval T z, heval M x, heval N y] at hp
    change (l.edge.ordinaryTensor.mu M N).hom.val.app U
      ((e.inv.app T).val.app U (RingedTensor.pure X.A M N U m n)) =
        RingedTensor.pure X.A _ _ U ((e.inv.app M).val.app U m)
          ((e.inv.app N).val.app U n) at hp
    change ((monoidalCategory X.A).tensorHom (e.hom.app M) (e.hom.app N)).val.app U
      ((l.edge.ordinaryTensor.mu M N).hom.val.app U
        ((e.inv.app T).val.app U (RingedTensor.pure X.A M N U m n))) =
      RingedTensor.pure X.A M N U m n
    rw [hp]
    erw [RingedTensor.pure_map]
    have hm := congrArg (fun a ↦ a.val.app U m) (e.inv_hom_id_app M)
    have hn := congrArg (fun a ↦ a.val.app U n) (e.inv_hom_id_app N)
    change (e.hom.app M).val.app U ((e.inv.app M).val.app U m) = m at hm
    change (e.hom.app N).val.app U ((e.inv.app N).val.app U n) = n at hn
    exact congrArg₂ (RingedTensor.pure X.A M N U) hm hn
  have hh := congrArg (fun a ↦ e.hom.app T ≫ a) hv
  dsimp only [v, Functor.id_obj] at hh ⊢
  simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Category.comp_id] using hh

open CategoryTheory.MonoidalCategory in
private abbrev totalTensor (X : Site.{u, w}) :=
  Functor.uncurry.obj ((@curriedTensor X.modules _ (monoidalCategory X.A)).map₂HomologicalComplex
    (.up ℤ) (.up ℤ) (.up ℤ))

private abbrev totalComparison {X : Site.{u, w}} {f : Morphism X X} (l : Lift f)
    (P Q : CochainComplex X.modules ℤ) :=
  l.edge.ordinaryTensor.totalIso X.A X.A l.edge.inverseRing l.edge.inverse
    l.edge.algebraic l.edge.ringMap l.edge.pullback l.edge.object_eq
    l.edge.pushforward l.edge.moduleAdjunction P Q

open CategoryTheory.MonoidalCategory in
private theorem totalIdentity {X : Site.{u, w}} {f : Morphism X X}
    (l : Lift f) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u)))
    (e : l.edge.pullback ≅ 𝟭 X.modules)
    (he : ∀ M, l.insertion M ≫ X.sets.map (e.hom.app M) = θ.hom.app (X.sets.obj M))
    (P Q : CochainComplex X.modules ℤ) :
    (totalComparison l P Q).hom ≫ (complexIdentity (X := X) e).hom.app
        ((totalTensor X).obj (P, Q)) =
      (totalTensor X).map (CategoryTheory.Prod.mkHom
        ((complexIdentity (X := X) e).hom.app P)
        ((complexIdentity (X := X) e).hom.app Q)) := by
  let := monoidalCategory X.A
  let := ringedTensorPreadditive X.A
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro a b hab
  simp only [HomologicalComplex.comp_f, totalComparison,
    CanonicalRingedTensorComparison.totalIso, asIso_hom,
    CanonicalRingedTensorComparison.total, tensorPullbackTotal,
    tensorPullbackTotalComponent, HomologicalComplex.ι_mapBifunctorDesc_assoc]
  change (l.edge.ordinaryTensor.mu (P.X a) (Q.X b)).inv ≫
      l.edge.pullback.map (CochainComplex.ιMapBifunctor P Q (curriedTensor X.modules)
        a b n hab) ≫ e.hom.app (((totalTensor X).obj (P, Q)).X n) = _
  erw [e.hom.naturality]
  erw [← ordinaryIdentity_tensor l θ e he (P.X a) (Q.X b)]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  simp only [totalTensor, Functor.uncurry_obj_map, Functor.map₂HomologicalComplex,
    HomologicalComplex.comp_f, HomologicalComplex.id_f, Functor.id_obj, Functor.id_map,
    HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorMap, curriedTensor_map_app, curriedTensor_obj_map,
    complexIdentity, NatIso.ofComponents_hom_app,
    HomologicalComplex.Hom.isoOfComponents_hom_f, Iso.app_hom]
  simp only [MonoidalCategory.whiskerLeft_id, MonoidalCategory.id_whiskerRight,
    ← Category.assoc]
  erw [← MonoidalCategory.tensorHom_def]

private theorem representative_tensor_identity
    {C : Type*} [Category C] (L : C ⥤ C) (T : C × C ⥤ C)
    (c : L ≅ 𝟭 C) (δ : T ⋙ L ⟶ (L.prod L) ⋙ T)
    {p q s fp fq fs : C} (r : s ≅ T.obj (p, q))
    (αp : L.obj p ⟶ fp) (αq : L.obj q ⟶ fq) (αs : L.obj s ⟶ fs)
    (ap : fp ⟶ p) (aq : fq ⟶ q) (as' : fs ⟶ s) (d : fs ⟶ T.obj (fp, fq))
    (hp : c.hom.app p = αp ≫ ap) (hq : c.hom.app q = αq ≫ aq)
    (hs : c.hom.app s = αs ≫ as')
    (hδ : L.map r.hom ≫ δ.app (p, q) ≫ T.map (CategoryTheory.Prod.mkHom αp αq) = αs ≫ d)
    (hd : d ≫ T.map (CategoryTheory.Prod.mkHom ap aq) = as' ≫ r.hom) :
    δ.app (p, q) ≫ T.map (CategoryTheory.Prod.mkHom (c.hom.app p) (c.hom.app q)) =
      c.hom.app (T.obj (p, q)) := by
  apply (cancel_epi (L.map r.hom)).mp
  rw [c.hom.naturality, hs, hp, hq]
  have hpair : CategoryTheory.Prod.mkHom (αp ≫ ap) (αq ≫ aq) =
      CategoryTheory.Prod.mkHom αp αq ≫ CategoryTheory.Prod.mkHom ap aq := rfl
  rw [hpair, T.map_comp]
  calc
    _ = (L.map r.hom ≫ δ.app (p, q) ≫ T.map (CategoryTheory.Prod.mkHom αp αq)) ≫
        T.map (CategoryTheory.Prod.mkHom ap aq) := by simp only [Category.assoc]
    _ = _ := by rw [hδ, Category.assoc, hd, Category.assoc]; rfl

set_option maxHeartbeats 800000 in
-- The representative equation specializes several universe-polymorphic tensor models.
open CategoryTheory.MonoidalCategory in
private theorem derivedIdentity_tensor_representative {X : Site.{u, w}} {f : Morphism X X}
    (l : Lift f) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u)))
    (e : l.edge.pullback ≅ 𝟭 X.modules)
    (he : ∀ M, l.insertion M ≫ X.sets.map (e.hom.app M) = θ.hom.app (X.sets.obj M))
    (c : l.edge.left ≅ 𝟭 X.D)
    (hc : ∀ P : CochainComplex X.modules ℤ, X.corner.mateFlat P →
      c.hom.app (DerivedCategory.Q.obj P) =
        l.alpha P ≫ DerivedCategory.Q.map ((complexIdentity (X := X) e).hom.app P))
    (P Q : CochainComplex X.modules ℤ) (hp : X.corner.mateFlat P)
    (hq : X.corner.mateFlat Q) :
    (l.tensor (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)).hom ≫ X.closed.tensor.map
        (CategoryTheory.Prod.mkHom (c.hom.app (DerivedCategory.Q.obj P))
          (c.hom.app (DerivedCategory.Q.obj Q))) =
      c.hom.app (X.closed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  let F : CochainComplex X.modules ℤ ⥤ CochainComplex X.modules ℤ :=
    l.edge.pullback.mapHomologicalComplex (.up ℤ)
  let aP : F.obj P ⟶ P := (complexIdentity (X := X) e).hom.app P
  let aQ : F.obj Q ⟶ Q := (complexIdentity (X := X) e).hom.app Q
  let r : DerivedCategory.Q.obj ((totalTensor X).obj (P, Q)) ⟶
      X.closed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
    l.tensorModelY.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)
  have ht : X.corner.mateFlat ((totalTensor X).obj (P, Q)) := by
    have h := KFlatTotalTensorModel.kFlat_total_tensor_model X.A P Q
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp.1)
      ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat Q).2 hq.1)
      (fun n ↦ (exactFunctor _ _).prop_of_iso
        (siteSheafTensorRightIso X.A (P.X n)).symm (hp.2 n))
      (fun n ↦ (exactFunctor _ _).prop_of_iso
        (siteSheafTensorRightIso X.A (Q.X n)).symm (hq.2 n))
    refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 h.1, ?_⟩
    intro n
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso X.A _) (h.2.1 n)
  have hrep := Classical.choose_spec
    (ringedTopoiCanonicalDerivedTensorPullback l.edge.inverse l.edge.direct l.edge.adjunction
      l.edge.algebraic l.edge.ringMap l.edge.pullback l.edge.object_eq l.edge.map_eq
      l.edge.left l.edge.epsilon l.edge.isLeftDerived X.corner.mateFlat X.corner.mateFlat
      (fun _ ↦ Iff.rfl) (fun _ ↦ Iff.rfl) X.closed.tensor X.closed.tensor
      l.tensorModelY.representative l.tensorModelX.representative l.edge.ordinaryTensor
      l.edge.pushforward l.edge.moduleAdjunction).2.exists
  obtain ⟨hp', hq', hrep⟩ := hrep P Q hp hq
  change l.edge.left.map r ≫
      (l.edge.tensorComparison l.tensorModelY l.tensorModelX).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      X.closed.tensor.map (CategoryTheory.Prod.mkHom (l.alpha P) (l.alpha Q)) =
    l.alpha ((totalTensor X).obj (P, Q)) ≫
      (DerivedCategory.Q.mapIso (totalComparison l P Q)).inv ≫
        l.tensorModelX.representative.hom.app (⟨F.obj P, hp'⟩, ⟨F.obj Q, hq'⟩) at hrep
  have hn := l.tensorModelX.representative.hom.naturality
    (CategoryTheory.Prod.mkHom
      (ObjectProperty.homMk aP : (⟨F.obj P, hp'⟩ : X.corner.mateFlat.FullSubcategory) ⟶ ⟨P, hp⟩)
      (ObjectProperty.homMk aQ : (⟨F.obj Q, hq'⟩ : X.corner.mateFlat.FullSubcategory) ⟶ ⟨Q, hq⟩))
  have hmodel : l.tensorModelX.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) = r :=
    (l.tensorModelX_eq P Q hp hq).trans (l.tensorModelY_eq P Q hp hq).symm
  change DerivedCategory.Q.map ((totalTensor X).map (CategoryTheory.Prod.mkHom aP aQ)) ≫
      l.tensorModelX.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩) =
    l.tensorModelX.representative.hom.app (⟨F.obj P, hp'⟩, ⟨F.obj Q, hq'⟩) ≫
      X.closed.tensor.map (CategoryTheory.Prod.mkHom
        (DerivedCategory.Q.map aP) (DerivedCategory.Q.map aQ)) at hn
  rw [hmodel] at hn
  have hm := totalIdentity l θ e he P Q
  have hm' : (totalComparison l P Q).inv ≫
      (totalTensor X).map (CategoryTheory.Prod.mkHom aP aQ) =
        (complexIdentity (X := X) e).hom.app ((totalTensor X).obj (P, Q)) := by
    rw [← hm]
    exact Iso.inv_hom_id_assoc _ _
  have hd : ((DerivedCategory.Q.mapIso (totalComparison l P Q)).inv ≫
      l.tensorModelX.representative.hom.app (⟨F.obj P, hp'⟩, ⟨F.obj Q, hq'⟩)) ≫
        X.closed.tensor.map (CategoryTheory.Prod.mkHom
          (DerivedCategory.Q.map aP) (DerivedCategory.Q.map aQ)) =
      DerivedCategory.Q.map ((complexIdentity (X := X) e).hom.app
        ((totalTensor X).obj (P, Q))) ≫ r := by
    calc
      _ = (DerivedCategory.Q.mapIso (totalComparison l P Q)).inv ≫
          (DerivedCategory.Q.map ((totalTensor X).map (CategoryTheory.Prod.mkHom aP aQ)) ≫ r) :=
        (Category.assoc _ _ _).trans
          (congrArg (fun z ↦ (DerivedCategory.Q.mapIso (totalComparison l P Q)).inv ≫ z)
            hn.symm)
      _ = _ := by
        change DerivedCategory.Q.map (totalComparison l P Q).inv ≫ _ = _
        rw [← DerivedCategory.Q.map_comp_assoc, hm']
  let ri : DerivedCategory.Q.obj ((totalTensor X).obj (P, Q)) ≅
      X.closed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
    l.tensorModelY.representative.app (⟨P, hp⟩, ⟨Q, hq⟩)
  have hh := representative_tensor_identity l.edge.left X.closed.tensor c
    (l.edge.tensorComparison l.tensorModelY l.tensorModelX).hom ri
    (l.alpha P) (l.alpha Q) (l.alpha ((totalTensor X).obj (P, Q)))
    (DerivedCategory.Q.map aP) (DerivedCategory.Q.map aQ)
    (DerivedCategory.Q.map ((complexIdentity (X := X) e).hom.app
      ((totalTensor X).obj (P, Q))))
    ((DerivedCategory.Q.mapIso (totalComparison l P Q)).inv ≫
      l.tensorModelX.representative.hom.app (⟨F.obj P, hp'⟩, ⟨F.obj Q, hq'⟩))
    (hc P hp) (hc Q hq) (hc ((totalTensor X).obj (P, Q)) ht)
    hrep hd
  rw [← l.tensor_canonical] at hh
  exact hh

private theorem flatRepresentative (X : Site.{u, w}) (U : X.D) :
    ∃ P : CochainComplex X.modules ℤ,
      X.corner.mateFlat P ∧ Nonempty (DerivedCategory.Q.obj P ≅ U) := by
  let K := (DerivedCategory.Q (C := X.modules)).objPreimage U
  obtain ⟨P, p, hk, hf, hp, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients K
  have : QuasiIso p := hp
  refine ⟨P, ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).1 hk, ?_⟩,
    ⟨asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso U⟩⟩
  intro n
  exact hf n

private theorem derivedIdentity_tensor {X : Site.{u, w}} {f : Morphism X X}
    (l : Lift f) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u)))
    (e : l.edge.pullback ≅ 𝟭 X.modules)
    (he : ∀ M, l.insertion M ≫ X.sets.map (e.hom.app M) = θ.hom.app (X.sets.obj M))
    (c : l.edge.left ≅ 𝟭 X.D)
    (hc : ∀ P : CochainComplex X.modules ℤ, X.corner.mateFlat P →
      c.hom.app (DerivedCategory.Q.obj P) =
        l.alpha P ≫ DerivedCategory.Q.map ((complexIdentity (X := X) e).hom.app P))
    (U V : X.D) :
    (l.tensor U V).hom ≫ X.closed.tensor.map
        (CategoryTheory.Prod.mkHom (c.hom.app U) (c.hom.app V)) =
      c.hom.app (X.closed.tensor.obj (U, V)) := by
  let a : X.closed.tensor ⋙ l.edge.left ⟶ X.closed.tensor :=
    Functor.whiskerLeft X.closed.tensor c.hom
  let b : X.closed.tensor ⋙ l.edge.left ⟶ X.closed.tensor :=
    (l.edge.tensorComparison l.tensorModelY l.tensorModelX).hom ≫
      Functor.whiskerRight (NatTrans.prod c.hom c.hom) X.closed.tensor
  have h (P Q : CochainComplex X.modules ℤ) (hp : X.corner.mateFlat P)
      (hq : X.corner.mateFlat Q) :
      a.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        b.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) := by
    dsimp only [a, b, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.comp_app, NatTrans.prod]
    rw [← l.tensor_canonical]
    exact (derivedIdentity_tensor_representative l θ e he c hc P Q hp hq).symm
  obtain ⟨P, hp, ⟨i⟩⟩ := flatRepresentative X U
  obtain ⟨Q, hq, ⟨j⟩⟩ := flatRepresentative X V
  have hh : a.app (U, V) = b.app (U, V) := by
    apply (cancel_epi ((X.closed.tensor ⋙ l.edge.left).map (i.prod j).hom)).mp
    exact (a.naturality (i.prod j).hom).trans
      ((congrArg (fun z ↦ z ≫ X.closed.tensor.map (i.prod j).hom) (h P Q hp hq)).trans
        (b.naturality (i.prod j).hom).symm)
  change c.hom.app (X.closed.tensor.obj (U, V)) =
    (l.edge.tensorComparison l.tensorModelY l.tensorModelX).hom.app (U, V) ≫
      X.closed.tensor.map (CategoryTheory.Prod.mkHom (c.hom.app U) (c.hom.app V)) at hh
  rw [← l.tensor_canonical] at hh
  exact hh.symm

open CategoryTheory.MonoidalCategory in
private theorem unit_of_tensor
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (c : F ≅ G)
    (h : ∀ U V, c.hom.app (U ⊗ V) ≫ Functor.OplaxMonoidal.δ G U V =
      Functor.OplaxMonoidal.δ F U V ≫ (c.hom.app U ⊗ₘ c.hom.app V)) :
    c.hom.app (𝟙_ C) ≫ Functor.OplaxMonoidal.η G = Functor.OplaxMonoidal.η F := by
  have hh := c.hom.naturality (λ_ (𝟙_ C)).hom
  rw [← Functor.OplaxMonoidal.left_unitality_hom F,
    ← Functor.OplaxMonoidal.left_unitality_hom G] at hh
  simp only [Category.assoc] at hh
  rw [← Category.assoc (c.hom.app _), h, Category.assoc] at hh
  rw [← leftUnitor_naturality] at hh
  simp only [← tensorHom_id, ← id_tensorHom] at hh
  have hh' := (cancel_epi (Functor.OplaxMonoidal.δ F (𝟙_ C) (𝟙_ C))).mp hh
  simp only [← Category.assoc] at hh'
  have hh'' := (cancel_mono (λ_ (G.obj (𝟙_ C))).hom).mp hh'
  have hright := congrArg (fun z ↦ z ≫ (𝟙 (𝟙_ D) ⊗ₘ c.inv.app (𝟙_ C))) hh''
  simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
    Iso.hom_inv_id_app] at hright
  let : (tensorRight (𝟙_ D)).Faithful :=
    Functor.Faithful.of_iso (rightUnitorNatIso D).symm
  let : (tensorRight (F.obj (𝟙_ C))).Faithful :=
    Functor.Faithful.of_iso ((curriedTensor D).flip.mapIso
      (Functor.Monoidal.εIso F))
  apply (tensorRight (F.obj (𝟙_ C))).map_injective
  change (c.hom.app (𝟙_ C) ≫ Functor.OplaxMonoidal.η G) ▷ F.obj (𝟙_ C) =
    Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ C)
  simpa only [← tensorHom_id] using hright.symm

/-- Representative normalization with the right comparison fixed as the derived
adjunction mate. Hom-bijection compatibility follows formally from that choice.
Source: Stacks Project, Tags 03D7, 03D8 and 07A6.
(blueprint: lem-sfb-ringed-derived-identity-comparison). -/
structure IdentityCore {X : Site.{u, w}} {f : Morphism X X} (l : Lift f)
    (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))) where
  ordinary : l.edge.pullback ≅ 𝟭 X.modules
  ordinary_insertion : ∀ M : X.modules,
    l.insertion M ≫ X.sets.map (ordinary.hom.app M) = θ.hom.app (X.sets.obj M)
  ordinary_right : l.edge.pushforward ≅ 𝟭 X.modules
  ordinary_mate : ordinary_right =
    conjugateIsoEquiv l.edge.moduleAdjunction (Adjunction.id (C := X.modules)) ordinary.symm
  pullback : l.edge.left ≅ 𝟭 X.D
  pullback_model : ∀ P : CochainComplex X.modules ℤ, X.corner.mateFlat P →
    ∃ a : (l.edge.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ P,
      (∀ n : ℤ, a.f n = ordinary.hom.app (P.X n)) ∧
      pullback.hom.app (DerivedCategory.Q.obj P) = l.alpha P ≫ DerivedCategory.Q.map a
  pushforward_model : ∀ I : CochainComplex X.modules ℤ,
    ∃ a : (l.edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ I,
      (∀ n : ℤ, a.f n = ordinary_right.hom.app (I.X n)) ∧
      l.eta.app I ≫ (conjugateIsoEquiv l.edge.derivedAdjunction (Adjunction.id (C := X.D))
        pullback.symm).hom.app (DerivedCategory.Q.obj I) = DerivedCategory.Q.map a
  tensor : ∀ U V : X.D,
    (l.tensor U V).hom ≫ X.closed.tensor.map
        (X := (l.edge.left.obj U, l.edge.left.obj V)) (Y := (U, V))
        (pullback.hom.app U, pullback.hom.app V) =
      pullback.hom.app (X.closed.tensor.obj (U, V))
  unit : l.unit.hom = pullback.hom.app X.closed.monoidal.tensorUnit

/-- Identity normalization for an already normalized lift.
Source: Stacks Project, Modules on Sites and Cohomology on Sites,
Tags 03D7, 03D8, 0D6D, 0D6E and 07A6.
(blueprint: lem-sfb-ringed-derived-identity-comparison).

Proof:
1. Transport module sections across the geometric identity. The structural-ring
map equation makes this transport linear. The geometric Hom bijection lifts it
through the specified direct image, and adjunction mates give ordinary with its
scalar-insertion normalization.
2. Apply right-derived uniqueness to the componentwise ordinary right mate.
Take its left adjunction mate. The canonical transpose formula, extended from
K-injective targets by a K-injective resolution, gives the required formula on
flat-term K-flat sources. The right-derived unit formula holds on every complex.
3. Check ordinary tensor compatibility on pure sections and totalize it degree
by degree. The canonical derived tensor representative equation and naturality
then give compatibility on flat-term K-flat complexes. Resolve arbitrary derived
objects to extend the equation to them. Finally the monoidal left-unit law and
cancellation give the unit equation from tensor compatibility. -/
theorem identityComparison_exists {X : Site.{u, w}} {f : Morphism X X}
    (l : Lift f) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u)))
    (hθ : f.ringMap = θ.hom.app
      ((sheafCompose X.J (CategoryTheory.forget CommRingCat.{u})).obj X.A)) :
    Nonempty (IdentityCore l θ) := by
  obtain ⟨e, he⟩ := ordinaryIdentity_exists l θ hθ
  obtain ⟨c, hc, hr⟩ := derivedIdentity_exists l e
  have ht := derivedIdentity_tensor l θ e he c hc
  refine ⟨{
    ordinary := e
    ordinary_insertion := he
    ordinary_right := conjugateIsoEquiv l.edge.moduleAdjunction
      (Adjunction.id (C := X.modules)) e.symm
    ordinary_mate := rfl
    pullback := c
    pullback_model := fun P hp ↦
      ⟨(complexIdentity (X := X) e).hom.app P, fun _ ↦ rfl, hc P hp⟩
    pushforward_model := fun I ↦
      ⟨(complexIdentity (X := X) (conjugateIsoEquiv l.edge.moduleAdjunction
        (Adjunction.id (C := X.modules)) e.symm)).hom.app I, fun _ ↦ rfl, hr I⟩
    tensor := ht
    unit := ?_ }⟩
  let : MonoidalCategory X.D := X.closed.monoidal
  let F : X.D ⥤ X.D := l.edge.left
  let : F.Monoidal := l.monoidal.toMonoidal
  let c' : F ≅ 𝟭 X.D := c
  have hu := unit_of_tensor c' (fun U V ↦ by
    change c.hom.app (X.closed.tensor.obj (U, V)) ≫ 𝟙 _ =
      (l.tensor U V).hom ≫ X.closed.tensor.map
        (CategoryTheory.Prod.mkHom (c.hom.app U) (c.hom.app V))
    rw [Category.comp_id]
    exact (ht U V).symm)
  change c.hom.app X.closed.monoidal.tensorUnit ≫ 𝟙 _ = l.unit.hom at hu
  rw [Category.comp_id] at hu
  exact hu.symm

end CategoryTheory.RingedDerivedComparisons
