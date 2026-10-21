/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.SixFunctors.RingedDerivedComparisonData
import Sheaf.Algebra.Homology.KFlatResolution
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Sheaf.SixFunctors.RingedDerivedAdjointLift
import Sheaf.SixFunctors.RingedDerivedTensorLift
import Sheaf.SixFunctors.RingedDerivedIdentityComparison
import Sheaf.Paper.RingedExchangeTensorCoherence
import Sheaf.Paper.RingedSquareTensorCompatibility
import Sheaf.Algebra.Homology.SiteDerivedTensorDescent

/-! # Normalized composition comparisons before the counit consequence

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0D6E, 07A6 and 0FPI.
(blueprint: lem-sfb-ringed-derived-composition-comparison).
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
private def underlyingComposition {X Y Z : Site.{u, w}}
    (f : Morphism X Y) (g : Morphism Y Z) (k : Morphism X Z)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse) :
    k.modules ⋙ Z.sets ≅ (f.modules ⋙ g.modules) ⋙ Z.sets :=
  k.underlying ≪≫
    Functor.isoWhiskerLeft X.sets (conjugateIsoEquiv k.adj (g.adj.comp f.adj) θ.symm) ≪≫
    (Functor.associator X.sets f.direct g.direct).symm ≪≫
    Functor.isoWhiskerRight f.underlying.symm g.direct ≪≫
    Functor.associator f.modules Y.sets g.direct ≪≫
    Functor.isoWhiskerLeft f.modules g.underlying.symm ≪≫
    (Functor.associator f.modules g.modules Z.sets).symm

open CategoryTheory.MonoidalCategory in
private theorem underlyingComposition_transpose {X Y Z : Site.{u, w}}
    (f : Morphism X Y) (g : Morphism Y Z) (k : Morphism X Z)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse) (M : X.modules)
    {T : Sheaf Z.J (Type u)} (x : T ⟶ Z.sets.obj (k.modules.obj M)) :
    transpose f M (transpose g (f.modules.obj M)
      (x ≫ (underlyingComposition f g k θ).hom.app M)) =
        θ.inv.app T ≫ transpose k M x := by
  apply ((g.adj.comp f.adj).homEquiv T (X.sets.obj M)).injective
  have hh := homEquiv_conjugate k.adj (g.adj.comp f.adj) θ T (X.sets.obj M)
    (transpose k M x)
  rw [Equiv.apply_symm_apply] at hh
  rw [← hh]
  rw [Adjunction.comp_homEquiv]
  change g.adj.homEquiv T (f.direct.obj (X.sets.obj M))
    ((f.adj.homEquiv (g.inverse.obj T) (X.sets.obj M))
      (transpose f M (transpose g (f.modules.obj M)
        (x ≫ (underlyingComposition f g k θ).hom.app M)))) = _
  simp only [transpose, Equiv.apply_symm_apply]
  simp only [underlyingComposition, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    Category.id_comp, Category.comp_id, Category.assoc]
  simp only [Iso.inv_hom_id_app]
  rw [← g.adj.homEquiv_naturality_right_symm, Equiv.apply_symm_apply]
  erw [Category.comp_id]
  simp only [Category.assoc]
  rw [← g.direct.map_comp, Iso.inv_hom_id_app, g.direct.map_id]
  erw [Category.comp_id]

open CategoryTheory.MonoidalCategory in
private theorem combination_precomp {X : Site.{u, w}} (M : X.modules)
    {T T' : Sheaf X.J (Type u)} (b : T' ⟶ T) (a : T ⟶ X.ringSets)
    (x y : T ⟶ X.sets.obj M) :
    b ≫ linearCombination M a x y = linearCombination M (b ≫ a) (b ≫ x) (b ≫ y) := rfl

open CategoryTheory.MonoidalCategory in
private theorem underlyingComposition_linear {X Y Z : Site.{u, w}}
    (f : Morphism X Y) (g : Morphism Y Z) (k : Morphism X Z)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse)
    (hθ : k.ringMap = θ.hom.app Z.ringSets ≫ f.inverse.map g.ringMap ≫ f.ringMap)
    (M : X.modules) (T : Sheaf Z.J (Type u)) (a : T ⟶ Z.ringSets)
    (x y : T ⟶ Z.sets.obj (k.modules.obj M)) :
    linearCombination (k.modules.obj M) a x y ≫ (underlyingComposition f g k θ).hom.app M =
      linearCombination ((f.modules ⋙ g.modules).obj M) a
        (x ≫ (underlyingComposition f g k θ).hom.app M)
        (y ≫ (underlyingComposition f g k θ).hom.app M) := by
  apply transpose_injective g (f.modules.obj M) T
  apply transpose_injective f M (g.inverse.obj T)
  dsimp only [Functor.comp_obj]
  rw [underlyingComposition_transpose, transpose_combination,
    transpose_combination, transpose_combination, combination_precomp,
    underlyingComposition_transpose, underlyingComposition_transpose]
  congr 1
  rw [hθ]
  simp only [Functor.map_comp, Category.assoc]
  rw [← θ.inv.naturality_assoc a]
  simp only [Iso.inv_hom_id_app_assoc, Functor.comp_map]

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

open CategoryTheory.MonoidalCategory in
private theorem ordinaryRight_exists {X Y Z : Site.{u, w}}
    (f : Morphism X Y) (g : Morphism Y Z) (k : Morphism X Z)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse)
    (hθ : k.ringMap = θ.hom.app Z.ringSets ≫ f.inverse.map g.ringMap ≫ f.ringMap) :
    ∃ d : k.modules ≅ f.modules ⋙ g.modules,
      ∀ M, Z.sets.map (d.hom.app M) = (underlyingComposition f g k θ).hom.app M := by
  classical
  have he (M : X.modules) : ∃ e : k.modules.obj M ≅ (f.modules ⋙ g.modules).obj M,
      Z.sets.map e.hom = (underlyingComposition f g k θ).hom.app M :=
    moduleIso_of_underlying ((underlyingComposition f g k θ).app M)
      (underlyingComposition_linear f g k θ hθ M)
  let e (M : X.modules) := (he M).choose
  have heq (M : X.modules) :
      Z.sets.map (e M).hom = (underlyingComposition f g k θ).hom.app M := (he M).choose_spec
  refine ⟨NatIso.ofComponents e ?_, heq⟩
  intro M N b
  apply Z.sets.map_injective
  simp only [Functor.map_comp, heq]
  exact (underlyingComposition f g k θ).hom.naturality b

open CategoryTheory.MonoidalCategory in
private def normalizedAdj {X Y : Site.{u, w}} {f : Morphism X Y} (l : Lift f) :
    l.edge.pullback ⊣ f.modules :=
  l.edge.moduleAdjunction.ofNatIsoRight (eqToIso l.pushforward_eq)

open CategoryTheory.MonoidalCategory in
private theorem normalized_transpose {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : Lift f) (M : Y.modules) (N : X.modules) (b : l.edge.pullback.obj M ⟶ N) :
    transpose f N (Y.sets.map ((normalizedAdj l).homEquiv M N b)) =
      l.insertion M ≫ X.sets.map b := by
  apply (f.adj.homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  simpa only [normalizedAdj, Adjunction.homEquiv_ofNatIsoRight_apply,
    Functor.map_comp, eqToIso.hom, Functor.whiskerRight_app, Lift.insertion,
    Category.assoc] using l.ordinary_adjunction M N b

open CategoryTheory.MonoidalCategory in
private theorem transpose_precomp {X Y : Site.{u, w}} (f : Morphism X Y)
    (M : X.modules) {T T' : Sheaf Y.J (Type u)} (a : T' ⟶ T)
    (x : T ⟶ Y.sets.obj (f.modules.obj M)) :
    transpose f M (a ≫ x) = f.inverse.map a ≫ transpose f M x := by
  dsimp only [transpose]
  rw [Category.assoc, f.adj.homEquiv_naturality_left_symm]

open CategoryTheory.MonoidalCategory in
private theorem composite_transpose {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} (lf : Lift f) (lg : Lift g)
    (M : Z.modules) (N : X.modules) (b : lf.edge.pullback.obj (lg.edge.pullback.obj M) ⟶ N) :
    transpose f N (transpose g (f.modules.obj N)
      (Z.sets.map (((normalizedAdj lg).comp (normalizedAdj lf)).homEquiv M N b))) =
      f.inverse.map (lg.insertion M) ≫ lf.insertion (lg.edge.pullback.obj M) ≫ X.sets.map b := by
  rw [Adjunction.comp_homEquiv]
  change transpose f N (transpose g (f.modules.obj N)
    (Z.sets.map ((normalizedAdj lg).homEquiv M (f.modules.obj N)
      ((normalizedAdj lf).homEquiv (lg.edge.pullback.obj M) N b)))) = _
  rw [normalized_transpose, transpose_precomp, normalized_transpose]

open CategoryTheory.MonoidalCategory in
private theorem ordinaryIso_exists {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    (lf : Lift f) (lg : Lift g) (lk : Lift k)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse)
    (hθ : k.ringMap = θ.hom.app Z.ringSets ≫ f.inverse.map g.ringMap ≫ f.ringMap) :
    ∃ e : lk.edge.pullback ≅ lg.edge.pullback ⋙ lf.edge.pullback,
      ∀ M, lk.insertion M ≫ X.sets.map (e.hom.app M) =
        θ.hom.app (Z.sets.obj M) ≫ f.inverse.map (lg.insertion M) ≫
          lf.insertion (lg.edge.pullback.obj M) := by
  obtain ⟨d, hd⟩ := ordinaryRight_exists f g k θ hθ
  let e := ((conjugateIsoEquiv (normalizedAdj lk)
    ((normalizedAdj lg).comp (normalizedAdj lf))).symm d).symm
  have he : conjugateIsoEquiv (normalizedAdj lk)
      ((normalizedAdj lg).comp (normalizedAdj lf)) e.symm = d :=
    Equiv.apply_symm_apply _ d
  refine ⟨e, ?_⟩
  intro M
  let N := lf.edge.pullback.obj (lg.edge.pullback.obj M)
  have hm := homEquiv_conjugate (normalizedAdj lk)
    ((normalizedAdj lg).comp (normalizedAdj lf)) e M N (e.hom.app M)
  rw [he, Iso.inv_hom_id_app] at hm
  have hh := underlyingComposition_transpose f g k θ N
    (Z.sets.map ((normalizedAdj lk).homEquiv M N (e.hom.app M)))
  rw [← hd, ← Z.sets.map_comp, hm, composite_transpose] at hh
  rw [normalized_transpose] at hh
  apply (cancel_epi (θ.inv.app (Z.sets.obj M))).mp
  simp only [Iso.inv_hom_id_app_assoc]
  calc
    _ = f.inverse.map (lg.insertion M) ≫ lf.insertion (lg.edge.pullback.obj M) ≫
        X.sets.map (𝟙 N) := hh.symm
    _ = _ := by
      erw [Functor.map_id, Category.comp_id]

open CategoryTheory.MonoidalCategory in
private theorem preserves_flat {X Y : Site.{u, w}} {f : Morphism X Y} (l : Lift f)
    (P : CochainComplex Y.modules ℤ) (hp : Y.corner.mateFlat P) :
    X.corner.mateFlat ((l.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) := by
  have hf (n : ℤ) : IsFlatOnSite (J := Y.J) (R := Y.A) (P.X n) := by
    let := monoidalCategory Y.A
    exact ObjectProperty.prop_of_iso (exactFunctor _ _)
      (siteSheafTensorRightIso Y.A (P.X n)).symm (hp.2 n)
  obtain ⟨hk, ht⟩ := isKFlat_ringedToposPullback l.edge.inverse l.edge.direct l.edge.adjunction
    l.edge.algebraic l.edge.ringMap l.edge.pullback l.edge.object_eq l.edge.map_eq P
    ((CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).2 hp.1) hf
  refine ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat _).1 hk, ?_⟩
  intro n
  let := monoidalCategory X.A
  exact ObjectProperty.prop_of_iso (exactFunctor _ _)
    (siteSheafTensorRightIso X.A _) (ht n)

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



open CategoryTheory.MonoidalCategory in
private theorem tensor_model (X : Site.{u, w}) :
    ∃ r : RingedTensorModel X.corner, ∀ P Q hP hQ,
      r.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        (X.model.iso X.J X.A X.closed P Q hP.1 hQ.1).hom := by
  let ι : ObjectProperty.FullSubcategory X.corner.mateFlat ⥤
      ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients.{u, u, u}
        (J := X.J) (R := X.A)) := {
    obj := fun P ↦ ⟨P.obj,
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P.obj).2 P.property.1⟩
    map := fun a ↦ ObjectProperty.homMk a.hom }
  let r : RingedTensorModel X.corner := {
    representative := Functor.isoWhiskerLeft (ι.prod ι) X.model.comparison }
  exact ⟨r, fun _ _ _ _ ↦ rfl⟩

open CategoryTheory.MonoidalCategory in
private theorem normalizedLift_exists {X Y : Site.{u, w}} (f : Morphism X Y) :
    Nonempty (Lift f) := by
  obtain ⟨d⟩ := adjointLift_exists f
  obtain ⟨rY, hY⟩ := tensor_model Y
  obtain ⟨rX, hX⟩ := tensor_model X
  obtain ⟨t⟩ := tensorLift_exists d.edge rY rX hY hX
  exact ⟨{
    edge := d.edge
    inverse_eq := d.inverse_eq
    direct_eq := d.direct_eq
    geometric_adjunction := d.geometric_adjunction
    pushforward_eq := d.pushforward_eq
    structural_map := d.structural_map
    ordinary_adjunction := d.ordinary_adjunction
    right_additive := d.right_additive
    eta := d.eta
    isRightDerived := d.isRightDerived
    eta_injective := d.eta_injective
    epsilon_flat := d.epsilon_flat
    canonical_adjunction := d.canonical_adjunction
    tensorModelY := rY
    tensorModelX := rX
    tensorModelY_eq := hY
    tensorModelX_eq := hX
    monoidal := t.monoidal
    tensor_canonical := t.tensor_canonical
    unit_canonical := t.unit_canonical
    symmetric := t.symmetric }⟩

open CategoryTheory.MonoidalCategory in
private theorem geometric_identities (X : Site.{u, w}) :
    ∃ (f : Morphism X X) (θ : f.inverse ≅ 𝟭 (Sheaf X.J (Type u))),
      f.ringMap = θ.hom.app ((sheafCompose X.J
        (CategoryTheory.forget CommRingCat.{u})).obj X.A) := by
  let f : Morphism X X := {
    inverse := 𝟭 _
    direct := 𝟭 _
    adj := Adjunction.id
    leftExact := inferInstance
    ringMap := 𝟙 _
    ring_zero := by intro T z hz U t; simpa using hz U t
    ring_one := by intro T z hz U t; simpa using hz U t
    ring_add := by intro T x y z hz U t; simpa using hz U t
    ring_mul := by intro T x y z hz U t; simpa using hz U t
    modules := 𝟭 _
    additive := inferInstance
    underlying := Iso.refl _
    module_linear := by
      intro M T a x y z hz U t
      simpa [Adjunction.homEquiv, Adjunction.id] using hz U t }
  exact ⟨f, Iso.refl _, rfl⟩

open CategoryTheory.MonoidalCategory in
private theorem conjugate_transpose
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (a' : L' ⊣ R')
    (c : L ≅ L') (U : C) (E : D) (b : U ⟶ R.obj E) :
    (a'.homEquiv U E).symm
        (b ≫ (conjugateIsoEquiv a a' c.symm).hom.app E) =
      c.inv.app U ≫ (a.homEquiv U E).symm b := by
  apply (a'.homEquiv U E).injective
  rw [Equiv.apply_symm_apply, ← homEquiv_conjugate, Equiv.apply_symm_apply]

open CategoryTheory.MonoidalCategory in
private theorem complex_conjugate {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    (lf : Lift f) (lg : Lift g) (lk : Lift k)
    (e : lk.edge.pullback ≅ lg.edge.pullback ⋙ lf.edge.pullback)
    (P : CochainComplex Z.modules ℤ) (I : CochainComplex X.modules ℤ)
    (b : P ⟶ (lk.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj I) :
    ((lf.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv
      ((lg.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) I).symm
      (((lg.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P
        ((lf.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj I)).symm
        (b ≫ (NatTrans.mapHomologicalComplex
          (conjugateIsoEquiv lk.edge.moduleAdjunction
            (lg.edge.moduleAdjunction.comp lf.edge.moduleAdjunction) e.symm).hom
          (.up ℤ)).app I)) =
      (NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app P ≫
        ((lk.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I).symm b := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [Adjunction.homEquiv_counit, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f]
  change _ = e.inv.app (P.X n) ≫ _
  have hh := conjugate_transpose lk.edge.moduleAdjunction
    (lg.edge.moduleAdjunction.comp lf.edge.moduleAdjunction) e (P.X n) (I.X n) (b.f n)
  rw [Adjunction.comp_homEquiv] at hh
  change (lf.edge.moduleAdjunction.homEquiv (lg.edge.pullback.obj (P.X n)) (I.X n)).symm
    ((lg.edge.moduleAdjunction.homEquiv (P.X n)
      (lf.edge.pushforward.obj (I.X n))).symm
      (b.f n ≫ (conjugateIsoEquiv lk.edge.moduleAdjunction
        (lg.edge.moduleAdjunction.comp lf.edge.moduleAdjunction) e.symm).hom.app (I.X n))) =
    _ at hh
  simp only [Adjunction.homEquiv_counit] at hh
  exact hh

open CategoryTheory.MonoidalCategory in
private theorem insertion_eq {X Y : Site.{u, w}} {f : Morphism X Y}
    (l : Lift f) (M : Y.modules) :
    l.insertion M = (eqToIso l.inverse_eq).inv.app (Y.sets.obj M) ≫
      l.edge.insertion M := by
  simp only [Lift.insertion, eqToIso.inv, eqToHom_app]

open CategoryTheory.MonoidalCategory in
private def edgePath {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    (lf : Lift f) (lg : Lift g) (lk : Lift k)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse) :
    lk.edge.inverse ≅ lg.edge.inverse ⋙ lf.edge.inverse :=
  eqToIso lk.inverse_eq ≪≫ θ ≪≫
    Functor.isoWhiskerLeft g.inverse (eqToIso lf.inverse_eq).symm ≪≫
    Functor.isoWhiskerRight (eqToIso lg.inverse_eq).symm lf.edge.inverse

open CategoryTheory.MonoidalCategory in
private theorem edgePath_insertion {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    (lf : Lift f) (lg : Lift g) (lk : Lift k)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse)
    (e : lk.edge.pullback ≅ lg.edge.pullback ⋙ lf.edge.pullback)
    (he : ∀ M, lk.insertion M ≫ X.sets.map (e.hom.app M) =
      θ.hom.app (Z.sets.obj M) ≫ f.inverse.map (lg.insertion M) ≫
        lf.insertion (lg.edge.pullback.obj M)) (M : Z.modules) :
    lk.edge.insertion M ≫ X.sets.map (e.hom.app M) =
      (edgePath lf lg lk θ).hom.app (Z.sets.obj M) ≫
        lf.edge.inverse.map (lg.edge.insertion M) ≫
          lf.edge.insertion (lg.edge.pullback.obj M) := by
  have hh := congrArg (fun z ↦ (eqToIso lk.inverse_eq).hom.app (Z.sets.obj M) ≫ z) (he M)
  simp only [insertion_eq, Category.assoc,
    Iso.hom_inv_id_app_assoc] at hh
  rw [hh]
  simp only [edgePath, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom, Category.assoc]
  rw [← Functor.map_comp_assoc]
  rw [← (eqToIso lf.inverse_eq).inv.naturality_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rfl

open CategoryTheory.MonoidalCategory in
private theorem triangleSquare_exists {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    {i : Morphism X X} (lf : Lift f) (lg : Lift g) (lk : Lift k) (li : Lift i)
    (ζ : i.inverse ≅ 𝟭 (Sheaf X.J (Type u))) (ci : IdentityCore li ζ)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse)
    (e : lk.edge.pullback ≅ lg.edge.pullback ⋙ lf.edge.pullback)
    (he : ∀ M, lk.insertion M ≫ X.sets.map (e.hom.app M) =
      θ.hom.app (Z.sets.obj M) ≫ f.inverse.map (lg.insertion M) ≫
        lf.insertion (lg.edge.pullback.obj M)) :
    ∃ s : RingedTensorSquare Z.corner Y.corner X.corner X.corner
        lg.edge lk.edge lf.edge li.edge,
      s.modules = Functor.isoWhiskerLeft lk.edge.pullback ci.ordinary ≪≫
        Functor.rightUnitor lk.edge.pullback ≪≫ e := by
  let t : li.edge.inverse ≅ 𝟭 (Sheaf X.J (Type u)) := eqToIso li.inverse_eq ≪≫ ζ
  have hi (M : X.modules) : li.edge.insertion M ≫ X.sets.map (ci.ordinary.hom.app M) =
      t.hom.app (X.sets.obj M) := by
    have hh := congrArg (fun z ↦ (eqToIso li.inverse_eq).hom.app (X.sets.obj M) ≫ z)
      (ci.ordinary_insertion M)
    simpa only [insertion_eq, Category.assoc,
      Iso.hom_inv_id_app_assoc, t, Iso.trans_hom, NatTrans.comp_app] using hh
  refine ⟨{
    sets := Functor.isoWhiskerLeft lk.edge.inverse t ≪≫
      Functor.rightUnitor lk.edge.inverse ≪≫ edgePath lf lg lk θ
    modules := Functor.isoWhiskerLeft lk.edge.pullback ci.ordinary ≪≫
      Functor.rightUnitor lk.edge.pullback ≪≫ e
    insertion := ?_ }, rfl⟩
  intro M
  change li.edge.inverse.map (lk.edge.insertion M) ≫ li.edge.insertion _ ≫
    X.sets.map (ci.ordinary.hom.app _ ≫ 𝟙 _ ≫ e.hom.app M) = _
  simp only [Category.id_comp, Functor.map_comp]
  rw [← Category.assoc (li.edge.insertion _), hi]
  erw [t.hom.naturality_assoc (lk.edge.insertion M)]
  change t.hom.app (lk.edge.inverse.obj (Z.sets.obj M)) ≫
    lk.edge.insertion M ≫ X.sets.map (e.hom.app M) = _
  erw [edgePath_insertion lf lg lk θ e he M]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.assoc]
  erw [Category.id_comp]
  rfl


open CategoryTheory.MonoidalCategory in
private theorem square_tensor {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    {i : Morphism X X} (lf : Lift f) (lg : Lift g) (lk : Lift k) (li : Lift i)
    (s : RingedTensorSquare Z.corner Y.corner X.corner X.corner
      lg.edge lk.edge lf.edge li.edge) :
    ∀ U V : Z.D,
      s.derivedComparison.hom.app (Z.closed.tensor.obj (U, V)) ≫
        lf.edge.left.map (lg.tensor U V).hom ≫
        (lf.tensor (lg.edge.left.obj U) (lg.edge.left.obj V)).hom =
      li.edge.left.map (lk.tensor U V).hom ≫
        (li.tensor (lk.edge.left.obj U) (lk.edge.left.obj V)).hom ≫
        X.closed.tensor.map
          (X := (li.edge.left.obj (lk.edge.left.obj U), li.edge.left.obj (lk.edge.left.obj V)))
          (Y := (lf.edge.left.obj (lg.edge.left.obj U), lf.edge.left.obj (lg.edge.left.obj V)))
          (s.derivedComparison.hom.app U, s.derivedComparison.hom.app V) := by
  have model_unique {A : Site.{u, w}} {r r' : RingedTensorModel A.corner}
      (h : ∀ P Q hP hQ, r.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩) =
        r'.representative.hom.app (⟨P, hP⟩, ⟨Q, hQ⟩)) : r = r' := by
    cases r with | mk r =>
    cases r' with | mk r' =>
    congr 1
    apply Iso.ext
    apply NatTrans.ext
    funext B
    exact h B.1.obj B.2.obj B.1.property B.2.property
  have hZY : lg.tensorModelY = lk.tensorModelY := model_unique
    (fun P Q hP hQ ↦ (lg.tensorModelY_eq P Q hP hQ).trans
      (lk.tensorModelY_eq P Q hP hQ).symm)
  have hYY : lg.tensorModelX = lf.tensorModelY := model_unique
    (fun P Q hP hQ ↦ (lg.tensorModelX_eq P Q hP hQ).trans
      (lf.tensorModelY_eq P Q hP hQ).symm)
  have hXX : lk.tensorModelX = li.tensorModelY := model_unique
    (fun P Q hP hQ ↦ (lk.tensorModelX_eq P Q hP hQ).trans
      (li.tensorModelY_eq P Q hP hQ).symm)
  have hXI : lf.tensorModelX = li.tensorModelX := model_unique
    (fun P Q hP hQ ↦ (lf.tensorModelX_eq P Q hP hQ).trans
      (li.tensorModelX_eq P Q hP hQ).symm)
  let l : Z.closed.tensor ⋙ lk.edge.left ⋙ li.edge.left ⟶
      ((lg.edge.left ⋙ lf.edge.left).prod (lg.edge.left ⋙ lf.edge.left)) ⋙ X.closed.tensor :=
    Functor.whiskerLeft Z.closed.tensor s.derivedComparison.hom ≫
      Functor.whiskerRight (lg.edge.tensorComparison lg.tensorModelY lg.tensorModelX).hom
        lf.edge.left ≫
      Functor.whiskerLeft (lg.edge.left.prod lg.edge.left)
        (lf.edge.tensorComparison lg.tensorModelX lf.tensorModelX).hom
  let r : Z.closed.tensor ⋙ lk.edge.left ⋙ li.edge.left ⟶
      ((lg.edge.left ⋙ lf.edge.left).prod (lg.edge.left ⋙ lf.edge.left)) ⋙ X.closed.tensor :=
    Functor.whiskerRight (lk.edge.tensorComparison lg.tensorModelY lk.tensorModelX).hom
      li.edge.left ≫
      Functor.whiskerLeft (lk.edge.left.prod lk.edge.left)
        (li.edge.tensorComparison lk.tensorModelX lf.tensorModelX).hom ≫
      Functor.whiskerRight
        (NatTrans.prod s.derivedComparison.hom s.derivedComparison.hom) X.closed.tensor
  have heq : l = r := by
    obtain ⟨P, hP, _, _, hd⟩ := site_derived_tensor_descent.{u, w, u + 1, w} Z.J Z.A
    apply (hd _ inferInstance _ _).injective
    ext A
    obtain ⟨hp, hpf⟩ := (hP A.1.obj).1 A.1.property
    obtain ⟨hq, hqf⟩ := (hP A.2.obj).1 A.2.property
    have hh : l.app (DerivedCategory.Q.obj A.1.obj.as, DerivedCategory.Q.obj A.2.obj.as) =
        r.app (DerivedCategory.Q.obj A.1.obj.as, DerivedCategory.Q.obj A.2.obj.as) :=
      ringedSquareTensorCompatibility s lg.tensorModelY lg.tensorModelX
        lk.tensorModelX lf.tensorModelX s.derivedComparison
        (Classical.choose_spec s.derivedComparison_existsUnique.exists)
        A.1.obj.as A.2.obj.as hp hpf hq hqf
    let e := (DerivedCategory.quotientCompQhIso Z.modules).app A.1.obj.as |>.symm.prod
      ((DerivedCategory.quotientCompQhIso Z.modules).app A.2.obj.as).symm
    change l.app (DerivedCategory.Qh.obj A.1.obj, DerivedCategory.Qh.obj A.2.obj) =
      r.app (DerivedCategory.Qh.obj A.1.obj, DerivedCategory.Qh.obj A.2.obj)
    apply (cancel_epi ((Z.closed.tensor ⋙ lk.edge.left ⋙ li.edge.left).map e.hom)).mp
    exact (l.naturality e.hom).trans
      ((congrArg (fun z ↦ z ≫
        (((lg.edge.left ⋙ lf.edge.left).prod (lg.edge.left ⋙ lf.edge.left)) ⋙
          X.closed.tensor).map e.hom) hh).trans (r.naturality e.hom).symm)
  have hLf : lf.edge.tensorComparison lg.tensorModelX lf.tensorModelX =
      lf.edge.tensorComparison lf.tensorModelY lf.tensorModelX := by rw [hYY]
  have hLk : lk.edge.tensorComparison lg.tensorModelY lk.tensorModelX =
      lk.edge.tensorComparison lk.tensorModelY lk.tensorModelX := by rw [hZY]
  have hLi : li.edge.tensorComparison lk.tensorModelX lf.tensorModelX =
      li.edge.tensorComparison li.tensorModelY li.tensorModelX := by rw [hXX, hXI]
  intro U V
  have hh := congr_app heq (U, V)
  simp only [l, r, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, NatTrans.prod, hLf, hLk, hLi,
    ← lf.tensor_canonical, ← lg.tensor_canonical, ← lk.tensor_canonical,
    ← li.tensor_canonical] at hh
  exact hh


set_option maxHeartbeats 800000 in
-- Comparing the four recorded site presentations requires additional definitional equality work.
open CategoryTheory.MonoidalCategory in
private theorem derivedTriangle_exists {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    {i : Morphism X X} (lf : Lift f) (lg : Lift g) (lk : Lift k) (li : Lift i)
    (ζ : i.inverse ≅ 𝟭 (Sheaf X.J (Type u))) (ci : IdentityCore li ζ)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse)
    (e : lk.edge.pullback ≅ lg.edge.pullback ⋙ lf.edge.pullback)
    (he : ∀ M, lk.insertion M ≫ X.sets.map (e.hom.app M) =
      θ.hom.app (Z.sets.obj M) ≫ f.inverse.map (lg.insertion M) ≫
        lf.insertion (lg.edge.pullback.obj M)) :
    ∃ c : lk.edge.left ≅ lg.edge.left ⋙ lf.edge.left,
      (∀ P : CochainComplex Z.modules ℤ, Z.corner.mateFlat P →
        c.hom.app (DerivedCategory.Q.obj P) ≫ lf.edge.left.map (lg.alpha P) ≫
          lf.alpha ((lg.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) =
        lk.alpha P ≫ DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P)) ∧
      ∀ U V : Z.D,
        c.hom.app (Z.closed.tensor.obj (U, V)) ≫
          lf.edge.left.map (lg.tensor U V).hom ≫
          (lf.tensor (lg.edge.left.obj U) (lg.edge.left.obj V)).hom =
        (lk.tensor U V).hom ≫ X.closed.tensor.map
          (X := (lk.edge.left.obj U, lk.edge.left.obj V))
          (Y := (lf.edge.left.obj (lg.edge.left.obj U), lf.edge.left.obj (lg.edge.left.obj V)))
          (c.hom.app U, c.hom.app V) := by
  obtain ⟨s, hs⟩ := triangleSquare_exists lf lg lk li ζ ci θ e he
  let c : lk.edge.left ≅ lg.edge.left ⋙ lf.edge.left :=
    (Functor.rightUnitor lk.edge.left).symm ≪≫
      (Functor.isoWhiskerLeft lk.edge.left ci.pullback).symm ≪≫ s.derivedComparison
  have hc (U : Z.D) : c.hom.app U =
      ci.pullback.inv.app (lk.edge.left.obj U) ≫ s.derivedComparison.hom.app U := by
    simp [c]
  refine ⟨c, ?_, ?_⟩
  · intro P hp
    have hd : s.derivedComparison.hom.app (DerivedCategory.Q.obj P) ≫
        lf.edge.left.map (lg.alpha P) ≫
          lf.alpha ((lg.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) =
        li.edge.left.map (lk.alpha P) ≫
          li.alpha ((lk.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map (s.complexComparison.hom.app P) := by
      exact (Classical.choose_spec s.derivedComparison_existsUnique.exists) P hp.1 hp.2
    obtain ⟨a, ha, hi⟩ := ci.pullback_model
      ((lk.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) (preserves_flat lk P hp)
    have hm : (s.complexComparison.hom.app P) =
        a ≫ (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P := by
      apply HomologicalComplex.hom_ext
      intro n
      change s.modules.hom.app (P.X n) = a.f n ≫ e.hom.app (P.X n)
      rw [ha, hs]
      simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
        Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
      erw [Category.id_comp]
      rfl
    rw [hc, Category.assoc, hd, hm]
    rw [(DerivedCategory.Q (C := X.modules)).map_comp a
      ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P)]
    rw [← ci.pullback.inv.naturality_assoc]
    rw [← Category.assoc (li.alpha _), ← hi, Iso.inv_hom_id_app_assoc]
    rfl
  · intro U V
    rw [hc, Category.assoc, square_tensor lf lg lk li s]
    rw [← ci.pullback.inv.naturality_assoc]
    have ht : ci.pullback.inv.app (X.closed.tensor.obj
        (lk.edge.left.obj U, lk.edge.left.obj V)) ≫
        (li.tensor (lk.edge.left.obj U) (lk.edge.left.obj V)).hom =
      X.closed.tensor.map
        (X := (lk.edge.left.obj U, lk.edge.left.obj V))
        (Y := (li.edge.left.obj (lk.edge.left.obj U), li.edge.left.obj (lk.edge.left.obj V)))
        (ci.pullback.inv.app (lk.edge.left.obj U), ci.pullback.inv.app (lk.edge.left.obj V)) := by
      let j := X.closed.tensor.mapIso
        ((ci.pullback.app (lk.edge.left.obj U)).prod (ci.pullback.app (lk.edge.left.obj V)))
      apply (cancel_mono j.hom).mp
      change (_ ≫ X.closed.tensor.map
        (CategoryTheory.Prod.mkHom (ci.pullback.hom.app (lk.edge.left.obj U))
          (ci.pullback.hom.app (lk.edge.left.obj V)))) = _
      rw [Category.assoc, ci.tensor, Iso.inv_hom_id_app]
      exact j.inv_hom_id.symm
    rw [← Category.assoc (ci.pullback.inv.app _)]
    erw [ht]
    simp only [Functor.id_map]
    rw [← X.closed.tensor.map_comp]
    simp only [hc]
    rfl


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


set_option maxHeartbeats 800000 in
-- The two complex adjunctions and their derived counterparts have different presentation wrappers.
open CategoryTheory.MonoidalCategory in
private theorem composite_canonical {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} (lf : Lift f) (lg : Lift g)
    (P : CochainComplex Z.modules ℤ) (I : CochainComplex X.modules ℤ)
    (hp : Z.corner.mateFlat P)
    (b : P ⟶ (lg.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj
      ((lf.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj I)) :
    ((lg.edge.derivedAdjunction.comp lf.edge.derivedAdjunction).homEquiv
      (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)).symm
      (DerivedCategory.Q.map b ≫
        lg.eta.app ((lf.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ≫
          lg.edge.right.map (lf.eta.app I)) =
    lf.edge.left.map (lg.alpha P) ≫
      lf.alpha ((lg.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          (((lf.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv _ I).symm
            (((lg.edge.moduleAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P _).symm
              b)) := by
  rw [Adjunction.comp_homEquiv]
  change (lf.edge.derivedAdjunction.homEquiv _ _).symm
    ((lg.edge.derivedAdjunction.homEquiv _ _).symm
      (DerivedCategory.Q.map b ≫
        lg.eta.app ((lf.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ≫
          lg.edge.right.map (lf.eta.app I))) = _
  rw [← Category.assoc (DerivedCategory.Q.map b),
    lg.edge.derivedAdjunction.homEquiv_naturality_right_symm]
  rw [canonical_all lg P _ hp b]
  rw [Category.assoc, lf.edge.derivedAdjunction.homEquiv_naturality_left_symm,
    canonical_all lf _ I (preserves_flat lg P hp)]

set_option maxHeartbeats 800000 in
-- Resolve the source and compare both composite adjunctions without unfolding their constructions.
open CategoryTheory.MonoidalCategory in
private theorem mate_model {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    (lf : Lift f) (lg : Lift g) (lk : Lift k)
    (e : lk.edge.pullback ≅ lg.edge.pullback ⋙ lf.edge.pullback)
    (c : lk.edge.left ≅ lg.edge.left ⋙ lf.edge.left)
    (hc : ∀ P : CochainComplex Z.modules ℤ, Z.corner.mateFlat P →
      c.hom.app (DerivedCategory.Q.obj P) ≫ lf.edge.left.map (lg.alpha P) ≫
        lf.alpha ((lg.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) =
      lk.alpha P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P))
    (I : CochainComplex X.modules ℤ) :
    lk.eta.app I ≫
        (conjugateIsoEquiv lk.edge.derivedAdjunction
          (lg.edge.derivedAdjunction.comp lf.edge.derivedAdjunction) c.symm).hom.app
            (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (conjugateIsoEquiv lk.edge.moduleAdjunction
            (lg.edge.moduleAdjunction.comp lf.edge.moduleAdjunction) e.symm).hom
          (.up ℤ)).app I) ≫
      lg.eta.app ((lf.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj I) ≫
        lg.edge.right.map (lf.eta.app I) := by
  obtain ⟨P, b, hp, hf, hb, _⟩ := CochainComplex.exists_isKFlatResolution
    ((lk.edge.pushforward.mapHomologicalComplex (.up ℤ)).obj I)
  let := hb
  have hP : Z.corner.mateFlat P := ⟨hp, hf⟩
  apply (cancel_epi (DerivedCategory.Q.map b)).mp
  apply ((lg.edge.derivedAdjunction.comp lf.edge.derivedAdjunction).homEquiv
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)).symm.injective
  rw [← Category.assoc, conjugate_transpose, canonical_all lk P I hP]
  rw [← (DerivedCategory.Q (C := Z.modules)).map_comp_assoc]
  rw [composite_canonical lf lg P I hP, complex_conjugate]
  have ht := congrArg (fun z ↦ c.inv.app (DerivedCategory.Q.obj P) ≫ z) (hc P hP)
  simp only [Iso.inv_hom_id_app_assoc] at ht
  have ht' : c.inv.app (DerivedCategory.Q.obj P) ≫ lk.alpha P =
      lf.edge.left.map (lg.alpha P) ≫
        lf.alpha ((lg.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.inv (.up ℤ)).app P) := by
    let j := (DerivedCategory.Q (C := X.modules)).mapIso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app P)
    apply (cancel_mono j.hom).mp
    change (c.inv.app (DerivedCategory.Q.obj P) ≫ lk.alpha P) ≫ j.hom =
      (lf.edge.left.map (lg.alpha P) ≫
        lf.alpha ((lg.edge.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≫ j.inv) ≫ j.hom
    simp only [Category.assoc, j.inv_hom_id]
    erw [Category.comp_id]
    exact ht.symm
  rw [← Category.assoc, ht']
  simp only [Category.assoc, DerivedCategory.Q.map_comp]

/-- The tensor and representative clauses for composition; the right comparison
is explicitly the adjunction mate of the left comparison.
Source: Stacks Project, Tags 0D6D, 0D6E, 07A6 and 0FPI.
(blueprint: lem-sfb-ringed-derived-composition-comparison). -/
structure CompositionCore {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    (lf : Lift f) (lg : Lift g) (lk : Lift k)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse) where
  ordinary : lk.edge.pullback ≅ lg.edge.pullback ⋙ lf.edge.pullback
  ordinary_insertion : ∀ M : Z.modules,
    lk.insertion M ≫ X.sets.map (ordinary.hom.app M) =
      θ.hom.app (Z.sets.obj M) ≫ f.inverse.map (lg.insertion M) ≫
        lf.insertion (lg.edge.pullback.obj M)
  ordinary_right : lk.edge.pushforward ≅ lf.edge.pushforward ⋙ lg.edge.pushforward
  ordinary_mate : ordinary_right =
    conjugateIsoEquiv lk.edge.moduleAdjunction
      (lg.edge.moduleAdjunction.comp lf.edge.moduleAdjunction) ordinary.symm
  pullback : lk.edge.left ≅ lg.edge.left ⋙ lf.edge.left
  pullback_model : ∀ (P : CochainComplex Z.modules ℤ), Z.corner.mateFlat P →
    pullback.hom.app (DerivedCategory.Q.obj P) ≫
      lf.edge.left.map (lg.alpha P) ≫
      lf.alpha ((lg.edge.pullback.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
    lk.alpha P ≫ DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex ordinary.hom (ComplexShape.up ℤ)).app P)
  kappa_model : ∀ I : CochainComplex X.modules ℤ,
    lk.eta.app I ≫
      (conjugateIsoEquiv lk.edge.derivedAdjunction
        (lg.edge.derivedAdjunction.comp lf.edge.derivedAdjunction)
        pullback.symm).hom.app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex ordinary_right.hom (ComplexShape.up ℤ)).app I) ≫
        lg.eta.app ((lf.edge.pushforward.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
          lg.edge.right.map (lf.eta.app I)
  tensor : ∀ U V : Z.D,
    pullback.hom.app (Z.closed.tensor.obj (U, V)) ≫
      lf.edge.left.map (lg.tensor U V).hom ≫
      (lf.tensor (lg.edge.left.obj U) (lg.edge.left.obj V)).hom =
    (lk.tensor U V).hom ≫
      X.closed.tensor.map
        (X := (lk.edge.left.obj U, lk.edge.left.obj V))
        (Y := (lf.edge.left.obj (lg.edge.left.obj U), lf.edge.left.obj (lg.edge.left.obj V)))
        (pullback.hom.app U, pullback.hom.app V)
  unit : pullback.hom.app Z.closed.monoidal.tensorUnit ≫
      lf.edge.left.map lg.unit.hom ≫ lf.unit.hom = lk.unit.hom

/-- The scalar-association pullback comparison and the normalized right-derived
composition comparison respect tensor, unit and the canonical Hom bijections.
Source: Stacks Project, Modules on Sites, Tags 03D7, 03D8 and 03EL;
Cohomology on Sites, Tags 0D6D, 0D6E, 07A6 and 0FPI.
(blueprint: lem-sfb-ringed-derived-composition-comparison).

Proof:
1. The geometric path isomorphism and structural ring-map equality identify
ordinary scalar extensions. On inserted generators the ordinary comparison is
one tensor x mapped to one tensor (one tensor x). Scalar multiplication extends
this to an invertible module map. The normalized underlying Hom bijections show
that its right mate is the supplied ordinary direct-image comparison. This gives
ordinary, ordinary_insertion, ordinary_right and ordinary_mate.
2. Both ordinary pullbacks preserve flat-term K-flat complexes. Hence the
ordinary comparison localizes to a unique left-derived isomorphism c, with
pullback_model. The signed cochain tensor-composition identity localizes to the
tensor equation; representatives and naturality give it for all derived objects.
On the coefficient unit both paths multiply by the same structural scalar,
giving the unit equation.
3. Use the adjunction mate of c as kappa. Right-derived composition is computed
on a K-injective I by a K-injective resolution j of f_*I. The map g_*j is a
quasi-isomorphism by the resolving-adjoint
acyclicity argument; f_*I need not be K-injective. The universal right-derived
comparison has the representative formula in kappa_model at every complex,
by naturality and the derived universal property.
4. For a flat-term K-flat P and K-injective I, use the two canonical inverse Hom
formulas. Naturality of the ordinary g-counit moves j across the transpose.
The two alpha comparisons and c identify the resulting map with Q of the ordinary
scalar-association transpose, which is the ordinary composite-adjunction formula
of step 1. A right fraction followed by a K-flat resolution represents every
morphism from QN; naturality therefore gives equality of the corresponding Hom bijections for
arbitrary sources. Every target has a K-injective representative, so naturality
also gives the equation at arbitrary targets. This identifies the universal
right-derived comparison with the adjunction mate of c and proves kappa_model.
This result concerns only composition; it asserts neither identity nor geometric
2-isomorphism normalization and does not assert existence of monoidal lifts. -/
theorem compositionCore_exists {X Y Z : Site.{u, w}}
    {f : Morphism X Y} {g : Morphism Y Z} {k : Morphism X Z}
    (lf : Lift f) (lg : Lift g) (lk : Lift k)
    (θ : k.inverse ≅ g.inverse ⋙ f.inverse)
    (hθ : k.ringMap = θ.hom.app
      ((sheafCompose Z.J (CategoryTheory.forget CommRingCat.{u})).obj Z.A) ≫
      f.inverse.map g.ringMap ≫ f.ringMap) :
    Nonempty (CompositionCore lf lg lk θ) := by
  obtain ⟨e, he⟩ := ordinaryIso_exists lf lg lk θ hθ
  obtain ⟨i, ζ, hζ⟩ := geometric_identities X
  obtain ⟨li⟩ := normalizedLift_exists i
  obtain ⟨ci⟩ := identityComparison_exists li ζ hζ
  obtain ⟨c, hc, ht⟩ := derivedTriangle_exists lf lg lk li ζ ci θ e he
  refine ⟨{
    ordinary := e
    ordinary_insertion := he
    ordinary_right := conjugateIsoEquiv lk.edge.moduleAdjunction
      (lg.edge.moduleAdjunction.comp lf.edge.moduleAdjunction) e.symm
    ordinary_mate := rfl
    pullback := c
    pullback_model := hc
    kappa_model := mate_model lf lg lk e c hc
    tensor := ht
    unit := ?_ }⟩
  let : MonoidalCategory Z.D := Z.closed.monoidal
  let : MonoidalCategory Y.D := Y.closed.monoidal
  let : MonoidalCategory X.D := X.closed.monoidal
  let F : Z.D ⥤ X.D := lk.edge.left
  let G : Z.D ⥤ Y.D := lg.edge.left
  let H : Y.D ⥤ X.D := lf.edge.left
  let : F.Monoidal := lk.monoidal.toMonoidal
  let : G.Monoidal := lg.monoidal.toMonoidal
  let : H.Monoidal := lf.monoidal.toMonoidal
  let c' : F ≅ G ⋙ H := c
  have hu := unit_of_tensor c' (fun U V ↦ by
    dsimp only [c', F, G, H, Functor.OplaxMonoidal.comp_δ,
      Functor.CoreMonoidal.toMonoidal, Functor.CoreMonoidal.toOplaxMonoidal]
    exact (ht U V).trans (by rfl))
  simp only [Functor.OplaxMonoidal.comp_η, c', F, G, H] at hu
  exact hu

end CategoryTheory.RingedDerivedComparisons
