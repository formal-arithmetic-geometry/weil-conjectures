/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
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
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Realizing derived sequences with varying coefficient sheaves

Source: the extraction of Step 4 of `lem-sf-compact-support-proper-image-tower`;
Stacks Project, Tags 03CW, 03DA, 015F, 04VG and 0030
(blueprint: lem-sf-derived-coefficient-sequence-realization).

All objects and arrows of a sequence live in the individual derived categories.
The index `n : ℕ` labels the positive level `n + 1`. No complex representatives
are chosen for a sequence. The scalar compositor is normalized by the identity
on every underlying section before localization.
-/

@[expose] public section

set_option autoImplicit false

universe u v r w d e

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.DerivedCoefficientSequence

section Scalars

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]

/-- Modules over the underlying ring sheaf, with the existing ringed-site encoding.
Source: Stacks Tag 03CW (blueprint: lem-sf-derived-coefficient-sequence-realization). -/
noncomputable abbrev Modules (A : Sheaf J CommRingCat.{r}) :=
  ringedSiteModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)

/-- Ordinary scalar restriction, unchanged on sections and underlying maps.
Source: Stacks Tag 03CW (blueprint: lem-sf-derived-coefficient-sequence-realization). -/
noncomputable abbrev restriction {A B : Sheaf J CommRingCat.{r}} (f : A ⟶ B) :
    Modules B ⥤ Modules A :=
  SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map f)

/-- Exactness of scalar restriction, using the recorded ordinary-adjunction dependency.
Source: Stacks Tag 03DA (blueprint: lem-sf-derived-coefficient-sequence-realization). -/
noncomputable instance restrictionFiniteLimits {A B : Sheaf J CommRingCat.{r}} (f : A ⟶ B) :
    PreservesFiniteLimits (restriction f) :=
  (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction f).choose

/-- Exactness of scalar restriction, using the recorded ordinary-adjunction dependency.
Source: Stacks Tag 03DA (blueprint: lem-sf-derived-coefficient-sequence-realization). -/
noncomputable instance restrictionFiniteColimits {A B : Sheaf J CommRingCat.{r}} (f : A ⟶ B) :
    PreservesFiniteColimits (restriction f) :=
  (SheafOfModules.sheafRingCoefficientOrdinaryAdjunction f).choose_spec.choose

set_option linter.unusedSectionVars false in
/-- The uniquely specified ordinary scalar compositor is the identity on sections.
Source: the sectionwise calculation in Step 2 of the node, Stacks Tag 03CW
(blueprint: lem-sf-derived-coefficient-sequence-realization).
Proof: On U the two actions are g_U(f_U(a)) and h_U(a), equal by hfg.
The identity function is linear in both directions and commutes with restrictions
and module maps. These maps define the natural isomorphism. Sectionwise equality
of maps gives uniqueness. -/
theorem existsUnique_ordinaryComparison {A B D : Sheaf J CommRingCat.{r}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (hfg : f ≫ g = h) :
    ∃! c : restriction g ⋙ restriction f ≅ restriction h,
      ∀ (M : Modules D) (U : Cᵒᵖ) (x : M.val.obj U),
        ((c.hom.app M).val.app U) x = x := by
  let c : restriction g ⋙ restriction f ≅ restriction h :=
    NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦
        (ModuleCat.restrictScalarsComp'App (f.hom.app U).hom (g.hom.app U).hom
          (h.hom.app U).hom (congrArg (fun a ↦ (a.hom.app U).hom) hfg.symm)
          (M.val.obj U)).symm) (by intros; ext x; rfl)))
      (by intros; ext U x; rfl)
  refine ⟨c, ?_, ?_⟩
  · intro M U x
    rfl
  · intro d hd
    apply Iso.ext
    ext M U x
    exact hd M U x

/-- The ordinary compositor selected by its unique identity-on-sections normalization.
Source: Step 2, Stacks Tag 03CW
(blueprint: lem-sf-derived-coefficient-sequence-realization). -/
noncomputable def ordinaryComparison {A B D : Sheaf J CommRingCat.{r}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (hfg : f ≫ g = h) :
    restriction g ⋙ restriction f ≅ restriction h :=
  (existsUnique_ordinaryComparison f g h hfg).exists.choose

private theorem ordinaryComparison_apply {A B D : Sheaf J CommRingCat.{r}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (hfg : f ≫ g = h)
    (M : Modules D) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((ordinaryComparison f g h hfg).hom.app M).val.app U x = x :=
  (existsUnique_ordinaryComparison f g h hfg).exists.choose_spec M U x

private theorem ordinaryComparison_inv_apply {A B D : Sheaf J CommRingCat.{r}}
    (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D) (hfg : f ≫ g = h)
    (M : Modules D) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((ordinaryComparison f g h hfg).inv.app M).val.app U x = x := by
  have hx := congrArg (fun a ↦ a.val.app U x)
    ((ordinaryComparison f g h hfg).inv_hom_id_app M)
  change ((ordinaryComparison f g h hfg).hom.app M).val.app U
    (((ordinaryComparison f g h hfg).inv.app M).val.app U x) = x at hx
  rw [ordinaryComparison_apply] at hx
  exact hx

variable {A B D E : Sheaf J CommRingCat.{r}}
  [HasDerivedCategory.{w} (Modules A)] [HasDerivedCategory.{w} (Modules B)]
  [HasDerivedCategory.{w} (Modules D)] [HasDerivedCategory.{w} (Modules E)]

/-- Termwise scalar restriction localized at quasi-isomorphisms, without resolutions.
Source: Stacks Tag 015F (blueprint: lem-sf-derived-coefficient-sequence-realization). -/
noncomputable abbrev derivedRestriction (f : A ⟶ B) :
    DerivedCategory (Modules B) ⥤ DerivedCategory (Modules A) :=
  (restriction f).mapDerivedCategory

/-- The derived compositor obtained by lifting the normalized ordinary compositor.
Source: Step 3, Stacks Tag 04VG
(blueprint: lem-sf-derived-coefficient-sequence-realization). -/
noncomputable def comparison (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D)
    (hfg : f ≫ g = h) :
    derivedRestriction g ⋙ derivedRestriction f ≅ derivedRestriction h := by
  letI := comp_preservesFiniteLimits (restriction g) (restriction f)
  letI := comp_preservesFiniteColimits (restriction g) (restriction f)
  exact ((restriction g).mapDerivedCategoryCompIso (restriction f)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (ordinaryComparison f g h hfg)

/-- Normalization of the derived compositor on every localized complex.
Source: Steps 2-3, Stacks Tags 015F and 04VG
(blueprint: lem-sf-derived-coefficient-sequence-realization).
Proof: The factorization isomorphisms identify the two derived functors after
precomposition with cochain localization. The natural-transformation localization
property lifts the degreewise identity of ordinaryComparison. Its defining
normalization is exactly the displayed conjugation by those factorizations. -/
theorem comparison_localized (f : A ⟶ B) (g : B ⟶ D) (h : A ⟶ D)
    (hfg : f ≫ g = h) (K : CochainComplex (Modules D) ℤ) :
    (comparison f g h hfg).hom.app (DerivedCategory.Q.obj K) ≫
        (restriction h).mapDerivedCategoryFactors.hom.app K =
      (derivedRestriction f).map ((restriction g).mapDerivedCategoryFactors.hom.app K) ≫
        (restriction f).mapDerivedCategoryFactors.hom.app
          (((restriction g).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (ordinaryComparison f g h hfg).hom (.up ℤ)).app K) :=
  by
    simp only [comparison, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc]
    rw [Functor.mapDerivedCategoryNatIso_fac]
    apply (cancel_epi (((restriction g).mapDerivedCategoryCompIso (restriction f)).hom.app
      (DerivedCategory.Q.obj K))).1
    rw [Iso.hom_inv_id_app_assoc,
      Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]

/-- Cutting a finite chain at an intermediate level gives the same compositor.
Source: Step 4, Stacks Tag 04VG
(blueprint: lem-sf-derived-coefficient-sequence-realization).
Proof: Precompose both sides with cochain localization and insert comparison_localized.
Adjacent factorization isomorphisms cancel. Both remaining chain maps are the identity
on each section, so are equal. Faithful precomposition with localization gives the
displayed equality. Iteration gives coherence for every finite chain and every cut. -/
theorem comparison_assoc (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E)
    (fg : A ⟶ D) (gh : B ⟶ E) (fgh : A ⟶ E)
    (hfg : f ≫ g = fg) (hgh : g ≫ h = gh)
    (hfgh : f ≫ gh = fgh) (hfgh' : fg ≫ h = fgh) :
    Functor.isoWhiskerRight (comparison g h gh hgh) (derivedRestriction f) ≪≫
        comparison f gh fgh hfgh =
      Functor.associator (derivedRestriction h) (derivedRestriction g) (derivedRestriction f) ≪≫
        Functor.isoWhiskerLeft (derivedRestriction h) (comparison f g fg hfg) ≪≫
        comparison fg h fgh hfgh' := by
  let F := restriction h
  let G := restriction g
  let H := restriction f
  let a := (ordinaryComparison g h gh hgh).symm
  let b := (ordinaryComparison f gh fgh hfgh).symm
  let c := (ordinaryComparison f g fg hfg).symm
  let d := (ordinaryComparison fg h fgh hfgh').symm
  have hab : b ≪≫ Functor.isoWhiskerRight a H =
      d ≪≫ Functor.isoWhiskerLeft F c := by
    apply Iso.ext
    ext M U x
    change ((ordinaryComparison g h gh hgh).inv.app M).val.app U
        (((ordinaryComparison f gh fgh hfgh).inv.app M).val.app U x) =
      ((ordinaryComparison f g fg hfg).inv.app ((restriction h).obj M)).val.app U
        (((ordinaryComparison fg h fgh hfgh').inv.app M).val.app U x)
    simp only [ordinaryComparison_inv_apply]
  have hm := congrArg (fun e ↦ (Functor.mapDerivedCategoryNatIso e).hom) hab
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hm
  have hwr := Functor.mapDerivedCategoryNatIso_isoWhiskerRight a H
  have hwl := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft F c
  have ha := Functor.mapDerivedCategoryCompIso_assoc F G H
  apply Iso.symm_eq_iff.mp
  apply Iso.ext
  simp only [comparison, Iso.trans_inv, Iso.symm_inv, Iso.symm_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, Functor.whiskerRight_comp,
    Functor.whiskerLeft_comp, Category.assoc]
  simp only [a, b, c, d, Functor.mapDerivedCategoryNatIso_symm] at hm hwr hwl
  rw [← reassoc_of% hwr, ← reassoc_of% hwl, ← ha, reassoc_of% hm]
  ext X
  simp only [NatTrans.comp_app, Functor.associator_inv_app, Category.comp_id]
  rfl

/-- Derived restriction along the identity is canonically the identity functor.
Source: Step 4, Stacks Tag 04VG
(blueprint: lem-sf-derived-coefficient-sequence-realization). -/
noncomputable def derivedIdentity (A : Sheaf J CommRingCat.{r})
    [HasDerivedCategory.{w} (Modules A)] :
    derivedRestriction (𝟙 A) ≅ 𝟭 (DerivedCategory (Modules A)) :=
  Functor.mapDerivedCategoryNatIso (F := restriction (𝟙 A)) (G := 𝟭 (Modules A))
    (Iso.refl _) ≪≫ Functor.mapDerivedCategoryIdIso (Modules A)

set_option backward.isDefEq.respectTransparency false in
private theorem comparison_identity_right (f : A ⟶ B) :
    comparison f (𝟙 B) f (Category.comp_id f) =
      Functor.isoWhiskerRight (derivedIdentity B) (derivedRestriction f) := by
  have ho : ordinaryComparison f (𝟙 B) f (Category.comp_id f) =
      Iso.refl (restriction f) := by
    apply Iso.ext
    ext M U x
    exact ordinaryComparison_apply f (𝟙 B) f (Category.comp_id f) M U x
  apply Iso.ext
  change (Functor.mapDerivedCategoryCompIso (𝟭 (Modules B)) (restriction f)).inv ≫
      (Functor.mapDerivedCategoryNatIso (ordinaryComparison f (𝟙 B) f
        (Category.comp_id f))).hom = _
  rw [ho]
  change (Functor.mapDerivedCategoryCompIso (𝟭 (Modules B)) (restriction f)).inv ≫
      (Functor.mapDerivedCategoryNatIso (Iso.refl (restriction f))).hom =
    Functor.whiskerRight
      ((Functor.mapDerivedCategoryNatIso (Iso.refl (𝟭 (Modules B)))).hom ≫
        (Functor.mapDerivedCategoryIdIso (Modules B)).hom) (derivedRestriction f)
  simp only [Functor.mapDerivedCategoryNatIso_refl, Category.id_comp]
  apply (cancel_epi (Functor.mapDerivedCategoryCompIso (𝟭 (Modules B))
    (restriction f)).hom).1
  rw [Iso.hom_inv_id_assoc]
  exact (Functor.mapDerivedCategoryCompIso_id_comp (restriction f)).symm

end Scalars

section Sequences

variable (D : ℕ → Type d) [∀ n, Category.{w} (D n)] (S : ∀ n, D n ⥤ D (n + 1))

/-- Objects of the varying-category sequence category in the node.
Source: Step 5 (blueprint: lem-sf-derived-coefficient-sequence-realization). -/
structure Sequence where
  /-- The object at positive level n+1. -/
  obj : ∀ n, D n
  /-- The consecutive semilinear transition. -/
  transition : ∀ n, obj (n + 1) ⟶ (S n).obj (obj n)

variable {D S}

/-- Compatible families of derived arrows, without simultaneous representatives.
Source: Step 5 (blueprint: lem-sf-derived-coefficient-sequence-realization). -/
@[ext]
structure Sequence.Hom (M N : Sequence D S) where
  /-- The level arrows. -/
  app : ∀ n, M.obj n ⟶ N.obj n
  /-- Compatibility with the consecutive transitions. -/
  comm : ∀ n, M.transition n ≫ (S n).map (app n) = app (n + 1) ≫ N.transition n

/-- The componentwise category structure specified in Step 5.
Source: Stacks Tag 0030 (blueprint: lem-sf-derived-coefficient-sequence-realization). -/
instance sequenceCategory : Category (Sequence D S) where
  Hom := Sequence.Hom
  id M := ⟨fun n ↦ 𝟙 (M.obj n), by intro n; simp⟩
  comp a b := ⟨fun n ↦ a.app n ≫ b.app n, by
    intro n
    rw [Functor.map_comp, ← Category.assoc, a.comm, Category.assoc, b.comm,
      ← Category.assoc]⟩
  id_comp a := by apply Sequence.Hom.ext; funext n; exact Category.id_comp _
  comp_id a := by apply Sequence.Hom.ext; funext n; exact Category.comp_id _
  assoc a b c := by apply Sequence.Hom.ext; funext n; exact Category.assoc _ _ _

variable {F : Type e} [Category.{w} F] (Q : ∀ n, D n ⥤ F)
  (γ : ∀ n, S n ⋙ Q (n + 1) ≅ Q n)

/-- Successively restrict along a finite consecutive chain, using the identity for length zero.
Source: Step 4 (blueprint: lem-sf-derived-coefficient-sequence-realization). -/
def iteratedRestriction (n : ℕ) : ∀ k : ℕ, D n ⥤ D (n + k)
  | 0 => 𝟭 (D n)
  | k + 1 => iteratedRestriction n k ⋙ S (n + k)

/-- The iterated adjacent comparisons, with the identity comparison for the empty chain.
Source: Step 4 (blueprint: lem-sf-derived-coefficient-sequence-realization). -/
def iteratedComparison (n : ℕ) :
    ∀ k : ℕ, iteratedRestriction (S := S) n k ⋙ Q (n + k) ≅ Q n
  | 0 => (Q n).leftUnitor
  | k + 1 => Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (iteratedRestriction (S := S) n k) (γ (n + k)) ≪≫
      iteratedComparison n k

/-- The specified consecutive transition after scalar realization.
Source: Step 5 (blueprint: lem-sf-derived-coefficient-sequence-realization). -/
def step (M : Sequence D S) (n : ℕ) :
    (Q (n + 1)).obj (M.obj (n + 1)) ⟶ (Q n).obj (M.obj n) :=
  (Q (n + 1)).map (M.transition n) ≫ (γ n).hom.app (M.obj n)

/-- Realization of an object as the ordinary inverse sequence of the node.
Long transitions are finite composites, with identity for length zero.
Source: Step 5, Stacks Tag 0030
(blueprint: lem-sf-derived-coefficient-sequence-realization). -/
def tower (M : Sequence D S) : ℕᵒᵖ ⥤ F :=
  Functor.ofOpSequence (X := fun n ↦ (Q n).obj (M.obj n)) (step Q γ M)

/-- Naturality of the consecutive realized transition.
Source: Step 6, Stacks Tag 0030
(blueprint: lem-sf-derived-coefficient-sequence-realization).
Proof: Move Q_n(a_n) past gamma_n by naturality, combine the two Q_(n+1) maps,
then use the defining equation of a. Split that composite by functoriality.
This gives exactly the displayed equation; induction gives the longer equations. -/
theorem step_naturality {M N : Sequence D S} (a : M ⟶ N) (n : ℕ) :
    step Q γ M n ≫ (Q n).map (a.app n) =
      (Q (n + 1)).map (a.app (n + 1)) ≫ step Q γ N n := by
  dsimp only [step]
  rw [Category.assoc, ← (γ n).hom.naturality, ← Category.assoc]
  dsimp only [Functor.comp_map]
  rw [← Functor.map_comp]
  rw [a.comm, Functor.map_comp, Category.assoc]

/-- The compatible tower arrow with the specified Q_n(a_n) components.
Source: Step 6, Stacks Tag 0030
(blueprint: lem-sf-derived-coefficient-sequence-realization). -/
def towerMap {M N : Sequence D S} (a : M ⟶ N) : tower Q γ M ⟶ tower Q γ N :=
  NatTrans.ofOpSequence (fun n ↦ (Q n).map (a.app n))
    (fun n ↦ by
      simpa only [tower, Functor.ofOpSequence_map_homOfLE_succ] using
        step_naturality Q γ a n)

/-- Scalar realization is a functor on objects and all derived arrows.
Source: Step 6, Stacks Tag 0030
(blueprint: lem-sf-derived-coefficient-sequence-realization). -/
def realization : Sequence D S ⥤ (ℕᵒᵖ ⥤ F) where
  obj := tower Q γ
  map := towerMap Q γ
  map_id M := by ext n; exact (Q n.unop).map_id (M.obj n.unop)
  map_comp a b := by ext n; exact (Q n.unop).map_comp (a.app n.unop) (b.app n.unop)

/-- The inverse components satisfy the inverse transition equation.
Source: Step 7, Stacks Tag 0030
(blueprint: lem-sf-derived-coefficient-sequence-realization).
Proof: Multiply step_naturality on the left and right by the mapped level inverses.
The inverse identities cancel by functoriality, giving the displayed equation. -/
theorem inverse_step {M N : Sequence D S} (a : M ⟶ N) [∀ n, IsIso (a.app n)] (n : ℕ) :
    (Q (n + 1)).map (inv (a.app (n + 1))) ≫ step Q γ M n =
      step Q γ N n ≫ (Q n).map (inv (a.app n)) := by
  apply (cancel_mono ((Q n).map (a.app n))).1
  simp only [Category.assoc, ← Functor.map_comp, IsIso.inv_hom_id, Functor.map_id,
    Category.comp_id]
  rw [step_naturality, ← Functor.map_comp_assoc, IsIso.inv_hom_id,
    Functor.map_id, Category.id_comp]

/-- The specified componentwise inverse makes the realized arrow an isomorphism.
Source: Step 7, Stacks Tag 0030
(blueprint: lem-sf-derived-coefficient-sequence-realization).
Proof: inverse_step gives a natural transformation with the displayed components,
using induction for longer transitions. Its two composites are componentwise
Q_n(a_n a_n⁻¹) and Q_n(a_n⁻¹ a_n), hence identities. -/
theorem realization_isIso {M N : Sequence D S} (a : M ⟶ N) [∀ n, IsIso (a.app n)] :
    ∃ b : tower Q γ N ⟶ tower Q γ M,
      (∀ n, b.app ⟨n⟩ = (Q n).map (inv (a.app n))) ∧
      (realization Q γ).map a ≫ b = 𝟙 _ ∧ b ≫ (realization Q γ).map a = 𝟙 _ := by
  let b : tower Q γ N ⟶ tower Q γ M :=
    NatTrans.ofOpSequence (fun n ↦ (Q n).map (inv (a.app n))) (fun n ↦ by
      simpa only [tower, Functor.ofOpSequence_map_homOfLE_succ] using
        (inverse_step Q γ a n).symm)
  refine ⟨b, fun _ ↦ rfl, ?_, ?_⟩
  · ext n
    change (Q n.unop).map (a.app n.unop) ≫
      (Q n.unop).map (inv (a.app n.unop)) = 𝟙 _
    rw [← Functor.map_comp, IsIso.hom_inv_id, Functor.map_id]
  · ext n
    change (Q n.unop).map (inv (a.app n.unop)) ≫
      (Q n.unop).map (a.app n.unop) = 𝟙 _
    rw [← Functor.map_comp, IsIso.inv_hom_id, Functor.map_id]

end Sequences

section Realization

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r}) (B : ℕ → Sheaf J CommRingCat.{r})
  [HasDerivedCategory.{w} (Modules R)] [∀ n, HasDerivedCategory.{w} (Modules (B n))]
  (q : ∀ n, B (n + 1) ⟶ B n) (π : ∀ n, R ⟶ B n)
  (hπ : ∀ n, π (n + 1) ≫ q n = π n)

/-- The requested scalar-realization functor for the given ring-sheaf tower.
Source: Steps 1-6, Stacks Tags 03DA, 015F, 04VG and 0030
(blueprint: lem-sf-derived-coefficient-sequence-realization).
The comparisons are the normalized comparisons on the individual derived categories;
`realization_isIso` specifies its componentwise inverse on levelwise isomorphisms. -/
noncomputable def derivedCoefficientSequenceRealization :
    Sequence (fun n ↦ DerivedCategory (Modules (B n)))
        (fun n ↦ derivedRestriction (q n)) ⥤ (ℕᵒᵖ ⥤ DerivedCategory (Modules R)) :=
  realization (fun n ↦ derivedRestriction (π n))
    (fun n ↦ comparison (π (n + 1)) (q n) (π n) (hπ n))

/-- The composite coefficient map along a finite chain; length zero is the identity.
Source: Steps 1-4 (blueprint: lem-sf-derived-coefficient-sequence-realization). -/
def chainMap (n : ℕ) : ∀ k : ℕ, B (n + k) ⟶ B n
  | 0 => 𝟙 (B n)
  | k + 1 => q (n + k) ≫ chainMap n k

include hπ in
set_option linter.unusedSectionVars false in
/-- The compatible projections remain compatible along every finite chain.
Source: Step 4 (blueprint: lem-sf-derived-coefficient-sequence-realization).
Proof: Induct on the chain length. Length zero is the identity law. At the
successor step, associate the composite, use hπ at n+k, then the induction hypothesis. -/
theorem projection_chain (n k : ℕ) : π (n + k) ≫ chainMap B q n k = π n := by
  induction k with
  | zero => simp [chainMap]
  | succ k ih =>
    change π (n + k + 1) ≫ (q (n + k) ≫ chainMap B q n k) = π n
    rw [← Category.assoc, hπ, ih]

/-- Iterated restriction is compared with restriction along the composite coefficient map.
Source: Steps 2-4 (blueprint: lem-sf-derived-coefficient-sequence-realization). -/
noncomputable def chainComparison (n : ℕ) :
    ∀ k : ℕ, iteratedRestriction (S := fun i ↦ derivedRestriction (q i)) n k ≅
      derivedRestriction (chainMap B q n k)
  | 0 => (derivedIdentity (B n)).symm
  | k + 1 => Functor.isoWhiskerRight (chainComparison n k)
      (derivedRestriction (q (n + k))) ≪≫
      comparison (q (n + k)) (chainMap B q n k) (chainMap B q n (k + 1)) rfl

set_option backward.isDefEq.respectTransparency false in
/-- Direct finite-chain comparisons equal the iterated adjacent comparisons, including
length zero. Combined with comparison_assoc this gives composition through every cut.
Source: Step 4, Stacks Tag 04VG
(blueprint: lem-sf-derived-coefficient-sequence-realization).
Proof: Induct on the chain length. Precomposition with cochain localization turns
all compositors into identities on underlying sections. The factorization isomorphisms
cancel, including the unit factors in length zero. Localization.natTrans_ext makes
the natural transformations equal. Equivalently use comparison_assoc at each successor;
the same identity-section check proves the unit case. -/
theorem finite_comparison (n k : ℕ) :
    Functor.isoWhiskerRight (chainComparison B q n k) (derivedRestriction (π (n + k))) ≪≫
        comparison (π (n + k)) (chainMap B q n k) (π n)
          (projection_chain R B q π hπ n k) =
      iteratedComparison (fun i ↦ derivedRestriction (π i))
        (fun i ↦ comparison (π (i + 1)) (q i) (π i) (hπ i)) n k := by
  induction k with
  | zero =>
    change Functor.isoWhiskerRight (derivedIdentity (B n)).symm (derivedRestriction (π n)) ≪≫
      comparison (π n) (𝟙 (B n)) (π n) (Category.comp_id _) =
        (derivedRestriction (π n)).leftUnitor
    rw [comparison_identity_right]
    apply Iso.ext
    ext X
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Iso.symm_hom, Functor.whiskerRight_app,
      ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id, Functor.leftUnitor_hom_app]
    rfl
  | succ k ih =>
    apply Iso.ext
    ext X
    dsimp only [chainComparison, iteratedComparison, iteratedRestriction, Functor.comp_obj]
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.map_comp, Category.assoc]
    have hc := congrArg (fun e ↦ e.hom.app X)
      (comparison_assoc (π (n + k + 1)) (q (n + k)) (chainMap B q n k)
        (π (n + k)) (chainMap B q n (k + 1)) (π n) (hπ (n + k)) rfl
        (projection_chain R B q π hπ n (k + 1)) (projection_chain R B q π hπ n k))
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app] at hc
    simp only [Category.id_comp] at hc ⊢
    erw [hc]
    have hn := (comparison (π (n + k + 1)) (q (n + k)) (π (n + k))
      (hπ (n + k))).hom.naturality ((chainComparison B q n k).hom.app X)
    dsimp only [Functor.comp_map] at hn
    rw [← Category.assoc]
    erw [hn]
    rw [Category.assoc]
    have hi := congrArg (fun e ↦ e.hom.app X) ih
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app] at hi
    erw [hi]

end Realization

end CategoryTheory.DerivedCoefficientSequence
