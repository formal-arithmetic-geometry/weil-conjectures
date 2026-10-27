/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q86
-/
module

public import Sheaf.Paper.FiniteCoefficientDescentTwoColimit
public import Sheaf.NumberTheory.Padics.FiniteCoefficientFields
public import Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.FilteredTwoColimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.CategoryTheory.PathCategory.Basic
import Sheaf.AlgebraicGeometry.SplitCoefficientDerivedFaithful
import Sheaf.Paper.QlbarDirectImageComparison
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Sigma

/-!
# Finite coefficient descent for diagrams over the algebraic closure

Source: Weil blueprint, sec-smooth-purity/sk-thm-sp-qbar/sk-thm-sp-qbar-descent.md,
assertions (1)--(3) (blueprint: det-sp-qbar-finite-descent).

A diagram is a functor out of the path category of a finite quiver. Only finitely
many pairs of parallel paths are required to have equal images. This includes
loops and empty paths without imposing infinitely many independent relations.
The Hom-colimit bijection is stated through representatives and eventual equality,
using the canonical scalar transitivity maps of the two-colimit theorem.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

private theorem finite_quiver_descends
    {I : Type*} [Preorder I] [Nonempty I] [IsDirectedOrder I]
    {C : I → Type*} [∀ i, Category (C i)] {D : Type*} [Category D]
    (c : CategoryCocone C D) (hc : c.IsFilteredTwoColimit) (i₀ : I)
    (V : Type v) [Quiver.{w} V] [Finite V] [∀ x y : V, Finite (x ⟶ y)]
    (A : Paths V ⥤ D) :
    ∃ i, i₀ ≤ i ∧ ∃ B : Paths V ⥤ C i, Nonempty (B ⋙ c.Φ i ≅ A) := by
  classical
  choose j X e using fun v : V ↦ hc.essSurjObj (A.obj v)
  let e := fun v ↦ Classical.choice (e v)
  obtain ⟨j₀, hj₀⟩ := Finite.bddAbove_range j
  obtain ⟨i, hi₀, hi⟩ := exists_ge_ge i₀ j₀
  let Y : V → C i := fun v ↦ (c.T ((hj₀ (Set.mem_range_self v)).trans hi)).obj (X v)
  let ε : ∀ v, (c.Φ i).obj (Y v) ≅ A.obj v := fun v ↦
    (c.iso ((hj₀ (Set.mem_range_self v)).trans hi)).app (X v) ≪≫ e v
  let Edge := Σ x y : V, x ⟶ y
  let : Fintype Edge := Fintype.ofFinite _
  have hfinite (S : Finset Edge) :
      ∃ (i : I), i₀ ≤ i ∧ ∃ (Y : V → C i)
        (ε : ∀ v, (c.Φ i).obj (Y v) ≅ A.obj v)
        (m : ∀ a : {a : Edge // a ∈ S}, Y a.val.1 ⟶ Y a.val.2.1),
        ∀ a, (c.Φ i).map (m a) ≫ (ε a.val.2.1).hom =
          (ε a.val.1).hom ≫ A.map (Quiver.Hom.toPath a.val.2.2) := by
    induction S using Finset.induction_on with
    | empty =>
      refine ⟨i, hi₀, Y, ε, ?_, ?_⟩
      · intro a
        exact False.elim (Finset.notMem_empty _ a.property)
      · intro a
        exact False.elim (Finset.notMem_empty _ a.property)
    | @insert a S ha ih =>
      obtain ⟨i, hi, Y, ε, m, hm⟩ := ih
      obtain ⟨j, h, h', f, hf⟩ := hc.homSurj i i (Y a.1) (Y a.2.1)
        ((ε a.1).hom ≫ A.map (Quiver.Hom.toPath a.2.2) ≫ (ε a.2.1).inv)
      have hh : h' = h := Subsingleton.elim _ _
      subst h'
      let Y' : V → C j := fun v ↦ (c.T h).obj (Y v)
      let ε' : ∀ v, (c.Φ j).obj (Y' v) ≅ A.obj v := fun v ↦
        (c.iso h).app (Y v) ≪≫ ε v
      have hnew : (c.Φ j).map f ≫ (ε' a.2.1).hom =
          (ε' a.1).hom ≫ A.map (Quiver.Hom.toPath a.2.2) := by
        dsimp only [ε', Iso.trans_hom, Iso.app_hom]
        apply (cancel_epi ((c.iso h).inv.app (Y a.1))).mp
        apply (cancel_mono ((ε a.2.1).inv)).mp
        simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_app_assoc,
          Iso.hom_inv_id, Iso.hom_inv_id_app, Category.comp_id] using hf.symm
      have hold (b : {b : Edge // b ∈ S}) :
          (c.Φ j).map ((c.T h).map (m b)) ≫ (ε' b.val.2.1).hom =
            (ε' b.val.1).hom ≫ A.map (Quiver.Hom.toPath b.val.2.2) := by
        dsimp only [ε', Iso.trans_hom, Iso.app_hom]
        have hn := (c.iso h).hom.naturality (m b)
        dsimp only [Functor.comp_map] at hn
        rw [← Category.assoc, hn]
        simpa only [Category.assoc] using congrArg ((c.iso h).hom.app (Y b.val.1) ≫ ·)
          (hm b)
      let m' (b : {b : Edge // b ∈ insert a S}) : Y' b.val.1 ⟶ Y' b.val.2.1 := by
        by_cases hb : b.val = a
        · exact eqToHom (congrArg (fun a : Edge ↦ Y' a.1) hb) ≫ f ≫
            eqToHom (congrArg (fun a : Edge ↦ Y' a.2.1) hb.symm)
        · exact (c.T h).map (m ⟨b.val, (Finset.mem_insert.mp b.property).resolve_left hb⟩)
      refine ⟨j, hi.trans h, Y', ε', m', ?_⟩
      rintro ⟨b, hbmem⟩
      by_cases hb : b = a
      · subst b
        simpa only [m', dif_pos rfl, eqToHom_refl, Category.id_comp,
          Category.comp_id] using hnew
      · simpa only [m', dif_neg hb] using
          hold ⟨b, (Finset.mem_insert.mp hbmem).resolve_left hb⟩
  obtain ⟨j, hj, Y, ε, m, hm⟩ := hfinite Finset.univ
  let φ : V ⥤q C j :=
    { obj := Y
      map := fun {x y} f ↦ m ⟨⟨x, y, f⟩, Finset.mem_univ _⟩ }
  let B := Paths.lift φ
  refine ⟨j, hj, B, ⟨NatIso.ofComponents ε ?_⟩⟩
  intro x y f
  induction f using Paths.induction with
  | id => simp
  | @comp x y z p q ih =>
    have hq : B.map ((Paths.of V).map q) = φ.map q := Paths.lift_toPath φ q
    have hm' : (c.Φ j).map (φ.map q) ≫ (ε z).hom =
        (ε y).hom ≫ A.map ((Paths.of V).map q) :=
      hm ⟨⟨y, z, q⟩, Finset.mem_univ _⟩
    simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at ih ⊢
    rw [hq]
    exact (congrArg ((c.Φ j).map (B.map p) ≫ ·) hm').trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ A.map ((Paths.of V).map q)) ih).trans (Category.assoc _ _ _)))

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
  CategoryTheory.Functor.leftDerivedFunctor
  AlgebraicGeometry.ProEtale.CondensedRing.derivedPullIso
  AlgebraicGeometry.ProEtale.CondensedRing.derivedOpenImmersionShriekIso
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
  AlgebraicGeometry.ProEtale.CondensedRing.derivedPushHom
  AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek

private noncomputable def composite_inclusion_iso
    {A B C A' B' C' : Type*}
    [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
    (F : A ⥤ B) (G : B ⥤ C) (iA : A ⥤ A') (iB : B ⥤ B') (iC : C ⥤ C')
    (F' : A' ⥤ B') (G' : B' ⥤ C')
    (eF : F ⋙ iB ≅ iA ⋙ F') (eG : G ⋙ iC ≅ iB ⋙ G') :
    (F ⋙ G) ⋙ iC ≅ iA ⋙ (F' ⋙ G') :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F eG ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eF G' ≪≫
    Functor.associator _ _ _

private noncomputable def qbar_pull_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (F : PadicAlgCl.FiniteIntermediateField ℓ) :
    CondensedRing.boundedConstructibleUpperStar (Profinite.continuousMapRingObj F) ℓ f ⋙
        constructibleToPadicAlgCl X.left ℓ F ≅
      constructibleToPadicAlgCl Y.left ℓ F ⋙
        CondensedRing.boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f := by
  apply Functor.fullyFaithfulCancelRight
    (boundedConstructible (padicAlgClRingObj X.left ℓ)).ι
  exact composite_inclusion_iso _ _ _ _ _ _ _
      (CondensedRing.boundedConstructibleUpperStarCompatibility
        (Profinite.continuousMapRingObj F) ℓ f)
      (ObjectProperty.liftCompιIso _ _ _) ≪≫
    Functor.isoWhiskerLeft (boundedConstructible (padicSubfieldRingObj Y.left ℓ F)).ι
      (CondensedRing.derivedPullIso
        (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) f.left) ≪≫
    (composite_inclusion_iso _ _ _ _ _ _ _
      (ObjectProperty.liftCompιIso _ _ _)
      (CondensedRing.boundedConstructibleUpperStarCompatibility
        (Profinite.padicAlgClRingObj ℓ) ℓ f)).symm

private theorem composite_comparison_naturality
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    (J : C ⥤ D) (R : D ⥤ E) (TX : C ⥤ C') (TZ : D ⥤ D') (TY : E ⥤ E')
    (J' : C' ⥤ D') (P : D' ⥤ E')
    (α : R ⋙ TY ⟶ TZ ⋙ P) (ε : J ⋙ TZ ≅ TX ⋙ J')
    {K L : C} (g : K ⟶ L) :
    TY.map (R.map (J.map g)) ≫ (α.app (J.obj L) ≫ P.map (ε.hom.app L)) =
      (α.app (J.obj K) ≫ P.map (ε.hom.app K)) ≫ P.map (J'.map (TX.map g)) := by
  have hα := α.naturality (J.map g)
  have hε := congrArg P.map (ε.hom.naturality g)
  dsimp only [Functor.comp_map] at hα hε
  simp only [Functor.map_comp] at hε
  calc
    _ = (TY.map (R.map (J.map g)) ≫ α.app (J.obj L)) ≫ P.map (ε.hom.app L) :=
      (Category.assoc _ _ _).symm
    _ = (α.app (J.obj K) ≫ P.map (TZ.map (J.map g))) ≫ P.map (ε.hom.app L) :=
      congrArg (· ≫ P.map (ε.hom.app L)) hα
    _ = α.app (J.obj K) ≫
        (P.map (TZ.map (J.map g)) ≫ P.map (ε.hom.app L)) := Category.assoc _ _ _
    _ = α.app (J.obj K) ≫
        (P.map (ε.hom.app K) ≫ P.map (J'.map (TX.map g))) := congrArg _ hε
    _ = _ := (Category.assoc _ _ _).symm

private theorem qbar_push_after_open_isIso
    (ℓ : ℕ) [Fact ℓ.Prime] (F : PadicAlgCl.FiniteIntermediateField ℓ)
    {U Z Y : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (g : Z ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1})
      (padicSubfieldRingObj U ℓ F)))
    (hK : DerivedCategory.TStructure.t.bounded K) :
    IsIso ((CondensedRing.derivedPushHom
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) g).app
        (((CondensedRing.openImmersionLowerShriek
          (Profinite.continuousMapRingObj F) j).mapDerivedCategory).obj K)) := by
  exact CondensedRing.isIso_derivedPushHom_padicAlgCl_of_boundedBelow ℓ F g
    ⟨_, ((CondensedRing.openImmersionLowerShriek
      (Profinite.continuousMapRingObj F) j).bounded_mapDerivedCategory_obj hK).1⟩


private noncomputable def scalar_open_proper_iso
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    (J : C ⥤ D) (R : D ⥤ E) (TX : C ⥤ C') (TZ : D ⥤ D') (TY : E ⥤ E')
    (J' : C' ⥤ D') (P : D' ⥤ E')
    (α : R ⋙ TY ⟶ TZ ⋙ P) (ε : J ⋙ TZ ≅ TX ⋙ J')
    (Q : ObjectProperty C) (hα : ∀ K : Q.FullSubcategory, IsIso (α.app (J.obj K.obj))) :
    Q.ι ⋙ ((J ⋙ R) ⋙ TY) ≅ Q.ι ⋙ (TX ⋙ (J' ⋙ P)) := by
  letI : ∀ K : Q.FullSubcategory, IsIso (α.app (J.obj K.obj)) := hα
  exact NatIso.ofComponents
    (fun K ↦ asIso (α.app (J.obj K.obj)) ≪≫ P.mapIso (ε.app K.obj))
    (fun g ↦ composite_comparison_naturality J R TX TZ TY J' P α ε g.hom)

private noncomputable def qbar_ambient_lower_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (F : PadicAlgCl.FiniteIntermediateField ℓ)
    {U Z Y : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j]
    (g : Z ⟶ Y) [QuasiCompact g] [QuasiSeparated g] :
    (boundedConstructible (padicSubfieldRingObj U ℓ F)).ι ⋙
        (((CondensedRing.openImmersionLowerShriek (Profinite.continuousMapRingObj F)
          j).mapDerivedCategory ⋙
            (CondensedRing.lowerStar (Profinite.continuousMapRingObj F) g).rightDerivedFunctor) ⋙
          derivedExtendScalarsToPadicAlgCl Y ℓ F) ≅
      (boundedConstructible (padicSubfieldRingObj U ℓ F)).ι ⋙
        (derivedExtendScalarsToPadicAlgCl U ℓ F ⋙
          ((CondensedRing.openImmersionLowerShriek (Profinite.padicAlgClRingObj ℓ)
            j).mapDerivedCategory ⋙
              (CondensedRing.lowerStar (Profinite.padicAlgClRingObj ℓ) g).rightDerivedFunctor)) :=
  scalar_open_proper_iso _ _ _ _ _ _ _
    (CondensedRing.derivedPushHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) g)
    (CondensedRing.derivedOpenImmersionShriekIso
      (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ F) j) _
    (fun K ↦ qbar_push_after_open_isIso ℓ F j g K.obj K.property.1)

private noncomputable def qbar_lower_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) (F : PadicAlgCl.FiniteIntermediateField ℓ)
    (c : Compactification f.left) :
    CondensedRing.boundedConstructibleLowerShriekOfCompactification
        (Profinite.continuousMapRingObj F) ℓ c ⋙
        constructibleToPadicAlgCl Y.left ℓ F ≅
      constructibleToPadicAlgCl X.left ℓ F ⋙
        CondensedRing.boundedConstructibleLowerShriekOfCompactification
          (Profinite.padicAlgClRingObj ℓ) ℓ c := by
  apply Functor.fullyFaithfulCancelRight
    (boundedConstructible (padicAlgClRingObj Y.left ℓ)).ι
  exact composite_inclusion_iso _ _ _ _ _ _ _
      (CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
        (Profinite.continuousMapRingObj F) ℓ c)
      (ObjectProperty.liftCompιIso _ _ _) ≪≫
    qbar_ambient_lower_iso ℓ F c.i c.g ≪≫
    (composite_inclusion_iso _ _ _ _ _ _ _
      (ObjectProperty.liftCompιIso _ _ _)
      (CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
        (Profinite.padicAlgClRingObj ℓ) ℓ c)).symm


/-- Finite diagrams with finitely many relations descend, shifted Hom sets are filtered
colimits, and pullback and compact support commute with extension to the algebraic closure.
Source: blueprint sk-thm-sp-qbar-descent, assertions (1)--(3)
(blueprint: det-sp-qbar-finite-descent).

Proof: Apply the Hom clause of `finiteCoefficientDescentTwoColimit`, using its equality
of rational constructibility predicates. For finite diagrams, choose models of all vertices
and lift the finitely many generating arrows successively using Hom surjectivity of the
filtered two-colimit cocone. Its scalar transitivity isomorphisms transport all previous
lifts at each enlargement. The universal property of the path category assembles the
resulting diagram and its natural isomorphism. Faithfulness of derived scalar extension
to the closure reflects the specified relations, so no further enlargement is needed.
For pullback, restrict `derivedPullIso` to bounded constructible objects. For compact
support, use the compactification in the definition of the actual functor. The open
extension preserves boundedness. The proper pushforward comparison is therefore invertible
by `isIso_derivedPushHom_padicAlgCl_of_boundedBelow`. Compose it with
`derivedOpenImmersionShriekIso`; restriction of this natural comparison to the full
bounded constructible subcategories gives the required natural isomorphism. -/
theorem qbarFiniteDescent
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ((∀ (K L : PadicSubfieldConstructible T ℓ E) (q : ℤ),
      (∀ ψ : (derivedExtendScalarsToPadicAlgCl T ℓ E).obj K.obj ⟶
          (derivedExtendScalarsToPadicAlgCl T ℓ E).obj (L.obj⟦q⟧),
        ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F)
          (a : (derivedExtendScalarsSubfield T ℓ h).obj K.obj ⟶
            (derivedExtendScalarsSubfield T ℓ h).obj (L.obj⟦q⟧)),
          finiteDescentDerivedHomToAlgCl T ℓ h a = ψ) ∧
      (∀ (F G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F) (h' : E ≤ G)
        (a : (derivedExtendScalarsSubfield T ℓ h).obj K.obj ⟶
          (derivedExtendScalarsSubfield T ℓ h).obj (L.obj⟦q⟧))
        (b : (derivedExtendScalarsSubfield T ℓ h').obj K.obj ⟶
          (derivedExtendScalarsSubfield T ℓ h').obj (L.obj⟦q⟧)),
        finiteDescentDerivedHomToAlgCl T ℓ h a = finiteDescentDerivedHomToAlgCl T ℓ h' b →
        ∃ (H : PadicAlgCl.FiniteIntermediateField ℓ) (s : F ≤ H) (t : G ≤ H),
          finiteDescentDerivedHomTransition T ℓ h s a =
            finiteDescentDerivedHomTransition T ℓ h' t b)) ∧
    (∀ (V : Type v) [Quiver.{w} V] [Finite V] [∀ x y : V, Finite (x ⟶ y)]
      (A : Paths V ⥤ PadicAlgClConstructible T ℓ)
      (n : ℕ) (s t : Fin n → Paths V) (r r' : ∀ i, s i ⟶ t i),
      (∀ i, A.map (r i) = A.map (r' i)) →
      ∃ (F : PadicAlgCl.FiniteIntermediateField ℓ), E ≤ F ∧
        ∃ B : Paths V ⥤ PadicSubfieldConstructible T ℓ F,
          Nonempty (B ⋙ constructibleToPadicAlgCl T ℓ F ≅ A) ∧
          ∀ i, B.map (r i) = B.map (r' i))) ∧
    (∀ (X Y : Over (Spec (.of k)))
      [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
      [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
      (f : X ⟶ Y) (F : PadicAlgCl.FiniteIntermediateField ℓ),
      Nonempty
        (CondensedRing.boundedConstructibleLowerShriek (Profinite.continuousMapRingObj F) ℓ f ⋙
            constructibleToPadicAlgCl Y.left ℓ F ≅
          constructibleToPadicAlgCl X.left ℓ F ⋙
            CondensedRing.boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f) ∧
      Nonempty
        (CondensedRing.boundedConstructibleUpperStar (Profinite.continuousMapRingObj F) ℓ f ⋙
            constructibleToPadicAlgCl X.left ℓ F ≅
          constructibleToPadicAlgCl Y.left ℓ F ⋙
            CondensedRing.boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f)) := by
  have h := finiteCoefficientDescentTwoColimit k (ringChar k) ℓ
    (Fact.out : (ringChar k).Prime).pos (Fact.out : ringChar k ≠ ℓ) T
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro K L q
    let K' : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) T :=
      ⟨K.obj, (congrFun (h.2.2.2.1 E).1 K.obj).mpr K.property⟩
    let L' : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E) T :=
      ⟨L.obj, (congrFun (h.2.2.2.1 E).1 L.obj).mpr L.property⟩
    exact h.2.1 E K' L' q
  · intro V _ _ _ A n s t r r' hr
    let : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace (T ↘ Spec (.of k))
    let : IsLocallyNoetherian T :=
      LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
    let : IsNoetherian T := {}
    let : IsDirectedOrder (PadicAlgCl.FiniteIntermediateField ℓ) := ⟨fun F G ↦
      ⟨⟨F.val ⊔ G.val, inferInstance⟩,
        (show F.val ≤ F.val ⊔ G.val from le_sup_left),
        (show G.val ≤ F.val ⊔ G.val from le_sup_right)⟩⟩
    obtain ⟨F, hF, B, ⟨e⟩⟩ := finite_quiver_descends (constructibleCocone T ℓ)
      h.2.2.2.2.2 E V A
    change B ⋙ constructibleToPadicAlgCl T ℓ F ≅ A at e
    refine ⟨F, hF, B, ⟨e⟩, ?_⟩
    have hf : (derivedExtendScalarsToPadicAlgCl T ℓ F).Faithful :=
      faithful_leftDerivedExtendScalarsToPadicAlgCl T ℓ F
    intro i
    apply (boundedConstructible (padicSubfieldRingObj T ℓ F)).ι.map_injective
    apply (derivedExtendScalarsToPadicAlgCl T ℓ F).map_injective
    have heq : (constructibleToPadicAlgCl T ℓ F).map (B.map (r i)) =
        (constructibleToPadicAlgCl T ℓ F).map (B.map (r' i)) := by
      apply (cancel_mono (e.hom.app (t i))).mp
      change (B ⋙ constructibleToPadicAlgCl T ℓ F).map (r i) ≫ _ =
        (B ⋙ constructibleToPadicAlgCl T ℓ F).map (r' i) ≫ _
      calc
        _ = e.hom.app (s i) ≫ A.map (r i) := e.hom.naturality (r i)
        _ = e.hom.app (s i) ≫ A.map (r' i) := congrArg (e.hom.app (s i) ≫ ·) (hr i)
        _ = _ := (e.hom.naturality (r' i)).symm
    exact congrArg (·.hom) heq
  · intro X Y _ _ _ _ _ _ f F
    exact ⟨⟨qbar_lower_iso ℓ k f F (CondensedRing.compactificationOverField f)⟩,
      ⟨qbar_pull_iso ℓ k f F⟩⟩

end AlgebraicGeometry.ProEtale
