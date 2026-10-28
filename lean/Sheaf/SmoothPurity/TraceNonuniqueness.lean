/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionUpperShriek
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.WeilObject.Sheaf.StalkUnit

/-!
# A representing trace is not unique without normalization

Source: the finite-orientation normalization in blueprint `def-route-smooth-trace`.
The two signs give distinct representing traces even for the identity of a geometric point.
(blueprint: lem-pur-geometric-point-trace-not-unique)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme
variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

private theorem representing_trace_of_iso
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {M : C} {L : D} (e : M ≅ G.obj L) :
    ∀ K : C, Function.Bijective
      (fun b : K ⟶ M ↦ F.map b ≫ F.map e.hom ≫ adj.counit.app L) := by
  intro K
  constructor
  · intro a b hab
    change F.map a ≫ F.map e.hom ≫ adj.counit.app L =
      F.map b ≫ F.map e.hom ≫ adj.counit.app L at hab
    have h' := congrArg (adj.homEquiv K L) hab
    have hc : (adj.homEquiv (G.obj L) L) (adj.counit.app L) = 𝟙 _ := by
      rw [adj.homEquiv_unit, adj.right_triangle_components]
    have h'' : a ≫ e.hom = b ≫ e.hom := by
      simp only [← Category.assoc, ← F.map_comp,
        adj.homEquiv_naturality_left, hc, Category.comp_id] at h'
      exact h'
    exact (cancel_mono e.hom).1 h''
  · intro y
    refine ⟨adj.homEquiv K L y ≫ e.inv, ?_⟩
    change F.map (adj.homEquiv K L y ≫ e.inv) ≫ F.map e.hom ≫
      adj.counit.app L = y
    rw [← Category.assoc, ← F.map_comp, Category.assoc, e.inv_hom_id,
      Category.comp_id]
    exact (adj.homEquiv_counit K L (adj.homEquiv K L y)).symm.trans
      ((adj.homEquiv K L).symm_apply_apply y)

/-- A nontrivial automorphism of a representing object changes its representing trace.
Source: the normalization requirement of `def-route-smooth-trace`. Precomposition
by an automorphism preserves each Hom bijection, and injectivity at the representing
object shows that the resulting trace differs. This diagnoses unnormalized uniqueness
without invoking the disputed trace-existence theorem. -/
private theorem representing_trace_not_unique_of_automorphism
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
    {M : C} {U : D} (e : M ≅ G.obj U)
    (a : M ≅ M) (ha : a.hom ≠ 𝟙 M) :
    ¬ ∃! t : F.obj M ⟶ U, ∀ K : C,
      Function.Bijective (fun b : K ⟶ M ↦ F.map b ≫ t) := by
  intro h
  let t : F.obj M ⟶ U := F.map e.hom ≫ adj.counit.app U
  have ht : ∀ K : C, Function.Bijective (fun b : K ⟶ M ↦ F.map b ≫ t) :=
    representing_trace_of_iso adj e
  let t' : F.obj M ⟶ U := F.map a.hom ≫ t
  have ht' : ∀ K : C, Function.Bijective (fun b : K ⟶ M ↦ F.map b ≫ t') := by
    intro K
    have ha' := (isIso_iff_yoneda_map_bijective a.hom).mp (by infer_instance) K
    simpa only [Function.comp_def, Functor.map_comp, Category.assoc, t'] using
      (ht K).comp ha'
  have heq : t' = t := h.unique ht' ht
  apply ha
  apply (ht M).1
  simpa only [t', CategoryTheory.Functor.map_id, Category.id_comp] using heq

attribute [local irreducible] AlgebraicGeometry.Spec

omit [Fact (ringChar k).Prime] in
private theorem pointObstruction_locallyOfFiniteType :
    LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))

omit [Fact (ringChar k).Prime] in
private theorem pointObstruction_quasiCompact :
    QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))

omit [Fact (ringChar k).Prime] in
private theorem pointObstruction_isSeparated :
    IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
  inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))


attribute [local irreducible] CategoryTheory.Over.mk

attribute [local instance] pointObstruction_locallyOfFiniteType
  pointObstruction_quasiCompact pointObstruction_isSeparated

attribute [local semireducible] CategoryTheory.Over.mk

/-- Nontriviality of the sign automorphism is preserved by an isomorphism.
Source: the normalization issue in `def-route-smooth-trace`. Conjugate the alleged
identity of the two endomorphisms by the supplied isomorphism and cancel it. -/
private theorem neg_id_ne_id_of_iso
    {C : Type*} [Category C] [Preadditive C] {A B : C} (e : A ≅ B)
    (hA : -(𝟙 A) ≠ 𝟙 A) : -(𝟙 B) ≠ 𝟙 B := by
  intro h
  apply hA
  have he := congrArg (fun z : B ⟶ B ↦ e.hom ≫ z ≫ e.inv) h
  simpa using he

/-- The regular condensed coefficient module has a nontrivial sign automorphism.
Source: `def-route-smooth-trace`, the missing normalization of a representing pair.
Evaluate an alleged equality at a singleton and apply it to the constant section
one. This would assert minus one equals one in the characteristic-zero field. -/
private theorem condensed_unit_neg_id_ne_id :
    -(𝟙 (𝟙_ (Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
      (Profinite.padicAlgClRingObj ℓ)))) ≠ 𝟙 _ := by
  intro h
  let C := Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (Profinite.padicAlgClRingObj ℓ)
  let S : Profinite.{u} := Profinite.of PUnit.{u + 1}
  have hv := congrArg
    (fun f : (𝟙_ C ⟶ 𝟙_ C) ↦
      (f.hom.hom.app (Opposite.op S)
        (1 : ULift.{u + 1} (PadicAlgCl.finiteIntermediateFieldValued ℓ S))).down.val
          PUnit.unit) h
  change -(1 : PadicAlgCl ℓ) = 1 at hv
  norm_num at hv

omit [Fact (ringChar k).Prime] in
/-- The bounded constructible coefficient unit at a separably closed point has a
nontrivial sign automorphism. Source: `def-route-smooth-trace`, the normalization
of the representing object. Pullback from condensed modules is fully faithful at
a geometric point and preserves the unit. The faithful degree-zero single functor
and the ambient unit comparison carry the same sign obstruction to the full
bounded constructible category. No smooth-purity statement is used. -/
private theorem pointObstruction_boundedUnit_neg_id_ne_id [IsSepClosed k] :
    -(𝟙 (𝟙_ (Dᵇc((Over.mk (𝟙 (Spec (.of k)))).left)⟦
      Profinite.padicAlgClRingObj ℓ⟧))) ≠ 𝟙 _ := by
  let C := Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    (Profinite.padicAlgClRingObj ℓ)
  let A := Mod (Sheaf (ProEt.topology (Spec (.of k))) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of k)))
  let F := upperStarFromPointMod (Profinite.padicAlgClRingObj ℓ) (Spec (.of k))
  let : F.Additive := Functor.additive_of_preserves_binary_products F
  have hF : -(𝟙 (F.obj (𝟙_ C))) ≠ 𝟙 _ := by
    intro h
    apply condensed_unit_neg_id_ne_id ℓ
    apply F.map_injective
    rw [Functor.map_neg, CategoryTheory.Functor.map_id]
    exact h
  have hA : -(𝟙 (𝟙_ A)) ≠ 𝟙 _ :=
    neg_id_ne_id_of_iso (Functor.Monoidal.εIso F).symm hF
  have hS : -(𝟙 ((_root_.DerivedCategory.singleFunctor A 0).obj (𝟙_ A))) ≠ 𝟙 _ := by
    intro h
    apply hA
    apply (_root_.DerivedCategory.singleFunctor A 0).map_injective
    rw [Functor.map_neg, CategoryTheory.Functor.map_id]
    exact h
  have hD : -(𝟙 (𝟙_ (_root_.DerivedCategory A))) ≠ 𝟙 _ :=
    neg_id_ne_id_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso A) hS
  intro h
  apply hD
  have hi := congrArg (ObjectProperty.ι _).map h
  simp only [Functor.map_neg, CategoryTheory.Functor.map_id] at hi
  change -(𝟙 (𝟙_ (_root_.DerivedCategory A))) = 𝟙 _ at hi
  exact hi


/-- The actual compact-support Hom pairing at a geometric point does not determine
a unique trace on its coefficient unit. Source: `def-route-smooth-trace`, where the
finite orientation is required as normalization. The open-unit isomorphism gives
one representing trace for the identity map. Its negative also represents the
same functor, and the preceding sign calculation proves that they are different.
(blueprint: lem-pur-geometric-point-trace-not-unique)
This is a counterexample to the unnormalized `existsUnique_smoothTrace` predicate,
proved without using that declaration or the disputed smooth-purity instance. -/
theorem not_existsUnique_representing_trace_at_point [IsSepClosed k] :
    letI : LocallyOfFiniteType (Over.mk (𝟙 (Spec (.of k)))).hom :=
      inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (.of k))))
    letI : QuasiCompact (Over.mk (𝟙 (Spec (.of k)))).hom :=
      inferInstanceAs (QuasiCompact (𝟙 (Spec (.of k))))
    letI : IsSeparated (Over.mk (𝟙 (Spec (.of k)))).hom :=
      inferInstanceAs (IsSeparated (𝟙 (Spec (.of k))))
    ¬ ∃! t :
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
          (𝟙 (Over.mk (𝟙 (Spec (.of k)))))).obj
            (𝟙_ (Dᵇc((Over.mk (𝟙 (Spec (.of k)))).left)⟦
              Profinite.padicAlgClRingObj ℓ⟧)) ⟶ 𝟙_ _,
      ∀ K : Dᵇc((Over.mk (𝟙 (Spec (.of k)))).left)⟦Profinite.padicAlgClRingObj ℓ⟧,
        Function.Bijective (fun a : K ⟶ 𝟙_ _ ↦
          (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ
            (𝟙 (Over.mk (𝟙 (Spec (.of k)))))).map a ≫ t) := by
  let j := 𝟙 (Over.mk (𝟙 (Spec (.of k))))
  exact representing_trace_not_unique_of_automorphism
    (boundedConstructibleUpperShriekAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ j)
    (boundedConstructibleUpperShriekUnitIso_padicAlgCl ℓ j).symm
    (-(Iso.refl _)) (pointObstruction_boundedUnit_neg_id_ne_id ℓ (k := k))


end AlgebraicGeometry.ProEtale.CondensedRing
