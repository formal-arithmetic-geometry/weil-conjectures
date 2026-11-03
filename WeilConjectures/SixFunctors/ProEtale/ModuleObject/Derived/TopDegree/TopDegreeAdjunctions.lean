/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.TopDegree.TopDegreeTraceDefs
import all Mathlib.Logic.Small.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # The normalized top-degree adjunction identities

Source: current blueprint sk-cor-trace, statement and complements (i)--(iii).
(blueprint: lem-pd-top-degree-adjunction-identities).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
open PurityTransport
variable (ell : ℕ) [Fact ell.Prime] (c : Coefficient ell)

/-- The ordinary adjunction carries the pullback of a unit endomorphism to
precomposition with the fixed constant unit section. Thus a connected-section
calculation on X can be used with the actual unitSection, rather than an
unspecified isomorphism. Source: sk-cor-trace, steps 2 and 8
(blueprint: lem-pd-top-degree-adjunction-identities).
Proof: compose the given bijection with the ordinary adjunction hom equivalence.
The adjunction unit's naturality identifies this composite with the stated map. -/
theorem unitSection_bijective_of_pull {k : Type u} [Field k]
    (X : Over (Spec (.of k)))
    (h : Function.Bijective
      (fun z : U ell c (Spec (.of k)) ⟶ U ell c (Spec (.of k)) ↦
        (actualPull (c.obj.{u} ell) X.hom).map z ≫ (tracePullUnit ell c X.hom).hom)) :
    Function.Bijective
      (fun z : U ell c (Spec (.of k)) ⟶ U ell c (Spec (.of k)) ↦
        z ≫ unitSection ell c X) := by
  let a := derivedUpperStarLowerStarAdjunction (c.obj.{u} ell) X.hom
  have hn (z : U ell c (Spec (.of k)) ⟶ U ell c (Spec (.of k))) :=
    a.unit.naturality z
  simp only [Functor.id_map, Functor.comp_map] at hn
  have he : (fun z ↦ a.homEquiv (U ell c (Spec (.of k))) (U ell c X.left)
      ((actualPull (c.obj.{u} ell) X.hom).map z ≫ (tracePullUnit ell c X.hom).hom)) =
      (fun z ↦ z ≫ unitSection ell c X) := by
    funext z
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, ← hn]
    simp only [unitSection, traceSupportedUnit, Category.assoc]
    rfl
  rw [← he]
  exact (a.homEquiv _ _).bijective.comp h

/-- The two adjunction bijections, with the same fixed unit, root-line and proper
comparisons used by `dualityMap`. This is a bijection before any cohomological
finiteness or connectedness is used. Source: complement (i), step 8
(blueprint: lem-pd-top-degree-adjunction-identities). -/
def dualityEquiv {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    TwistedClasses ell c X d ≃
      ((actualPush (c.obj.{u} ell) X.hom).obj (U ell c X.left) ⟶
        U ell c (Spec (.of k))) := by
  let s := geometry X d
  let := residueInverse ell hEll s.X
  let := residueInverse ell hEll s.Y
  let a := smoothAdjunction ell c hEll X d
  let K : c.ctf ell s.Y.left :=
    ⟨U ell c s.Y.left, CurrentTraceCup.tateLine_mem ell c s.Y.left 0⟩
  let L : c.ctf ell s.X.left :=
    ⟨U ell c s.X.left, CurrentTraceCup.tateLine_mem ell c s.X.left 0⟩
  let e₁ := ((derivedUpperStarLowerStarAdjunction (c.obj.{u} ell) X.hom).homEquiv
    K.obj (c.derivedLine ell X.left d)).symm
  let e₂ := (tracePullUnit ell c X.hom).homCongr (sourceUnit ell c s.map d).symm
  let e₃ := (property ell c s.X.left).fullyFaithfulι.homEquiv
    (X := L) (Y := (source ell c s.map d a.source_closed).obj K)
  let e₄ := (a.adjunction.homEquiv L K).symm
  let e₅ := (property ell c s.Y.left).fullyFaithfulι.homEquiv
    (X := (support ell c s.compactification a.support_closed).obj L) (Y := K)
  let e₆ := ((TraceCupProper.comparison (c.obj.{u} ell) X.hom).app L.obj).homCongr
    (Iso.refl K.obj)
  exact e₁.trans (e₂.trans (e₃.symm.trans (e₄.trans (e₅.trans e₆))))

/-- The specified degree-zero duality map is bijective. It is precisely the
composite of the two adjunction equivalences and the three fixed comparisons.
Source: complement (i), step 8 (blueprint: lem-pd-top-degree-adjunction-identities). -/
theorem dualityMap_bijective {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    Function.Bijective (dualityMap ell c hEll X d) := by
  have h : ⇑(dualityEquiv ell c hEll X d) = dualityMap ell c hEll X d := by
    funext z
    dsimp [dualityEquiv, dualityMap, Iso.homCongr]
    simp only [Category.comp_id]
    rfl
  rw [← h]
  exact (dualityEquiv ell c hEll X d).bijective

set_option maxHeartbeats 1000000 in
-- The two restricted adjunctions unfold several derived coefficient functors.
/-- Evaluation at the constant unit of the specified duality map is the twisted
trace. Naturality of proper coincidence moves it past the adjunct, the pullback
unit cancels its inverse, and the ordinary adjunction recovers the original
class. Source: complement (i), step 8 (blueprint: lem-pd-top-degree-adjunction-identities). -/
theorem dualityMap_evaluation {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z : TwistedClasses ell c X d) :
    twistedTrace ell c hEll X d z =
      unitSection ell c X ≫ dualityMap ell c hEll X d z := by
  let s := geometry X d
  let := residueInverse ell hEll s.X
  let := residueInverse ell hEll s.Y
  let a := smoothAdjunction ell c hEll X d
  let K : c.ctf ell s.Y.left :=
    ⟨U ell c s.Y.left, CurrentTraceCup.tateLine_mem ell c s.Y.left 0⟩
  let L : c.ctf ell s.X.left :=
    ⟨U ell c s.X.left, CurrentTraceCup.tateLine_mem ell c s.X.left 0⟩
  let adj := derivedUpperStarLowerStarAdjunction (c.obj.{u} ell) X.hom
  let v := (adj.homEquiv K.obj (c.derivedLine ell X.left d)).symm z
  let w : L ⟶ (source ell c s.map d a.source_closed).obj K :=
    ⟨(tracePullUnit ell c X.hom).inv ≫ v ≫ (sourceUnit ell c s.map d).inv⟩
  let F := rightDerivedLowerShriekOfCompactification (c.obj.{u} ell) s.compactification
  let H := actualPush (c.obj.{u} ell) X.hom
  let κ := TraceCupProper.comparison (c.obj.{u} ell) X.hom
  have hz : adj.unit.app K.obj ≫ H.map v = z := by
    exact (adj.homEquiv K.obj (c.derivedLine ell X.left d)).apply_symm_apply z
  have hw : unitSection ell c X ≫ H.map w.hom =
      z ≫ H.map (sourceUnit ell c s.map d).inv := by
    change (adj.unit.app K.obj ≫ H.map (tracePullUnit ell c X.hom).hom) ≫
      H.map ((tracePullUnit ell c X.hom).inv ≫ v ≫
        (sourceUnit ell c s.map d).inv) = _
    simp only [Functor.map_comp, Category.assoc]
    rw [← Functor.map_comp_assoc H (tracePullUnit ell c X.hom).hom
      (tracePullUnit ell c X.hom).inv, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp, ← Category.assoc, hz]
  have ht := congrArg (fun f ↦ f.hom)
    (a.adjunction.homEquiv_counit (X := L) (Y := K) (g := w))
  change z ≫ κ.inv.app _ ≫ (F.map (sourceUnit ell c s.map d).inv ≫ a.trace K) =
    unitSection ell c X ≫ κ.inv.app L.obj ≫ ((a.adjunction.homEquiv L K).symm w).hom
  rw [ht]
  calc
    _ = (z ≫ H.map (sourceUnit ell c s.map d).inv) ≫
        κ.inv.app _ ≫ a.trace K := by
      simpa only [F, H, s, geometry, Category.assoc] using congrArg
        (fun f ↦ z ≫ f ≫ a.trace K)
        (κ.inv.naturality (sourceUnit ell c s.map d).inv).symm
    _ = (unitSection ell c X ≫ H.map w.hom) ≫ κ.inv.app _ ≫ a.trace K := by
      exact congrArg (fun f ↦ f ≫ κ.inv.app _ ≫ a.trace K) hw.symm
    _ = _ := by
      simp only [ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
      change unitSection ell c X ≫ H.map w.hom ≫ κ.inv.app _ ≫ a.trace K =
        unitSection ell c X ≫ κ.inv.app L.obj ≫ F.map w.hom ≫ a.trace K
      simpa only [F, H, s, geometry, Category.assoc] using congrArg
        (fun f ↦ unitSection ell c X ≫ f ≫ a.trace K) (κ.inv.naturality w.hom)

set_option maxHeartbeats 1000000 in
-- Unfolding the constructible restriction compares the ambient derived source objects.
/-- Transposing the point-return arrow and then applying the same normalized
counit recovers that arrow. The root-line source comparison cancels with its
inverse. Source: sk-cor-trace.proof.md, point-class paragraph, step 7
(blueprint: lem-pd-top-degree-adjunction-identities). -/
theorem pointMap_trace {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : Spec (.of k) ⟶ X.left) [IsClosedImmersion x]
    (hx : x ≫ X.hom = 𝟙 _) :
    (rightDerivedLowerShriekOfCompactification (c.obj.{u} ell)
      (Compactification.ofIsProper X.hom)).map (pointMap ell c hEll X d x hx) ≫
        twistedDerived ell c hEll X d =
      (TraceCupProper.comparison (c.obj.{u} ell) X.hom).hom.app _ ≫
        (pointReturn ell c X x hx).hom := by
  let s := geometry X d
  let := residueInverse ell hEll s.Y
  let a := smoothAdjunction ell c hEll X d
  let K : c.ctf ell s.Y.left :=
    ⟨U ell c s.Y.left, CurrentTraceCup.tateLine_mem ell c s.Y.left 0⟩
  let L : c.ctf ell s.X.left :=
    ⟨(actualPush (c.obj.{u} ell) x).obj K.obj, pointSupport_mem ell c X x⟩
  let v : (support ell c s.compactification a.support_closed).obj L ⟶ K :=
    ⟨(TraceCupProper.comparison (c.obj.{u} ell) X.hom).hom.app L.obj ≫
      (pointReturn ell c X x hx).hom⟩
  have h := (a.adjunction.homEquiv L K).symm_apply_apply v
  rw [Adjunction.homEquiv_counit] at h
  have h' := congrArg (fun f ↦ f.hom) h
  change (rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification).map
      (((a.adjunction.homEquiv L K) v).hom ≫ (sourceUnit ell c s.map d).hom) ≫
    ((rightDerivedLowerShriekOfCompactification (c.obj ell) s.compactification).map
      (sourceUnit ell c s.map d).inv ≫ a.trace K) = v.hom
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc _ (sourceUnit ell c s.map d).hom
    (sourceUnit ell c s.map d).inv, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact h'

/-- The supported counit point class has twisted trace one. This is the
triangle identity for the very adjunction used to construct that class, followed
by naturality of proper coincidence and cancellation of the unital point-return
isomorphism. Source: sk-cor-trace.proof.md, point-class paragraph, step 7
(blueprint: lem-pd-top-degree-adjunction-identities). -/
theorem pointClass_trace {k : Type u} [Field k] [IsAlgClosed k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hEll : IsUnit (ell : k)) (X : Over (Spec (.of k)))
    [IsProper X.hom] (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x : Spec (.of k) ⟶ X.left) [IsClosedImmersion x]
    (hx : x ≫ X.hom = 𝟙 _) :
    twistedTrace ell c hEll X d (pointClass ell c hEll X d x hx) = 𝟙 _ := by
  unfold twistedTrace pointClass
  simp only [Category.assoc]
  rw [NatTrans.naturality_assoc, pointMap_trace]
  simp


end AlgebraicGeometry.ProEtale.CondensedRing.TopDegree
