/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.FieldTheory.Separable
public import WeilConjectures.FieldTheory.TensorProductDiagonal
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift

/-! # Constructible descent along finite etale field towers

Source: latest blueprint, det-pd-biduality-coefficients.proof.md (i), finite-base-field
paragraph; Stacks 09YU, 03TT, 0GIT
(blueprint: lem-sf-finite-etale-tower-constructible-descent).

The tower schemes and arrows are literal scheme pullbacks. The Hom diagram takes values
in abelian groups. Its cocone is defined by the actual total derived coefficient pullbacks,
conjugated by their specified composition isomorphisms. Thus its colimit assertion identifies
the canonical comparison, rather than asserting an unspecified group isomorphism.

## Main statements

* `finiteEtaleTower_constructible_descent`: descent of objects and the Hom-colimit property.

Shifts are applied before pullback; `Functor.commShiftIso` identifies these Hom groups with
the displayed shifted-target groups in the source. All auxiliary constructions belong to
this node's tower and introduce no alternative coefficient or derived-category encoding.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.FiniteEtaleTower

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- The actual finite intermediate fields, with their inherited inclusion order.
Source: blueprint finite-base-field paragraph; Stacks 09YU
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
abbrev Index := IntermediateField.FiniteSubext k L

variable {k L}
variable {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))

/-- The literal scalar base change to an intermediate field, including the top field.
Source: blueprint finite-base-field paragraph
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
abbrev stage (E : IntermediateField k L) : Scheme.{u} :=
  pullback y (Spec.map (CommRingCat.ofHom (algebraMap k E)))

/-- The scalar base change to L, with no finiteness assumption on L/k.
Source: blueprint finite-base-field paragraph
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
abbrev limitScheme : Scheme.{u} :=
  pullback y (Spec.map (CommRingCat.ofHom (algebraMap k L)))

/-- The square defining the projection between two scalar base changes commutes.
Source: blueprint tower construction; functoriality of Spec and the algebra-map equation
(blueprint: lem-sf-finite-etale-tower-constructible-descent).
Proof: expand Spec of the composite ring homomorphism; the algebra-hom commutation
identity identifies its composite with the structure map, then use pullback.condition. -/
theorem projection_condition (E F : IntermediateField k L) (g : E →ₐ[k] F) :
    (pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap k F)))) ≫ y =
      ((pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap k F)))) ≫
        Spec.map (CommRingCat.ofHom g.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [AlgHom.toRingHom_eq_coe, g.comp_algebraMap]
  exact pullback.condition

/-- Canonical projection induced by the inclusion of intermediate fields.
Source: blueprint finite-base-field paragraph
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
def transition {E F : IntermediateField k L} (h : E ≤ F) : stage y F ⟶ stage y E :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom
      (IntermediateField.inclusion h).toRingHom))
    (projection_condition y E F (IntermediateField.inclusion h))

/-- The square defining the projection from the L-base change commutes.
Source: blueprint tower construction
(blueprint: lem-sf-finite-etale-tower-constructible-descent).
Proof: use the algebra-hom equation for E.val, functoriality of Spec, and the
pullback commutativity equation, exactly as for projection_condition. -/
theorem limitProjection_condition (E : IntermediateField k L) :
    (pullback.fst y (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ≫ y =
      ((pullback.snd y (Spec.map (CommRingCat.ofHom (algebraMap k L)))) ≫
        Spec.map (CommRingCat.ofHom E.val.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact pullback.condition

/-- The specified projection from Y_L to Y_E.
Source: blueprint finite-base-field paragraph
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
def projection (E : IntermediateField k L) : limitScheme (L := L) y ⟶ stage y E :=
  pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom E.val.toRingHom))
    (limitProjection_condition y E)

/-- Tower projection composition, as an equality of the actual scheme morphisms.
Source: blueprint tower construction
(blueprint: lem-sf-finite-etale-tower-constructible-descent).
Proof: compose with the two pullback projections; Spec functoriality and composition
of IntermediateField.inclusion identify both components. Pullback uniqueness concludes. -/
theorem transition_comp {E F G : IntermediateField k L} (h : E ≤ F) (a : F ≤ G) :
    transition y a ≫ transition y h = transition y (h.trans a) := by
  apply pullback.hom_ext
  · simp [transition]
  · simp only [transition, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

/-- Compatibility of the L-projection with a transition of the tower.
Source: blueprint tower construction
(blueprint: lem-sf-finite-etale-tower-constructible-descent).
Proof: compose with both pullback projections. Inclusion followed by F.val is E.val,
so Spec functoriality gives equality of the second components; the first are identical. -/
theorem projection_transition {E F : IntermediateField k L} (h : E ≤ F) :
    projection y F ≫ transition y h = projection y E := by
  apply pullback.hom_ext
  · simp [projection, transition]
  · simp only [projection, transition, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The existing actual unbounded internal-module category at a scheme.
Source: det-def-sfb-derived-categories, module-object row
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
abbrev D (V : Scheme.{u}) := DerivedCategory
  (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousCoefficientRingObj A) V))

/-- The recorded full bounded constructible finite-Tor subcategory, without alteration.
Source: sk-def-sfb-constructible, final paragraph
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
abbrev C (V : Scheme.{u}) :=
  ConstantModelConstructibleFiniteTor (Profinite.continuousCoefficientRingObj A) V

/-- The specified total derived coefficient pullback, abbreviated for this tower.
Source: det-def-sfb-module-derived-pushpull
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
abbrev pull {V W : Scheme.{u}} (f : V ⟶ W) : D A W ⥤ D A V :=
  CondensedRing.moduleObjectDerivedPullback (Profinite.continuousCoefficientRingObj A) f

/-- Additivity of the actual total derived pullback: the existing published instance
(the triangulated structure of `L((f)^*⟦Λ⟧)` in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift`), read through
the abbreviation `pull`; no new argument.
Source: det-def-sfb-module-derived-pushpull, exact pullback comparison
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
instance pull_additive {V W : Scheme.{u}} (f : V ⟶ W) : (pull A f).Additive :=
  inferInstanceAs
    (CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A)
      f).leftDerivedFunctor.Additive

/-- The canonical shift structure transported from the exact termwise pullback: the existing
published instance of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift`
(`Functor.CommShift.ofIso` along `leftDerivedUpperStarIsoMapDerivedCategory.symm`), read through
the abbreviation `pull`; not a second shift structure.
Source: det-def-sfb-module-derived-pushpull, exact pullback convention
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
@[instance_reducible]
def pullCommShift {V W : Scheme.{u}} (f : V ⟶ W) : (pull A f).CommShift ℤ :=
  inferInstanceAs
    ((CondensedRing.upperStar (Profinite.continuousCoefficientRingObj A)
      f).leftDerivedFunctor.CommShift ℤ)

attribute [instance] pullCommShift

/-- Canonical derived composition identification, including an equality of scheme maps.
Source: det-def-sfb-module-derived-pushpull, exact pullback convention
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
def compIso {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) (h : U ⟶ W)
    (w : f ≫ g = h) : pull A h ≅ pull A g ⋙ pull A f :=
  eqToIso (congrArg (pull A) w.symm) ≪≫
    CondensedRing.leftDerivedUpperStarComp (Profinite.continuousCoefficientRingObj A) f g

/-- The specified composition identification respects the canonical shifts.
Source: the shift-compatibility clause of the node
(blueprint: lem-sf-finite-etale-tower-constructible-descent).
Proof: substitute the equality w; eqToIso of equal functors commutes with shifts, and
the published instance `CondensedRing.commShift_leftDerivedUpperStarComp_hom` (module
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift`) gives the rest. -/
theorem compIso_commShift {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W)
    (h : U ⟶ W) (w : f ≫ g = h) : NatTrans.CommShift (compIso A f g h w).hom ℤ := by
  subst h
  simpa only [compIso, eqToIso_refl, Iso.refl_trans] using
    (CondensedRing.commShift_leftDerivedUpperStarComp_hom
      (Profinite.continuousCoefficientRingObj A) f g)

/-- Pullback of a Hom group with precisely the canonical composition transports.
Source: the actual-pullback clause of the node
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
def mapHom {U V W : Scheme.{u}} (f : U ⟶ V) (g : V ⟶ W) (h : U ⟶ W)
    (w : f ≫ g = h) (P Q : D A W) :
    ((pull A g).obj P ⟶ (pull A g).obj Q) →+
      ((pull A h).obj P ⟶ (pull A h).obj Q) :=
  (Preadditive.rightComp _ ((compIso A f g h w).inv.app Q)).comp
    ((Preadditive.leftComp _ ((compIso A f g h w).hom.app P)).comp
      ((pull A f).mapAddHom))

/-- Stages above a specified finite intermediate field; no stage is omitted.
Source: Stacks 09YU, directed colimit after fixing a stage
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
abbrev Above (i : Index k L) := {j : Index k L // i ≤ j}

/-- The abelian group of derived morphisms at a later stage.
Source: the displayed Hom-colimit in the node
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
abbrev homGroup (i : Index k L) (P Q : D A (stage y i.val)) (j : Above i) :=
  ((pull A (transition y j.property)).obj P ⟶
    (pull A (transition y j.property)).obj Q)

/-- The actual transition on Hom groups, not an arbitrary compatible homomorphism.
Source: the actual-pullback clause of the node
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
def homTransition (i : Index k L) (P Q : D A (stage y i.val))
    {j j' : Above i} (h : j ≤ j') : homGroup y A i P Q j →+ homGroup y A i P Q j' :=
  mapHom A (transition y h) (transition y j.property)
    (transition y j'.property) (transition_comp y j.property h) P Q

/-- The actual comparison from a finite-stage Hom group to the L-stage Hom group.
Source: the actual-pullback clause of the node
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
def homComparison (i : Index k L) (P Q : D A (stage y i.val)) (j : Above i) :
    homGroup y A i P Q j →+
      ((pull A (projection y i.val)).obj P ⟶ (pull A (projection y i.val)).obj Q) :=
  mapHom A (projection y j.val.val) (transition y j.property)
    (projection y i.val) (projection_transition y j.property) P Q

/-- Identity law for the transported actual Hom transitions.
Source: the identities clause of the node
(blueprint: lem-sf-finite-etale-tower-constructible-descent).
Proof: the transition of a reflexive inclusion is the identity scheme map by pullback
uniqueness. The unit law of derived pullback and naturality cancel the two transports. -/
theorem homTransition_id (i : Index k L) (P Q : D A (stage y i.val)) (j : Above i) :
    homTransition y A i P Q (le_refl j) = AddMonoidHom.id _ := by
  sorry

/-- Composition law for the transported actual Hom transitions.
Source: the composition clause of the node
(blueprint: lem-sf-finite-etale-tower-constructible-descent).
Proof: expand mapHom, use naturality and the associativity coherence of the specified
leftDerivedUpperStarComp, and cancel inverse comparison components. -/
theorem homTransition_comp (i : Index k L) (P Q : D A (stage y i.val))
    {j j' j'' : Above i} (h : j ≤ j') (a : j' ≤ j'') :
    homTransition y A i P Q (h.trans a) =
      (homTransition y A i P Q a).comp (homTransition y A i P Q h) := by
  sorry

/-- Cocone compatibility for the specified comparison maps.
Source: the actual-pullback clause of the node
(blueprint: lem-sf-finite-etale-tower-constructible-descent).
Proof: use projection_transition and the same composition coherence as for
homTransition_comp. Naturality cancels the intermediate composition transports. -/
theorem homComparison_transition (i : Index k L) (P Q : D A (stage y i.val))
    {j j' : Above i} (h : j ≤ j') :
    (homComparison y A i P Q j').comp (homTransition y A i P Q h) =
      homComparison y A i P Q j := by
  sorry

/-- The ordinary diagram of abelian groups with the actual pullback maps.
Source: the Hom-colimit clause of the node; def-weil-pbc-category-colimit
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
def homDiagram (i : Index k L) (P Q : D A (stage y i.val)) : Above i ⥤ Ab.{u + 1} where
  obj j := AddCommGrpCat.of (homGroup y A i P Q j)
  map h := AddCommGrpCat.ofHom (homTransition y A i P Q (leOfHom h))
  map_id j := congrArg AddCommGrpCat.ofHom (homTransition_id y A i P Q j)
  map_comp h a := congrArg AddCommGrpCat.ofHom
    (homTransition_comp y A i P Q (leOfHom h) (leOfHom a))

/-- The cocone compatibility equation in its exact abelian-category coordinates.
Source: the actual-pullback comparison clause of the node
(blueprint: lem-sf-finite-etale-tower-constructible-descent).
Proof: homComparison_transition is precisely this equality of additive homomorphisms.
Apply AddCommGrpCat.ofHom and the identity composition law. Keeping this equation
in categorical coordinates avoids unfolding the internal-module tensor structures. -/
theorem homComparison_naturality (i : Index k L) (P Q : D A (stage y i.val))
    (j j' : Above i) (h : j ⟶ j') :
    (homDiagram y A i P Q).map h ≫ AddCommGrpCat.ofHom (homComparison y A i P Q j') =
      AddCommGrpCat.ofHom (homComparison y A i P Q j) ≫
        ((Functor.const (Above i)).obj
          (AddCommGrpCat.of ((pull A (projection y i.val)).obj P ⟶
            (pull A (projection y i.val)).obj Q))).map h := by
  dsimp only [homDiagram]
  rw [Functor.const_obj_map, Category.comp_id, ← AddCommGrpCat.ofHom_comp,
    homComparison_transition]

/-- The canonical comparison cocone, whose vertex is the Hom group over L.
Source: the displayed comparison in the node; def-weil-pbc-category-colimit
(blueprint: lem-sf-finite-etale-tower-constructible-descent). -/
def homCocone (i : Index k L) (P Q : D A (stage y i.val)) :
    Cocone (homDiagram y A i P Q) where
  pt := AddCommGrpCat.of
    ((pull A (projection y i.val)).obj P ⟶ (pull A (projection y i.val)).obj Q)
  ι :=
    { app j := AddCommGrpCat.ofHom (homComparison y A i P Q j)
      naturality j j' h := homComparison_naturality y A i P Q j j' h }

/-- Descent of bounded constructible finite-Tor objects, and the canonical ordinary
filtered colimit of their shifted derived Hom groups, including the point case.
Source: latest det-pd-biduality-coefficients.proof.md (i), finite-base-field paragraph;
Stacks 09YU, 03TT and 0GIT
(blueprint: lem-sf-finite-etale-tower-constructible-descent).

Proof, following the nine DAG steps:
1. Finite separable field extensions are finite etale; their scalar base changes form
an affine-transition inverse system with limit Y_L, also on affine opens of Y.
2. Use finiteCtfInternalEtaleRealization, comparison_torAmplitudeIn_iff, direct-image
comparison and internal_module_operations_transport to identify the actual condensed
pullbacks with the ordinary etale pullbacks, preserving fixed Tor intervals.
3. Represent an etale origin by a finite flat constructible complex (03TT), and descend
its finitely many terms by constructible etale module descent (09YU).
4. Each projection is fpqc-surjective. Its exact faithful tensor-compatible inverse
image reflects injectivity, so the descended terms are flat.
5. Move all terms to a common stage. The constructible Hom-colimit theorem descends
finitely many differentials and their zero-composite equations at a further common stage.
6. Constructible Serre closure gives constructible cohomology. The reverse flat-model
criterion gives finite Tor amplitude with the same finite support interval.
7. Transport the descended complex back by the finite-coefficient realization and
ordinary-coefficient equivalence, including the canonical composition comparisons.
8. For fixed i,P,Q,m use the ind-etale internal-Hom comparison for RHom(P,Q[m]).
It is bounded below. Apply derived etale cohomology continuity (0GIT), scalar-forgetting
evaluation, and H^0(RHom)=Hom. This gives exactly the cocone defined above.
9. The index is directed: composita of finite intermediate fields give common bounds.
The filtered-colimit representative and eventual-equality criteria descend a morphism,
its inverse and finitely many equations to a common stage. Functorial pullback preserves
identities and composition; its canonical CommShift structure gives the shift clause.
No argument excludes Y=Spec k, Y empty, the zero ring, or L=k. -/
theorem finiteEtaleTower_constructible_descent
    [Finite k] [Algebra.IsSeparable k L]
    (p ell : ℕ) [Fact p.Prime] [Fact ell.Prime] [CharP k p] (hne : p ≠ ell)
    [Finite A] [DiscreteTopology A] (r : ℕ) (hr : 1 ≤ r) (hA : (ell ^ r : A) = 0)
    [LocallyOfFiniteType y] [QuasiCompact y] [IsSeparated y] :
    (∀ P : C A (limitScheme (L := L) y),
      ∃ (i : Index k L) (P_i : C A (stage y i.val)),
        Nonempty ((pull A (projection y i.val)).obj P_i.obj ≅ P.obj)) ∧
    (∀ (i : Index k L) (P_i Q_i : C A (stage y i.val)) (m : ℤ),
      Nonempty (IsColimit (homCocone y A i P_i.obj (Q_i.obj⟦m⟧)))) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteEtaleTower
