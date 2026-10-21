/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q54
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Monoidal.Internal.Limits

/-!
# Finite limits of internal abelian groups

Source: Stacks Project, Sites and Sheaves, Tag 00YV, abelian-group part and preceding
quadruple discussion (blueprint: lem-sfb-internal-abelian-finite-limit-creation).
The finite-limit-category formulation is the categorical argument extracted from that passage.
-/

@[expose] public section

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace CategoryTheory.CommGrp

/-- Factor the inverse cone through the explicit monoid limit. -/
private noncomputable def liftObject
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {I : Type w} [Category I] (D : I ⥤ CommGrp C)
    (c : Cone (D ⋙ forget C)) (hc : IsLimit c) : CommGrp C := by
  let M := Mon.limit (D ⋙ forget₂Grp C ⋙ Grp.forget₂Mon C) c hc
  letI : MonObj c.pt := M.mon
  have hm (j : I) : M.mon.mul ≫ c.π.app j =
      (c.π.app j ⊗ₘ c.π.app j) ≫ MonObj.mul (X := (D.obj j).X) := hc.fac _ j
  have he (j : I) : M.mon.one ≫ c.π.app j = MonObj.one (X := (D.obj j).X) :=
    hc.fac _ j
  let ci : Cone (D ⋙ forget C) :=
    { pt := c.pt
      π.app j := c.π.app j ≫ GrpObj.inv (X := (D.obj j).X)
      π.naturality i j f := by
        change 𝟙 c.pt ≫ c.π.app j ≫ GrpObj.inv (X := (D.obj j).X) =
          (c.π.app i ≫ GrpObj.inv (X := (D.obj i).X)) ≫ (D.map f).hom.hom.hom
        rw [Category.id_comp]
        calc
          _ = (c.π.app i ≫ (D.map f).hom.hom.hom) ≫
              GrpObj.inv (X := (D.obj j).X) :=
            congrArg (fun t ↦ t ≫ GrpObj.inv (X := (D.obj j).X))
              (by simpa using c.π.naturality f)
          _ = _ := by
            simpa only [Category.assoc] using
              congrArg (fun t ↦ c.π.app i ≫ t)
                (GrpObj.inv_hom (D.map f).hom.hom.hom).symm }
  letI : GrpObj c.pt :=
    { M.mon with
      inv := hc.lift ci
      left_inv := by
        apply hc.hom_ext
        intro j
        simp only [Category.assoc]
        change lift (hc.lift ci) (𝟙 c.pt) ≫ M.mon.mul ≫ c.π.app j =
          toUnit _ ≫ M.mon.one ≫ c.π.app j
        rw [hm, he, lift_map_assoc]
        simp [ci]
      right_inv := by
        apply hc.hom_ext
        intro j
        simp only [Category.assoc]
        change lift (𝟙 c.pt) (hc.lift ci) ≫ M.mon.mul ≫ c.π.app j =
          toUnit _ ≫ M.mon.one ≫ c.π.app j
        rw [hm, he, lift_map_assoc]
        simp [ci] }
  exact
    { X := c.pt
      comm.mul_comm := by
        apply hc.hom_ext
        intro j
        simp only [Category.assoc]
        change (β_ c.pt c.pt).hom ≫ M.mon.mul ≫ c.π.app j =
          M.mon.mul ≫ c.π.app j
        rw [hm]
        rw [← BraidedCategory.braiding_naturality_assoc]
        exact congrArg (fun t ↦ (c.π.app j ⊗ₘ c.π.app j) ≫ t)
          (IsCommMonObj.mul_comm (X := (D.obj j).X)) }

/-- The projections preserve the constructed operations. -/
private noncomputable def liftCone
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {I : Type w} [Category I] (D : I ⥤ CommGrp C)
    (c : Cone (D ⋙ forget C)) (hc : IsLimit c) : Cone D where
  pt := liftObject D c hc
  π.app j := InducedCategory.homMk
    (Grp.homMk' ((Mon.limitCone (D ⋙ forget₂Grp C ⋙ Grp.forget₂Mon C) c hc).π.app j))
  π.naturality i j f := by
    apply CommGrp.hom_ext
    exact c.π.naturality f

/-- The monoid universal factorization is also a group morphism. -/
private noncomputable def liftConeIsLimit
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {I : Type w} [Category I] (D : I ⥤ CommGrp C)
    (c : Cone (D ⋙ forget C)) (hc : IsLimit c) : IsLimit (liftCone D c hc) where
  lift s := InducedCategory.homMk (Grp.homMk'
    ((Mon.limitConeIsLimit (D ⋙ forget₂Grp C ⋙ Grp.forget₂Mon C) c hc).lift
      ((forget₂Grp C ⋙ Grp.forget₂Mon C).mapCone s)))
  fac s j := by
    apply CommGrp.hom_ext
    exact hc.fac ((forget C).mapCone s) j
  uniq s m hm := by
    apply CommGrp.hom_ext
    apply hc.hom_ext
    intro j
    exact (congrArg (fun f ↦ (forget C).map f) (hm j)).trans
      (hc.fac ((forget C).mapCone s) j).symm

@[instance_reducible]
private noncomputable def forgetCreates
    (C : Type u) [Category.{v} C] [CartesianMonoidalCategory C] [BraidedCategory C]
    {I : Type w} [Category I] (D : I ⥤ CommGrp C) : CreatesLimit D (forget C) := by
  letI : (forget C).ReflectsIsomorphisms :=
    inferInstanceAs ((forget₂Grp C ⋙ Grp.forget₂Mon C ⋙ Mon.forget C).ReflectsIsomorphisms)
  exact createsLimitOfReflectsIso fun c hc ↦
    { liftedCone := liftCone D c hc
      validLift := Iso.refl c
      makesLimit := liftConeIsLimit D c hc }

/-- Source: Stacks Project, Tag 00YV, abelian-group part and preceding quadruple discussion
(blueprint: lem-sfb-internal-abelian-finite-limit-creation).

The Cartesian monoidal structures specify chosen terminal objects and binary products; they
exist in every category with finite limits. The braidings are uniquely determined by these
products. Multiplication, one and inverse in `CommGrp` mean addition, zero and negation.
The subtype in the first clause fixes the underlying object literally, rather than up to
isomorphism. The equalities of forgetful functors in the last clause specify the underlying
object and morphism maps literally; `eqToIso` only supplies the corresponding type casts.

Proof (using def-galois-finite-limits-colimits and def-weil-category-product):
(1) The projections of any underlying limit are jointly monic, by uniqueness of
factorizations, also for the empty diagram. (2) Multiplication, unit and inverse in the diagram
form cones with vertices the square of the limit, the terminal object and the limit itself.
Their unique factorizations define its three operations. (3) Compose the two associativity
expressions with every projection and use the corresponding law in each diagram object;
joint monicity gives associativity. The same argument gives commutativity. (4) The two unit
and two inverse laws follow by the same projection test and terminal uniqueness. Any other
structure making the projections homomorphisms has the same three operations by limit
uniqueness. (5) For a cone of group objects, its unique underlying factorization preserves
each operation: compose the required equation with every projection. Faithfulness gives
uniqueness as a group morphism. (6) Conversely, compare a limiting group cone with the lifted
underlying limit. The two universal properties give mutually inverse cone maps, so its
underlying cone is limiting. These steps give creation, preservation and reflection.
(7) For the empty diagram all operations and laws are unique maps to a terminal object,
and every object has a unique homomorphism to it. (8) Product and terminal comparisons for
a finite-limit-preserving functor are invertible; projection tests give their compatibility
with pairings, product maps and terminal maps. (9) Induct on terms in multiplication, unit,
inverse and variables to show that transported terms agree with images of terms after the
product comparison. (10) Apply this to the two sides of every group law, obtaining the laws
for the transported operations. (11) Naturality of comparisons shows that images of
homomorphisms preserve all operations; functoriality gives the asserted functor.
(12) Forget a limiting group cone, apply preservation by the original functor, and reflect
its image limit using step (5) in the target category. This includes the empty limit. -/
theorem finiteLimitCreation
    (C : Type u) [Category.{v} C] [HasFiniteLimits C]
    [CartesianMonoidalCategory C] [BraidedCategory C] :
    (∀ (I : Type w) [SmallCategory I] [FinCategory I]
        (D : I ⥤ CommGrp C) (c : Cone (D ⋙ forget C)),
      IsLimit c →
        ∃! A : { A : CommGrp C // A.X = c.pt },
          (∀ j : I, ∃ f : A.val ⟶ D.obj j,
            eqToHom A.property.symm ≫ (forget C).map f = c.π.app j) ∧
          ∃ s : Cone D, s.pt = A.val ∧ (forget C).mapCone s = c ∧ Nonempty (IsLimit s)) ∧
    (∀ (I : Type w) [SmallCategory I] [FinCategory I]
        (D : I ⥤ CommGrp C) (c : Cone D),
      Nonempty (IsLimit c) ↔ Nonempty (IsLimit ((forget C).mapCone c))) ∧
    Nonempty (CreatesFiniteLimits (forget C)) ∧
    PreservesFiniteLimits (forget C) ∧ ReflectsFiniteLimits (forget C) ∧
    (∀ (E : Type u') [Category.{v'} E] [HasFiniteLimits E]
        [CartesianMonoidalCategory E] [BraidedCategory E]
        (F : C ⥤ E) [PreservesFiniteLimits F],
      ∃ (H : CommGrp C ⥤ CommGrp E) (hH : H ⋙ forget E = forget C ⋙ F),
        (∀ A : CommGrp C,
          MonObj.mul (X := (H.obj A).X) ≫ (eqToIso hH).hom.app A =
            ((eqToIso hH).hom.app A ⊗ₘ (eqToIso hH).hom.app A) ≫
              (prodComparisonIso F A.X A.X).inv ≫ F.map (MonObj.mul (X := A.X)) ∧
          MonObj.one (X := (H.obj A).X) ≫ (eqToIso hH).hom.app A =
            (preservesTerminalIso F).inv ≫ F.map (MonObj.one (X := A.X)) ∧
          GrpObj.inv (X := (H.obj A).X) ≫ (eqToIso hH).hom.app A =
            (eqToIso hH).hom.app A ≫ F.map (GrpObj.inv (X := A.X))) ∧
        PreservesFiniteLimits H) := by
  classical
  let : CreatesFiniteLimits (forget C) :=
    { createsFiniteLimits I _ _ := { CreatesLimit := forgetCreates C _ } }
  have : PreservesFiniteLimits (forget C) := inferInstance
  have : ReflectsFiniteLimits (forget C) := { reflects _ _ _ := inferInstance }
  refine ⟨?_, ?_, ⟨inferInstance⟩, inferInstance, inferInstance, ?_⟩
  · intro I _ _ D c hc
    refine ⟨⟨(liftCone D c hc).pt, rfl⟩, ⟨?_, ?_⟩, ?_⟩
    · intro j
      exact ⟨(liftCone D c hc).π.app j, by
        simp only [eqToHom_refl, Category.id_comp]
        rfl⟩
    · exact ⟨liftCone D c hc, rfl, rfl, ⟨liftConeIsLimit D c hc⟩⟩
    · rintro ⟨A, e⟩ ⟨hp, _⟩
      rcases A with @⟨X, g, comm⟩
      dsimp at e
      subst X
      apply Subtype.ext
      have hg : g = (liftObject D c hc).grp := by
        apply GrpObj.ext
        apply MonObj.ext
        apply hc.hom_ext
        intro j
        obtain ⟨f, hf⟩ := hp j
        simp only [eqToHom_refl, Category.id_comp] at hf
        change f.hom.hom.hom = c.π.app j at hf
        have hm := IsMonHom.mul_hom f.hom.hom.hom
        calc
          g.toMonObj.mul ≫ c.π.app j =
              (c.π.app j ⊗ₘ c.π.app j) ≫ MonObj.mul (X := (D.obj j).X) := by
            simpa only [hf] using hm
          _ = (liftObject D c hc).grp.toMonObj.mul ≫ c.π.app j :=
            (IsMonHom.mul_hom
              ((Mon.limitCone (D ⋙ forget₂Grp C ⋙ Grp.forget₂Mon C) c hc).π.app j).hom).symm
      cases hg
      rfl
  · intro I _ _ D c
    exact ⟨fun ⟨h⟩ ↦ ⟨isLimitOfPreserves (forget C) h⟩,
      fun ⟨h⟩ ↦ ⟨isLimitOfReflects (forget C) h⟩⟩
  · intro E _ _ _ _ F _
    let : CreatesFiniteLimits (forget E) :=
      { createsFiniteLimits I _ _ := { CreatesLimit := forgetCreates E _ } }
    have : ReflectsFiniteLimits (forget E) := { reflects _ _ _ := inferInstance }
    let : F.Braided := .ofChosenFiniteProducts F
    refine ⟨F.mapCommGrp, rfl, ?_, ?_⟩
    · intro A
      change
        (Functor.LaxMonoidal.μ F A.X A.X ≫ F.map (MonObj.mul (X := A.X))) ≫ 𝟙 _ =
          (𝟙 _ ⊗ₘ 𝟙 _) ≫ (prodComparisonIso F A.X A.X).inv ≫
            F.map (MonObj.mul (X := A.X)) ∧
        (Functor.LaxMonoidal.ε F ≫ F.map (MonObj.one (X := A.X))) ≫ 𝟙 _ =
          (preservesTerminalIso F).inv ≫ F.map (MonObj.one (X := A.X)) ∧
        F.map (GrpObj.inv (X := A.X)) ≫ 𝟙 _ =
          𝟙 _ ≫ F.map (GrpObj.inv (X := A.X))
      simp only [Category.comp_id, Category.id_comp, tensorHom_id,
        Functor.Monoidal.μ_of_cartesianMonoidalCategory,
        Functor.Monoidal.ε_of_cartesianMonoidalCategory, id_whiskerRight, and_self]
    · have : PreservesFiniteLimits (F.mapCommGrp ⋙ forget E) :=
        comp_preservesFiniteLimits (forget C) F
      exact preservesFiniteLimits_of_reflects_of_preserves _ (forget E)

end CategoryTheory.CommGrp
