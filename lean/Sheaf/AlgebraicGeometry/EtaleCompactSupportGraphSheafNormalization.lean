/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.EtaleCompactSupportNormalizationData
import Sheaf.AlgebraicGeometry.EtaleSheafClopenProduct
import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# The graph map into the compactification sheaf

Source: Stacks Project Tag 0F4L (lemma-shriek-into-star-separated-etale),
and SGA 4 XVII 6.2.11 (blueprint: lem-asd-compact-support-graph-sheaf-normalization).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem graph_baseChange_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {P : D ⥤ E} {S : E ⥤ D}
    {Q : C ⥤ F} {T : F ⥤ C} {V : F ⥤ E} {W : E ⥤ F}
    (a : L ⊣ R) (b : P ⊣ S) (c : Q ⊣ T) (d : V ⊣ W)
    (x : S ⋙ R ≅ W ⋙ T) (M : C) {N : E} (φ : (Q ⋙ V).obj M ⟶ N) :
    a.unit.app M ≫ R.map (b.unit.app (L.obj M)) ≫
        R.map (S.map
          ((((a.comp b).ofNatIsoRight x).leftAdjointUniq (c.comp d)).hom.app M ≫ φ)) ≫
        x.hom.app N =
      c.unit.app M ≫ T.map (d.unit.app (Q.obj M) ≫ W.map φ) := by
  have h := Adjunction.homEquiv_naturality_right
    ((a.comp b).ofNatIsoRight x)
    ((((a.comp b).ofNatIsoRight x).leftAdjointUniq (c.comp d)).hom.app M) φ
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app] at h
  simp only [Adjunction.homEquiv_unit, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.comp_unit_app,
    Functor.comp_map, Functor.map_comp, Category.assoc] at h ⊢
  simp only [← Functor.comp_map] at h ⊢
  rw [← x.hom.naturality_assoc, ← x.hom.naturality] at h
  exact h



/-- The transpose of the graph comparison is the graph extension unit.
Source: Stacks Project Tag 0F4L and SGA 4 XVII 6.2.11; the adjunction-transpose part
of the graph restriction calculation.
Proof: transpose the explicit graph map through the lower-shriek restriction adjunction;
then simplify the graph and complement restrictions using the clopen decomposition.
(blueprint: lem-asd-compact-support-graph-sheaf-normalization-transpose).
-/
theorem compactSupportGraphSheafComparison_normalization_transpose
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X)
    [Etale f] [IsSeparated f] (c : Compactification f)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).homEquiv M
        ((f)_*[ModuleCat.{u + 1} A].obj M)
      ((etaleCompactificationGraphMap A f c).app M ≫
        (compactificationSheafToDirectImage A c).app M) =
      (lowerStarUnit (ModuleCat.{u + 1} A) f).app M := by
  sorry

/-- The graph transpose extends each sheet section by zero in the compactification.
Source: Stacks Project Tag 0F4L, lemma-shriek-into-star-separated-etale;
SGA 4 XVII 6.2.11.
(blueprint: lem-asd-compact-support-graph-sheaf-normalization).

Proof:
1. Transpose both sides under the sum-extension/restriction adjunction. A section over
an etale test object is thereby tested on each lift of that object to U.
2. The inverse beta in the graph projection identifies that lift with its base change
in Z times_X U. The composition comparison preserves the same left-adjoint units.
3. The projection to the graph is identity on the graph and zero on its complement:
its map into the graph direct image is the adjoint of the section identity, and the
clopen comparison between extension and direct image is inverted.
4. Inclusion of extension by zero into direct image keeps the underlying section.
Both transposes are therefore the graph-extension unit defining
etaleLowerShriekToLowerStar. Injectivity of the adjunction bijection proves equality.
Concretely, apply the injective homEquiv of etaleLowerShriekRestrictionAdjunction,
then lowerStarUnit_app_hom_app. Scheme.Etale.graph_hom_ext reduces the resulting
section equation to its graph and complement restrictions. The target restrictions
are graphExtend_graph and graphExtend_graphComplι. For the constructed transpose,
the inverse-conjugate counit equation for beta, the counit equation for leftAdjointUniq,
and the triangle identity for the clopen projection give respectively identity and zero.
The argument is valid for the empty graph, where all relevant sections are zero. -/
theorem compactSupportGraphSheafComparison_normalization
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (f : U ⟶ X)
    [Etale f] [IsSeparated f] (c : Compactification f)
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (etaleCompactificationGraphMap A f c).app M ≫
        (compactificationSheafToDirectImage A c).app M =
      etaleLowerShriekToLowerStar (ModuleCat.{u + 1} A) f M := by
  apply ((etaleLowerShriekRestrictionAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _).injective
  rw [compactSupportGraphSheafComparison_normalization_transpose A f c M]
  rw [etaleLowerShriekToLowerStar]
  exact (Equiv.apply_symm_apply _ _).symm

end AlgebraicGeometry.Etale
