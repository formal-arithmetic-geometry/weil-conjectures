/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Z6
-/
module

public import Sheaf.AlgebraicGeometry.ConnectedAbelianTowerDescentObject

/-! # Equivariant morphism descent for normalized finite splittings

Source: Stacks Project, Tags 04TQ and 086J; Bhatt--Scholze, Lemma 5.1.2
(blueprint: lem-sfb-connected-abelian-tower-descent-hom).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped FintypeCatDiscrete
namespace AlgebraicGeometry.ProEtale

variable {U : Scheme.{u}} {I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]

/-- The actual map on finite labels induced by a sheaf map and the stalk equivalences.
Source: transport of the geometric stalk map
(blueprint: lem-sfb-connected-abelian-tower-descent-hom). -/
def AbelianTowerDescentObject.labelMap (T : ConnectedAbelianCoverTower U I)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {z : Spec (.of Ω) ⟶ T.cone.pt.left}
    {F F' : Sheaf (Scheme.ProEt.topology U) (Type (u + 1))}
    (d : AbelianTowerDescentObject T z F) (d' : AbelianTowerDescentObject T z F')
    (f : F ⟶ F') : d.action.obj.V ⟶ d'.action.obj.V :=
  FintypeCat.homMk fun q ↦ (d'.fibre.symm
    (colim.map (Functor.whiskerLeft
      (Scheme.proEtaleGeometricNeighbourhoodForget (z ≫ T.cone.pt.hom)).op f.hom)
        (d.fibre (ULift.up q)))).down

/-- Applying the fibre bijection cancels the inverse used in labelMap.
Source: transport by an equivalence
(blueprint: lem-sfb-connected-abelian-tower-descent-hom). -/
@[simp]
theorem AbelianTowerDescentObject.fibre_labelMap (T : ConnectedAbelianCoverTower U I)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {z : Spec (.of Ω) ⟶ T.cone.pt.left}
    {F F' : Sheaf (Scheme.ProEt.topology U) (Type (u + 1))}
    (d : AbelianTowerDescentObject T z F) (d' : AbelianTowerDescentObject T z F')
    (f : F ⟶ F') (q : d.action.obj.V) :
    d'.fibre (ULift.up (ConcreteCategory.hom (d.labelMap T d' f) q)) =
      colim.map (Functor.whiskerLeft
        (Scheme.proEtaleGeometricNeighbourhoodForget (z ≫ T.cone.pt.hom)).op f.hom)
          (d.fibre (ULift.up q)) := by
  exact d'.fibre.apply_symm_apply _

/-- Equivariant label maps are precisely maps of the original sheaves. The first
clause pins the map to the actual normalized universal sections.
Source: Stacks Project, Tags 04TQ and 086J; Bhatt--Scholze, Lemma 5.1.2
(blueprint: lem-sfb-connected-abelian-tower-descent-hom).

Proof: On the connected limit scheme, a map between constant finite sheaves is
constant in its labels and its label map is determined by its geometric stalk.
Conjugate a given sheaf map by the normalized splittings. Its stalk map is exactly
labelMap, so the constant-map calculation proves the universal-section equation.
Naturality of restriction on the double overlap intertwines the two descent
comparisons. Restrict along each constant group section and evaluate the fibre;
this proves that labelMap is equivariant.

Conversely let a be an equivariant label map. Conjugating its constant-sheaf map
by the splittings gives a map over the limit. Take a common later finite level
trivializing both sheaves. Both overlap comparisons are constant permutations on
the finitely many clopen cylinders for this level. The group-limit projection to
this finite group is surjective, by the finite nonempty inverse-limit lemma and
the surjective transition hypothesis. Thus G-equivariance gives intertwining at
every finite group label, hence on every entire cylinder, and sheaf separatedness
gives intertwining on the whole overlap. Morphism descent along the singleton
cover of U therefore gives a unique global sheaf map. Its stalk label map is a.
Two global maps with the same label map agree after restriction to the limit by
the constant-map calculation, hence globally by uniqueness of morphism descent.
This works also for empty labels: maps out of the empty constant sheaf are unique,
and a nonempty source admits no map to an empty target. -/
theorem abelianTowerDescentHom {U : Scheme.{u}} {I : Type u} [Preorder I]
    [Nonempty I] [IsDirected I (· ≤ ·)] (T : ConnectedAbelianCoverTower U I)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {z : Spec (.of Ω) ⟶ T.cone.pt.left}
    {F F' : Sheaf (Scheme.ProEt.topology U) (Type (u + 1))}
    (d : AbelianTowerDescentObject T z F) (d' : AbelianTowerDescentObject T z F') :
    (∀ f : F ⟶ F',
      (∀ g : T.groupCone.pt,
        d.action.obj.ρ g ≫ d.labelMap T d' f = d.labelMap T d' f ≫ d'.action.obj.ρ g) ∧
      F'.obj.map ((abelianTowerLabels T.cone.pt).map
        (FintypeCat.toProfinite.map (d.labelMap T d' f))).op d'.section_ =
          f.hom.app _ d.section_) ∧
    ∀ a : d.action.obj.V ⟶ d'.action.obj.V,
      (∀ g : T.groupCone.pt, d.action.obj.ρ g ≫ a = a ≫ d'.action.obj.ρ g) →
      ∃! f : F ⟶ F', d.labelMap T d' f = a := by sorry

end AlgebraicGeometry.ProEtale
