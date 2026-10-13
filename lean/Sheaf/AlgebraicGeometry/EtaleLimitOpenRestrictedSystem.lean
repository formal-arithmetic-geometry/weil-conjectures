/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Sheaf.AlgebraicGeometry.EtaleLimitOpenCohomologyCocone

/-! # Explicit restriction of a coherent system to inverse-image opens

Source: Stacks Project, Tag 09YQ, restriction of coherent systems.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

/-- The upper tail, viewed in the over category of the initial stage.
Source: Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-open-restricted-system). -/
def tailOpenIndexFunctor {I : Type u} [Preorder I] (i₀ : I) :
    (Set.Ici i₀)ᵒᵖ ⥤ Over (op i₀) where
  obj j := Over.mk (homOfLE j.unop.property).op
  map f := Over.homMk (homOfLE (leOfHom f.unop)).op (Subsingleton.elim _ _)
  map_id _ := by apply Over.OverMorphism.ext; apply Subsingleton.elim
  map_comp _ _ := by apply Over.OverMorphism.ext; apply Subsingleton.elim

/-- The explicit inverse diagram of inverse-image opens.
Source: Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-open-restricted-system). -/
noncomputable abbrev tailOpenDiagram {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) : (Set.Ici i₀)ᵒᵖ ⥤ Scheme.{u} :=
  { obj j := (tailStageOpen D g₀ W j.unop).toScheme
    map f := tailStageOpenMap D g₀ W f.unop
    map_id j := by
      apply (cancel_mono (tailStageOpen D g₀ W j.unop).ι).mp
      simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι, Category.id_comp]
      have h : (homOfLE (show j.unop.val ≤ j.unop.val from le_rfl)).op =
          𝟙 (op j.unop.val) := Subsingleton.elim _ _
      rw [h, D.map_id, Category.comp_id]
    map_comp f g := by
      apply (cancel_mono (tailStageOpen D g₀ W _).ι).mp
      simp only [Category.assoc, tailStageOpenMap, Scheme.Hom.resLE_comp_ι]
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, ← D.map_comp]
      rfl }

/-- The explicit cone of inverse-image opens.
Source: Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-open-restricted-system). -/
noncomputable abbrev tailOpenCone {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) : Cone (tailOpenDiagram D g₀ W) :=
  { pt := ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).toScheme
    π :=
    { app j := tailLimitOpenMap D c g₀ W j.unop
      naturality j k f := by
        apply (cancel_mono (tailStageOpen D g₀ W k.unop).ι).mp
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map, tailOpenDiagram]
        simp only [tailStageOpenMap, tailLimitOpenMap, Category.id_comp,
          Category.assoc, Scheme.Hom.resLE_comp_ι]
        rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, c.w]
    } }

/-- Inclusion of the upper tail into the original directed preorder.
Source: Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-open-restricted-system). -/
def tailOpenInclusion {I : Type u} [Preorder I] (i₀ : I) : Set.Ici i₀ ⥤ I where
  obj j := j.val
  map f := homOfLE f.le

/-- Restriction of the coefficient sheaves at each stage.
Source: Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-open-restricted-system). -/
noncomputable abbrev tailOpenSheaf {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (j : Set.Ici i₀) :
    Sheaf ((tailOpenDiagram D g₀ W).obj (op j)).smallEtaleTopology
      AddCommGrpCat.{u + 1} :=
  (upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)

set_option backward.isDefEq.respectTransparency true in
/-- Restricted coefficient transitions, constructed by the commuting open square.
Source: Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-open-restricted-system). -/
noncomputable abbrev tailOpenCoefficient {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    {j k : Set.Ici i₀} (f : j ⟶ k) :
    (upperStar AddCommGrpCat.{u + 1} ((tailOpenDiagram D g₀ W).map f.op)).obj
      (tailOpenSheaf D g₀ W F j) ⟶ tailOpenSheaf D g₀ W F k :=
  openSquareCoefficient (D.map (homOfLE (show j.val ≤ k.val from f.le)).op)
    (tailStageOpen D g₀ W j).ι (tailStageOpen D g₀ W k).ι
    (tailStageOpenMap D g₀ W f)
    (by simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι])
    (F j.val) (F k.val) (φ (homOfLE (show j.val ≤ k.val from f.le)))

/-- The canonical identification of restricted limit coefficients.
Source: Stacks Project, Tag 09YQ and inverse-image composition.
(blueprint: lem-weil-pbc-etale-limit-open-restricted-system). -/
noncomputable abbrev tailOpenLimitIso {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (j : Set.Ici i₀) :
    (upperStar AddCommGrpCat.{u + 1}
      ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι).obj (G.obj j.val) ≅
    (upperStar AddCommGrpCat.{u + 1} ((tailOpenCone D c g₀ W).π.app (op j))).obj
      (tailOpenSheaf D g₀ W F j) :=
  (upperStar AddCommGrpCat.{u + 1} _).mapIso (eG j.val) ≪≫
    (upperStarComp AddCommGrpCat.{u + 1}
      ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι (c.π.app (op j.val))).symm.app (F j.val) ≪≫
    (upperStarComp AddCommGrpCat.{u + 1} (tailLimitOpenMap D c g₀ W j)
      (tailStageOpen D g₀ W j).ι
      (((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι ≫ c.π.app (op j.val))
      (by simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι])).app (F j.val)

/-- Restriction preserves the coherence of a system of inverse-image coefficients.

Source: Stacks Project, Tag 09YQ, coherent systems; inverse-image composition.
(blueprint: lem-weil-pbc-etale-limit-open-restricted-system).

Proof: Write a_j for the stage open inclusion and b for the limit open inclusion.
The restricted coefficient map is the composite of the inverse composition
isomorphism for the restricted transition and a_j, the composition isomorphism
for a_k and the original transition, and a_k^* applied to the original map.
For an identity transition, apply the original identity law. The left and right
unit laws for upperStarComp cancel the two composition isomorphisms, yielding
the required identity law. For two composable transitions, substitute the
original composition law. Move the pulled-back coefficient maps through the
composition isomorphisms by naturality, and apply the associativity coherence
for three inverse-image functors. The intermediate inverse isomorphisms cancel;
the remaining composite is exactly the restricted composition law.
For the diagram on the limit, apply b^* to the original G-map formula. Expand
the specified tailOpenLimitIso on both ends. Naturality moves the eG maps past
the composition isomorphisms, and associativity identifies the two ways of
pulling back around the projection and transition squares. Cancelling adjacent
inverse isomorphisms gives the displayed restricted G-map formula.
For any cocone L, expand the canonical cohomology leg and tailOpenLimitIso.
Functoriality of inverse image and the inverse-of-composite formula identify
the coefficient with the inverse of tailOpenLimitIso followed by restriction
of L.ι. Applying Sheaf.H.map proves the displayed leg formula. This argument
needs no scheme limit, compactness, colimit, or cohomological continuity. It
also applies to empty opens, zero coefficients and identity diagrams. -/
theorem tailOpenRestrictedSystem_coherence
    {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    (hidentity : ∀ i : I, φ (𝟙 i) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (D.map_id (op i)))).hom.app
        (F i) ≫ (upperStarId AddCommGrpCat.{u + 1} (D.obj (op i))).hom.app (F i))
    (hcomposition : ∀ (i j k : I) (f : i ⟶ j) (g : j ⟶ k),
      φ (f ≫ g) =
        (upperStarComp AddCommGrpCat.{u + 1} (D.map g.op) (D.map f.op)
          (D.map (f ≫ g).op) (D.map_comp g.op f.op)).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (D.map g.op)).map (φ f) ≫ φ g)
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (hG : ∀ (i j : I) (f : i ⟶ j), G.map f =
      (eG i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (c.π.app (op j)) (D.map f.op)
          (c.π.app (op i)) (c.w f.op).symm).hom.app (F i) ≫
        (upperStar AddCommGrpCat.{u + 1} (c.π.app (op j))).map (φ f) ≫ (eG j).inv)
    {X : Scheme.{u}} (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) :
    let E := tailOpenDiagram D g₀ W
    let cE := tailOpenCone D c g₀ W
    let F' := tailOpenSheaf D g₀ W F
    let φ' := @tailOpenCoefficient _ _ D _ _ g₀ W F φ
    let R := upperStar AddCommGrpCat.{u + 1} ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι
    let G' := (tailOpenInclusion i₀ ⋙ G) ⋙ R
    let eG' := tailOpenLimitIso D c g₀ W F G eG
    (∀ j : Set.Ici i₀, φ' (𝟙 j) =
      (eqToIso (congrArg (upperStar AddCommGrpCat.{u + 1}) (E.map_id (op j)))).hom.app
        (F' j) ≫ (upperStarId AddCommGrpCat.{u + 1} (E.obj (op j))).hom.app (F' j)) ∧
    (∀ (i j k : Set.Ici i₀) (f : i ⟶ j) (g : j ⟶ k), φ' (f ≫ g) =
      (upperStarComp AddCommGrpCat.{u + 1} (E.map g.op) (E.map f.op)
        (E.map (f ≫ g).op) (E.map_comp g.op f.op)).hom.app (F' i) ≫
      (upperStar AddCommGrpCat.{u + 1} (E.map g.op)).map (φ' f) ≫ φ' g) ∧
    (∀ (i j : Set.Ici i₀) (f : i ⟶ j), G'.map f =
      (eG' i).hom ≫
        (upperStarComp AddCommGrpCat.{u + 1} (cE.π.app (op j)) (E.map f.op)
          (cE.π.app (op i)) (cE.w f.op).symm).hom.app (F' i) ≫
        (upperStar AddCommGrpCat.{u + 1} (cE.π.app (op j))).map (φ' f) ≫ (eG' j).inv) ∧
    (∀ (L : Cocone G) (j : Set.Ici i₀),
      tailOpenCohomologyLeg D c g₀ W F G eG L j =
        AddCommGrpCat.ofHom (cohomologyMap (cE.π.app (op j)) (F' j) 0) ≫
          AddCommGrpCat.ofHom (Sheaf.H.map ((eG' j).inv ≫
            R.map (L.ι.app j.val)) 0)) := by
  sorry

end AlgebraicGeometry.Etale
