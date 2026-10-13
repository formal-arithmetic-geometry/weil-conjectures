/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import Mathlib.AlgebraicGeometry.Restrict
import Sheaf.AlgebraicGeometry.EtaleLimitCanonicalCohomologyDiagram
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial

/-! # Canonical cohomology cocone on inverse-image opens

Source: Stacks Project, Tags 09YQ and 01F7.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false

/-- Restrict a coefficient map across a commuting square.
Source: Stacks Project, Tag 01F7, composition and coefficient naturality.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
noncomputable def openSquareCoefficient
    {X Y X' Y' : Scheme.{u}} (f : Y ⟶ X) (a : X' ⟶ X) (b : Y' ⟶ Y)
    (g : Y' ⟶ X') (h : b ≫ f = g ≫ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G) :
    (upperStar AddCommGrpCat.{u + 1} g).obj
      ((upperStar AddCommGrpCat.{u + 1} a).obj F) ⟶
        (upperStar AddCommGrpCat.{u + 1} b).obj G :=
  (upperStarComp AddCommGrpCat.{u + 1} g a (b ≫ f) h).inv.app F ≫
    (upperStarComp AddCommGrpCat.{u + 1} b f).hom.app F ≫
      (upperStar AddCommGrpCat.{u + 1} b).map φ

private theorem pullback_comp_transport {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (k : A ⟶ C) (h : k = a ≫ b)
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ)
    (x : Sheaf.H F n) :
    Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} a b k h).hom.app F) n
      (cohomologyMap k F n x) = cohomologyMap a _ n (cohomologyMap b F n x) := by
  subst k
  exact ((cohomologyPullbackFunctorial a b F n).2.1 x).symm

set_option backward.isDefEq.respectTransparency false in
/-- Pullback on cohomology commutes with restriction across a commuting square.
Source: Stacks Project, Tag 01F7.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
theorem openSquareCoefficient_cohomology
    {X Y X' Y' : Scheme.{u}} (f : Y ⟶ X) (a : X' ⟶ X) (b : Y' ⟶ Y)
    (g : Y' ⟶ X') (h : b ≫ f = g ≫ a)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : (upperStar AddCommGrpCat.{u + 1} f).obj F ⟶ G) (n : ℕ) :
    AddCommGrpCat.ofHom (cohomologyMap a F n) ≫
      AddCommGrpCat.ofHom
        (cohomologyMap g ((upperStar AddCommGrpCat.{u + 1} a).obj F) n) ≫
      AddCommGrpCat.ofHom (Sheaf.H.map (openSquareCoefficient f a b g h F G φ) n) =
    AddCommGrpCat.ofHom (cohomologyMap f F n) ≫
      AddCommGrpCat.ofHom (Sheaf.H.map φ n) ≫
      AddCommGrpCat.ofHom (cohomologyMap b G n) := by
  ext x
  change Sheaf.H.map (openSquareCoefficient f a b g h F G φ) n
    (cohomologyMap g _ n (cohomologyMap a F n x)) =
      cohomologyMap b G n (Sheaf.H.map φ n (cohomologyMap f F n x))
  have hs : Sheaf.H.map
      ((upperStarComp AddCommGrpCat.{u + 1} g a (b ≫ f) h).hom.app F) n
      (cohomologyMap (b ≫ f) F n x) =
        cohomologyMap g _ n (cohomologyMap a F n x) := by
    exact pullback_comp_transport g a (b ≫ f) h F n x
  rw [← hs]
  dsimp only [openSquareCoefficient]
  rw [Sheaf.H.map_comp_apply, Sheaf.H.map_comp_apply]
  have hi := Sheaf.H.map_comp_apply
    ((upperStarComp AddCommGrpCat.{u + 1} g a (b ≫ f) h).hom.app F)
    ((upperStarComp AddCommGrpCat.{u + 1} g a (b ≫ f) h).inv.app F)
    (cohomologyMap (b ≫ f) F n x)
  simp only [Iso.hom_inv_id_app, Sheaf.H.map_id_apply] at hi
  exact (congrArg (fun y ↦ Sheaf.H.map
    ((upperStar AddCommGrpCat.{u + 1} b).map φ) n
    (Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} b f).hom.app F) n y))
    hi.symm).trans
      ((congrArg (Sheaf.H.map ((upperStar AddCommGrpCat.{u + 1} b).map φ) n)
        ((cohomologyPullbackFunctorial b f F n).2.1 x).symm).trans
          (cohomologyMap_map b n φ (cohomologyMap f F n x)).symm)

/-- The open at a tail stage, pulled back from a morphism at the least index.
Source: Stacks Project, Tag 09YQ, inverse-image open system.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
abbrev tailStageOpen {I : Type u} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u})
    {X : Scheme.{u}} {i₀ : I} (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (j : Set.Ici i₀) : (D.obj (op j.val)).Opens :=
  (D.map (homOfLE j.property).op ≫ g₀) ⁻¹ᵁ W

/-- Transition between the inverse-image opens.
Source: Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
noncomputable def tailStageOpenMap {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    {j k : Set.Ici i₀} (f : j ⟶ k) :
    (tailStageOpen D g₀ W k).toScheme ⟶ (tailStageOpen D g₀ W j).toScheme :=
  (D.map (homOfLE (show j.val ≤ k.val from f.le)).op).resLE _ _ (by
    dsimp only [tailStageOpen]
    rw [← Scheme.Hom.comp_preimage, ← Category.assoc, ← D.map_comp]
    rfl)

/-- Projection of the limit open to a tail-stage open.
Source: Stacks Project, Tag 09YQ.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
noncomputable def tailLimitOpenMap {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) (j : Set.Ici i₀) :
    ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).toScheme ⟶
      (tailStageOpen D g₀ W j).toScheme :=
  (c.π.app (op j.val)).resLE _ _ (by
    dsimp only [tailStageOpen]
    rw [← Scheme.Hom.comp_preimage, ← Category.assoc, c.w])

/-- Canonical cohomology transition on the restricted stage opens.
Source: Stacks Project, Tags 09YQ and 01F7.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
noncomputable def tailOpenCohomologyMap {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (upperStar AddCommGrpCat.{u + 1} (D.map f.op)).obj (F i) ⟶ F j)
    {j k : Set.Ici i₀} (f : j ⟶ k) :
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) 0) ⟶
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W k).ι).obj (F k.val)) 0) :=
  AddCommGrpCat.ofHom (cohomologyMap (tailStageOpenMap D g₀ W f) _ 0) ≫
    AddCommGrpCat.ofHom (Sheaf.H.map
      (openSquareCoefficient (D.map (homOfLE (show j.val ≤ k.val from f.le)).op)
        (tailStageOpen D g₀ W j).ι (tailStageOpen D g₀ W k).ι
        (tailStageOpenMap D g₀ W f)
        (by simp only [tailStageOpenMap, Scheme.Hom.resLE_comp_ι])
        (F j.val) (F k.val)
        (φ (homOfLE (show j.val ≤ k.val from f.le)))) 0)

/-- Canonical cohomology leg from a stage open to the limit open.
Source: Stacks Project, Tags 09YQ and 01F7.
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone). -/
noncomputable def tailOpenCohomologyLeg {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) {X : Scheme.{u}} {i₀ : I}
    (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens)
    (F : ∀ i : I, Sheaf (D.obj (op i)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : I ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (eG : ∀ i : I, G.obj i ≅
      (upperStar AddCommGrpCat.{u + 1} (c.π.app (op i))).obj (F i))
    (L : Cocone G) (j : Set.Ici i₀) :
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) 0) ⟶
    AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι).obj L.pt) 0) :=
  AddCommGrpCat.ofHom (cohomologyMap (tailLimitOpenMap D c g₀ W j) _ 0) ≫
    AddCommGrpCat.ofHom (Sheaf.H.map
      (openSquareCoefficient (c.π.app (op j.val)) (tailStageOpen D g₀ W j).ι
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι (tailLimitOpenMap D c g₀ W j)
        (by simp only [tailLimitOpenMap, Scheme.Hom.resLE_comp_ι]) (F j.val) L.pt
        ((eG j.val).inv ≫ L.ι.app j.val)) 0)

/-- The canonical restricted cohomology arrows and legs form a diagram and cocone.

Source: Stacks Project, Tag 09YQ (coherent systems) and Tag 01F7 (functoriality).
(blueprint: lem-weil-pbc-etale-limit-open-cohomology-cocone).

Proof: For each tail index j put W_j = (D(j -> i₀); g₀)^-1(W) and use
`tailStageOpenMap` for the restricted transitions. Pull F_j back along W_j.ι.
The coefficient transition is `openSquareCoefficient`: its first factor undoes
composition along the restricted transition and W_j.ι, its second factor composes
along W_k.ι and the original transition, and its last factor restricts φ.
The inverse-image identity and associativity coherences, applied to hidentity and
hcomposition, prove the restricted coefficient identity and composition equations.
Restrict G along the limit open inclusion, and whisker with the tail inclusion.
The original eG, the projection squares, and inverse-image composition identify
this diagram with the pullbacks of the restricted F_j. Naturality and hG give
its transition formula. Restrict and reindex L as a cocone; colimithood is not
needed here. Apply `etale_limit_canonical_cohomology_diagram` in degree zero to
this restricted system. Its object identifications give eK and its arrow formula
is exactly `tailOpenCohomologyMap`. Transport its cocone point using the
coefficient identification with the restriction of L.pt. The canonical leg
formula becomes `tailOpenCohomologyLeg`. No limit, compactness, affine transition,
or cohomology continuity assertion is used. For empty W all terms are the
cohomology of the empty schemes; for an identity singleton diagram these are
ordinary restriction maps. Arbitrary coefficients, including zero, are allowed. -/
theorem etale_limit_open_cohomology_cocone
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
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
    (L : Cocone G)
    {X : Scheme.{u}} (i₀ : I) (g₀ : D.obj (op i₀) ⟶ X) (W : X.Opens) :
    let BW := AddCommGrpCat.of (Sheaf.H
      ((upperStar AddCommGrpCat.{u + 1}
        ((c.π.app (op i₀) ≫ g₀) ⁻¹ᵁ W).ι).obj L.pt) 0)
    ∃ (K : Set.Ici i₀ ⥤ AddCommGrpCat.{u + 1})
      (eK : ∀ j : Set.Ici i₀, K.obj j ≅ AddCommGrpCat.of (Sheaf.H
        ((upperStar AddCommGrpCat.{u + 1} (tailStageOpen D g₀ W j).ι).obj (F j.val)) 0)),
      (∀ (j k : Set.Ici i₀) (f : j ⟶ k), K.map f =
        (eK j).hom ≫ tailOpenCohomologyMap D g₀ W F φ f ≫ (eK k).inv) ∧
      ∃ (ι : K ⟶ (Functor.const (Set.Ici i₀)).obj BW),
        ∀ j, ι.app j = (eK j).hom ≫ tailOpenCohomologyLeg D c g₀ W F G eG L j := by
  sorry

end AlgebraicGeometry.Etale
