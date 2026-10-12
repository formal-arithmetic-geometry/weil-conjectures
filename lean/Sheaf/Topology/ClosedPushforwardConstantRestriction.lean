/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.LocallyConstant.Basic
import Sheaf.Topology.InverseImageClosedPushforwardConstant
import Sheaf.Topology.ClosedPushforwardConstantPresheaf

/-!
# Restricting a constant sheaf pushed forward from a closed subset

Source: Stacks Project, Etale Cohomology, proof of Lemma 59.82.1 (Tag 09ZG),
the displayed global-section identifications
(blueprint: lem-weil-pbc-closed-pushforward-constant-restriction).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- Source: Stacks Project, proof of Lemma 59.82.1 (Tag 09ZG), displayed identifications
(blueprint: lem-weil-pbc-closed-pushforward-constant-restriction).
The presheaf `G` below is exactly `V ↦ LC(V ∩ Z', S)` with restriction of maps.
Its inverse image is the sheafification of the presheaf pullback, and `eta` is the
presheaf adjunction unit (the colimit coprojection), followed below by `theta`.

Proof, following the node's five steps:
1. On `Z` form the sheaf `H(U) = LC(U ∩ Z', S)`. Restriction gives compatible maps
   from the diagram defining the presheaf pullback, hence a presheaf map to `H`
   by the colimit universal property (def-weil-pbc-category-colimit).
2. Factor through sheafification (def-weil-pbc-sheafification). Its global component
   is beta, and the factorization gives the asserted restriction compatibility.
3. The comparison is injective on stalks (lem-weil-pbc-sets-inverse-image-stalk and
   lem-weil-pbc-filtered-colimit-sets-elementwise): outside `Z'` use its open complement;
   inside `Z'`, equality of values and local constancy give equality on a neighbourhood.
4. Sections are determined by germs (lem-weil-pbc-sheaf-sections-determined-by-germs),
   so the comparison, and in particular beta, is injective on sections.
5. Every locally constant map on the intersection has local preimages: empty maps
   outside `Z'`, constant maps near points of the intersection. Injectivity makes
   these preimages agree on overlaps, and the sheaf axiom glues them. Thus beta is
   surjective. Taking `Z' = Set.univ` gives the parenthetical special case. -/
theorem closed_pushforward_constant_restriction
    (X : TopCat.{u}) (Z Z' : Set X) (hZ : IsClosed Z) (hZ' : IsClosed Z') (S : Type u) :
    let G : X.Presheaf (Type u) :=
      { obj := fun U ↦ LocallyConstant {x : X // x ∈ unop U ∧ x ∈ Z'} S
        map := fun {U V} f ↦ TypeCat.ofHom (LocallyConstant.comap
          ⟨fun x : {x : X // x ∈ unop V ∧ x ∈ Z'} ↦
              ⟨x.1, f.unop.le x.2.1, x.2.2⟩,
            continuous_subtype_val.subtype_mk _⟩)
        map_id := by intros; rfl
        map_comp := by intros; rfl }
    let i : TopCat.of Z ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
    let P := (Presheaf.pullback (Type u) i).obj G
    let F := (presheafToSheaf (Opens.grothendieckTopology (TopCat.of Z)) (Type u)).obj P
    let eta := (Presheaf.pullbackPushforwardAdjunction (Type u) i).unit.app G
    let theta := (sheafificationAdjunction
      (Opens.grothendieckTopology (TopCat.of Z)) (Type u)).unit.app P
    ∃ beta : F.obj.obj (op ⊤) ≃ LocallyConstant {x : X // x ∈ Z ∧ x ∈ Z'} S,
      ∀ g : LocallyConstant Z' S,
        beta (theta.app (op ⊤)
          (P.map (homOfLE (show (⊤ : Opens Z) ≤ (Opens.map i).obj ⊤ from
            fun _ _ ↦ Set.mem_univ _)).op
            (eta.app (op ⊤) (LocallyConstant.comap
              ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩ g)))) =
          LocallyConstant.comap
            ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩ g := by
  have _ := hZ
  let Y := TopCat.of Z
  let i : Y ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let G := closedPushforwardConstantPresheaf X Z' S
  let Q := closedPushforwardConstantPresheaf Y (i ⁻¹' Z') S
  obtain ⟨hG, hQ, alpha, halpha, hbeta, hbij, hunit, huniq⟩ :=
    inverse_image_closed_pushforward_constant Y X i Z' hZ' S
  let A : X.Sheaf (Type u) := ⟨G, hG⟩
  let B : Y.Sheaf (Type u) := ⟨Q, hQ⟩
  let adj := Sheaf.pullbackPushforwardAdjunction (Type u) i
  let b := (adj.homEquiv A B).symm alpha
  let a := (Sheaf.pullbackIso (Type u) i).app A
  let P := (Presheaf.pullback (Type u) i).obj G
  let F := (presheafToSheaf (Opens.grothendieckTopology Y) (Type u)).obj P
  let eta := (Presheaf.pullbackPushforwardAdjunction (Type u) i).unit.app G
  let theta := (sheafificationAdjunction (Opens.grothendieckTopology Y) (Type u)).unit.app P
  let e : Q.obj (op ⊤) ≃ LocallyConstant {x : X // x ∈ Z ∧ x ∈ Z'} S :=
    { toFun := LocallyConstant.comap
        ⟨fun x ↦ ⟨⟨x.1, x.2.1⟩, (by trivial), x.2.2⟩,
          (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
      invFun := LocallyConstant.comap
        ⟨fun x ↦ ⟨x.1.1, x.1.2, x.2.2⟩,
          (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
      left_inv := by intro g; apply LocallyConstant.ext; intro x; rfl
      right_inv := by intro g; apply LocallyConstant.ext; intro x; rfl }
  change ∃ beta : F.obj.obj (op ⊤) ≃ _, _
  refine ⟨(Equiv.ofBijective (a.inv.hom.app (op ⊤))
    (ConcreteCategory.bijective_of_isIso _)).trans
      ((Equiv.ofBijective (b.hom.app (op ⊤)) (hbij ⊤)).trans e), ?_⟩
  intro g
  have hc : (adj.unit.app A).hom ≫ ((Sheaf.pushforward (Type u) i).map a.hom).hom =
      eta ≫ (Presheaf.pushforward (Type u) i).map theta := by
    have : (Opens.map i).IsContinuous (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology Y) := by
      apply Functor.isContinuous_of_coverPreserving
      · exact compatiblePreserving_opens_map i
      · exact coverPreserving_opens_map i
    exact congrArg (fun f ↦ f.hom) (Adjunction.unit_leftAdjointUniq_hom_app
      adj (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map i) (Type u) (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology Y)) A)
  let g0 : G.obj (op ⊤) := LocallyConstant.comap
    ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩ g
  have hc0 := congrArg (fun f ↦ f.app (op ⊤) g0) hc
  change a.hom.hom.app (op ⊤) ((adj.unit.app A).hom.app (op ⊤) g0) =
      theta.app (op ⊤) (eta.app (op ⊤) g0) at hc0
  have hinv : a.inv.hom.app (op ⊤) (theta.app (op ⊤) (eta.app (op ⊤) g0)) =
      (adj.unit.app A).hom.app (op ⊤) g0 := by
    rw [← hc0]
    change (a.hom.hom.app (op ⊤) ≫ a.inv.hom.app (op ⊤)) _ = _
    have he := congrArg (fun f ↦ f.hom.app (op ⊤)) a.hom_inv_id
    change a.hom.hom.app (op ⊤) ≫ a.inv.hom.app (op ⊤) = 𝟙 _ at he
    rw [he]
    rfl
  change e (b.hom.app (op ⊤)
    (a.inv.hom.app (op ⊤) (theta.app (op ⊤) (P.map _ (eta.app (op ⊤) g0))))) = _
  have hid : P.map (homOfLE (show (⊤ : Opens Z) ≤ (Opens.map i).obj ⊤ from
      fun _ _ ↦ Set.mem_univ _)).op = 𝟙 (P.obj (op ⊤)) := by
    convert P.map_id (op ⊤) using 1 <;> rfl
  rw [hid]
  change e (b.hom.app (op ⊤)
    (a.inv.hom.app (op ⊤) (theta.app (op ⊤) (eta.app (op ⊤) g0)))) = _
  rw [hinv]
  have hu : b.hom.app (op ⊤) ((adj.unit.app A).hom.app (op ⊤) g0) =
      alpha.hom.app (op ⊤) g0 := hunit ⊤ g0
  rw [hu, halpha ⊤ g0]
  ext x
  rfl

end TopCat
