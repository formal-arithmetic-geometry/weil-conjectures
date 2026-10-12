/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Topology.LocallyConstant.Basic
import Sheaf.Topology.ClosedPushforwardConstantStalks

/-!
# Inverse image of a constant sheaf pushed forward from a closed subset

Source: Stacks Project, Modules, proof of Tag 0CAL (reduction by Tag 0CAK);
Sheaves, Tags 008H, 00AE and 007T, for the proof on stalks.
(blueprint: lem-weil-pbc-inverse-image-closed-pushforward-constant).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace

namespace TopCat

/-- Source: Stacks Project, Modules, proof of Tag 0CAL; Sheaves, Tags 008H, 00AE, 007T.
(blueprint: lem-weil-pbc-inverse-image-closed-pushforward-constant).
The presheaves `P` and `Q` are the sectionwise descriptions of the two closed direct
images. The existential sheaf proofs assert that these actual presheaves are sheaves.
The map `alpha` is prescribed on every section by composition with `f`. Its adjoint
`beta` is taken along the project's inverse image of sheaves of sets,
`TopCat.Sheaf.pullback` with `TopCat.Sheaf.pullbackPushforwardAdjunction` (as in
lem-weil-pbc-h0-spectral-closed-restriction); `TopCat.Sheaf.pullbackIso` identifies it
with the sheafified presheaf inverse image of def-weil-pbc-topological-inverse-image.

Proof, following the node's five steps:
1. Both section presheaves are sheaves by
   lem-weil-pbc-closed-pushforward-constant-stalks (0). Composition with `f` preserves
   local constancy and commutes with restrictions, giving `alpha`. The sets adjunction
   of lem-weil-pbc-sets-inverse-image-colimits-finite-products (a) gives `beta` and its
   unique unit compatibility (def-weil-pbc-topological-inverse-image (3)).
2. For x in X, the inverse-image stalk comparison of
   lem-weil-pbc-sets-inverse-image-stalk sends a germ of g at f(x) to the germ of eta(g)
   at x. Unit compatibility sends this to the germ of g composed with f.
3. At x in the preimage of W, evaluation identifies both closed-direct-image stalks
   with R, by lem-weil-pbc-closed-pushforward-constant-stalks (a). The map on germs
   respects evaluation, so it is bijective; equality on all coprojections gives the
   equality on the colimit (def-weil-pbc-category-colimit).
4. Outside the preimage of W, both stalks are singletons, by
   lem-weil-pbc-closed-pushforward-constant-stalks (b), so the stalk map is bijective.
5. Apply lem-weil-pbc-sets-sheaf-iso-on-stalks (Tag 007T). Evaluating the inverse sheaf
   morphism on every open gives the inverse section maps and hence bijectivity. -/
theorem inverse_image_closed_pushforward_constant
    (X Y : TopCat.{u}) (f : X ⟶ Y) (W : Set Y) (hW : IsClosed W) (R : Type u) :
    let Z : Set X := f ⁻¹' W
    let P : Y.Presheaf (Type u) :=
      { obj := fun V ↦ LocallyConstant {y : Y // y ∈ unop V ∧ y ∈ W} R
        map := fun {U V} i ↦ TypeCat.ofHom (LocallyConstant.comap
          ⟨fun y : {y : Y // y ∈ unop V ∧ y ∈ W} ↦
              ⟨y.1, i.unop.le y.2.1, y.2.2⟩,
            continuous_subtype_val.subtype_mk _⟩)
        map_id := by intros; rfl
        map_comp := by intros; rfl }
    let Q : X.Presheaf (Type u) :=
      { obj := fun U ↦ LocallyConstant {x : X // x ∈ unop U ∧ x ∈ Z} R
        map := fun {U V} i ↦ TypeCat.ofHom (LocallyConstant.comap
          ⟨fun x : {x : X // x ∈ unop V ∧ x ∈ Z} ↦
              ⟨x.1, i.unop.le x.2.1, x.2.2⟩,
            continuous_subtype_val.subtype_mk _⟩)
        map_id := by intros; rfl
        map_comp := by intros; rfl }
    ∃ (hP : P.IsSheaf) (hQ : Q.IsSheaf),
      let A : Y.Sheaf (Type u) := ⟨P, hP⟩
      let B : X.Sheaf (Type u) := ⟨Q, hQ⟩
      let L := Sheaf.pullback (Type u) f
      let adj : L ⊣ Sheaf.pushforward (Type u) f := Sheaf.pullbackPushforwardAdjunction (Type u) f
      ∃ alpha : A ⟶ (Sheaf.pushforward (Type u) f).obj B,
        (∀ (V : Opens Y) (g : P.obj (op V)),
          alpha.hom.app (op V) g = LocallyConstant.comap
            ⟨fun x : {x : X // x ∈ (Opens.map f).obj V ∧ x ∈ Z} ↦
                ⟨f x.1, x.2.1, x.2.2⟩,
              (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩ g) ∧
        let beta := (adj.homEquiv A B).symm alpha
        IsIso beta ∧
          (∀ U : Opens X, Function.Bijective (beta.hom.app (op U))) ∧
          (∀ (V : Opens Y) (g : P.obj (op V)),
            beta.hom.app (op ((Opens.map f).obj V))
              ((adj.unit.app A).hom.app (op V) g) = alpha.hom.app (op V) g) ∧
          (∀ beta' : L.obj A ⟶ B,
            (∀ (V : Opens Y) (g : P.obj (op V)),
              beta'.hom.app (op ((Opens.map f).obj V))
                ((adj.unit.app A).hom.app (op V) g) = alpha.hom.app (op V) g) →
            beta' = beta) := by
  sorry

end TopCat
