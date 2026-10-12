/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Inverse image of representable sheaves on the small étale site

Source: Stacks Project, Étale Cohomology, Tag 03Q1, part (4), and Sites, Tag 04D3
(blueprint: lem-galois-inverse-image-representable).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Inverse image carries the representable sheaf of an étale `Y`-scheme to the
representable sheaf of its base change, naturally in the étale `Y`-scheme.
Source: Stacks Project, Tag 03Q1 (4), and Tag 04D3
(blueprint: lem-galois-inverse-image-representable).

Here `f.Etale` sends `V` to `V ×_Y X` with projection to `X`; symmetry of the
scheme fibre product identifies this with `X ×_Y V` with its first projection.
The existing subcanonical instance packages the representable presheaves as sheaves,
as asserted by `lem-weil-pbc-small-etale-representable-presheaf-sheaf`.
`uliftYoneda` only raises the universe of the sets of morphisms.

Proof:
1. Étale morphisms are stable under base change
(`lem-weil-pbc-etale-scheme-base-change`), and the fibre-product universal property
(`def-pc-fibre-product`) gives the functor `f.Etale`.
2. The adjunction identifies maps from `L(h_V)` to `F` with maps from `h_V` to
`f_* F`. The representable-sheaf lemma above, the full sheaf subcategory
(`def-weil-pbc-etale-sheaf-of-sets`), and Yoneda
(`lem-galois-yoneda-hom-bijection`) identify these with `(f_* F)(V)`.
3. By direct-image evaluation this is `F(V ×_Y X)`. The same representable-sheaf
lemma and Yoneda identify it with maps from `h_(V ×_Y X)` to `F`, naturally in `F`.
4. Apply `lem-weil-pbc-coyoneda-iso-of-natural-hom-bijection` to these Hom bijections.
Naturality of adjunction, Yoneda evaluation, and base change in a morphism `V → V'`
shows that the resulting objectwise isomorphisms form the asserted natural isomorphism.
-/
theorem nonempty_inverseImage_representable_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (L : Sheaf Y.smallEtaleTopology (Type (max u v)) ⥤
      Sheaf X.smallEtaleTopology (Type (max u v)))
    (_adj : L ⊣ f.Etale.sheafPushforwardContinuous (Type (max u v))
      Y.smallEtaleTopology X.smallEtaleTopology) :
    Nonempty
      (Y.smallEtaleTopology.uliftYoneda.{v} ⋙ L ≅
        f.Etale ⋙ X.smallEtaleTopology.uliftYoneda.{v}) := by
  let A := Y.smallEtaleTopology.uliftYoneda.{v} ⋙ L
  let B := f.Etale ⋙ X.smallEtaleTopology.uliftYoneda.{v}
  let e (V : Y.Etale) (F : Sheaf X.smallEtaleTopology (Type (max u v))) :
      (A.obj V ⟶ F) ≃ (B.obj V ⟶ F) :=
    ((_adj.homEquiv _ _).trans Y.smallEtaleTopology.uliftYonedaEquiv).trans
      X.smallEtaleTopology.uliftYonedaEquiv.symm
  have ee (V : Y.Etale) (F : Sheaf X.smallEtaleTopology (Type (max u v)))
      (a : A.obj V ⟶ F) :
      X.smallEtaleTopology.uliftYonedaEquiv (e V F a) =
        Y.smallEtaleTopology.uliftYonedaEquiv (_adj.homEquiv _ _ a) := by
    exact X.smallEtaleTopology.uliftYonedaEquiv.apply_symm_apply _
  have er (V : Y.Etale) {F G : Sheaf X.smallEtaleTopology (Type (max u v))}
      (a : A.obj V ⟶ F) (g : F ⟶ G) : e V G (a ≫ g) = e V F a ≫ g := by
    apply X.smallEtaleTopology.uliftYonedaEquiv.injective
    rw [ee, GrothendieckTopology.uliftYonedaEquiv_comp, ee,
      _adj.homEquiv_naturality_right, GrothendieckTopology.uliftYonedaEquiv_comp]
    rfl
  have el {V W : Y.Etale} (g : V ⟶ W)
      (F : Sheaf X.smallEtaleTopology (Type (max u v))) (a : A.obj W ⟶ F) :
      e V F (A.map g ≫ a) = B.map g ≫ e W F a := by
    apply X.smallEtaleTopology.uliftYonedaEquiv.injective
    rw [ee]
    change Y.smallEtaleTopology.uliftYonedaEquiv
      (_adj.homEquiv _ _ (L.map (Y.smallEtaleTopology.uliftYoneda.map g) ≫ a)) =
        X.smallEtaleTopology.uliftYonedaEquiv
          (X.smallEtaleTopology.uliftYoneda.map (f.Etale.map g) ≫ e W F a)
    rw [_adj.homEquiv_naturality_left,
      ← GrothendieckTopology.uliftYonedaEquiv_naturality,
      ← GrothendieckTopology.uliftYonedaEquiv_naturality, ee]
    rfl
  let E : A.op ⋙ coyoneda ≅ B.op ⋙ coyoneda :=
    NatIso.ofComponents (fun V ↦
      NatIso.ofComponents (fun F ↦ (e V.unop F).toIso) (by
        intro F G g
        ext a
        exact er V.unop a g)) (by
      intro V W g
      ext F a
      exact el g.unop F a)
  exact ⟨(NatIso.removeOp
    ((Coyoneda.fullyFaithful.whiskeringRight _).preimageIso E)).symm⟩

end AlgebraicGeometry
