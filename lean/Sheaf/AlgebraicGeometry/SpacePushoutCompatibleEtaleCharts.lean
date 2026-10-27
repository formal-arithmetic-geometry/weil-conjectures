/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import Sheaf.AlgebraicGeometry.SpaceAffineThickeningPushout
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits

/-! # Compatible scheme charts for infinitesimal pushouts

Source: Stacks Project, spaces-pushouts.tex, Tags 07W0, 07W2 and 07VX;
spaces-more-morphisms.tex, Tag 05ZS
(blueprint: lem-sfb-space-pushout-compatible-etale-charts).

The two pullback squares sharing the map `t` encode exactly the specified isomorphism
of the chart overlaps over `U`, with the second square using `t ≫ φ.hom`.
All schemes are objects of `Over B`; their maps are sent to the actual fppf Yoneda sheaves.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Every surjective etale scheme chart of `X` extends to a compatible one of `Y`.
The first square identifies `U₁` with `X₁ ×_X U = X₁ ×_S T`; the second identifies
it with `Y₁ ×_Y (Y ×_T' T)`, using exactly `φ` on the overlap.
Source: Stacks, Tags 07W0 and 05ZS
(blueprint: lem-sfb-space-pushout-compatible-etale-charts).

Proof, node step 1: the overlap map to Y is the base change of the thickening i,
and its map to X is the base change of the affine map a. By
lem-sfb-space-thickening-base-change and lem-weil-pbc-affine-morphism-permanence,
the scheme pullback U₁ of the given chart is affine over X₁. It is a surjective
etale chart of U by lem-trf-space-fibre-products-etale-covers. Apply
lem-sfb-space-thickening-etale-scheme-equivalence to U into Y to lift U₁ to an
etale scheme Y₁ over Y. The lift restricts to U₁ with the specified map through φ.
Both thickening maps are homeomorphisms on points, so surjectivity of U₁ over U
implies surjectivity of Y₁ over Y. No finite nilpotence bound is used. -/
theorem exists_pushout_compatible_etale_charts {B : Scheme.{u}}
    (T T' S : Over B) (i : T ⟶ T') (a : T ⟶ S)
    [IsClosedImmersion i.left] (hi : IsHomeomorph i.left.base) [IsAffineHom a.left]
    (X Y : AlgebraicSpace B) (x : X ⟶ schemeSpace S) (y : Y ⟶ schemeSpace T')
    (φ : enlargedFibreProduct x
        (ObjectProperty.homMk (X := schemeSpace T)
          ((Scheme.fppfTopology.over B).yoneda.map a)) ≅
      enlargedFibreProduct y
        (ObjectProperty.homMk (X := schemeSpace T)
          ((Scheme.fppfTopology.over B).yoneda.map i)))
    (hφ : φ.hom.hom ≫ Limits.pullback.snd y.hom
        ((Scheme.fppfTopology.over B).yoneda.map i) =
      Limits.pullback.snd x.hom ((Scheme.fppfTopology.over B).yoneda.map a))
    (X₁ : Over B) (c : schemeSpace X₁ ⟶ X)
    (hc : IsEtale c.hom.hom) (hcs : IsSurjective c.hom.hom) :
    ∃ (Y₁ U₁ : Over B) (d : schemeSpace Y₁ ⟶ Y) (r : U₁ ⟶ X₁) (s : U₁ ⟶ Y₁)
      (t : schemeSpace U₁ ⟶ enlargedFibreProduct x
        (ObjectProperty.homMk (X := schemeSpace T)
          ((Scheme.fppfTopology.over B).yoneda.map a))),
      IsEtale d.hom.hom ∧ IsSurjective d.hom.hom ∧
      IsPullback (ObjectProperty.homMk ((Scheme.fppfTopology.over B).yoneda.map r)) t c
        (enlargedFibreProductFst x
          (ObjectProperty.homMk (X := schemeSpace T)
          ((Scheme.fppfTopology.over B).yoneda.map a))) ∧
      IsPullback (ObjectProperty.homMk ((Scheme.fppfTopology.over B).yoneda.map s))
        (t ≫ φ.hom) d (enlargedFibreProductFst y
          (ObjectProperty.homMk (X := schemeSpace T)
          ((Scheme.fppfTopology.over B).yoneda.map i))) := by
  sorry

/-- Any compatible pair of scheme charts has a scheme pushout, and every such scheme
pushout maps to the specified algebraic-space pushout by a surjective etale map.
The equations characterize the induced map on both pieces; the final two squares
are the asserted cartesian chart squares.
Source: Stacks, Tags 07W2, 07VX, 07SY and 05ZS
(blueprint: lem-sfb-space-pushout-compatible-etale-charts).

Proof, node steps 2--4: by lem-sfb-space-affine-thickening-pushout, X into Z is
a thickening. Lift X₁ to an etale scheme E over Z using
lem-sfb-space-thickening-etale-scheme-equivalence. The two thickenings identify
point spaces, so E over Z is surjective. The recovery part of
lem-sfb-space-affine-thickening-pushout gives Y = Z times_P T'. Hence E times_Z Y
is E times_P T', a scheme. Its restriction to U is U₁. Full faithfulness in
lem-sfb-space-thickening-etale-scheme-equivalence identifies it with Y₁, with
the prescribed overlap map. Apply lem-sfb-space-pushout-etale-base-change to E:
it is the space pushout of X₁ and Y₁ along U₁. By the scheme clause of
lem-sfb-space-affine-thickening-pushout, the scheme pushout exists and is also a
space pushout. The two universal properties identify every such Z₁ with E,
fixing both pieces. The induced map is therefore etale and surjective, and its
pullbacks to X and Y are the given charts. The affine and thickening properties
of the overlap maps use lem-weil-pbc-affine-morphism-permanence and
lem-sfb-space-thickening-base-change. -/
theorem compatible_etale_charts_pushout {B : Scheme.{u}}
    (T T' S : Over B) (i : T ⟶ T') (a : T ⟶ S)
    [IsClosedImmersion i.left] (hi : IsHomeomorph i.left.base) [IsAffineHom a.left]
    (X Y : AlgebraicSpace B) (x : X ⟶ schemeSpace S) (y : Y ⟶ schemeSpace T')
    (φ : enlargedFibreProduct x
        (ObjectProperty.homMk (X := schemeSpace T)
          ((Scheme.fppfTopology.over B).yoneda.map a)) ≅
      enlargedFibreProduct y
        (ObjectProperty.homMk (X := schemeSpace T)
          ((Scheme.fppfTopology.over B).yoneda.map i)))
    (hφ : φ.hom.hom ≫ Limits.pullback.snd y.hom
        ((Scheme.fppfTopology.over B).yoneda.map i) =
      Limits.pullback.snd x.hom ((Scheme.fppfTopology.over B).yoneda.map a))
    (Z : AlgebraicSpace B) (j : X ⟶ Z) (k : Y ⟶ Z)
    (hz : IsPushout (enlargedFibreProductFst x
        (ObjectProperty.homMk (X := schemeSpace T)
          ((Scheme.fppfTopology.over B).yoneda.map a)))
      (φ.hom ≫ enlargedFibreProductFst y
        (ObjectProperty.homMk (X := schemeSpace T)
          ((Scheme.fppfTopology.over B).yoneda.map i))) j k)
    (X₁ Y₁ U₁ : Over B) (c : schemeSpace X₁ ⟶ X) (d : schemeSpace Y₁ ⟶ Y)
    (hc : IsEtale c.hom.hom) (hcs : IsSurjective c.hom.hom)
    (hd : IsEtale d.hom.hom) (hds : IsSurjective d.hom.hom)
    (r : U₁ ⟶ X₁) (s : U₁ ⟶ Y₁)
    (t : schemeSpace U₁ ⟶ enlargedFibreProduct x
      (ObjectProperty.homMk (X := schemeSpace T)
          ((Scheme.fppfTopology.over B).yoneda.map a)))
    (hr : IsPullback
      (ObjectProperty.homMk ((Scheme.fppfTopology.over B).yoneda.map r)) t c
      (enlargedFibreProductFst x
        (ObjectProperty.homMk (X := schemeSpace T)
          ((Scheme.fppfTopology.over B).yoneda.map a))))
    (hs : IsPullback
      (ObjectProperty.homMk ((Scheme.fppfTopology.over B).yoneda.map s)) (t ≫ φ.hom) d
      (enlargedFibreProductFst y
        (ObjectProperty.homMk (X := schemeSpace T)
          ((Scheme.fppfTopology.over B).yoneda.map i)))) :
    (∃ (Z₁ : Over B) (j₁ : X₁ ⟶ Z₁) (k₁ : Y₁ ⟶ Z₁),
      IsPushout r.left s.left j₁.left k₁.left) ∧
    ∀ (Z₁ : Over B) (j₁ : X₁ ⟶ Z₁) (k₁ : Y₁ ⟶ Z₁),
      IsPushout r.left s.left j₁.left k₁.left →
      ∃ e : schemeSpace Z₁ ⟶ Z,
        ObjectProperty.homMk ((Scheme.fppfTopology.over B).yoneda.map j₁) ≫ e = c ≫ j ∧
        ObjectProperty.homMk ((Scheme.fppfTopology.over B).yoneda.map k₁) ≫ e = d ≫ k ∧
        IsEtale e.hom.hom ∧ IsSurjective e.hom.hom ∧
        IsPullback
          (ObjectProperty.homMk ((Scheme.fppfTopology.over B).yoneda.map j₁)) c e j ∧
        IsPullback
          (ObjectProperty.homMk ((Scheme.fppfTopology.over B).yoneda.map k₁)) d e k := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
