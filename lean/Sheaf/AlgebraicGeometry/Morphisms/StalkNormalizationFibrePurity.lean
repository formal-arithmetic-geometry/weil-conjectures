/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteEtale
public import Mathlib.AlgebraicGeometry.Normalization

import Sheaf.RingTheory.NormalLocalDepthTwo
import Sheaf.RingTheory.FlatLocalDepthFormula

/-!
# Propagating etaleness across the local special fibre

Source: Stacks Project, Tags 0EYE and 0EYB, as used in Tag 0EYJ.
(blueprint: lem-sbc-stalk-normalization-fibre-purity)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A finite normalization etale on the punctured open and on an open meeting
its missing fibre is etale everywhere on the local total space.

Source: Stacks Project, Tag 0EYE (purity across a regular Cartier divisor),
Tag 0EYB (fibrewise dense etale open), and Tag 0EY6 (depth-two extension).
(blueprint: lem-sbc-stalk-normalization-fibre-purity)

Proof: Localizing at s makes the base a normal Noetherian local domain A,
and hmin identifies U with its punctured spectrum. Integral closure commutes
with localization, so the indicated finite model is the local normalization.
The special fibre is geometrically integral: it is smooth and geometrically
connected. Thus the open W, which contains a point of that fibre, contains
its generic point. Away from the special fibre the normalization is etale by
hU and stability of etaleness under base change. In dimension one, A is a DVR;
the special fibre is a regular effective Cartier divisor, and etaleness at
its generic point gives absence of ramification in codimension one. Purity
extends the punctured cover to a finite etale cover. Both this extension and
the normalization have the same normal finite algebra, namely the integral
closure in the punctured algebra, so they agree. In dimension at least two,
normality gives depth at least two on A and flatness gives the same lower
bound along the special fibre of the smooth total space. The normalization
is the unique depth-two extension of the punctured cover: a finite normal
algebra satisfies the depth condition, and Hartogs extension identifies its
sections with the pushforward. The union of the punctured open and W meets
every fibre densely and contains every fibre over a base point of depth at
most one. The fibrewise purity theorem 0EYB extends the cover on this union
etale to the whole local total space. Uniqueness for the depth-two extension
identifies that extension with the normalization. Dimension zero cannot
occur since the generic point belongs to U but s does not. No section,
torsor action, group order or connectedness of the finite cover is used. -/
theorem stalk_normalization_etale_of_fibre_neighbourhood {S C : Scheme.{u}}
    [IsNoetherian S] [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (U : S.Opens) (hηU : genericPoint S ∈ U)
    (PA : (c ⁻¹ᵁ U).toScheme.FiniteEtale)
    (s : S) (hs : s ∉ U)
    (hmin : ∀ t : S, t ⤳ s → t ∉ U → t = s) :
    letI : IsFinite PA.obj.hom := PA.property
    letI : QuasiCompact (c ⁻¹ᵁ U).ι :=
      MorphismProperty.of_isPullback (isPullback_morphismRestrict c U)
        (inferInstance : QuasiCompact U.ι)
    let f := PA.obj.hom ≫ (c ⁻¹ᵁ U).ι
    let l := pullback.fst c (S.fromSpecStalk s)
    let n := pullback.snd f.fromNormalization l
    IsFinite n → Etale (f.fromNormalization ∣_ (c ⁻¹ᵁ U)) →
    (∃ (W : (pullback c (S.fromSpecStalk s)).Opens)
      (x : (pullback c (S.fromSpecStalk s) : Scheme.{u})),
      x ∈ W ∧ (l ≫ c) x = s ∧ Etale (n ∣_ W)) → Etale n := by sorry

end AlgebraicGeometry.Scheme
