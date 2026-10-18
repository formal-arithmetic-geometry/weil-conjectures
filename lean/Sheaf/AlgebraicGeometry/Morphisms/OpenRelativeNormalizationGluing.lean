/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Localization.Integral

/-!
# Affine charts for relative normalization over an open

Source: Stacks Project, Morphisms, Section 29.54, Tags 035H, 035K and 03GP;
More on Morphisms, Tag 0CNX, normalization step.
(blueprint: lem-trf-open-relative-normalization-gluing)

The normalization input is quasi-compact, as required in Tag 035H. Its charts use
sections over the full inverse images of affine opens of the base. Gluing closures
computed separately over a principal cover of the open does not give this construction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

/-- Relative normalization charts and recovery of an integral morphism over an open.
Source: Stacks Project, Tags 035H, 035K and 03GP, and the normalization step of 0CNX.
(blueprint: lem-trf-open-relative-normalization-gluing)

Proof: Set `f = g ≫ j`. The composite is separated, hence quasi-separated, because an
integral morphism and an open immersion are separated. Quasi-compactness is assumed,
as in the definition of relative normalization in Tag 035H. On each affine open `W`
of `S`, take the integral closure of `Γ(S,W)` in `Γ(V,f⁻¹W)`. The integral-closure
localization theorem (lem-weil-pbc-integral-closure-commutes-localization) says that
these rings localize along principal restrictions; this is precisely the coequifibered
property of `f.normalizationDiagramMap`. The restriction maps form a functor, so all
transition maps obey the cocycle law. The relative scheme-gluing construction
(lem-weil-pbc-glue-schemes) gives `f.normalizationOpenCover`: its chart morphisms are
open immersions, jointly cover the normalization, and have image exactly the inverse
images of the corresponding affine opens of `S`. Their maps to `S` are induced by
inclusion of the base ring into its integral closure. Thus `f.fromNormalization` is
integral, since this is affine-local on the target, as in
lem-weil-pbc-relative-normalization. Finally, normalization commutes with open base
change (035K). After base change along the monomorphism `j`, the input is `g`; since
`g` is integral its normalization is itself (03GP). The composite of these canonical
isomorphisms identifies the restriction with `V` over `U`, including the stated
projection equation. -/
theorem open_relative_normalization_gluing {S U V : Scheme.{u}}
    (j : U ⟶ S) [IsOpenImmersion j] (g : V ⟶ U) [IsIntegralHom g]
    [QuasiCompact (g ≫ j)] :
    ((AffineZariskiSite.toOpensFunctor S).op.whiskerLeft
      (g ≫ j).normalizationDiagramMap).Coequifibered ∧
    (∀ W : S.affineOpens,
      IsOpenImmersion ((g ≫ j).normalizationOpenCover.f W) ∧
      (g ≫ j).normalizationOpenCover.f W ≫ (g ≫ j).fromNormalization =
        Spec.map ((g ≫ j).normalizationDiagramMap.app (.op W.1)) ≫ W.2.fromSpec ∧
      (g ≫ j).fromNormalization ⁻¹ᵁ W.1 =
        ((g ≫ j).normalizationOpenCover.f W).opensRange) ∧
    (∀ x : (g ≫ j).normalization,
      ∃ (W : S.affineOpens) (y : ((g ≫ j).normalizationOpenCover.X W)),
        (g ≫ j).normalizationOpenCover.f W y = x) ∧
    IsIntegralHom (g ≫ j).fromNormalization ∧
    (∃ e : pullback (g ≫ j).fromNormalization j ≅ V,
      e.hom ≫ g = pullback.snd (g ≫ j).fromNormalization j) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
