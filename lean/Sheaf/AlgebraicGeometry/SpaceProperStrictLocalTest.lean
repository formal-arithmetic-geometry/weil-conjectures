/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q69
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Properness detected on strict localizations

Source: Stacks Project, spaces-limits.tex, Tag 08K1, lemma-eventually-proper;
etale-cohomology.tex, Tag 04HX, lemma-describe-etale-local-ring; spaces-descent.tex,
Tag 0422, lemma-descending-property-proper
(blueprint: lem-sfb-space-proper-strict-local-test).

This is the strict-local corollary of eventual properness, rather than the verbatim
statement of Tag 08K1. The source is an algebraic space, with no representability assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical strict-localization morphism, regarded as a map of algebraic spaces.
It is the actual Yoneda image of `Scheme.strictHenselizationStructuralMap`.
Source: Stacks Project, etale-cohomology.tex, Tag 04HX, and the compatible pointed
neighbourhood projections (blueprint: lem-sfb-space-proper-strict-local-test). -/
def strictLocalizationSpaceMap {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barT : Spec (.of Ω) ⟶ T) :
    schemeSpace (Over.mk (Scheme.strictHenselizationStructuralMap barT)) ⟶
      schemeSpace (Over.mk (𝟙 T)) :=
  ObjectProperty.homMk ((Scheme.fppfTopology.over T).yoneda.map
    (Over.homMk (Scheme.strictHenselizationStructuralMap barT)))

/-- A finitely presented algebraic space over a scheme is proper exactly when its
pullback to every strict localization of that scheme is proper.
Source: Stacks Project, spaces-limits.tex, Tag 08K1, lemma-eventually-proper, with
etale-cohomology.tex, Tag 04HX, and spaces-descent.tex, Tag 0422
(blueprint: lem-sfb-space-proper-strict-local-test).

Proof:
1. Proper base change [lem-sfb-space-proper-base-change] makes every strict-local
   pullback proper.
2. Conversely, fix a geometric point. Use the small cofiltered category of affine pointed
   etale neighbourhoods and its strict-localization limit
   [def-weil-pbc-strict-henselization-limit], with the compatible projections over the
   target [def-weil-pbc-strict-henselization-structural-map]. Every transition is affine
   because both schemes are affine, by [pqf-lem-affine-local-target].
3. Apply [lem-weil-pbc-cofiltered-limit-directed-reindex] to obtain a small nonempty
   directed inverse system with the same limit and projections. Choose an initial stage.
4. Base change the given finitely presented morphism to that stage, using
   [lem-sfb-space-flat-proper-fp-locality]. Fibre-product associativity
   [lem-trf-space-fibre-products-etale-covers] identifies its limit pullback with the
   proper strict-local pullback. By [lem-sfb-space-eventually-proper], some neighbourhood
   has proper pullback. Its pointed lift ensures its image contains the original point.
5. Restrict the set of representatives from
   [lem-weil-pbc-affine-etale-essentially-small-cover] to neighbourhoods with proper
   pullback. They cover the target: each point has a geometric point obtained by an
   algebraic closure of its residue field [def-weil-algebraic-closure], and step 4
   supplies a neighbourhood through it. Etale maps [def-weil-etale-morphism] are flat
   and locally finitely presented, so this is an fppf covering [def-pc-fppf-site]. For an
   empty target the empty family is a covering as well.
6. The properness clause of [lem-sfb-space-flat-proper-fp-locality] descends properness
   along this covering, proving the reverse implication. -/
theorem proper_iff_strictLocalization {T : Scheme.{u}} (X : AlgebraicSpace T)
    (f : X ⟶ schemeSpace (Over.mk (𝟙 T)))
    (hqc : MapIsQuasiCompact f.hom.hom)
    (hqs : MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (hlfp : MapIsLocallyOfFinitePresentation f) :
    MapIsProper f ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (barT : Spec (.of Ω) ⟶ T),
        MapIsProper (enlargedFibreProductFst (strictLocalizationSpaceMap barT) f) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
