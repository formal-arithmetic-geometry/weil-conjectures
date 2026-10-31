/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceOpenSubspace
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.AlgebraicGeometry.SpaceNodalLocusBaseChange
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceEtaleOpenImage
import WeilConjectures.AlgebraicGeometry.SpaceOpenChartTests
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests
import WeilConjectures.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceFlatLfpUniversallyOpen
import WeilConjectures.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus

/-! # The largest flat locally finitely presented base open

Source: Stacks Project, Descent on Spaces, Tag 06R2, specialized to flatness and
local finite presentation; Tags 041W and 041T for target descent
(blueprint: lem-sfb-space-maximal-flat-lfp-base-open).

Restrictions use the literal inverse-image subfunctor and its canonical projection.
Thus the base-change equality is an equality of subfunctors, not just point images.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The restriction of a presheaf map over a target subfunctor is flat and locally
of finite presentation on étale scheme charts. For an open subspace `A`, the map
`A.fromPreimage f` is precisely `X ×_Y A → A`.
Source: Stacks Project, Descent on Spaces, Tag 06R2, with Tags 041W and 041T
(blueprint: lem-sfb-space-maximal-flat-lfp-base-open). -/
def IsFlatLfpOverSubfunctor {S : Scheme.{u}}
    {E F : (Over S)ᵒᵖ ⥤ Type u} (f : E ⟶ F) (A : Subfunctor F) : Prop :=
  OnEtaleCharts (@Flat) (A.fromPreimage f) ∧
    OnEtaleCharts (@LocallyOfFinitePresentation) (A.fromPreimage f)

/-- Every algebraic-space morphism has a unique largest flat locally finitely presented
base open, and this open pulls back to the largest such open under any flat locally
finitely presented morphism, without a surjectivity hypothesis.
Source: Stacks Project, Descent on Spaces, Tag 06R2; Tags 041W and 041T
(blueprint: lem-sfb-space-maximal-flat-lfp-base-open).

Proof:
1. Let G be the good open subspaces. By lem-a1-space-etale-open-image they form a
set-indexed family of open point subsets. Their union corresponds to an open W,
containing every member of G.
2. The members of G cover W and their inverse images cover X_W by
lem-a1-space-open-factor-scheme-tests. Open inclusions are representable étale by
lem-a1-space-open-chart-tests. By lem-sfb-stack-chartwise-smooth-etale-calculus,
composition with these inclusions preserves flatness and local finite presentation,
and the source-open-cover criterion gives both properties for X_W → W. This includes
the empty open, whose inverse image and source-open-cover test are empty.
3. Every good V belongs to G, so V ≤ W. Any two good largest opens contain one another;
antisymmetry of subfunctor inclusion proves uniqueness.
4. For flat locally finitely presented g : Y' → Y, let W' be the largest good open
for f' : X ×_Y Y' → Y'. The inverse image H of W is open by
lem-a1-space-open-factor-scheme-tests. Base-change stability from
lem-sfb-stack-chartwise-smooth-etale-calculus makes H good, so H ≤ W'.
5. Restrict g to W'. It remains flat and locally finitely presented by the chartwise
calculus, so its image I is open by lem-sfb-flat-lfp-space-universally-open.
The correspondence of lem-a1-space-etale-open-image gives its open subspace.
By lem-a1-space-open-factor-scheme-tests the restricted map factors through I;
its map q : W' → I is a base change of that restriction and has both properties.
Its point image is all of I, and lem-a1-space-point-open-calculus gives surjectivity
also after scheme base change.
6. The pullback of f_I by q is (f')_W', hence good. The algebraic-space case of
lem-sfb-representable-fppf-etale-open-descent descends flatness and local finite
presentation separately along q. Thus I is good and I ≤ W. The inverse-image and
inclusion criteria of lem-a1-space-open-factor-scheme-tests and
lem-a1-space-point-open-calculus give W' ≤ H. Therefore W' = H as subfunctors.
Sheaf fibre products and their algebraic-space structures throughout are supplied by
lem-trf-space-fibre-products-etale-covers. No finiteness, separation or reducedness
hypothesis on f is used. -/
theorem existsUnique_maximal_flat_lfp_base_open {S : Scheme.{u}}
    (X Y : AlgebraicSpace S) (f : X ⟶ Y) :
    ∃! W : OpenSubspace Y,
      IsFlatLfpOverSubfunctor f.hom.hom W.val ∧
      (∀ V : OpenSubspace Y, IsFlatLfpOverSubfunctor f.hom.hom V.val → V ≤ W) ∧
      ∀ (Y' : AlgebraicSpace S) (g : Y' ⟶ Y),
        MapIsFlat g → MapIsLocallyOfFinitePresentation g →
        ∃ W' : OpenSubspace Y',
          W'.val = W.val.preimage g.hom.hom ∧
          IsFlatLfpOverSubfunctor (Limits.pullback.snd f.hom.hom g.hom.hom) W'.val ∧
          ∀ V : OpenSubspace Y',
            IsFlatLfpOverSubfunctor (Limits.pullback.snd f.hom.hom g.hom.hom) V.val →
              V ≤ W' := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
