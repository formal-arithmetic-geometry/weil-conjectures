/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F5
-/
module

public import Sheaf.SixFunctors.CartesianCandidateCompositor
public import Sheaf.SixFunctors.CartesianTowerRestriction

/-! # The canonical candidate-compositor site square on a Cartesian tower

Source: Stacks Project, Tags 0F7B and 0F7J
(blueprint: lem-sf-cartesian-candidate-site-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale.AmbientProperOpen
open AlgebraicGeometry.ProEtale.CompactCompositionProjection
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  ProjectionTriangleAssembly.candidateCompositor
/-- The site square for the canonical compositor evaluated on a Cartesian tower.
The chosen origin witness is retained on both boundary maps.
The pro-etale arrow is built solely from canonical candidate comparisons and origin
composition; the etale arrow is the independent normalized tower AE. There is no raw
clopen mate or raw triangle alpha in this statement.
Source: Stacks 0F7J--0F7K, compactification independence and compatible triangle
(blueprint: lem-sf-cartesian-candidate-site-square).

Proof: On the three factor compactifications the etale tower normalization identifies
AE with the bounded-below restriction of the unbounded etale compact-support compositor.
Indeed etale_compositor_normalization inserts the two proper/open inclusion
compatibilities, and the canonical etale candidate comparisons identify its source and
target with the chosen compactifications. Expand originCompositionModel and evaluate
originCompositionAmbient along comparisonUpperStarPlusEtaleOrigin using the fully
faithful preimage equation. Evaluate each towerCandidateComparison by the same preimage
equation: it is the canonical etale candidate change conjugated by compactSupportSiteComparison.
Naturality moves the inner candidate change through the outer site boundary; the common
refinement cocycle identifies the two candidate-change paths. Adjacent site comparisons
cancel. The remaining boundary is B for the output and D for the input, followed by the
canonical D+ inclusion comparisons targetInclusion and sourceInclusion. This proves the
square on the comparison image. Paste the naturality squares for the inner candidate
comparison, outer candidate comparison, originCompositionAmbient, and final comparison
along the specified isomorphism e. This moves its source-functor image to the input
boundary and its output-functor image to the output boundary, giving the displayed
square for K. Only the proper factors and the individual factored maps are separated;
no separated structure map or coefficient-ring presentation is needed. Empty opens give
the same zero-object square, and identity factors give the unit normalizations. -/
theorem cartesianCandidateSiteSquare
    (F : WeilConjectures.FiniteFieldDatum.{u})
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X V W Y B Z : Spaces F}
    (j : X ⟶ V) (b : V ⟶ W) (q : V ⟶ Y) (p : W ⟶ B) (i : Y ⟶ B) (s : B ⟶ Z)
    [IsOpenImmersion ((geometry F).map j)] [IsOpenImmersion ((geometry F).map b)]
    [IsOpenImmersion ((geometry F).map i)] [QuasiCompact ((geometry F).map b)]
    [QuasiCompact ((geometry F).map i)]
    [IsProper ((geometry F).map q)] [IsProper ((geometry F).map p)]
    [IsProper ((geometry F).map s)]
    (hb : b ≫ p = q ≫ i)
    (sq : IsPullback b.hom.left q.hom.left p.hom.left i.hom.left)
    (E : FiniteSiteTower.DE A X.obj.left)
    (K : (DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A)
      X.obj.left).FullSubcategory)
    (e : (comparisonUpperStarPlusEtaleOrigin (ModuleCat.{u + 1} A) X.obj.left).obj E ≅ K) :
    letI : IsOpenImmersion j.hom.left := ‹IsOpenImmersion ((geometry F).map j)›
    letI : IsOpenImmersion b.hom.left := ‹IsOpenImmersion ((geometry F).map b)›
    letI : IsOpenImmersion i.hom.left := ‹IsOpenImmersion ((geometry F).map i)›
    letI : QuasiCompact b.hom.left := ‹QuasiCompact ((geometry F).map b)›
    letI : QuasiCompact i.hom.left := ‹QuasiCompact ((geometry F).map i)›
    letI : IsProper q.hom.left := ‹IsProper ((geometry F).map q)›
    letI : IsProper p.hom.left := ‹IsProper ((geometry F).map p)›
    letI : IsProper s.hom.left := ‹IsProper ((geometry F).map s)›
    letI : IsOpenImmersion (j ≫ b).hom.left :=
      mappedCompositeOpen (geo := geometry F) j b
    letI : IsProper (p ≫ s).hom.left := mappedCompositeProper (geo := geometry F) p s
    let cf := WeilConjectures.sixFunctorFactorCompactification j q
      ‹IsOpenImmersion ((geometry F).map j)› ‹IsProper ((geometry F).map q)›
      (j ≫ q) rfl
    let cg := WeilConjectures.sixFunctorFactorCompactification i s
      ‹IsOpenImmersion ((geometry F).map i)› ‹IsProper ((geometry F).map s)›
      (i ≫ s) rfl
    let cfg := WeilConjectures.sixFunctorFactorCompactification (j ≫ b) (p ≫ s)
      (mappedCompositeOpen (geo := geometry F) j b)
      (mappedCompositeProper (geo := geometry F) p s) ((j ≫ q) ≫ (i ≫ s)) (by
        simp only [Category.assoc]
        rw [← Category.assoc q i s, ← hb]
        simp only [Category.assoc])
    let C := ProjectionTriangleAssembly.candidateCompositor A cf cg cfg K
    DerivedCategory.Plus.ι.map
        ((FiniteSiteTower.N A Z.obj.left).map
          (FiniteSiteTower.AE A j.hom.left b.hom.left p.hom.left s.hom.left i.hom.left
            q.hom.left sq E)) ≫
      DerivedCategory.Plus.ι.map
        (FiniteSiteTower.B A (j ≫ b).hom.left (p ≫ s).hom.left E) ≫
      (CartesianTower.targetInclusion A (j ≫ b).hom.left (p ≫ s).hom.left
        ((FiniteSiteTower.N A X.obj.left).obj E)).hom ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cfg).map e.hom.hom =
    DerivedCategory.Plus.ι.map
        (FiniteSiteTower.D A j.hom.left s.hom.left i.hom.left q.hom.left E) ≫
      (CartesianTower.sourceInclusion A j.hom.left q.hom.left i.hom.left s.hom.left
        ((FiniteSiteTower.N A X.obj.left).obj E)).hom ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cg).map
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) cf).map
          e.hom.hom) ≫ C := by sorry

end AlgebraicGeometry.ProEtale
