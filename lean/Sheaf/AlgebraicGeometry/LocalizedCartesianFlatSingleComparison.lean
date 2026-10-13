/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Sheaf.AlgebraicGeometry.LocalizedMixedDerivedPullback

/-! # Flat single base change on a cartesian source
Source: Stacks Project, Tag 0A1D (lemma-base-change-tensor).
(blueprint: lem-pc-localized-cartesian-flat-single-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u wX wS wW wY
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products

/-- Flat single base change on a cartesian source.
Source: Stacks Project, Tag 0A1D (lemma-base-change-tensor).
Proof: in the standard localization apply relatively flat tensor base change to
p with the perfect tensor unit O_Y[0] and the single complex M[0]. This complex
is bounded above, quasi-coherent termwise and flat over p; its other terms are zero.
The tensor unit and its derived pullback unit comparisons remove the perfect factor.
Ordinary pullback of the single complex is the single complex of q^*M. Identify Z
with the canonical pullback of p and g by the unique projection-preserving
isomorphism supplied by sq, and transport its direct image through that exact scheme
isomorphism. This gives Rr_*(q^*M)[0] isomorphic to Lg^*Rp_*M[0]. Compare the supplied
localizations on Y and W with standard ones using localization uniqueness. A common
K-injective resolution of M[0] identifies the direct images under that equivalence;
the universal derived pullback comparison is compatible with it. Apply the exact
inverse overEquiv V. The resulting composite is precisely
localizedMixedDerivedPullback. No ambient f, coefficient F, or restriction from S
is used, and empty schemes and the zero module obey the same comparisons.
(blueprint: lem-pc-localized-cartesian-flat-single-comparison). -/
theorem localized_cartesian_flat_single_comparison
    {S T Y Z : Scheme.{u}} (U : S.Opens) (V : U.toScheme.Opens) (W : T.Opens)
    [HasDerivedCategory.{wS}
      (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    [HasDerivedCategory.{wW}
      (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (p : Y ⟶ W.toScheme) [QuasiCompact p] [QuasiSeparated p]
    (M : Y.Modules) [M.IsQuasicoherent] (hM : M.IsFlatOver p)
    (g : V.toScheme ⟶ W.toScheme) (q : Z ⟶ Y) (r : Z ⟶ V.toScheme)
    (sq : IsPullback q r p g) :
  let dV := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
  letI := dV
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
  Nonempty ((@Functor.mapDerivedCategory _ _ _ dV _ _ _ _
      (Scheme.Modules.overEquiv V).inverse _ _ _).obj
      ((schemeDerivedDirectImage r).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj
          (Scheme.Modules.tensorPullbackObj q M))) ≅
    (localizedMixedDerivedPullback U V W g).obj
      ((schemeDerivedDirectImage p).obj ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj M))) := by
  sorry

end AlgebraicGeometry
