/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W5
-/
module

public import Sheaf.SmoothPurity.TensorMateInverseProjection
public import Sheaf.AlgebraicGeometry.EtaleSumExtensionTensor
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-! # The normalized projection square for etale precomposition

Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3, expanded in step 3 of
lem-asd-tensor-mate-etale-precomp.
-/

@[expose] public section

set_option autoImplicit false

universe v

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Etale

/-- The coefficient-first inverse projections intertwine the graph-normalized etale
compact-support compositor and the sum-extension projection.
Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3; Stacks Tag 0GL5;
step 3 of lem-asd-tensor-mate-etale-precomp
(blueprint: lem-asd-etale-precomp-projection).

Proof: Fix the chosen compactifications of f and h = u ≫ f. Their proper/open tower
uses the induced compactification of u. Apply compactSupportProjectionMap_comp and
compactSupportProjectionMap_comparison to identify its projection with the projection
for h. The graph-normalized comparison of etaleSupportMapCompatibility identifies
the compact-support projection for u with the sum-extension projection: both inverse
comparisons extend a sheet section by zero from its graph. Uniqueness follows by
embedding the sheaf comparison into direct image and then descending its prescribed
map on homotopy representatives. Thus this comparison equals N.comparison at the
induced compactification. Transport the tower equation along that comparison.
Conjugate by the signed tensor symmetries and the exact-pullback comparisons, then
invert the three projection maps. Naturality moves the compositor past these changes
of presentation; the pullback-composition comparison supplies the displayed map on
the first tensor factor. The result is precisely the equation below, for arbitrary
unbounded K and M. The argument uses no exceptional right adjoint or dualizing object.
-/
theorem etalePrecompProjection
    (A : Type (v + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {U X S : Scheme.{v}} (u : U ⟶ X) (f : X ⟶ S)
    [Etale u] [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian S]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated (u ≫ f)] [LocallyOfFiniteType (u ≫ f)] [QuasiCompact (u ≫ f)]
    [HasCompactification f] [HasCompactification (u ≫ f)]
    (K : DerivedCategoryModule A S) (M : DerivedCategoryModule A U) :
    let c := etaleAmbientLeftComparison A N u f
      (HasCompactification.compactification f)
      (HasCompactification.compactification (u ≫ f))
    R(f)_![ModuleCat A].map
        (etaleSumExtensionTensorComparison A u
          ((f)^*[ModuleCat A].mapDerivedCategory.obj K) M) ≫
        (tensorMateInverseProjection A f K).app
          ((etaleLowerShriek (ModuleCat A) u inferInstance).mapDerivedCategory.obj M) ≫
        ((derivedTensor (ModuleCat A) S).obj K).map (c.hom.app M) =
      c.hom.app (((derivedTensor (ModuleCat A) U).obj
          ((u)^*[ModuleCat A].mapDerivedCategory.obj
            ((f)^*[ModuleCat A].mapDerivedCategory.obj K))).obj M) ≫
        R(u ≫ f)_![ModuleCat A].map
          (((derivedTensor (ModuleCat A) U).map
            ((unboundedEtaleUpperStarCompIso A u f).inv.app K)).app M) ≫
        (tensorMateInverseProjection A (u ≫ f) K).app M := by sorry

end AlgebraicGeometry.Etale
