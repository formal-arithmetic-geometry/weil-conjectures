/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Pointwise conjugacy for termwise affine spectrum representatives

Source: Stacks Project, Tag 0DJ8, equation-bc and affine reduction;
Tag 0098, stalks of pullback, and Tag 0D5S, pullback composition.
(blueprint: lem-pc-affine-spectrum-stalk-conjugacy).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

/-- Pointwise comparison arrows are conjugate when the spectrum representatives
are the termwise pullbacks. This does not construct such representatives, nor
assert a stalk condition for either square.

Proof: write z = X'.isoSpec.inv z0. Naturality of isoSpec and stalkMap_comp
identify the four local rings of the original square at z with those of the
spectrum square at z0. These ring isomorphisms intertwine f, f', g and g' on
stalks, including the stalkCongr used in rightAlgebra. The tensorMap restriction
equations then identify the maps from A tensor_R B to C by tensor universality.
The pullback-stalk isomorphism of Tag 0098 and the assumed equalities hP and hN
identify the transported stalk complexes with scalar transport of c.P and c.N.
Ring isomorphisms give exact scalar equivalences. Applying them to the universal
left-derived R-to-B extension and using uniqueness of its counit gives the
isomorphism on derived tensor cohomology. Naturality for multiplication by each
a in A identifies the full A tensor_R B action, not just its B restriction.
Extending to C gives an isomorphism of the sources of stalkComparison.
Exactness of stalks gives an isomorphism of the target homology objects.
If the chosen representative isomorphisms d.e and d.e' differ from those induced
by c.e and c.e', compose with their ratios in the derived categories; the same
source transport and exact target cohomology give corresponding isomorphisms.
The represents equations for c and d identify their localized coefficient maps
with phi and its specified affineSpectrumDerivedMorphism. The universal
leftDerivedLift equation defining affineSpectrumDerivedPullbackIso and the two
model equations comparison_eq and localized_eq identify the intervening maps.
Naturality of the tensor-stalk isomorphism therefore makes the square of source
and target isomorphisms commute. Forget the scalar actions and package this
square with Arrow.isoMk. No comparison is assumed invertible; both may be zero
or noninvertible. A point z0 excludes an empty X', while zero rings and arbitrary
unbounded complexes are allowed.
Source: Stacks Project, Tag 0DJ8, affine reduction and equation-bc;
Tag 0098, tensor-pullback stalk formula; Tag 0D5S, composition of derived pullback.
(blueprint: lem-pc-affine-spectrum-stalk-conjugacy). -/
theorem nonempty_affineSpectrum_stalkComparison_arrow_iso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    [IsAffine X] [IsAffine X'] [IsAffine S] [IsAffine S']
    (sq0 : IsPullback (Spec.map g'.appTop) (Spec.map f'.appTop)
      (Spec.map f.appTop) (Spec.map g.appTop))
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (c : Coordinates g' K K' φ)
    (d : Coordinates (Spec.map g'.appTop)
      (affineSpectrumDerivedObject X K) (affineSpectrumDerivedObject X' K')
      (affineSpectrumDerivedMorphism g' K K' φ))
    (hP : d.P = ((Scheme.Modules.tensorPullback X.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj c.P)
    (hN : d.N = ((Scheme.Modules.tensorPullback X'.isoSpec.inv).mapHomologicalComplex
      (.up ℤ)).obj c.N)
    (z0 : Spec Γ(X', ⊤)) (i : ℤ) :
    Nonempty
      (Arrow.mk ((forget₂ (ModuleCat.{u} (X'.presheaf.stalk (X'.isoSpec.inv z0)))
          AddCommGrpCat.{u}).map
            (stalkComparison f f' g g' sq c (X'.isoSpec.inv z0) i)) ≅
        Arrow.mk ((forget₂ (ModuleCat.{u} ((Spec Γ(X', ⊤)).presheaf.stalk z0))
          AddCommGrpCat.{u}).map
            (stalkComparison (Spec.map f.appTop) (Spec.map f'.appTop)
              (Spec.map g.appTop) (Spec.map g'.appTop) sq0 d z0 i))) := by sorry

end AlgebraicGeometry.SingleComplexBaseChange
