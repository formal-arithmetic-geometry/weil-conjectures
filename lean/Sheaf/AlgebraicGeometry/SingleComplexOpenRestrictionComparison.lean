/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K4
-/
module

public import Sheaf.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.AlgebraicGeometry.StalkComparisonCoordinateInvariance

/-! # Restriction of the single-complex base-change arrow

Source: Stacks Project, Tag 0DJ9, first paragraph; Tag 08HY, counit description.
(blueprint: lem-pc-single-complex-open-restriction-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The comparison from pullback along an open immersion to exact restriction,
constructed using the pinned tensor-pullback adjunction and left-derived counit.
Source: Stacks Project, Tag 08DW, restriction of derived pullback.
(blueprint: lem-pc-single-complex-open-restriction-comparison). -/
noncomputable def singleComplexOpenPullbackIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (Y : Scheme.{u}) (U : Y.Opens) :
    derivedPullback U.ι ≅ (schemeOpenRestriction Y U).mapDerivedCategory := by
  classical
  let T : SheafOfModules.{u} (moduleRings Y.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback U.ι
  have : T.Additive := (Classical.choose exists_derivedPullbackComposition) U.ι
  let ε := (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) U.ι
  let W := HomotopyCategory.quasiIso
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)
  have : (derivedPullback U.ι).IsLeftDerivedFunctor ε W :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) U.ι
  let η : T ≅ Scheme.Modules.restrictFunctor U.ι :=
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.ι)).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι) ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm
  let θ : schemeOpenRestriction Y U ≅ T := Scheme.Modules.overFunctorEquiv U ≪≫ η.symm
  have : PreservesFiniteLimits (schemeOpenRestriction Y U) :=
    schemeOpenRestriction_preservesFiniteLimits Y U
  have : PreservesFiniteColimits (schemeOpenRestriction Y U) :=
    schemeOpenRestriction_preservesFiniteColimits Y U
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso θ
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso θ
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom W :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  exact Functor.leftDerivedUnique T.mapDerivedCategory (derivedPullback U.ι) ε
    T.mapDerivedCategoryFactorsh.hom W ≪≫ (Functor.mapDerivedCategoryNatIso θ).symm

/-- Restrict the coefficient morphism using the canonical pullback composition
comparisons and the constructed open-pullback comparisons. Both objects and the
morphism are constructed; no existence theorem supplies arbitrary coefficient data.
Source: Stacks Project, Tag 0DJ9, first paragraph.
(blueprint: lem-pc-single-complex-open-restriction-comparison). -/
noncomputable def singleComplexRestrictedCoefficient
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (U : X.Opens) (U' : X'.Opens) (j : U'.toScheme ⟶ U.toScheme)
    (hj : j ≫ U.ι = U'.ι ≫ g') :
    (derivedPullback j).obj ((schemeOpenRestriction X U).mapDerivedCategory.obj K) ⟶
      (schemeOpenRestriction X' U').mapDerivedCategory.obj K' :=
  (derivedPullback j).map ((singleComplexOpenPullbackIso X U).inv.app K) ≫
  ((Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) j U.ι).hom.app K ≫
  eqToHom (congrArg (fun k ↦ (derivedPullback k).obj K) hj) ≫
  ((Classical.choose (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)))) U'.ι g').inv.app K ≫
  (singleComplexOpenPullbackIso X' U').hom.app ((derivedPullback g').obj K) ≫
  (schemeOpenRestriction X' U').mapDerivedCategory.map φ

/-- Restricting a single-complex base-change problem to compatible base opens gives
an arrow isomorphic to the restriction of the original arrow, and preserves its
stalk condition. No affineness, quasi-compactness, or invertibility is assumed.
The two restricted complexes are explicitly given by exact restriction.
Source: Stacks Project, perfect.tex, Tag 0DJ9, first paragraph; cohomology.tex,
Tag 08HY (derived base-change counit), and Tag 08FE (direct-image restriction).
(blueprint: lem-pc-single-complex-open-restriction-comparison).

Proof: Put U = f inverse-image V and U' = f' inverse-image V'. Restrict a K-flat
representative P of K to U and a K-injective representative N of K' to U'.
Restriction preserves K-flatness and K-injectivity. Termwise pullback commutes
with these restrictions, so the map representing phi restricts to a map
representing phi0 from Lj* of K|U to K'|U'. The pullback comparison used here is
induced by the left-derived universal property, rather than an arbitrary functor
isomorphism. Stalks of restricted complexes and local rings on an open agree with
the original stalks and local rings. In these coordinates the tensor-stalk map
is exactly the original map, transported through these identifications. Thus it
is invertible by the original stalk condition. For any other K-flat coordinates
of phi0, compare the two resolutions in the localized homotopy category; tensor
and stalk comparisons are natural and carry quasi-isomorphisms of K-flat models
to isomorphisms. The representing equations identify the maps induced by phi0,
so the same stalk assertion holds for all coordinates.

The source comparison a is the composite of the pullback-open comparison for g
and the direct-image-open comparison for f; the target comparison b is the
direct-image-open comparison for f'. These identify the restricted derived
counit with the counit for f restricted to V. Transpose under the compatible
derived adjunction for f' restricted to V'. Naturality of the counit and the
composition comparisons in the definition of schemeDerivedBaseChangeMap give
the displayed arrow equality. Naturality of the direct-image comparison with
respect to phi supplies its final factor. These computations do not require
quasi-coherence, boundedness, nonempty opens, or affine bases. -/
theorem singleComplexBaseChange_openRestrictionComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (h_stalk : SingleComplexBaseChange.StalkCondition f f' g g' sq K K' φ)
    (V : S.Opens) (V' : S'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (j : (f' ⁻¹ᵁ V').toScheme ⟶ (f ⁻¹ᵁ V).toScheme)
    (hj : j ≫ (f ⁻¹ᵁ V).ι = (f' ⁻¹ᵁ V').ι ≫ g')
    (sq₀ : IsPullback j (f' ∣_ V') (f ∣_ V) (g.resLE V V' hV')) :
    let K₀ := (schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategory.obj K
    let K₀' := (schemeOpenRestriction X' (f' ⁻¹ᵁ V')).mapDerivedCategory.obj K'
    let R := (schemeOpenRestriction S' V').mapDerivedCategory
    let φ₀ := singleComplexRestrictedCoefficient g' K K' φ
      (f ⁻¹ᵁ V) (f' ⁻¹ᵁ V') j hj
    SingleComplexBaseChange.StalkCondition
        (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀ K₀ K₀' φ₀ ∧
      ∃ (a : R.obj ((derivedPullback g).obj ((schemeDerivedDirectImage f).obj K)) ≅
          (derivedPullback (g.resLE V V' hV')).obj
            ((schemeDerivedDirectImage (f ∣_ V)).obj K₀))
        (b : R.obj ((schemeDerivedDirectImage f').obj K') ≅
          (schemeDerivedDirectImage (f' ∣_ V')).obj K₀'),
        R.map (schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
          (schemeDerivedDirectImage f').map φ) =
        a.hom ≫ (schemeDerivedBaseChangeMap
          (f ∣_ V) (f' ∣_ V') (g.resLE V V' hV') j sq₀.w K₀ ≫
            (schemeDerivedDirectImage (f' ∣_ V')).map φ₀) ≫ b.inv := by sorry

end AlgebraicGeometry
