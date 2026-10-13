/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.RingTheory.KoszulQuotientCoefficientComplex
public import Sheaf.RingTheory.KoszulRegularSequence
public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import Sheaf.RingTheory.KoszulProjectiveResolution
import Sheaf.AlgebraicGeometry.AffineQuotientResolutionSheafification
import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.Algebra.Homology.DerivedHomFiniteFreeModel
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Sheaf.AlgebraicGeometry.TildePreservesFiniteLimits
/-! # Affine sheaf model of the Koszul Ext coefficient morphism

Source: Stacks Project, Tag 0BQZ, affine computation of regular immersion Ext. -/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

namespace AlgebraicGeometry

/-- On the affine chart, the two Ext sheaves and their coefficient map are the
sheafifications of the dual Koszul cohomology modules and their reduction map.
Source: Stacks Project, Tag 0BQZ, lemma-regular-immersion-ext.
(blueprint: new-k1-koszul-ext-coefficient-affine-model).

Proof: The closed immersion on the chart is the quotient spectrum for the kernel
ideal. Augment the Koszul complex by its degree-zero quotient map. Koszul
regularity makes this a resolution, and its exterior terms are finite free and
zero above n. Sheafification on the affine chart is exact, so it resolves the
restricted pushforward of the structure sheaf. Extend the chain complex to
nonpositive integer cochain degrees. Apply the bounded finite free internal Hom
comparison with coefficients O and the quotient sheaf. Use a common K-injective
comparison to make both identifications natural in the coefficient variable.
The supplied equality ha identifies the coefficient map with the quotient map,
which acts on Hom cochains by reduction of values. In degree k the differential
is (-1)^(k+1) times precomposition with the Koszul boundary for both coefficients,
so these are precisely the two recorded natural-number dual complexes after
extension to integer degrees. The degree-m homology comparisons for this
extension commute with the reduction map. Tilde preserves finite limits by
tilde_preserves_finite_limits and colimits by its adjunction, hence is exact.
Restriction along the chart is an exact equivalence. They commute with homology
and its maps, producing the two sheaf isomorphisms and their square.
Work through representatives in the supplied derived universe, so no derived
category on the chart in a different universe is compared. For n=0 the quotient
ideal is zero and the resolution is the degree-zero ring; for m>n both Hom
cohomology modules vanish. These cases require no additional hypotheses. -/
theorem koszulExtCoefficient_affine_model
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n m : ℕ)
    (U : Y.affineOpens) (f : Fin n → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (hreg : RingTheory.Sequence.IsKoszulRegular f)
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    (ha : a = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
      (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackObjUnitIso i).hom) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let F := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℤ)).obj
        (H.obj (op (S.obj B), S.obj (SheafOfModules.unit Y.ringCatSheaf)))
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    let c : F ⟶ G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℤ)).map
        (H.map (𝟙 (op (S.obj B)), S.map a))
    let A := (Γ(Y, U.1) : Type u)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let P := (ExteriorAlgebra.koszulDualComplex A n f).homology m
    let Q := (ExteriorAlgebra.koszulQuotientDualComplex A (i.ker.ideal U) n f).homology m
    let q := HomologicalComplex.homologyMap
      (ExteriorAlgebra.koszulCoefficientReduction A (i.ker.ideal U) n f) m
    ∃ (eF : (Scheme.Modules.restrictFunctor U.1.ι).obj F ≅ T.obj P)
      (eG : (Scheme.Modules.restrictFunctor U.1.ι).obj G ≅ T.obj Q),
      (Scheme.Modules.restrictFunctor U.1.ι).map c ≫ eG.hom = eF.hom ≫ T.map q := by sorry

end AlgebraicGeometry
