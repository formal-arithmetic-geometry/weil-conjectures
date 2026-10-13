/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.KoszulQuotientCoefficientComplex
public import Sheaf.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
import Sheaf.Algebra.Homology.HomComplexToSingle
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Sheaf.AlgebraicGeometry.AffineQuotientRestrictedIso
import Sheaf.AlgebraicGeometry.TildePreservesFiniteLimits

/-! # Underived affine coordinates for the Koszul coefficient square

Source: Stacks Project, Tag 0BQZ, the map between the two Hom complexes. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The underived Hom complexes of the explicit sheafified Koszul complex give
precisely the coefficient reduction on dual Koszul homology.
Source: Stacks Project, Tag 0BQZ, proof of Lemma 48.15.5, the displayed map of
Hom complexes; Tag 01HV, exactness of associated sheafification.
(blueprint: lem-sc-affine-koszul-coefficient-hom-coordinates).

Proof: Identify the restriction of i_*O_Z with the associated sheaf of A/I,
where A = Gamma(Y,U) and I = ker(i)(U), using the affine quotient presentation.
Identify the restricted structure sheaf with the associated sheaf of A. On each
basic open, the adjunction unit is the localized quotient map A_g -> (A/I)_g;
the hypothesis ha therefore identifies the coefficient map under these two
identifications. In Hom degree k the coefficient single complex has only its
zero term. Projection to source degree -k identifies the Hom term with internal
Hom from the sheafification of wedge^k(A^n) to the coefficient sheaf. The finite
wedge basis identifies this with the associated sheaf of the corresponding
module Hom, by localization of the functional's values. The identifications
commute with the coefficient quotient map, since both maps reduce these values.
The source differential acts by precomposition multiplied by -(-1)^k, which is
(-1)^(k+1); the coefficient differentials are zero. Thus the identifications
form a commuting square of integer-indexed complexes. Tilde and chart transport
are exact, so their homology comparison is natural in this square. Finally the
extension from natural to integer cochain degrees has its canonical natural
homology comparison at m. Compose these comparisons to obtain the two stated
isomorphisms and their square. This argument does not use Koszul regularity,
ideal generation by f, or any derived category. For n=0 the complexes have only
degree zero; for m>n their homology vanishes; zero rings and empty charts give
the unique maps of zero objects. -/
theorem affine_koszul_coefficient_hom_coordinates
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    (U : Y.affineOpens) (n m : ℕ) (f : Fin n → Γ(Y, U.1))
    (a : SheafOfModules.unit Y.ringCatSheaf ⟶
      (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
    (ha : a = (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app _ ≫
      (Scheme.Modules.pushforward i).map (Scheme.Modules.pullbackObjUnitIso i).hom) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let R := Scheme.Modules.restrictFunctor U.1.ι
    let S := CochainComplex.singleFunctor U.1.toScheme.Modules 0
    let A := (Γ(Y, U.1) : Type u)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    let E := (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((ExteriorAlgebra.koszulComplex A n f).extend ComplexShape.embeddingDownNat)
    let H := (homComplexFunctor (R := U.1.toScheme.toRingedSpace.sheaf)).obj (op E)
    let D := HomologicalComplex.homologyFunctor U.1.toScheme.Modules
      (ComplexShape.up ℤ) (m : ℤ)
    let P := (ExteriorAlgebra.koszulDualComplex A n f).homology m
    let Q := (ExteriorAlgebra.koszulQuotientDualComplex A (i.ker.ideal U) n f).homology m
    let q := HomologicalComplex.homologyMap
      (ExteriorAlgebra.koszulCoefficientReduction A (i.ker.ideal U) n f) m
    ∃ (eF : D.obj (H.obj (S.obj (R.obj (SheafOfModules.unit Y.ringCatSheaf)))) ≅ T.obj P)
      (eG : D.obj (H.obj (S.obj (R.obj B))) ≅ T.obj Q),
      D.map (H.map (S.map (R.map a))) ≫ eG.hom = eF.hom ≫ T.map q := by sorry

end AlgebraicGeometry
