/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
public import Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf
public import Sheaf.AlgebraicGeometry.RelativeDifferentialsPullbackMap
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteExteriorPower
public import Sheaf.AlgebraicGeometry.ExteriorSheafComparison

import WeilConjectures.AlgebraicGeometry.SmoothRelativeDifferentialsFiniteLocallyFree
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkIsoNeighborhood
import Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties
import Sheaf.AlgebraicGeometry.SchemeZariskiEtaleQuasiCoherentEquivalence
import WeilConjectures.AlgebraicGeometry.Thickening
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! # The cotangent criterion for etaleness between smooth schemes

Source: Bosch--Luetkebohmert--Raynaud, Neron Models, Section 2.2, Corollary 10,
printed page 41, with Proposition 8; determinant reformulation by local square matrices
(blueprint: lem-sfb-smooth-cotangent-etale-criterion).

The differential is the existing canonical pullback map, followed by transport along
its triangle over the base. Its determinant uses the existing sectionwise exterior maps
and the canonical comparison of the two exterior sheaf constructions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- The exterior power of the canonical differential of a morphism over a base.
Source: BLR, Neron Models, 2.2, Corollary 10, with the exterior-power construction;
Stacks, Tag 01UV, functoriality of differentials
(blueprint: lem-sfb-smooth-cotangent-etale-criterion).

The two comparison maps are induced by the identity on sectionwise wedges. The middle
map is the sheafification of the actual exterior linear maps of the differential.
Thus this is the map sending a wedge of pulled-back differentials to the wedge of
its images, including the empty wedge; no morphism is chosen arbitrarily. -/
noncomputable def smoothCotangentDeterminantMap {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : X ⟶ Y) (w : h ≫ g = f) (n : ℕ) :
    Modules.exteriorSheaf ((Modules.tensorPullback h).obj g.relativeDifferentials) n ⟶
      Modules.exteriorSheaf f.relativeDifferentials n :=
  (Modules.exteriorSheafIsoExteriorPower
      ((Modules.tensorPullback h).obj g.relativeDifferentials) n).hom ≫
    SheafOfModules.siteExteriorHom (B := X.sheaf)
      (g.relativeDifferentialsPullbackMap h ≫ ((h ≫ g).relativeDifferentialsCongr w).hom) n ≫
    (Modules.exteriorSheafIsoExteriorPower f.relativeDifferentials n).inv

/-- Etaleness between smooth schemes is detected by the relative cotangent map,
pointwise, globally, and by its determinant in equal finite rank.
Source: BLR, Neron Models, 2.2, Corollary 10, printed page 41, with Proposition 8;
Stacks, Tags 04BX, 02G1, 02H5, 02H6, 02HM and 02GJ
(blueprint: lem-sfb-smooth-cotangent-etale-criterion).

Proof:
1. On an etale source neighbourhood, etale localization of relative differentials
   (lem-sfb-etale-localization-relative-differentials) makes the canonical map invertible.
   Open immersions are etale (lem-weil-pbc-open-immersion-etale), so restriction identifies
   this map with the original differential on that neighbourhood and hence at the stalk.
2. Conversely, smooth differentials are finite locally free
   (lem-ag-smooth-relative-differentials-finite-locally-free), as is their tensor pullback:
   pull back local bases. An invertible stalk map therefore extends to an invertible map
   on an open neighbourhood (lem-sc-finite-locally-free-stalk-iso-neighborhood).
   Smoothness persists on this open (lem-sfb-scheme-etale-source-target-properties).
   The map to Y is locally finitely presented by lem-a1-map-over-base-finite-presentation.
3. For square-zero lifts, lem-sfb-space-square-zero-lift-linearization identifies
   differences of lifts with derivations. The scheme etale/Zariski differential comparison
   (lem-sfb-scheme-etale-relative-differentials-comparison) and the quasi-coherent equivalence
   (lem-trf-scheme-zariski-etale-quasi-coherent-equivalence) identify postcomposition with h
   with precomposition by the pulled-back differential: both send db to D(h-sharp b).
4. Given a first order affine thickening (def-sbc-first-order-thickening), smoothness
   supplies a lift over S. Correct it by the unique derivation obtained using the inverse
   differential, to obtain a unique lift over Y. Thus
   lem-sfb-lfp-unique-infinitesimal-lifts-etale makes h etale on this neighbourhood.
5. The neighbourhoods cover X. Source locality (lem-weil-pbc-etale-local-on-source)
   gives the global criterion; stalk inverses also glue uniquely. The empty source is
   covered by the empty family and causes no exception.
6. In equal-rank local frames the exterior map is multiplication by the matrix
   determinant. It is invertible exactly when that determinant is a unit; the adjugate
   identities (lem-weil-pbc-matrix-adjugate-identity) then invert the original matrix.
   Conversely an inverse induces an exterior inverse. These local inverses glue.
   In degree zero, both normalized exterior identifications send the empty wedge to 1,
   and the induced map preserves the empty wedge, so its conjugate is the identity.
-/
theorem smooth_cotangent_etale_criterion {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [Smooth f] [Smooth g]
    (h : X ⟶ Y) (w : h ≫ g = f) :
    (∀ x : X, (∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ h)) ↔
      IsIso ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).map
        (g.relativeDifferentialsPullbackMap h ≫ ((h ≫ g).relativeDifferentialsCongr w).hom))) ∧
    (Etale h ↔ IsIso
      (g.relativeDifferentialsPullbackMap h ≫ ((h ≫ g).relativeDifferentialsCongr w).hom)) ∧
    (∀ d : ℕ, f.relativeDifferentials.IsFiniteLocallyFreeOfRank d →
      g.relativeDifferentials.IsFiniteLocallyFreeOfRank d →
      (Etale h ↔ IsIso (smoothCotangentDeterminantMap f g h w d))) ∧
    ((Classical.choose (Modules.exteriorSheaf_zero_iso
        ((Modules.tensorPullback h).obj g.relativeDifferentials))).inv ≫
      smoothCotangentDeterminantMap f g h w 0 ≫
      (Classical.choose (Modules.exteriorSheaf_zero_iso f.relativeDifferentials)).hom =
        𝟙 (SheafOfModules.unit X.ringCatSheaf)) := by
  sorry

end AlgebraicGeometry.Scheme.Hom
