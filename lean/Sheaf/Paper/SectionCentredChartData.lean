/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Paper.SectionLocalComparisonData
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace

/-! # Affine centred charts and their actual extended-Rees comparison maps

Source: main-20261015, sec-smooth-purity/sk-thm-dnc, opening and Local construction
(blueprint: def-trf-section-centred-chart-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.SectionLocalDualizingComparisons
open SectionComparisonArrows

/-- An affine centred coordinate neighbourhood, with its actual open inclusion in V_T.
The Cartesian centre condition is scheme-theoretic, not an equality of underlying sets.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-centred-chart-data). -/
structure Chart {V S : Scheme.{u}} (d : ℕ) (g : V ⟶ S) (s : S ⟶ V)
    (hs : s ≫ g = 𝟙 S) where
  T : Scheme.{u}
  b : T ⟶ S
  affineT : IsAffine T
  openB : IsOpenImmersion b
  U : Scheme.{u}
  affineU : IsAffine U
  j : U ⟶ pullback g b
  openJ : IsOpenImmersion j
  r : T ⟶ U
  closedR : IsClosedImmersion r
  section_eq : r ≫ j = Scheme.Hom.baseChangeSection g s hs b
  e : U ⟶ AffineSpace (ULift.{u} (Fin d)) T
  etaleE : Etale e
  separatedE : IsSeparated e
  overE : e ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = j ≫ pullback.snd g b
  centres : IsPullback r (𝟙 T) e (AffineSpace.zeroSection (ULift.{u} (Fin d)) T)

attribute [instance] Chart.affineT Chart.openB Chart.affineU Chart.openJ
  Chart.closedR Chart.etaleE Chart.separatedE

/-- The base-changed closed section is closed.
Source: sk-thm-dnc, base restriction
(blueprint: def-trf-section-centred-chart-data).
Proof: the section square is Cartesian, so closedness is stable under base change. -/
theorem baseSectionClosed {V S T : Scheme.{u}} (g : V ⟶ S) (s : S ⟶ V)
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) (b : T ⟶ S) :
    IsClosedImmersion (Scheme.Hom.baseChangeSection g s hs b) := by
  sorry

/-- A map of the specified centred pairs carries the centre ideal into the new ideal.
Source: sk-thm-dnc, Local construction, Rees maps
(blueprint: def-trf-section-centred-chart-data).
Proof: a section of the kernel restricts to zero on the centre. The commuting square
makes its image restrict to zero on the new centre. Apply Ideal.map_le_iff_le_comap. -/
theorem pairIdeal {U X T : Scheme.{u}} (v : U ⟶ X) (r : T ⟶ X) (r' : T ⟶ U)
    [IsClosedImmersion r] [IsClosedImmersion r'] (hr : r' ≫ v = r) :
    ∀ ⦃P : U.AffineZariskiSite⦄ ⦃Q : X.AffineZariskiSite⦄ (h : P.1 ≤ v ⁻¹ᵁ Q.1),
      (r.ker.siteIdeal Q).map (v.appLE Q.1 P.1 h).hom ≤ r'.ker.siteIdeal P := by
  sorry

/-- The actual extended-Rees map on the open chart of the base-changed pair.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-centred-chart-data). -/
@[irreducible]
def Chart.reesOpen {V S : Scheme.{u}} {d : ℕ} {g : V ⟶ S} {s : S ⟶ V}
    [IsClosedImmersion s] {hs : s ≫ g = 𝟙 S} (c : Chart d g s hs) :
    c.r.ker.deformationSpace ⟶ (Scheme.Hom.baseChangeSection g s hs c.b).ker.deformationSpace :=
  letI := baseSectionClosed g s hs c.b
  Scheme.IdealSheafData.deformationSpaceMap c.j
    (Scheme.Hom.baseChangeSection g s hs c.b).ker c.r.ker
      (pairIdeal c.j (Scheme.Hom.baseChangeSection g s hs c.b) c.r c.section_eq)

/-- The canonical Rees map for the open change of base, fixing t and every b/t.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-centred-chart-data). -/
@[irreducible]
def Chart.reesBase {V S : Scheme.{u}} {d : ℕ} {g : V ⟶ S} {s : S ⟶ V}
    [IsClosedImmersion s] {hs : s ≫ g = 𝟙 S} (c : Chart d g s hs) :
    (Scheme.Hom.baseChangeSection g s hs c.b).ker.deformationSpace ⟶ s.ker.deformationSpace :=
  letI := baseSectionClosed g s hs c.b
  Scheme.IdealSheafData.deformationSpaceMap (pullback.fst g c.b) s.ker
    (Scheme.Hom.baseChangeSection g s hs c.b).ker
      (Scheme.Hom.map_siteIdeal_ker_le_baseChangeSection g s hs c.b)

/-- The deformed coordinate map, obtained from e on extended Rees algebras and x_j=t*u_j.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-centred-chart-data). -/
@[irreducible]
def Chart.reesCoordinates {V S : Scheme.{u}} {d : ℕ} {g : V ⟶ S} {s : S ⟶ V}
    {hs : s ≫ g = 𝟙 S} (c : Chart d g s hs) :
    c.r.ker.deformationSpace ⟶
      AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) c.T) :=
  Scheme.IdealSheafData.deformationSpaceMap c.e
    (AffineSpace.zeroSection (ULift.{u} (Fin d)) c.T).ker c.r.ker
      (pairIdeal c.e (AffineSpace.zeroSection (ULift.{u} (Fin d)) c.T) c.r
        (c.centres.w.trans (Category.id_comp _))) ≫
    Scheme.Hom.deformationSpaceToAffineSpace (ULift.{u} (Fin d)) c.T

/-- Proofs of the geometric properties needed to evaluate the chart comparisons.
Every scheme and map is fixed by the chart and the Rees construction; there is no
arbitrary map or auxiliary dualizing object in this proposition.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-centred-chart-data). -/
class Chart.Geometry {V S : Scheme.{u}} {d : ℕ} {g : V ⟶ S} {s : S ⟶ V}
    [IsClosedImmersion s] {hs : s ≫ g = 𝟙 S} (c : Chart d g s hs) : Prop where
  noethT : IsNoetherian c.T
  noethBase : IsNoetherian (pullback g c.b)
  noethU : IsNoetherian c.U
  noethLine : IsNoetherian (AffineSpace (ULift.{u} (Fin 1)) c.T)
  noethDBase : IsNoetherian (Scheme.Hom.baseChangeSection g s hs c.b).ker.deformationSpace
  noethDU : IsNoetherian c.r.ker.deformationSpace
  compactU : HasCompactification (c.j ≫ pullback.snd g c.b)
  compactDBase : HasCompactification (Scheme.Hom.deformationSpaceProj (pullback.snd g c.b)
    (Scheme.Hom.baseChangeSection g s hs c.b))
  qcDBase : QuasiCompact (Scheme.Hom.deformationSpaceProj (pullback.snd g c.b)
    (Scheme.Hom.baseChangeSection g s hs c.b))
  compactDU : HasCompactification (Scheme.Hom.deformationSpaceProj
    (c.j ≫ pullback.snd g c.b) c.r)
  lftE : LocallyOfFiniteType c.e
  qcE : QuasiCompact c.e
  etaleDOpen : Etale c.reesOpen
  separatedDOpen : IsSeparated c.reesOpen
  lftDOpen : LocallyOfFiniteType c.reesOpen
  qcDOpen : QuasiCompact c.reesOpen
  etaleDCoordinates : Etale c.reesCoordinates
  separatedDCoordinates : IsSeparated c.reesCoordinates
  lftDCoordinates : LocallyOfFiniteType c.reesCoordinates
  qcDCoordinates : QuasiCompact c.reesCoordinates
  baseSquare : IsPullback c.reesBase
    (Scheme.Hom.deformationSpaceProj (pullback.snd g c.b)
      (Scheme.Hom.baseChangeSection g s hs c.b))
    (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.map (ULift.{u} (Fin 1)) c.b)
  baseSections : (Scheme.Hom.baseChangeSection g s hs c.b).deformationSpaceSection ≫
    c.reesBase = AffineSpace.map (ULift.{u} (Fin 1)) c.b ≫ s.deformationSpaceSection
  openOver : c.reesOpen ≫ Scheme.Hom.deformationSpaceProj (pullback.snd g c.b)
    (Scheme.Hom.baseChangeSection g s hs c.b) =
      Scheme.Hom.deformationSpaceProj (c.j ≫ pullback.snd g c.b) c.r
  openSections : c.r.deformationSpaceSection ≫ c.reesOpen =
    (Scheme.Hom.baseChangeSection g s hs c.b).deformationSpaceSection
  coordinatesOver : c.reesCoordinates ≫
    (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) c.T) ↘ _) =
      Scheme.Hom.deformationSpaceProj (c.j ≫ pullback.snd g c.b) c.r

attribute [instance] Chart.Geometry.noethT Chart.Geometry.noethBase Chart.Geometry.noethU
  Chart.Geometry.noethLine Chart.Geometry.noethDBase Chart.Geometry.noethDU
  Chart.Geometry.compactU Chart.Geometry.compactDBase Chart.Geometry.qcDBase
  Chart.Geometry.compactDU Chart.Geometry.lftE Chart.Geometry.qcE
  Chart.Geometry.etaleDOpen Chart.Geometry.separatedDOpen Chart.Geometry.lftDOpen
  Chart.Geometry.qcDOpen Chart.Geometry.etaleDCoordinates
  Chart.Geometry.separatedDCoordinates Chart.Geometry.lftDCoordinates Chart.Geometry.qcDCoordinates

/-- All locality domains for an affine centred chart are consequences of its geometry.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-centred-chart-data).
Proof: finite type over Noetherian bases gives all Noetherian schemes. The Cartesian
centres identify the new ideals with the pulled-back ideals. Flatness of the etale maps
identifies their Rees algebras with tensor products, fixing t and b/t. For the standard
pair the algebra is R[t,u], x_j=t*u_j, by independence of Laurent monomials. Thus both
Rees chart maps are separated etale of finite type. Open base change gives the displayed
Cartesian square. The augmentations give both section equations and the structure maps.
Nagata over each affine Noetherian base supplies the compactifications. -/
theorem chartGeometry {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] [IsSeparated g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S) (c : Chart d g s hs) :
    c.Geometry := by
  sorry

/-- The specified source comparison on an affine centred neighbourhood.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-centred-chart-data). -/
@[irreducible]
def localSourceMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) (c : Chart d g s hs)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) c.T ↘ c.T) ⊣ affineRight A N hA c.T d) :
    (upperStar (ModuleCat.{u + 1} A) c.b).leftDerivedFunctor.obj (sectionInvariant A g s) ⟶
      tateObject A N hA c.T d :=
  letI := chartGeometry d g s hs c
  sectionMap A g (pullback.snd g c.b) c.b (pullback.fst g c.b)
      (IsPullback.of_hasPullback g c.b) s (Scheme.Hom.baseChangeSection g s hs c.b)
      (Scheme.Hom.baseChangeSection_fst g s hs c.b) ≫
    (sectionLocality A c.j (pullback.snd g c.b) (c.j ≫ pullback.snd g c.b) rfl
      (Scheme.Hom.baseChangeSection g s hs c.b) c.r c.section_eq).hom ≫
    chartMap A N hN hA (invertibleOnSource N c.b hS) d (c.j ≫ pullback.snd g c.b)
      c.r c.e c.overE adj

/-- The specified family comparison on the actual deformation of that same neighbourhood.
Source: sk-thm-dnc, Local construction
(blueprint: def-trf-section-centred-chart-data). -/
@[irreducible]
def localFamilyMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {V S : Scheme.{u}} [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ) (g : V ⟶ S) [SmoothOfRelativeDimension d g] [IsSeparated g]
    [QuasiCompact g] (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] (c : Chart d g s hs)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) c.T) ↘ _) ⊣
        affineRight A N hA (AffineSpace (ULift.{u} (Fin 1)) c.T) d) :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.map (ULift.{u} (Fin 1)) c.b)).leftDerivedFunctor.obj (family A g s) ⟶
        tateObject A N hA (AffineSpace (ULift.{u} (Fin 1)) c.T) d :=
  letI := chartGeometry d g s hs c
  sectionMap A (Scheme.Hom.deformationSpaceProj g s)
      (Scheme.Hom.deformationSpaceProj (pullback.snd g c.b)
        (Scheme.Hom.baseChangeSection g s hs c.b))
      (AffineSpace.map (ULift.{u} (Fin 1)) c.b) c.reesBase (Chart.Geometry.baseSquare)
      s.deformationSpaceSection (Scheme.Hom.baseChangeSection g s hs c.b).deformationSpaceSection
      (Chart.Geometry.baseSections) ≫
    (sectionLocality A c.reesOpen
      (Scheme.Hom.deformationSpaceProj (pullback.snd g c.b)
        (Scheme.Hom.baseChangeSection g s hs c.b))
      (Scheme.Hom.deformationSpaceProj (c.j ≫ pullback.snd g c.b) c.r)
      (Chart.Geometry.openOver) (Scheme.Hom.baseChangeSection g s hs c.b).deformationSpaceSection
      c.r.deformationSpaceSection (Chart.Geometry.openSections)).hom ≫
    chartMap A N hN hA
      (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) c.T ↘ c.T)
        (invertibleOnSource N c.b hS)) d
      (Scheme.Hom.deformationSpaceProj (c.j ≫ pullback.snd g c.b) c.r)
      c.r.deformationSpaceSection c.reesCoordinates (Chart.Geometry.coordinatesOver) adj
end AlgebraicGeometry.Etale.SectionLocalDualizingComparisons
