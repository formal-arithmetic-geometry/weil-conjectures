/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.Paper.SectionComparisonArrows
public import Sheaf.Paper.FiniteSmoothCanonicalInterfaces

/-! # The specified symmetric normal bundle and its counit fibre map

Source: main-20261015, sec-smooth-purity/sk-thm-dnc, opening and Local construction
(blueprint: def-trf-section-normal-fibre-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.SectionLocalDualizingComparisons
open SectionComparisonArrows

/-- The conormal module of a smooth closed section has rank d.
Source: sk-thm-dnc, centred coordinates
(blueprint: def-trf-section-normal-fibre-map).
Proof: the Cartesian centre square identifies the ideal with (x_1,...,x_d) in an
etale algebra over R[x]. Flat base change identifies I/I^2 with the free module
on the classes of x_j. These charts cover the section, including d=0. -/
theorem conormalRank {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : (ConormalGradedAlgebra.piece s 1).IsFiniteLocallyFreeOfRank d := by
  sorry

/-- The actual canonical symmetric-to-conormal-graded comparison is invertible.
Source: sk-thm-dnc, centred coordinates
(blueprint: def-trf-section-normal-fibre-map).
Proof: on the centred etale charts, the coordinate regular sequence identifies the
graded algebra with the polynomial algebra on I/I^2, by the same monomials in every
degree. Flat base change and localization preserve these identifications. -/
theorem conormalSymmetricIsIso {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : IsIso (ConormalGradedAlgebra.symmetricComparison s) := by
  sorry

/-- The normal bundle has the specified relative-Spec symmetric algebra as its total space.
Source: sk-thm-dnc, definition of N_s
(blueprint: def-trf-section-normal-fibre-map). -/
def normalBundle {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : Scheme.{u} :=
  letI := conormalRank d g s hs
  VectorBundleZeroSection.scheme S d (ConormalGradedAlgebra.piece s 1)

/-- The specified normal bundle is relative Spec Sym(I/I^2), with its actual projection.
Source: sk-thm-dnc, definition of N_s
(blueprint: def-trf-section-normal-fibre-map). -/
def normalProjection {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : normalBundle d g s hs ⟶ S :=
  letI := conormalRank d g s hs
  VectorBundleZeroSection.π S d (ConormalGradedAlgebra.piece s 1)

/-- The zero section is the augmentation killing all degree-one conormal generators.
Source: sk-thm-dnc, definition of z
(blueprint: def-trf-section-normal-fibre-map). -/
def normalZero {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : S ⟶ normalBundle d g s hs :=
  letI := conormalRank d g s hs
  VectorBundleZeroSection.zero S d (ConormalGradedAlgebra.piece s 1)

/-- The Rees cone-to-Sym comparison is fixed on every homogeneous representative.
The first factor sends a/t modulo t to the degree-one conormal class; the second is
relative Spec of the canonical symmetric-algebra comparison. No bundle isomorphism
is chosen from bare existence.
Source: sk-thm-dnc, definition of the canonical zero fibre
(blueprint: def-trf-section-normal-fibre-map). -/
@[irreducible]
def normalBundleIso {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : s.ker.normalCone ≅ normalBundle d g s hs :=
  letI := conormalRank d g s hs
  letI := conormalSymmetricIsIso d g s hs
  FiniteSmoothPurity.reesConeComparison s ≪≫
    (Over.forget S).mapIso
      ((ObjectProperty.ι (fun Y : Over S ↦ IsAffineHom Y.hom)).mapIso
        (((VectorBundleZeroSection.antiEquivalence S).inverse.mapIso
          (ObjectProperty.isoMk _ (asIso (ConormalGradedAlgebra.symmetricComparison s)))).unop))

/-- The canonical inclusion of Spec Sym(I/I^2) in the actual deformation at zero.
Source: sk-thm-dnc, zero fibre (blueprint: def-trf-section-normal-fibre-map). -/
@[irreducible]
def normalFibreInclusion {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : normalBundle d g s hs ⟶ s.ker.deformationSpace :=
  (normalBundleIso d g s hs).inv ≫ s.ker.normalConeToDeformationSpace

/-- The specified normal-bundle inclusion is the Cartesian zero fibre and respects z.
Source: sk-thm-dnc, canonical pair at zero
(blueprint: def-trf-section-normal-fibre-map).
Proof: the homogeneous-normalized Rees comparison respects projection and augmentation.
The symmetric comparison fixes constants and degree-one generators, so its relative
Spec respects the projection and the zero section. Paste its isomorphism with the
actual Rees zero-fibre square. The augmentation identity gives the section equation. -/
theorem normalFibre_spec {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) :
    IsPullback (normalFibreInclusion d g s hs) (normalProjection d g s hs)
      (Scheme.Hom.deformationSpaceProj g s) (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) ∧
    normalZero d g s hs ≫ normalFibreInclusion d g s hs =
      AffineSpace.zeroSection (ULift.{u} (Fin 1)) S ≫ s.deformationSpaceSection := by
  sorry

/-- The finite-rank bundle projection is quasi-compact.
Source: sk-thm-dnc, domain checks (blueprint: def-trf-section-normal-fibre-map).
Proof: relative Spec is affine, and affine morphisms are quasi-compact. -/
theorem normalProjectionQuasiCompact {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ)
    (g : V ⟶ S) [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) : QuasiCompact (normalProjection d g s hs) := by
  sorry

/-- Eta is the counit-defined exceptional comparison for the specified normal bundle.
Source: sk-thm-dnc, opening paragraph
(blueprint: def-trf-section-normal-fibre-map). -/
@[irreducible]
def normalFibreMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {V S : Scheme.{u}} [IsNoetherian S] (d : ℕ) (g : V ⟶ S)
    [SmoothOfRelativeDimension d g] (s : S ⟶ V) [IsClosedImmersion s]
    (hs : s ≫ g = 𝟙 S) [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (normalProjection d g s hs)] :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj (family A g s) ⟶
      sectionInvariant A (normalProjection d g s hs) (normalZero d g s hs) :=
  letI := normalProjectionQuasiCompact d g s hs
  sectionMap A (Scheme.Hom.deformationSpaceProj g s) (normalProjection d g s hs)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) (normalFibreInclusion d g s hs)
    (normalFibre_spec d g s hs).1 s.deformationSpaceSection (normalZero d g s hs)
    (normalFibre_spec d g s hs).2
end AlgebraicGeometry.Etale.SectionLocalDualizingComparisons
