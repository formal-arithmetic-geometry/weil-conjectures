/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.Topology.GDelta.Basic
import WeilConjectures.AlgebraicGeometry.Ample
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import WeilConjectures.AlgebraicGeometry.UnramifiedQuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Sheaf.AlgebraicGeometry.DeJongRelativeMarkedSemistable
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective

/-!
# Marked nodal reduction of a relative curve

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé IX, Theorem 1.2 (i),
(iii)--(vi), printed p. 131; Stacks Project, Tags 087S, 01WE, 02V5, 02LS
(blueprint: lem-trf-relative-marked-nodal-reduction).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper relative generic curve with generically étale markings admits a nodal model
with finite étale Cartier markings after alterations of source and base.
Source: ILO, Exposé IX, Theorem 1.2 (i), (iii)--(vi), printed p. 131; Stacks Project,
Tags 087S, 01WE, 02V5, 02LS (blueprint: lem-trf-relative-marked-nodal-reduction).

Proof:
1. Apply `lem-trf-dejong-relative-marked-semistable` to `(f,Z)`. It gives the square,
   excellent integral altered schemes, the projective-bundle flat finitely presented nodal
   curve, the smooth geometrically integral generic fibre, the Cartier divisor proper étale
   over the new base, and the closed nowhere dense exceptional set with boundary containment.
2. The hypothesis on `Y` gives an ample invertible sheaf by
   `lem-weil-pbc-projective-ample-invertible`. Apply
   `lem-trf-projective-bundle-to-h-projective` (Stacks 087S) to the base alteration.
   Compose with `Y → Spec R` using `lem-trf-h-projective-composition` (01WE), obtain an
   ample sheaf on the new base, and apply 087S again to the nodal family. Only properness
   of the alteration of the total space is needed.
3. Keep the exceptional subset from the semistable theorem itself. Its smooth-complement
   and boundary-containment clauses are exactly the required assertions.
4. The divisor map is proper and étale, hence unramified and locally quasi-finite by
   `lem-weil-pbc-unramified-quasi-finite-at-points` (02V5). The criterion
   `pqf-lem-proper-lqf-finite` (02LS) makes it finite. The Cartier and smooth-locus
   assertions remain those from step 1. No condition on the alteration degrees is used.
-/
theorem exists_relativeMarkedNodalReduction
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y] [IsNoetherian X] [IsNoetherian Y]
    (hX : ∀ U : X.Opens, IsAffineOpen U → IsExcellent Γ(X, U))
    (hY : ∀ U : Y.Opens, IsAffineOpen U → IsExcellent Γ(Y, U))
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (p : Y ⟶ Spec (CommRingCat.of R)) [IsHProjective p]
    (y : Y) (hy : IsGenericPoint y Set.univ)
    [Smooth (f.fiberToSpecResidueField y)] [IrreducibleSpace (f.fiber y)]
    (hdim : topologicalKrullDim (f.fiber y) = 1)
    (Z : Scheme.{u}) (j : Z ⟶ X) [IsClosedImmersion j]
    (hZ : IsNowhereDense (Set.range j))
    [Etale ((j ≫ f).fiberToSpecResidueField y)] :
    ∃ (X' Y' : Scheme.{u}) (a : X' ⟶ X) (b : Y' ⟶ Y) (f' : X' ⟶ Y'),
      a ≫ f = f' ≫ b ∧
      IsProper a ∧ IsDominant a ∧
      (∃ U : X.Opens, Dense (U : Set X) ∧ IsFinite (a ∣_ U)) ∧
      IsProper b ∧ IsDominant b ∧ IsHProjective b ∧
      (∃ U : Y.Opens, Dense (U : Set Y) ∧ IsFinite (b ∣_ U)) ∧
      IsIntegral X' ∧ IsIntegral Y' ∧
      (∀ U : X'.Opens, IsAffineOpen U → IsExcellent Γ(X', U)) ∧
      (∀ U : Y'.Opens, IsAffineOpen U → IsExcellent Γ(Y', U)) ∧
      IsHProjective f' ∧ Flat f' ∧
      (∃ hfp : LocallyOfFinitePresentation f', @HasNodalGeometricFibres _ _ f' hfp) ∧
      (∃ (T : Set Y') (hT : IsClosed T) (D : Scheme.{u}) (i : D ⟶ X'),
        IsNowhereDense T ∧ IsEffectiveCartierCenter i ∧
        Smooth (f' ∣_ (⟨Tᶜ, hT.isOpen_compl⟩ : Y'.Opens)) ∧
        IsFinite (i ≫ f') ∧ Etale (i ≫ f') ∧
        (∀ d : D, (f'.stalkMap (i d)).hom.FormallySmooth) ∧
        a ⁻¹' Set.range j ⊆ Set.range i ∪ f' ⁻¹' T) ∧
      ∃ y' : Y', IsGenericPoint y' Set.univ ∧
        Smooth (f'.fiberToSpecResidueField y') ∧
        GeometricallyIntegral (f'.fiberToSpecResidueField y') := by
  sorry

end AlgebraicGeometry
