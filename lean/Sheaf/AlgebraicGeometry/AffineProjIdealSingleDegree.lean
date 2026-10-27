/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q56
-/
module

public import Sheaf.AlgebraicGeometry.HomogeneousQuotientProj
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.AlgebraicGeometry.GradedSheafStructures
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import WeilConjectures.Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Finite equations of one degree for a closed subscheme of an affine-base Proj

Source: Stacks Project, Divisors, Tag 0802, lemma-closed-subscheme-proj-finite,
affine-base proof (blueprint: lem-sfb-affine-proj-ideal-single-degree).

The homogeneous ideal is prescribed. The concluding isomorphism commutes with the
quotient-induced morphisms into Proj(A), so it identifies the closed scheme structures.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- A finitely presented homogeneous quotient of a quasi-compact Proj is cut out by
finitely many elements of one positive degree in the prescribed ideal.
Source: Stacks Project, Tag 0802, lemma-closed-subscheme-proj-finite, affine proof
(blueprint: lem-sfb-affine-proj-ideal-single-degree).

Proof: (1) The positive homogeneous standard opens form a basis by
lem-weil-pbc-proj-standard-open-inclusion. Choose a finite cover D₊(fᵢ), deg(fᵢ)=aᵢ>0.
For empty Proj take degree 1 and the empty family. The closed immersion's ideal
sheaf is quasi-coherent and of finite type by def-sbc-closed-immersion-ideal-sheaf
and lem-trf-closed-immersion-finite-presentation-ideal.
(2) For any homogeneous H, lem-sfb-proj-map-standard-charts identifies the chart
map with h/f^e ↦ h-bar/f-bar^e. It is surjective by homogeneous lifting. Its kernel
consists of fractions with numerator in H: an element mapping to zero has f^k h
in H for some k, and equals (f^k h)/f^(e+k), by def-weil-ring-localization-away.
(3) On each affine chart choose finitely many kernel generators hᵢⱼ/fᵢ^eᵢⱼ using
lem-weil-pbc-quasi-coherent-finite-type-affine. Their numerators lie in I and have
degree eᵢⱼ aᵢ by def-nagata-homogeneous-localization-degree-zero. Empty lists are allowed.
(4) Put L=product aᵢ and E=max({0} union {eᵢⱼ}), and d=L(E+1)>0. The elements
gᵢⱼ=hᵢⱼ fᵢ^(d/aᵢ-eᵢⱼ) lie in I_d. Their R-span F is contained in I_d since R acts
in degree zero. The ideal H=FA is homogeneous and contained in I.
(5) On chart i every original generator equals gᵢⱼ/fᵢ^(d/aᵢ), so the two kernel
ideals agree; the reverse containment follows from H ⊆ I, also for generators
chosen on other charts.
(6) By prop-nagata-relative-proj-functoriality both quotient maps are closed
immersions. Their ideal sheaves and quotient structure sheaves agree on this
cover by def-weil-closed-immersion and def-sbc-closed-immersion-ideal-sheaf.
Glue the chart identifications to obtain the stated isomorphism over Proj(A).
No finiteness of A, I, or the homogeneous components is used. -/
theorem exists_affineProjIdeal_single_degree
    (R : Type v) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (I : HomogeneousIdeal 𝒜)
    [CompactSpace (Proj 𝒜)] [LocallyOfFinitePresentation (homogeneousQuotientProjι 𝒜 I)] :
    ∃ (d : ℕ) (_hd : 0 < d) (r : ℕ) (g : Fin r → 𝒜 d),
      (∀ j : Fin r, (g j : A) ∈ I) ∧
      ∃ H : HomogeneousIdeal 𝒜,
        H.toIdeal = Ideal.span
          (Submodule.span R (Set.range (fun j : Fin r ↦ (g j : A))) : Set A) ∧
        ∃ e : Proj (homogeneousQuotientPiece 𝒜 H) ≅
            Proj (homogeneousQuotientPiece 𝒜 I),
          e.hom ≫ homogeneousQuotientProjι 𝒜 I = homogeneousQuotientProjι 𝒜 H := by
  sorry

end AlgebraicGeometry
