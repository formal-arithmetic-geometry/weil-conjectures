/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StandardGroupSchemes
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Actual semi-invariant section modules

Source: Milne, Algebraic Groups (2017), Section 18c and 22.48--22.49; Alper,
Section 9.7, immediately before Lemma 9.7.2, positive right-semi-invariance convention
(blueprint: def-sfb-rho-section-module-data).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite
open scoped MonObj

namespace AlgebraicGeometry.RhoSection

/-- The actual coordinate algebra, with the scalar structure induced by the structure map.
Source: Milne, Section 18c (blueprint: def-sfb-rho-section-module-data). -/
abbrev Coordinate {F : Type u} [Field F] (G : Over (Spec (.of F))) :=
  ((algΓ (.of F)).obj G).unop

/-- Evaluate a regular function at an algebra-valued point, through the canonical
Spec--Gamma unit and the fully faithful algebraic Spec functor.
Source: Milne, Section 18c (blueprint: def-sfb-rho-section-module-data). -/
def evaluate {F : Type u} [Field F] {G : Over (Spec (.of F))}
    {A : Type u} [CommRing A] [Algebra F A]
    (g : StandardGroupSchemes.affine F A ⟶ G) : Coordinate G →ₐ[F] A :=
  (algSpec.fullyFaithful.preimage
    (g ≫ (algΓAlgSpecAdjunction (.of F)).unit.app G)).unop.hom

/-- The value of a character, read at the Laurent coordinate of the recorded G_m.
Source: Milne, Section 18c (blueprint: def-sfb-rho-section-module-data). -/
def characterValue {F : Type u} [Field F]
    {A : Type u} [CommRing A] [Algebra F A]
    (x : StandardGroupSchemes.affine F A ⟶ StandardGroupSchemes.multiplicative F) : A :=
  evaluate x ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv
    (LaurentPolynomial.T 1))

/-- The specified subspace of F[G], without replacing it by an abstract induced module.
It is the intersection of kernels of the linear semi-invariance equations over every
commutative F-algebra, including nonreduced algebras.
Source: Alper, Section 9.7 before Lemma 9.7.2, and Milne, Section 18c
(blueprint: def-sfb-rho-section-module-data). -/
def sectionModule {F : Type u} [Field F]
    (G B : Grp (Over (Spec (.of F)))) (i : B ⟶ G)
    (χ : B ⟶ Grp.mk (StandardGroupSchemes.multiplicative F)) (m : ℕ) :
    Submodule F (Coordinate G.X) :=
  ⨅ (A : Type u) (_ : CommRing A) (_ : Algebra F A)
    (g : StandardGroupSchemes.affine F A ⟶ G.X)
    (b : StandardGroupSchemes.affine F A ⟶ B.X),
    LinearMap.ker ((evaluate (g * (b ≫ i.hom.hom))).toLinearMap -
      characterValue (b ≫ χ.hom.hom) ^ m • (evaluate g).toLinearMap)

/-- A rational group-scheme representation on the actual section subspace, whose
matrix coefficients are exactly left translation on functions. A basis is only a
coordinate description of this action, never a replacement for the subspace.
The identity holds over every F-algebra; its columns give the action on a basis,
and hence its scalar extension on every vector. Such a group-scheme representation
is equivalently a counital coassociative coaction on W. Tensor products carry the
usual diagonal action, and invariants are the vectors with coaction v tensor 1.
Source: Milne, Section 4a, pp.83--84 (linear representations) and Definition 22.21, p.468
(blueprint: def-sfb-rho-section-module-data). -/
def HasRationalLeftTranslation {F : Type u} [Field F]
    (G : Grp (Over (Spec (.of F)))) (W : Submodule F (Coordinate G.X)) : Prop :=
  ∃ (I : Type u) (_ : Fintype I) (_ : DecidableEq I)
    (e : (I → F) ≃ₗ[F] W) (r : GeneralLinearGroup.RationalHom G.X I)
    (_ : IsMonHom r),
    ∀ (A : Type u) [CommRing A] [Algebra F A]
      (s g : StandardGroupSchemes.affine F A ⟶ G.X) (j : I),
      ∑ i, (GeneralLinearGroup.homMulEquiv I F A (s ≫ r) : Matrix I I A) i j *
        evaluate g (e (Pi.single i 1)).val =
          evaluate (s⁻¹ * g) (e (Pi.single j 1)).val

end AlgebraicGeometry.RhoSection
