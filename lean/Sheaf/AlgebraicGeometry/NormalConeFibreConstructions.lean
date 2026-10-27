/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.AlgebraicGeometry.HilbertSamuelInvariant
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Blowup.Affine.Functoriality
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.RingTheory.AssociatedGradedRing
public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.Field.ULift
/-! # Normal-cone fibre constructions

The centre stalk ideal, its residue-field scalar action, and the explicit normal-fibre
and polynomial degree subspaces shared by the reduced and nonreduced near-point theorems.
Source: Cossart--Jannsen--Saito, March 2009 preprint, Theorems 2.3 and 2.14
(blueprint: def-per-near-point-normal-fibre-constructions).
-/

@[expose] public section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits TensorProduct

namespace AlgebraicGeometry.HilbertSamuel

/-- The ideal of the closed centre in the stalk at its point. Source: ILO VIII 2.3.13;
Stacks Tag 0630 (blueprint: lem-trf-hilbert-samuel-near-normal-cone). -/
noncomputable abbrev centerStalkIdeal {X C : Scheme.{u}} (c : C ⟶ X) (z : C) :
    Ideal (X.presheaf.stalk (c z)) := RingHom.ker (c.stalkMap z).hom

/-- The canonical quotient-to-residue-field scalar action. Source: CJS Theorem 2.3,
normal-cone fibre (blueprint: lem-trf-hilbert-samuel-near-normal-cone). -/
noncomputable instance centerResidueAlgebra {X C : Scheme.{u}} (c : C ⟶ X) (z : C) :
    Algebra (X.presheaf.stalk (c z) ⧸ centerStalkIdeal c z) (X.residueField (c z)) :=
  (Ideal.Quotient.factor (IsLocalRing.le_maximalIdeal
    (RingHom.ker_ne_top (c.stalkMap z).hom))).toAlgebra

/-- The normal-cone fibre algebra, with the tensor factors commuted from the paper's
`G ⊗_A k`. Source: CJS Theorems 2.3 and 2.14
(blueprint: lem-trf-hilbert-samuel-near-normal-cone). -/
abbrev normalFibre {X C : Scheme.{u}} (c : C ⟶ X) (z : C) : Type u :=
  X.residueField (c z) ⊗[X.presheaf.stalk (c z) ⧸ centerStalkIdeal c z]
    Ideal.associatedGraded (centerStalkIdeal c z)

/-- The degree-n part of the tensor-product grading, spanned by homogeneous pure tensors.
Source: CJS Theorems 2.3 and 2.14
(blueprint: lem-trf-hilbert-samuel-near-normal-cone). -/
noncomputable def normalFibreGrade {X C : Scheme.{u}} (c : C ⟶ X) (z : C) (n : ℕ) :
    Submodule (X.residueField (c z)) (normalFibre c z) :=
  Submodule.span (X.residueField (c z))
    {s | ∃ a : Ideal.associatedGradedPiece (centerStalkIdeal c z) n,
      s = (1 : X.residueField (c z)) ⊗ₜ[X.presheaf.stalk (c z) ⧸ centerStalkIdeal c z]
        DirectSum.of (Ideal.associatedGradedPiece (centerStalkIdeal c z)) n a}

/-- Total-degree grading of `B[T]`: a coefficient of degree j times a monomial of
 degree d has degree j+d. Source: CJS Theorem 2.14, characteristic-zero linear directrix
(blueprint: lem-trf-hilbert-samuel-near-normal-cone). -/
noncomputable def normalPolynomialGrade {k B : Type u} [Field k] [CommRing B] [Algebra k B]
    (𝓑 : ℕ → Submodule k B) (r n : ℕ) : Submodule k (MvPolynomial (Fin r) B) :=
  Submodule.span k {p | ∃ (d : Fin r →₀ ℕ) (j : ℕ) (b : B),
    b ∈ 𝓑 j ∧ j + d.degree = n ∧ p = MvPolynomial.monomial d b}

end AlgebraicGeometry.HilbertSamuel
