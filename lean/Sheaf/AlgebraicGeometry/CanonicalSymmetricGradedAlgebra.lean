/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction
public import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra

/-!
# Canonical affine-basis symmetric algebra

Source: Stacks Project, Constructions, Tag 01OB; Modules, Tags 01CG and 01CL
(blueprint: def-trf-canonical-symmetric-graded-algebra).

The rings, grades and restriction homomorphisms are specified constructions. Only the
homogeneity and coefficientwise base-change properties are postponed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.SymmetricAlgebraSheaf

/-- The canonical symmetric grading on an affine section algebra. The decomposition is the
unique inverse of the summation map, using the internality recorded by the symmetric-grading
node; it chooses no algebra or grading.
Source: Stacks Project, Algebra, Section 00DM; Constructions, Tag 01OB
(blueprint: def-trf-canonical-symmetric-graded-algebra). -/
noncomputable instance sectionGradedAlgebra {X : Scheme.{u}} (E : X.Modules)
    (U : X.affineOpens) :
    GradedAlgebra (fun n : ℕ ↦ (SymmetricAlgebra.ι Γ(X, U.1)
      (E.val.obj (op U.1))).range ^ n) := by
  have h := (SymmetricAlgebra.graded_by_tensor_images Γ(X, U.1)
    (E.val.obj (op U.1))).2.2.2.2.1
  simp only [Submodule.map_pow, ← LinearMap.range_comp] at h
  exact DirectSum.IsInternal.gradedAlgebra h

/-- Restriction preserves every symmetric degree.
Source: Stacks Project, Modules, Tag 01CG; Constructions, Tag 01OB
(blueprint: def-trf-canonical-symmetric-graded-algebra).

Proof: the degree-n submodule is spanned by products of n degree-one generators.
Restriction sends each generator to the restricted module section and sends scalars by
structure-sheaf restriction. It therefore sends each such product to a product of the same
length, and additivity and semilinearity extend this to its span. -/
theorem restriction_mem_symmetricDegree {X : Scheme.{u}} (E : X.Modules)
    {U V : X.affineOpens} (h : U ≤ V) (n : ℕ)
    (a : sections E (op V.1))
    (ha : a ∈ (SymmetricAlgebra.ι Γ(X, V.1) (E.val.obj (op V.1))).range ^ n) :
    restriction E (homOfLE (X := X.Opens) h).op a ∈
      (SymmetricAlgebra.ι Γ(X, U.1) (E.val.obj (op U.1))).range ^ n := by
  sorry

/-- The actual symmetric-algebra restriction, bundled with its degree-preservation proof.
Source: Stacks Project, Modules, Tag 01CG; Constructions, Tag 01OB
(blueprint: def-trf-canonical-symmetric-graded-algebra). -/
noncomputable def gradedRestriction {X : Scheme.{u}} (E : X.Modules)
    {U V : X.affineOpens} (h : U ≤ V) :
    (fun n : ℕ ↦ (SymmetricAlgebra.ι Γ(X, V.1) (E.val.obj (op V.1))).range ^ n) →+*ᵍ
      (fun n : ℕ ↦ (SymmetricAlgebra.ι Γ(X, U.1) (E.val.obj (op U.1))).range ^ n) where
  toRingHom := restriction E (homOfLE (X := X.Opens) h).op
  map_mem := fun {n} {a} ha ↦ restriction_mem_symmetricDegree E h n a ha

/-- Affine restriction is coefficientwise base change in each symmetric degree.
Source: Stacks Project, Modules, Tags 01CG and 01CL; Constructions, Tag 01LN
(blueprint: def-trf-canonical-symmetric-graded-algebra).

Proof: for affine U contained in V, quasi-coherence identifies E(U) with
O(U) tensor over O(V) E(V), through m tensor r mapping to r times the restricted m.
Symmetric powers commute with this base change: the tensor-algebra base-change
isomorphism preserves degree and takes the commutator ideal to the corresponding
commutator ideal, hence descends degree by degree to symmetric algebras. On generators
this is precisely restriction E, and its scalar equation is restriction_algebraMap.
The resulting bijections in every degree give IsGradedBaseChangeAlong. -/
theorem gradedRestriction_isGradedBaseChangeAlong {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] {U V : X.affineOpens} (h : U ≤ V) :
    (gradedRestriction E h).IsGradedBaseChangeAlong
      (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom := by
  sorry

/-- The canonical affine-basis graded algebra of Sym(E). Its section rings are the
sectionwise symmetric algebras, its degree-n part is the nth power of the degree-one
inclusion range, and its restrictions are the canonical symmetric-algebra restrictions.
Source: Stacks Project, Constructions, Tag 01OB; Modules, Tags 01CG and 01CL
(blueprint: def-trf-canonical-symmetric-graded-algebra). -/
noncomputable def gradedAlgebraData {X : Scheme.{u}} (E : X.Modules)
    [E.IsQuasicoherent] : X.GradedAlgebraData where
  obj U := sections E (op U.1)
  commRing _ := inferInstance
  algebra _ := inferInstance
  grading U n := (SymmetricAlgebra.ι Γ(X, U.1) (E.val.obj (op U.1))).range ^ n
  gradedAlgebra U := sectionGradedAlgebra E U
  res h := gradedRestriction E h
  res_id U x :=
    congrArg (fun q ↦ q.hom x) ((presheaf E).map_id (op U.1))
  res_res h₁ h₂ x :=
    congrArg (fun q ↦ q.hom x) ((presheaf E).map_comp
      ((homOfLE (X := X.Opens) h₂).op)
      ((homOfLE (X := X.Opens) h₁).op)).symm
  isGradedBaseChangeAlong h := gradedRestriction_isGradedBaseChangeAlong E h

end AlgebraicGeometry.SymmetricAlgebraSheaf
