/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import Sheaf.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist
/-! # Finiteness of twisted sections for the canonical base-field action

Source: Stacks Project, Lemma 01YS(3).
(blueprint: lem-sc-p1-twisted-sections-finite-dimensional).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/-- Twisted sections are finite-dimensional for the action induced by the structure map.
Source: Stacks Project, Lemma 01YS(3), together with coherent cohomology finiteness
(Tags 02O5 and 02O6).
(blueprint: lem-sc-p1-twisted-sections-finite-dimensional).

Proof: the opens D₊(X₀) and D₊(X₁) cover polynomial Proj. On each of these opens,
O(n) is free on the homogeneous fraction Xᵢⁿ, for every integer n. Tensoring with
this local rank-one module preserves finite type and the finite-type kernel condition
in the definition of coherence. Hence G tensor O(n) is coherent. Polynomial Proj is
Noetherian, so coherence gives quasi-coherence and finite presentation. Use the
chart-compatible isomorphism and shifted-free twist comparison to transport this
module to the glued projective line. Its degree-zero cohomology is finite-dimensional
by ProjectiveLine.finiteDimensional_H. The H-zero/global-sections linear equivalence
and the chart comparison identify this vector space with the sections in the statement.
The charts carry a constant c to C(c)/1, so the transported scalar action is exactly
restriction of scalars along ρ below: degree-zero constants, the inverse affine
sections isomorphism, and the structure morphism on global sections. Transport finite
dimensionality along this linear equivalence. For the zero module the resulting
space has dimension zero; negative n and n=0 have the same local trivializations. -/
/- Transport finite dimensionality across a linear equivalence. -/
theorem finiteDimensional_of_linearEquiv
    {K V W : Type*} [Field K] [AddCommGroup V] [AddCommGroup W]
    [Module K V] [Module K W] (e : V ≃ₗ[K] W)
    [FiniteDimensional K W] : FiniteDimensional K V := by
  exact e.symm.finiteDimensional

/-- The chart comparison supplies the linear equivalence used in the finiteness proof.
Source: Stacks Project, Lemma 01YS(3), chart comparison with the glued projective line.
(blueprint: lem-sc-p1-twisted-sections-transport).
Proof: transport sections along the projective-line chart isomorphism and the
identification of the twisted sheaf with the transported glued twist; the resulting
map is linear over the specified structure-map action. -/
theorem serreTwistedSectionsTransport
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toRingedSpace G)
    (n : ℤ) :
    let ρ := ((Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k)).appTop.hom.comp
      (Scheme.ΓSpecIso _).inv.hom).comp
        (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k).toRingHom
    letI := Module.compHom
      Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤) ρ
    ∃ (L : (ProjectiveLine (Spec (.of k))).Modules),
      Nonempty (Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤)
        ≃ₗ[k] L.H 0) ∧ FiniteDimensional k (L.H 0) := by sorry

set_option linter.style.haveILetI false in
theorem serreTwistedSectionsFiniteDimensional
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules)
    (hG : RingedSpace.IsCoherent
      (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).toRingedSpace G)
    (n : ℤ) :
    let ρ := ((Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k)).appTop.hom.comp
      (Scheme.ΓSpecIso _).inv.hom).comp
        (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k).toRingHom
    letI := Module.compHom
      Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤) ρ
    FiniteDimensional k
      Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤) := by
  dsimp
  let ρ := ((Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin 2) k)).appTop.hom.comp
    (Scheme.ΓSpecIso _).inv.hom).comp
      (MvPolynomial.homogeneousSubmoduleZeroEquiv (Fin 2) k).toRingHom
  letI := Module.compHom
    Γ(G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) n, ⊤) ρ
  obtain ⟨L, ⟨e⟩, hL⟩ := serreTwistedSectionsTransport k G hG n
  letI := hL
  exact finiteDimensional_of_linearEquiv e

end AlgebraicGeometry
