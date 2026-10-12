/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker P2
-/
module

public import Mathlib.Algebra.BrauerGroup.Defs
public import Sheaf.FieldTheory.GaloisUnitsCohomology
import WeilConjectures.Algebra.Central.ReducedNorm
import Sheaf.FieldTheory.BrauerScalarDefectExists
import Sheaf.FieldTheory.BrauerScalarDefectFaithful
import Sheaf.FieldTheory.BrauerScalarDefectSurjective

/-!
# Algebraic Brauer classes and continuous Galois cohomology

Source: Stacks Project, Theorem 03R7, and Section 0DVG.
(blueprint: lem-sc-brauer-galois-units-comparison).
-/

@[expose] public section

universe u

namespace Field

/-- Central simple algebras up to Brauer equivalence are classified by second continuous
Galois cohomology with coefficients in separable-closure units.

Proof: a central simple algebra splits over a finite Galois extension. Its descent datum
is a projective-linear cocycle; lifts to general linear matrices have scalar defects,
giving a continuous two-cocycle in the units of the separable closure. Changing the
lifts changes this by a continuous coboundary. Tensor products multiply the cocycles,
and matrix amplification preserves their class, so the construction descends to
Brauer equivalence. If the scalar defect is a coboundary, change the lifts to a general
linear cocycle; matrix Hilbert 90 trivializes it, so the algebra is a matrix algebra.
Applying this to the tensor product with an opposite algebra gives injectivity.
Compactness makes a continuous cocycle into discrete units locally constant with finite
image. Choose an open normal subgroup on whose cosets it is constant and which fixes
its values; its fixed field is a finite Galois extension representing the cocycle. The
associated crossed-product algebra is central simple and has that scalar-defect
class. This gives surjectivity. Continuous homogeneous and inhomogeneous cochains are
identified by the usual change of variables. Since the Galois group is compact Hausdorff,
the compact-open exponential law identifies Mathlib's iterated continuous maps with
jointly continuous maps on finite powers of the group. Homology in `TopModuleCat` uses
the algebraic kernel modulo image, with its quotient topology; forgetting that topology
therefore gives the usual cocycle classes. Thus their degree-two classes agree with
`GaloisUnitsH2`. The inverse bijection gives the asserted equivalence.

Source: Stacks Project, Theorem 03R7 (Brauer groups), and Section 0DVG (continuous
homogeneous and inhomogeneous cochains). All fields, including imperfect fields, use
separable-closure units, not algebraic-closure units.
(blueprint: lem-sc-brauer-galois-units-comparison). -/
theorem nonempty_equiv_brauerGroup_galoisUnitsH2 (K : Type u) [Field K] :
    Nonempty (BrauerGroup.{u, u} K ≃ GaloisUnitsH2 K) := by
  classical
  have uniqueClass (A : CSA.{u, u} K) :
      ∃! x : GaloisUnitsH2 K, HasBrauerScalarDefect K A x := by
    obtain ⟨n, hn, ⟨e⟩⟩ :=
      Algebra.IsCentral.exists_algEquiv_matrix_of_isSepClosed K A (SeparableClosure K)
    obtain ⟨b, hb, z, hdesc, hdefect⟩ :=
      exists_brauerScalarDefect_lifts K A n hn.ne e
    let x : GaloisUnitsH2 K := (ContinuousCohomology.π (galoisUnitsTopRep K) 2).hom z
    have hx : HasBrauerScalarDefect K A x :=
      ⟨n, hn.ne, e, b, hb, z, rfl, hdesc, hdefect⟩
    refine ⟨x, hx, ?_⟩
    intro y hy
    exact (brauerScalarDefect_eq_iff K A A y x hy hx).mpr
      (IsBrauerEquivalent.refl A)
  let f : CSA.{u, u} K → GaloisUnitsH2 K :=
    fun A ↦ Classical.choose (uniqueClass A)
  have hf (A : CSA.{u, u} K) : HasBrauerScalarDefect K A (f A) :=
    (Classical.choose_spec (uniqueClass A)).1
  have respects (A B : CSA.{u, u} K) (h : IsBrauerEquivalent A B) : f A = f B :=
    (brauerScalarDefect_eq_iff K A B (f A) (f B) (hf A) (hf B)).mpr h
  let F : BrauerGroup.{u, u} K → GaloisUnitsH2 K :=
    Quotient.lift f respects
  refine ⟨Equiv.ofBijective F ⟨?_, ?_⟩⟩
  · intro a b
    induction a using Quotient.inductionOn with
    | h A =>
      induction b using Quotient.inductionOn with
      | h B =>
        intro h
        apply Quotient.sound
        exact (brauerScalarDefect_eq_iff K A B (f A) (f B) (hf A) (hf B)).mp h
  · intro x
    obtain ⟨A, hx⟩ := exists_csa_brauerScalarDefect K x
    refine ⟨Quotient.mk _ A, ?_⟩
    exact (brauerScalarDefect_eq_iff K A A (f A) x (hf A) hx).mpr
      (IsBrauerEquivalent.refl A)

end Field
