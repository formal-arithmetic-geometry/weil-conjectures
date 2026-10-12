/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
import Sheaf.RingTheory.SymmetricProjectivePresentationConormal

/-! # Free conormal presentation of the symmetric algebra of a projective conormal module

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07CE, lines 357–414.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra.Presentation

/-- A finite polynomial presentation with projective conormal module produces a symmetric
algebra whose canonical finite polynomial map has free conormal module. The linear
equivalence permits a universe change of the conormal module.

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07CE, lines 357–414, at `a = 1`.
(blueprint: lem-weil-pbc-symmetric-conormal-free-presentation)

Proof. Write `P = R[x]/I`, and let the `m` relations generate `I`. Their classes give a
surjection `q : A^m → P.toExtension.Cotangent`. Projectivity splits this map; if `K` is its
kernel, the splitting identifies `P.toExtension.Cotangent × K` with `A^m`. Present the
symmetric algebra by `R[x,y]`, sending each `y` to the class of the corresponding relation.
The symmetric-projective-presentation-conormal lemma gives the conormal module of this
surjection as `Sym_A(I/I²) ⊗_A ((I/I²) × K)`, hence as the free module `Sym_A(I/I²)^m`.
Use `P.quotientEquiv` to identify `R[x]/I` with `A`, and the given equivalence to identify
its conormal module with `M`. The universal property transports the symmetric algebra and
its polynomial surjection along these equivalences. Reindex the two finite sets of
variables by `Fin (n + m)`. The induced isomorphisms of ideals, their squares and their
quotients transport the free conormal module to the kernel of the resulting map. These
operations also apply when either finite index is empty or `A` is the zero ring. -/
theorem symmetric_conormal_free_presentation
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {n m : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin m))
    (M : Type w) [AddCommGroup M] [Module A M] [Module.Projective A M]
    (e : P.toExtension.Cotangent ≃ₗ[A] M)
    [Algebra R (SymmetricAlgebra A M)] [IsScalarTower R A (SymmetricAlgebra A M)] :
    let x : Fin m → M := fun j ↦ e (Extension.Cotangent.mk
      ⟨P.relation j, P.relation_mem_ker j⟩)
    let f : MvPolynomial (Fin (n + m)) R →ₐ[R] SymmetricAlgebra A M :=
      MvPolynomial.aeval (fun i ↦ Sum.elim
        (fun j ↦ algebraMap A (SymmetricAlgebra A M) (P.val j))
        (fun j ↦ SymmetricAlgebra.ι A M (x j)) (finSumFinEquiv.symm i))
    Module.Free (MvPolynomial (Fin (n + m)) R ⧸ RingHom.ker f.toRingHom)
      (RingHom.ker f.toRingHom).Cotangent := by
  sorry

end Algebra.Presentation
