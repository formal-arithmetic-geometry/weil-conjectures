/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
import WeilConjectures.RingTheory.SymmetricConormalPresentationTransport
import WeilConjectures.RingTheory.SymmetricProjectivePresentationConormal

/-! # Free conormal presentation of the symmetric algebra of a projective conormal module

If a finite polynomial presentation `P` of `A` has projective conormal module `M`, then the
symmetric algebra `Sym_A(M)` has a finite polynomial presentation with free conormal module
(`Algebra.Presentation.symmetric_conormal_free_presentation`).

## Implementation details

The classes of the `m` relations give a surjection `q : A^m → I/I²`, which splits by
projectivity; with `K = ker q` this identifies `I/I² × K` with `A^m`. Presenting the symmetric
algebra by `R[x, y]`, with each `y` sent to the class of the corresponding relation, the
conormal module is `Sym_A(I/I²) ⊗_A (I/I² × K)`, hence free
(`symmetric_projective_presentation_conormal`). The result is then transported along
`P.quotientEquiv` and the given equivalence with `M`, and the variables are reindexed by
`Fin (n + m)` (`symmetric_conormal_presentation_transport`).

## References

* [Stacks, Tag 07CE], proof, at `a = 1`
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra.Presentation

/-- Identity on conormal representatives, with the quotient coefficient equivalence. -/
private noncomputable def conormalQuotientEquiv
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {n m : ℕ} (P : Algebra.Presentation R A (Fin n) (Fin m)) :
    let ρ := P.quotientEquiv.toRingEquiv
    let _ := RingHomInvPair.of_ringEquiv ρ
    let _ := RingHomInvPair.of_ringEquiv_symm ρ
    P.ker.Cotangent ≃ₛₗ[(↑ρ : P.Quotient →+* A)] P.toExtension.Cotangent := by
  have := RingHomInvPair.of_ringEquiv P.quotientEquiv.toRingEquiv
  have := RingHomInvPair.of_ringEquiv_symm P.quotientEquiv.toRingEquiv
  refine
    { __ := P.toExtension.cotangentEquivCotangentKer.symm.toAddEquiv
      map_smul' := ?_ }
  intro r x
  induction r using Quotient.inductionOn' with
  | h r =>
    apply Extension.Cotangent.ext
    change (Ideal.Quotient.mk P.ker r) • x =
      (algebraMap P.Ring A r • (Extension.Cotangent.of x)).val
    rw [algebraMap_smul, Extension.Cotangent.val_smul']
    rfl

/-- A finite polynomial presentation with projective conormal module produces a symmetric
algebra whose canonical finite polynomial map has free conormal module. The linear
equivalence permits a universe change of the conormal module. -/
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
  classical
  let I : Ideal (MvPolynomial (Fin n) R) := P.ker
  let B := MvPolynomial (Fin n) R ⧸ I
  let C := SymmetricAlgebra B I.Cotangent
  let z : Fin m → I := fun j ↦ ⟨P.relation j, P.relation_mem_ker j⟩
  let q : (Fin m → B) →ₗ[B] I.Cotangent :=
    (Pi.basisFun B (Fin m)).constr B (fun j ↦ I.toCotangent (z j))
  have hq (j : Fin m) : q (Pi.single j 1) = I.toCotangent (z j) := by
    rw [← Pi.basisFun_apply B]
    exact (Pi.basisFun B (Fin m)).constr_basis B _ j
  have := RingHomInvPair.of_ringEquiv P.quotientEquiv.toRingEquiv
  have := RingHomInvPair.of_ringEquiv_symm P.quotientEquiv.toRingEquiv
  have : Module.Projective B I.Cotangent :=
    Module.Projective.of_equiv (P.conormalQuotientEquiv.trans e).symm
  let φ : MvPolynomial (Fin m) (MvPolynomial (Fin n) R) →+* C :=
    MvPolynomial.eval₂Hom ((algebraMap B C).comp (Ideal.Quotient.mk I))
      (fun j ↦ SymmetricAlgebra.ι B I.Cotangent (I.toCotangent (z j)))
  let α : MvPolynomial (Fin m) B →ₐ[B] C :=
    MvPolynomial.aeval (fun j ↦ SymmetricAlgebra.ι B I.Cotangent (I.toCotangent (z j)))
  obtain ⟨hφ, _, _, _, _, _, _, _, _, _, _, _, ⟨d⟩, ⟨d'⟩⟩ :=
    Algebra.symmetric_projective_presentation_conormal R n m I z
      P.span_range_relation_eq_ker q hq φ
      (by intro r; exact MvPolynomial.eval₂Hom_C _ _ _)
      (by intro j; rw [hq]; exact MvPolynomial.eval₂Hom_X' _ _ _)
      α (by intro j; rw [hq]; exact MvPolynomial.aeval_X _ _)
  have : Module.Free C (TensorProduct B C (I.Cotangent × LinearMap.ker q)) :=
    Module.Free.of_equiv d'.symm
  have : Module.Free C (Extension.ofSurjective φ.toIntAlgHom hφ).Cotangent :=
    Module.Free.of_equiv d.symm
  obtain ⟨ρ, ⟨c⟩⟩ := P.symmetric_conormal_presentation_transport M e hφ
  have := RingHomInvPair.of_ringEquiv ρ
  have := RingHomInvPair.of_ringEquiv_symm ρ
  exact Module.Free.of_equiv c.symm

end Algebra.Presentation
