module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Artinian.Module
import WeilConjectures.AlgebraicGeometry.ArtinianIdealLengthOneFiltration
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField

/-!
# Prime-to-ell residue degrees after field extension

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose II, Proposition 1.2.7,
printed pp. 25--26 (blueprint: lem-per-prime-to-ell-residue-base-change).

The scheme below is the actual fibre product of the two field spectra.
`pullbackSpecIso k L K` identifies it with the spectrum of the commutative algebra
`L ⊗[k] K`, whose pure tensors multiply by multiplying both factors. Its second
projection corresponds to the map `b ↦ 1 ⊗ₜ[k] b`. The residue field of `Spec K`
at its unique point is canonically `K`; thus the residue degree of this projection
is exactly the degree over `K` in the statement.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Every residue field of `Spec L ×[Spec k] Spec K` is finite over `K`, and one
has degree prime to `ell`, provided `[L : k]` is finite and prime to `ell`.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose II, Proposition 1.2.7,
printed pp. 25--26 (blueprint: lem-per-prime-to-ell-residue-base-change).

Proof, following the six steps of the DAG node:
1. Identify the pullback with `Spec (L ⊗[k] K)` by
   lem-weil-pbc-fibre-product-affine-spectra. By lem-weil-pbc-fibre-product-points
   and lem-weil-pbc-fibre-product-point-residue-field, its points correspond to
   primes of this tensor algebra and their residue fields are the fraction fields
   of the prime quotients, compatibly with the map from `K`.
2. A `k`-basis of `L` gives a `K`-basis `e_i ⊗ 1` of the tensor algebra: coordinate
   maps prove independence and the tensor relations prove spanning. Hence its
   dimension over `K` is `d > 0` (def-weil-pbc-module-tensor-product and
   def-weil-vector-space-dimension), without any dimension condition on `K/k`.
3. Each prime quotient is a finite-dimensional domain, hence a field by
   lem-weil-pbc-finite-dimensional-domain-is-field. This proves finiteness of
   every residue extension, using the identification in step 1.
4. The tensor algebra is Artinian by lem-weil-pbc-finite-dim-algebra-artinian.
   Apply lem-weil-pbc-artinian-ideal-length-one-filtration to its unit ideal.
   The filtration has positive length since the tensor algebra is nonzero.
5. A nonzero element of each simple quotient generates it. Its annihilator is
   maximal, and multiplication by that element identifies the quotient with the
   corresponding residue field, as a `K`-vector space.
6. Lift bases through successive quotients to add dimensions. This gives `d` as
   the sum of the residue degrees in step 5, with repetitions accounting for
   nilpotents. If all degrees were divisible by `ell`, then so would `d` be.
   Choose a degree not divisible by `ell`, and combine with step 3.
-/
theorem prime_to_ell_residue_base_change
    (k L K : Type u) [Field k] [Field L] [Field K] [Algebra k L] [Algebra k K]
    [FiniteDimensional k L] (d ell : ℕ) (hd : Module.finrank k L = d)
    (hell : Nat.Prime ell) (hdegree : ¬ ell ∣ d) :
    (∀ z : ↑(pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      ((pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueFieldMap z).hom.Finite) ∧
    ∃ z : ↑(pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))),
      ¬ ell ∣ (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k L)))
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).residueDegree z := by
  sorry

end AlgebraicGeometry
