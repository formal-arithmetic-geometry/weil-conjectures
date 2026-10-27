module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Additive vector schemes in basis coordinates

Source: Milne, Algebraic Groups (2017), 2.6 and 14.31, printed p.288.
(blueprint: def-sfb-additive-vector-scheme)

The scheme is the spectrum of the polynomial algebra, with the coordinatewise additive
law. A chosen basis identifies its points with actual scalar extensions of the vector space.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped TensorProduct MonObj

namespace AlgebraicGeometry.FiniteVectorGroup

variable (k : Type u) [Field k] (d : ℕ)

/-- The polynomial affine scheme underlying the additive vector group of dimension d.
Source: Milne 2.6 (blueprint: def-sfb-additive-vector-scheme). -/
def scheme : Over (Spec (.of k)) :=
  StandardGroupSchemes.affine k (MvPolynomial (Fin d) k)

/-- Coordinatewise addition, dual to t_i mapping to t_i tensor 1 + 1 tensor t_i.
Source: Milne 2.6 (blueprint: def-sfb-additive-vector-scheme). -/
def comul : MvPolynomial (Fin d) k →ₐ[k]
    MvPolynomial (Fin d) k ⊗[k] MvPolynomial (Fin d) k :=
  MvPolynomial.aeval (fun i ↦ MvPolynomial.X i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] MvPolynomial.X i)

/-- The zero section is evaluation of every coordinate at zero.
Source: Milne 2.6 (blueprint: def-sfb-additive-vector-scheme). -/
def counit : MvPolynomial (Fin d) k →ₐ[k] k :=
  MvPolynomial.aeval (fun _ ↦ 0)

/-- The inverse sends each coordinate to its negative.
Source: Milne 2.6 (blueprint: def-sfb-additive-vector-scheme). -/
def antipode : MvPolynomial (Fin d) k →ₐ[k] MvPolynomial (Fin d) k :=
  MvPolynomial.aeval (fun i ↦ -MvPolynomial.X i)

/-- The displayed coordinate maps determine the additive group structure uniquely.
Source: Milne 2.6 (blueprint: def-sfb-additive-vector-scheme).
Proof: the two iterated additions send t_i to t_i tensor 1 tensor 1 +
1 tensor t_i tensor 1 + 1 tensor 1 tensor t_i. Evaluation at zero gives both units,
and substituting -t_i gives both inverses. Polynomial algebra maps agree on all
coordinates; the affine tensor-product correspondence gives the group diagrams.
All three structure maps are fixed, so the group structure is unique. -/
theorem group_existsUnique :
    ∃! h : GrpObj (scheme k d),
      h.one = StandardGroupSchemes.identitySection k (counit k d) ∧
      h.mul = StandardGroupSchemes.multiplication k (comul k d) ∧
      h.inv = StandardGroupSchemes.map k (antipode k d) := by
  sorry

/-- The unique group structure with these three coordinate maps.
Source: Milne 2.6 (blueprint: def-sfb-additive-vector-scheme). -/
instance group : GrpObj (scheme k d) :=
  (group_existsUnique k d).exists.choose

variable {k d} {V : Type u} [AddCommGroup V] [Module k V]

/-- The point whose i-th coordinate is the i-th scalar-extended basis coefficient of X.
Source: Milne 2.6 and 14.31 (blueprint: def-sfb-additive-vector-scheme). -/
def point (b : Module.Basis (Fin d) k V)
    (R : Type u) [CommRing R] [Algebra k R] (X : R ⊗[k] V) :
    (Spec (.of R)).asOver (Spec (.of k)) ⟶ scheme k d :=
  StandardGroupSchemes.map k (MvPolynomial.aeval (fun i ↦ (b.baseChange R).repr X i))

/-- The basis-coordinate points represent scalar extension, with its additive law and
naturality for every coefficient algebra, including the zero algebra.
Source: Milne 2.6 (blueprint: def-sfb-additive-vector-scheme).
Proof: the polynomial universal property identifies points with d-tuples over R.
The base-changed basis identifies these tuples with R tensor V, bijectively.
The comultiplication adds the two tuples coordinatewise. Applying an algebra map to
basis coefficients gives the tuple of the scalar-extended vector, proving naturality.
For d=0 all tuples are empty and the scalar extension is zero. -/
theorem point_represents (b : Module.Basis (Fin d) k V) :
    (∀ (R : Type u) [CommRing R] [Algebra k R], Function.Bijective (point b R)) ∧
    (∀ (R : Type u) [CommRing R] [Algebra k R] (X Y : R ⊗[k] V),
      point b R (X + Y) = point b R X * point b R Y) ∧
    (∀ (R S : Type u) [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
      (α : R →ₐ[k] S) (X : R ⊗[k] V),
      (Spec.map (CommRingCat.ofHom α.toRingHom)).asOver (Spec (.of k)) ≫ point b R X =
        point b S (α.toLinearMap.rTensor V X)) := by
  sorry

end AlgebraicGeometry.FiniteVectorGroup
