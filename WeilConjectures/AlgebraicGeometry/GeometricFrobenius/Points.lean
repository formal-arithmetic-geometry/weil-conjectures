/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.PointCount

/-!
# Geometric points over closed points and rational points

Let `X₀` be a scheme over a finite field `k` with `q` elements, `X = X₀ ×_k k̄` its geometric
fiber and `g_X = 𝟙 × σ` its geometric Galois Frobenius. This file constructs the geometric
points `s : Spec k̄ ⟶ X` over the closed points and over the `𝔽_{qⁿ}`-rational points of `X₀`,
and shows that they are fixed by a power of `g_X` up to reparametrisation by `σ`:
`s ≫ g_Xᵐ = σᵐ ≫ s`, with `m` the degree of the point, respectively `m = n`.

## Main definitions

- `AlgebraicGeometry.Scheme.Hom.geometricFiberPointOfFinitePoint`: the geometric point over a
  point with finite residue field `κ(x)`, for an embedding `κ(x) ↪ k̄` chosen by
  `IsAlgClosed.lift`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow`:
  the geometric point over a closed point `x` satisfies `s ≫ g_X^{deg x} = σ^{deg x} ≫ s`.
- `AlgebraicGeometry.Scheme.Hom.geometricFiberPoint_fieldPoints_comp_geometricGaloisFrobenius_pow`:
  a geometric point over an `𝔽_{qⁿ}`-rational point satisfies `s ≫ g_Xⁿ = σⁿ ≫ s`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The geometric point of the geometric fiber over a point `x` of `X` with finite residue
field `κ(x)` (a closed point, for `X` of finite type over a finite field): the geometric point
`AlgebraicGeometry.Scheme.Hom.geometricFiberPoint` over `Spec κ(x) ⟶ X`, for the `k`-algebra
structure of `κ(x)` given by the structure morphism and an embedding `κ(x) ↪ k̄` chosen by
`IsAlgClosed.lift`. -/
noncomputable def geometricFiberPointOfFinitePoint (x : X.finitePoints) :
    Spec (.of (AlgebraicClosure k)) ⟶ f.geometricFiber :=
  letI := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  -- `Algebra.IsAlgebraic`, needed by `IsAlgClosed.lift`, is found through `Module.Finite`,
  -- which is not found from `Finite` by instance search
  have : Module.Finite k (X.residueField x.1) := Module.Finite.of_finite
  f.geometricFiberPoint (K := X.residueField x.1) IsAlgClosed.lift (X.fromSpecResidueField x.1)
    (f.specMap_residueFieldAlgebraMap x.1).symm

/-- The geometric point `s` over a closed point `x` is fixed by `g_X^{deg x}` up to
reparametrisation, `deg x = [κ(x) : k]`:

```
              s
  Spec k̄ ---------> X
    |               |
 σ^{deg x}      g_X^{deg x}
    v               v
  Spec k̄ ---------> X
              s
```
-/
theorem geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow [Finite k]
    (x : X.finitePoints) :
    f.geometricFiberPointOfFinitePoint x ≫
        (f.geometricGaloisFrobenius ^ f.degreeOver x.1).hom =
      (specGeometricFrobenius k ^ f.degreeOver x.1).hom ≫
        f.geometricFiberPointOfFinitePoint x := by
  let := (f.residueFieldAlgebraMap x.1).toAlgebra
  have : Finite (X.residueField x.1) := X.mem_finitePoints.1 x.2
  have : Module.Finite k (X.residueField x.1) := Module.Finite.of_finite
  exact f.geometricFiberPoint_comp_geometricGaloisFrobenius_pow (K := X.residueField x.1)
    IsAlgClosed.lift (X.fromSpecResidueField x.1) (f.specMap_residueFieldAlgebraMap x.1).symm _
    (Module.natCard_eq_pow_finrank (K := k) (V := X.residueField x.1))

/-- A geometric point `s` over an `𝔽_{qⁿ}`-rational point `y` of `X`, for any embedding
`ι : 𝔽_{qⁿ} ↪ k̄`, is fixed by `g_Xⁿ` up to reparametrisation:

```
             s
  Spec k̄ -------> X
    |             |
   σⁿ           g_Xⁿ
    v             v
  Spec k̄ -------> X
             s
```
-/
theorem geometricFiberPoint_fieldPoints_comp_geometricGaloisFrobenius_pow [Finite k] (n : ℕ)
    (ι : FiniteField.galoisExtension k n →ₐ[k] AlgebraicClosure k)
    (y : f.fieldPoints (FiniteField.galoisExtension k n)) :
    f.geometricFiberPoint ι y.1 y.2 ≫ (f.geometricGaloisFrobenius ^ n).hom =
      (specGeometricFrobenius k ^ n).hom ≫ f.geometricFiberPoint ι y.1 y.2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  have : Finite (FiniteField.galoisExtension k n) := Module.finite_of_finite k
  exact f.geometricFiberPoint_comp_geometricGaloisFrobenius_pow _ _ _ _
    (FiniteField.nat_card_galoisExtension k n hn)

end AlgebraicGeometry.Scheme.Hom
