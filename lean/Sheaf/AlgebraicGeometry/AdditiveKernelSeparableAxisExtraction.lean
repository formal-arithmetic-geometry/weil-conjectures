module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Algebra.MvPolynomial.Basic
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas

/-!
# Extracting an additive coordinate axis from a kernel

Source: Conrad, The Structure of Solvable Groups over General Fields, Lemmas 1.11--1.13,
printed pp.6--7 (blueprint: lem-sfb-additive-kernel-separable-axis-extraction).

The dimension is written as `n + 1`. Products are products in the category of group
schemes, so their projections, automorphisms and the factor map are group morphisms.
The curve is a morphism over the separable closure, and the kernel is the fibre over zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- A nonconstant affine line in the kernel after separable closure allows a group
coordinate automorphism making the first coordinate irrelevant. The first axis then
factors through the scheme-theoretic kernel. In dimension one the original map is zero.
Source: Conrad, The Structure of Solvable Groups over General Fields, Lemmas 1.11--1.13,
printed pp.6--7 (blueprint: lem-sfb-additive-kernel-separable-axis-extraction).

Proof:
1. The affine-spectrum dictionary and the multivariable polynomial universal property
identify f with a polynomial F satisfying F(X+Y)=F(X)+F(Y). Its constant is zero.
Apply `lem-trf-additive-polynomial-monomial-classification` to the homogeneous components:
F is a sum of one-variable p-polynomials. Conversely these are additive by Frobenius.
2. If a coordinate polynomial is zero, permute it to the first position and omit it.
Otherwise write the coordinate degrees as p^(m_i), their leading coefficients as c_i,
and induct on the sum of these degrees.
3. After each group coordinate change the inverse-transformed curve remains nonconstant.
Its coordinate polynomials v_i(t) over K have positive maximal weighted degree
N = max_i(deg(v_i) p^(m_i)). The coefficient of t^N in F(v) is zero and gives a
nonzero tuple annihilating the principal part. By
`lem-sfb-diagonal-p-form-separable-isotropy-descent`, descend a principal-part zero to k.
4. Order the m_i decreasingly and let r be the first nonzero coordinate of that zero b.
Substitute x_r=b_r y_r and x_i=y_i+b_i y_r^(p^(m_r-m_i)) for i>r, leaving i<r fixed.
This is additive and invertible: y_r=x_r/b_r and the other y_i are recovered by subtraction.
The principal coefficient in y_r cancels; all lower contributions have smaller degree.
Thus its coordinate vanishes or the total coordinate degree decreases. Induction terminates.
5. Compose these automorphisms and move the vanished coordinate to the first position.
The remaining polynomial defines g and the factorization through the last n coordinates.
Polynomial identities hold on every algebra, including nonreduced ones, so the first
axis factors as a group morphism through the fibre over zero, `GrpObj.ker`.
For n=0 a nonzero one-variable F composed with the nonconstant v has positive degree,
contradicting its vanishing. Hence f=0, and the factor map from the empty product is zero. -/
theorem additive_kernel_separable_axis_extraction
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) (K : Type u) [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [Algebra.IsSeparable k K] [IsSepClosed K]
    (f : (∏ᶜ (fun _ : Fin (n + 1) ↦ Grp.mk (StandardGroupSchemes.additive k))) ⟶
      Grp.mk (StandardGroupSchemes.additive k))
    (u : StandardGroupSchemes.additive K ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
        (∏ᶜ (fun _ : Fin (n + 1) ↦ Grp.mk (StandardGroupSchemes.additive k))).X)
    (hu : ¬ ∃ c : 𝟙_ (Over (Spec (.of K))) ⟶
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj
          (∏ᶜ (fun _ : Fin (n + 1) ↦ Grp.mk (StandardGroupSchemes.additive k))).X,
      toUnit (StandardGroupSchemes.additive K) ≫ c = u)
    (hfu : u ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
        f.hom.hom =
      u ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
        (1 : (∏ᶜ (fun _ : Fin (n + 1) ↦ Grp.mk (StandardGroupSchemes.additive k))).X ⟶
          StandardGroupSchemes.additive k)) :
    ∃ α : (∏ᶜ (fun _ : Fin (n + 1) ↦ Grp.mk (StandardGroupSchemes.additive k))) ≅
        (∏ᶜ (fun _ : Fin (n + 1) ↦ Grp.mk (StandardGroupSchemes.additive k))),
      ∃ g : (∏ᶜ (fun _ : Fin n ↦ Grp.mk (StandardGroupSchemes.additive k))) ⟶
          Grp.mk (StandardGroupSchemes.additive k),
        α.hom ≫ f = Pi.map' Fin.succ
          (fun _ : Fin n ↦ 𝟙 (Grp.mk (StandardGroupSchemes.additive k))) ≫ g ∧
        (∃ l : Grp.mk (StandardGroupSchemes.additive k) ⟶ Grp.mk (GrpObj.ker f.hom.hom),
          l.hom.hom ≫ GrpObj.kerι f.hom.hom =
            (Pi.lift (fun i : Fin (n + 1) ↦
              if i = 0 then 𝟙 (Grp.mk (StandardGroupSchemes.additive k)) else 0)).hom.hom ≫
                α.hom.hom.hom) ∧
        (n = 0 → f = 0) := by
  sorry

end AlgebraicGeometry
