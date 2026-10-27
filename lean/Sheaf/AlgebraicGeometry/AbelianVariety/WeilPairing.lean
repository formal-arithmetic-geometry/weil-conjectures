module

public import Sheaf.AlgebraicGeometry.AbelianVariety.RationalDualityData
public import Sheaf.AlgebraicGeometry.AbelianVariety.DualPoincareDatum
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TateModule
public import WeilConjectures.GroupTheory.TateModule
public import Sheaf.AlgebraicGeometry.AbelianVariety.PolarizationCalculus
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs

import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction
import Mathlib.NumberTheory.Padics.RingHoms
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Rigidity
import Sheaf.AlgebraicGeometry.AbelianSpacePoincareCalculus
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final

/-! # Functorial rational Weil pairings

Source: Milne, Abelian Varieties, I Remark 8.5, §9 opening, and §13,
Lemma 13.1 and Proposition 13.2(a),(d), pp.57–58.
(blueprint: lem-sfb-abelian-weil-pairing)

## Main statements

- `IsAbelianVariety.exists_functorial_weilPairing`: additive contravariant duality,
  its rational extension, the cyclotomic line, perfect pairings and alternating forms.

All maps on rational homomorphisms are characterized on pure tensors. The line is the
existing rational Tate module of `Additive kˣ`, whose integral coordinates are exactly
compatible roots of unity. No basis of this line is chosen.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

namespace AlgebraicGeometry

open IsAbelianVariety

/-- Functorial duality and perfect rational Weil pairings, with the alternating form
associated to any invertible sheaf, including at `ℓ = 2`.
Source: Milne AV I Remark 8.5, §9, §13 Lemma 13.1 and Proposition 13.2(a),(d), pp.57–58
(blueprint: lem-sfb-abelian-weil-pairing).

Proof plan:
1. Specialize [lem-sfb-abelian-space-poincare-calculus] to `Spec k`. Abelian varieties are
commutative [lem-sc-av-commutative], proper, smooth and geometrically reduced
[sbc-lem-smooth-geometrically-reduced], and geometrically connected
[lem-weil-separably-closed-geometrically-connected]. Yoneda identifies the two normalized
representing duals of [lem-sfb-abelian-polarization-calculus]. Rigidity [lem-sc-rigidity]
makes the comparison a group isomorphism. Transport Poincare biadditivity and pullback.
2. Pull back first biadditivity along `(a,b,1)` and second biadditivity along
`(1,aDual,bDual)`. Tensor pullback [lem-weil-pbc-module-pullback-tensor] and composition
[def-pc-module-pullback] identify the classifying families. Representability proves
additivity, reversed composition and identity. The tensor universal property
[def-weil-pbc-module-tensor-product] extends these to rational homomorphisms; expansion
on pure tensors gives the displayed normalizations and rational composition formula.
3. Choose compatible primitive roots using [lem-sc-primitive-root] and algebraic
closedness [def-weil-algebraic-closure]. Their orders are `ℓ^n`. Exponents identify the
root tower with the residue tower. The universal property and residue separation
[lem-exc-padic-residue-universal-property] identify its limit with `ℤ_[ℓ]`.
Rationalizing gives the asserted one-dimensional line, without fixing a basis here.
4. Apply [lem-sfb-finite-torsion-weil-pairing] coordinatewise to the actual torsion
coordinates of [sk-def-av-tate]. Its compatibility gives a root sequence. Bilinearity
and residue scalar action give an integral bilinear map; extend separately in both
factors by [def-weil-pbc-module-tensor-product], with value `E(x,y) ⊗ ab` on pure tensors.
5. By [thm-av-final] the integral Tate modules are finite free and all projections to
finite torsion are surjective: lift points successively by divisibility. Perfectness
at each finite level detects every coordinate of a vector in either radical.
Finite freeness and injectivity into rationalizations preserve this after clearing
denominators. Trivialize the root line for the argument and apply
[lem-sfb-finite-dimensional-perfect-pairing]; undoing the trivialization gives both
bijections to the line-valued linear duals stated below.
6. Finite functoriality [lem-sfb-finite-torsion-weil-pairing] proves adjointness on each
coordinate, then on integral Tate modules, then after scalar extension. The actual
componentwise maps of [sk-def-av-tate] are additive. Extend their actions rationally
by the tensor universal property. A rational homomorphism has a common denominator,
so multiplying the integral adjoint identity by its inverse proves the rational one.
7. The finite skew identity [lem-sfb-finite-torsion-weil-pairing] passes to the limits
and rationalizations. At equal arguments it gives `2 e(x,x) = 0`; characteristic zero
of `ℚ_[ℓ]` [def-weil-l-adic-numbers] gives alternation, also when `ℓ = 2`.
For an isogeny, [lem-sfb-simple-isogeny-decomposition] supplies a multiple inverse.
Its rational Tate action is an inverse after dividing by the positive integer.
Perfectness therefore detects both radicals of the induced form; its degree need
not be prime to `ℓ`.
-/
theorem IsAbelianVariety.exists_functorial_weilPairing
    (k : Type u) [Field k] [IsAlgClosed k] (ℓ : ℕ) [Fact ℓ.Prime]
    (hℓ : ℓ ≠ ringChar k) :
    ∃ (d : ∀ A B : AbelianVarietyWithDual k,
        abelianHom A.variety B.variety →+
          abelianHom B.datum.dual A.datum.dual)
      (dQ : ∀ A B : AbelianVarietyWithDual k,
        abelianRationalHom A.variety B.variety →ₗ[ℚ]
          abelianRationalHom B.datum.dual A.datum.dual)
      (cQ : ∀ A B C : AbelianVarietyWithDual k,
        abelianRationalHom A.variety B.variety →ₗ[ℚ]
          abelianRationalHom B.variety C.variety →ₗ[ℚ]
            abelianRationalHom A.variety C.variety)
      (cD : ∀ A B C : AbelianVarietyWithDual k,
        abelianRationalHom C.datum.dual B.datum.dual →ₗ[ℚ]
          abelianRationalHom B.datum.dual A.datum.dual →ₗ[ℚ]
            abelianRationalHom C.datum.dual A.datum.dual),
      (∀ (A B : AbelianVarietyWithDual k)
        (f : abelianHom A.variety B.variety)
        (g : abelianHom B.datum.dual A.datum.dual),
          A.dualHomClassifies B f g ↔ g = d A B f) ∧
      (∀ (A B C : AbelianVarietyWithDual k)
        (f : abelianHom A.variety B.variety)
        (g : abelianHom B.variety C.variety),
          d A C (Additive.ofMul (f.toMul ≫ g.toMul)) =
            Additive.ofMul ((d B C g).toMul ≫ (d A B f).toMul)) ∧
      (∀ A : AbelianVarietyWithDual k,
        d A A (Additive.ofMul (𝟙 (Grp.mk A.variety))) =
          Additive.ofMul (𝟙 (Grp.mk A.datum.dual))) ∧
      (∀ (A B : AbelianVarietyWithDual k) (q : ℚ)
        (f : abelianHom A.variety B.variety),
          dQ A B (q ⊗ₜ[ℤ] f) = q ⊗ₜ[ℤ] d A B f) ∧
      (∀ (A B C : AbelianVarietyWithDual k) (q r : ℚ)
        (f : abelianHom A.variety B.variety)
        (g : abelianHom B.variety C.variety),
          cQ A B C (q ⊗ₜ[ℤ] f) (r ⊗ₜ[ℤ] g) =
            (q * r) ⊗ₜ[ℤ] Additive.ofMul (f.toMul ≫ g.toMul)) ∧
      (∀ (A B C : AbelianVarietyWithDual k) (q r : ℚ)
        (g : abelianHom C.datum.dual B.datum.dual)
        (f : abelianHom B.datum.dual A.datum.dual),
          cD A B C (q ⊗ₜ[ℤ] g) (r ⊗ₜ[ℤ] f) =
            (q * r) ⊗ₜ[ℤ] Additive.ofMul (g.toMul ≫ f.toMul)) ∧
      (∀ (A B C : AbelianVarietyWithDual k)
        (f : abelianRationalHom A.variety B.variety)
        (g : abelianRationalHom B.variety C.variety),
          dQ A C (cQ A B C f g) = cD A B C (dQ B C g) (dQ A B f)) ∧
      (∀ A : AbelianVarietyWithDual k,
        dQ A A ((1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul (𝟙 (Grp.mk A.variety))) =
          (1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul (𝟙 (Grp.mk A.datum.dual))) ∧
      Nonempty (AddCommGroup.rationalTateModule ℓ (Additive kˣ) ≃ₗ[ℚ_[ℓ]] ℚ_[ℓ]) ∧
      ∃ (v : ∀ A B : AbelianVarietyWithDual k,
          abelianRationalHom A.variety B.variety →+
            (rationalTateModule ℓ A.variety →ₗ[ℚ_[ℓ]] rationalTateModule ℓ B.variety))
        (vD : ∀ A B : AbelianVarietyWithDual k,
          abelianRationalHom B.datum.dual A.datum.dual →+
            (rationalTateModule ℓ B.datum.dual →ₗ[ℚ_[ℓ]]
              rationalTateModule ℓ A.datum.dual))
        (e : ∀ A : AbelianVarietyWithDual k,
          rationalTateModule ℓ A.variety →ₗ[ℚ_[ℓ]]
            rationalTateModule ℓ A.datum.dual →ₗ[ℚ_[ℓ]]
              AddCommGroup.rationalTateModule ℓ (Additive kˣ)),
        (∀ (A B : AbelianVarietyWithDual k) (q : ℚ)
          (f : abelianHom A.variety B.variety),
            v A B (q ⊗ₜ[ℤ] f) = (q : ℚ_[ℓ]) • rationalTateModuleMap f.toMul.hom.hom) ∧
        (∀ (A B : AbelianVarietyWithDual k) (q : ℚ)
          (f : abelianHom B.datum.dual A.datum.dual),
            vD A B (q ⊗ₜ[ℤ] f) = (q : ℚ_[ℓ]) • rationalTateModuleMap f.toMul.hom.hom) ∧
        (∀ A : AbelianVarietyWithDual k,
          Function.Bijective (e A) ∧ Function.Bijective (e A).flip) ∧
        (∀ (A B : AbelianVarietyWithDual k)
          (f : abelianRationalHom A.variety B.variety)
          (x : rationalTateModule ℓ A.variety) (y : rationalTateModule ℓ B.datum.dual),
            e B (v A B f x) y = e A x (vD A B (dQ A B f) y)) ∧
        (∀ (A : AbelianVarietyWithDual k) (L : A.variety.left.Modules),
          L.IsInvertible → ∀ φ : A.variety ⟶ A.datum.dual,
            ClassifiesAbelianDifference A.datum L φ → ∃ hφ : IsMonHom φ,
              (∀ x : rationalTateModule ℓ A.variety,
                e A x (@rationalTateModuleMap k _ ℓ _ A.variety _ _ A.datum.dual _ _ φ hφ x)
                  = 0) ∧
              (IsIsogeny φ →
                (∀ x : rationalTateModule ℓ A.variety,
                  (∀ y : rationalTateModule ℓ A.variety,
                    e A x (@rationalTateModuleMap k _ ℓ _ A.variety _ _
                      A.datum.dual _ _ φ hφ y) = 0) → x = 0) ∧
                (∀ y : rationalTateModule ℓ A.variety,
                  (∀ x : rationalTateModule ℓ A.variety,
                    e A x (@rationalTateModuleMap k _ ℓ _ A.variety _ _
                      A.datum.dual _ _ φ hφ y) = 0) → y = 0))) := by
  sorry

end AlgebraicGeometry
