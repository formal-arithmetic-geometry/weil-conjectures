module

public import Sheaf.AlgebraicGeometry.StandardGroupSchemes
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Cotangent

import Sheaf.RingTheory.FiniteSubcomodule
import Sheaf.AlgebraicGeometry.GmRepresentationWeightBasis

/-! # Homogeneous lifts of a cotangent basis at a fixed point

Source: Milne, Algebraic Groups (2017), Lemma 13.36 and its proof, pp.267--268,
specialized to G_m. Only the homogeneous cotangent lifts are asserted, so smoothness
is unnecessary (blueprint: lem-sfb-fixed-point-homogeneous-cotangent-lifts).

The action and fixedness are identities of morphisms over Spec F. Homogeneity is an
identity of global sections on G_m times Z, hence holds after evaluation on every
commutative F-algebra, including nonreduced algebras.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

namespace AlgebraicGeometry

/-- Evaluation of global regular functions at a rational point, using the canonical
Gamma(Spec F) = F identification. Source: Milne, Lemma 13.36 proof, p.268
(blueprint: lem-sfb-fixed-point-homogeneous-cotangent-lifts). -/
def cotangentLiftEvaluation {F : Type u} [Field F] (Z : Over (Spec (.of F)))
    (z : 𝟙_ (Over (Spec (.of F))) ⟶ Z) : Γ(Z.left, ⊤) →+* F :=
  (Scheme.ΓSpecIso (.of F)).hom.hom.comp z.left.appTop.hom

/-- Restriction of scalars on the cotangent quotient along the scheme's structure map.
Source: Milne, Lemma 13.36 proof, p.268
(blueprint: lem-sfb-fixed-point-homogeneous-cotangent-lifts). -/
@[instance_reducible]
def cotangentLiftModule {F : Type u} [Field F] (Z : Over (Spec (.of F)))
    (z : 𝟙_ (Over (Spec (.of F))) ⟶ Z) :
    Module F (RingHom.ker (cotangentLiftEvaluation Z z)).Cotangent :=
  Module.compHom _ (((Scheme.ΓSpecIso (.of F)).inv ≫ Z.hom.appTop).hom)

/-- A fixed rational point on an affine finite-type G_m-scheme has homogeneous regular
functions lifting a basis of its cotangent space. Weights are arbitrary integers.
Source: Milne, Algebraic Groups (2017), Lemma 13.36, pp.267--268
(blueprint: lem-sfb-fixed-point-homogeneous-cotangent-lifts).

Proof:
1. The action gives the Laurent coaction on A = Gamma(Z, O_Z), by
   def-weil-affine-spectrum and lem-weil-pbc-fibre-product-affine-spectra.
   Its identity and associativity give counitality and coassociativity.
2. Fixedness says (ev_z tensor 1)c(a) = ev_z(a). Comparing Laurent coefficients
   (def-weil-laurent-polynomial-ring) shows that m = ker(ev_z) is a subcomodule.
   The linear retraction a maps to a - ev_z(a) splits its inclusion, so tensoring
   preserves injectivity and the coalgebra identities restrict to m
   (def-weil-pbc-module-tensor-product).
3. By lem-weil-pbc-lft-affine-pairs, choose finitely many algebra generators of A.
   Center them at z. Expanding polynomials shows their classes span m/m^2:
   terms of degree at least two lie in m^2 (def-weil-pbc-algebra-hom-quotient).
4. By lem-sfb-comodule-finite-subcomodule, these centered generators lie in a
   finite-dimensional subcomodule V of m. Apply lem-sfb-gm-representation-weight-basis
   to obtain an integer-weight basis of V whose images span m/m^2.
5. Retain successive basis images outside the span of the preceding retained ones.
   They give a basis of m/m^2 (def-weil-pbc-free-module), with homogeneous lifts a_i.
   If the quotient is zero the retained list is empty, giving d = 0.
6. The coaction equations c(a_i) = a_i tensor t^(n_i) are precisely the displayed
   global-section identities, by lem-weil-pbc-fibre-product-affine-spectra.
   Pulling back along any R-point evaluates t at a unit of R, giving the asserted
   identity over every F-algebra, also for negative weights and in any characteristic. -/
theorem exists_homogeneous_cotangent_basis
    {F : Type u} [Field F] [IsAlgClosed F]
    (Z : Over (Spec (.of F))) [IsAffine Z.left]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (act : StandardGroupSchemes.multiplicative F ⊗ Z ⟶ Z)
    (hidentity : (MonObj.one (X := StandardGroupSchemes.multiplicative F) ▷ Z) ≫ act =
      (λ_ Z).hom)
    (hassoc : (MonObj.mul (X := StandardGroupSchemes.multiplicative F) ▷ Z) ≫ act =
      (α_ (StandardGroupSchemes.multiplicative F)
        (StandardGroupSchemes.multiplicative F) Z).hom ≫
        (StandardGroupSchemes.multiplicative F ◁ act) ≫ act)
    (z : 𝟙_ (Over (Spec (.of F))) ⟶ Z)
    (hfixed : lift (𝟙 (StandardGroupSchemes.multiplicative F))
      (toUnit (StandardGroupSchemes.multiplicative F) ≫ z) ≫ act =
      toUnit (StandardGroupSchemes.multiplicative F) ≫ z) :
    ∃ (d : ℕ)
      (a : Fin d → RingHom.ker (cotangentLiftEvaluation Z z))
      (n : Fin d → ℤ)
      (b : @Module.Basis (Fin d) F (RingHom.ker (cotangentLiftEvaluation Z z)).Cotangent
        _ _ (cotangentLiftModule Z z)),
      (∀ i : Fin d, b i = (RingHom.ker (cotangentLiftEvaluation Z z)).toCotangent (a i)) ∧
      ∀ i : Fin d, act.left.appTop (a i).val =
        (fst (StandardGroupSchemes.multiplicative F) Z).left.appTop
          ((Scheme.ΓSpecIso (.of (LaurentPolynomial F))).inv (LaurentPolynomial.T (n i))) *
        (snd (StandardGroupSchemes.multiplicative F) Z).left.appTop (a i).val := by
  sorry

end AlgebraicGeometry
