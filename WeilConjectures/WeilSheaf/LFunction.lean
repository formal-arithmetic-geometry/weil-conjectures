/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.LocalFrobenius
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.ZetaLinearAlgebra.DetTrace

/-!
# The Euler-product form of the trace formula for Weil complexes

Let `X₀` be a separated scheme of finite type over the finite field `k₀`, `X = X₀ ⊗ k̄` and `K`
a Weil complex on `X₀`. For a closed point `x` of degree `e_x` the local factor of the
`L`-function of `K` at `x` is the inverse of the alternating determinant

`det (1 - T ^ {e_x} F_x ∣ K_x̄) = ∏_j det (1 - T ^ {e_x} F_x ∣ 𝓗ʲ(K)_x̄) ^ ((-1) ^ j)`

(`LinearMap.alternatingCharpolyRevProd`), and the Euler-product form of the
Grothendieck–Lefschetz trace formula says

`L (X₀, K, T) = ∏_x det (1 - T ^ {e_x} F_x ∣ K_x̄)⁻¹`
`  = ∏_i det (1 - T F ∣ H_cⁱ(X, K)) ^ ((-1) ^ (i + 1))`

in `1 + T ℚ̄_ℓ⟦T⟧`, the product over the closed points being locally finite for the `T`-adic
topology (`AlgebraicGeometry.WeilComplex.coeff_prod_inv_alternatingCharpolyRevProd_stalk`).
For a Weil sheaf placed in degree zero, the stalk cohomology is the stalk itself
(`AlgebraicGeometry.WeilSheaf.coeff_prod_inv_localPolynomial_stalk`).

## Main statements

- `AlgebraicGeometry.WeilComplex.coeff_prod_inv_alternatingCharpolyRevProd_stalk`
  (`thm-trf-l-function-euler-product`): the Euler-product form of the trace formula.
- `AlgebraicGeometry.WeilSheaf.coeff_prod_inv_localPolynomial_stalk`: its form for a Weil
  sheaf.

## Implementation notes

*Local finiteness.* The `L`-function is an infinite product over the closed points. Instead of
choosing a topology on `ℚ̄_ℓ⟦T⟧` in which it converges, the statement is coefficientwise: the
coefficient of `T ^ n` of the finite product over any finite set of closed points containing
all points of degree at most `n` is the coefficient of `T ^ n` of the cohomological side. This
is the `T`-adic local finiteness of item (1) of the blueprint theorem, together with item (2).
Item (3), the curve case, is obtained from it with the vanishing of `H_cⁱ` outside `[0, 2]`,
and item (4), the transport along `ι : ℚ̄_ℓ → ℂ`, by applying `ι` coefficientwise.

*Degrees.* The finite products over the cohomological degrees run over finite sets `S` and `T`
of integers outside of which the compactly supported cohomology, respectively the cohomology
sheaves, vanish; such sets exist by finiteness
(`AlgebraicGeometry.WeilComplex.exists_subsingleton_compactlySupportedCohomology` and
`AlgebraicGeometry.WeilComplex.exists_finset_isZero_homologySheaf`), and enlarging them does
not change the alternating determinants, the added factors being `1`.

*Hypotheses.* The blueprint theorem is stated for a Weil complex satisfying the finite-level
hypotheses of `thm-trf-trace-formula-e` (étale-origin witnesses and compactification
admissibility for the reductions of a lattice of a representative). The Weil complexes of this
repository are constructible `ℚ̄_ℓ`-complexes on the pro-étale site of `X`, built directly from
pro-étale sheaves with no chosen lattice; those hypotheses are properties of the integral
models used in the proof, and are not part of the statement.
-/

@[expose] public section

universe u

open CategoryTheory Limits PowerSeries

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace WeilSheaf

/-- An isomorphism of Weil sheaves induces an isomorphism of the stalks at a geometric point,
compatible with the Frobenius. -/
noncomputable def stalkAtEquivOfIso {F G : WeilSheaf k₀ l X} (e : F ≅ G)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (m : ℕ) (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s) :
    (F.stalkAt s m hs).Equiv (G.stalkAt s m hs) where
  toLinearEquiv := LinearEquiv.ofLinear (stalkAtMap s m hs e.hom) (stalkAtMap s m hs e.inv)
    (LinearMap.ext fun y ↦ (stalkAtMap_comp s m hs e.inv e.hom y).symm.trans <| by
      rw [e.inv_hom_id]
      exact stalkAtMap_id s m hs G y)
    (LinearMap.ext fun y ↦ (stalkAtMap_comp s m hs e.hom e.inv y).symm.trans <| by
      rw [e.hom_inv_id]
      exact stalkAtMap_id s m hs F y)
  map_frobenius v := stalkAtMap_frobenius s m hs e.hom v

/-- An isomorphism of Weil sheaves induces an isomorphism of the geometric stalks at a closed
point, compatible with the local Frobenius. -/
noncomputable def stalkEquivOfIso {F G : WeilSheaf k₀ l X} (e : F ≅ G) (x : X.finitePoints) :
    (F.stalk x).Equiv (G.stalk x) :=
  stalkAtEquivOfIso e _ _ _

/-- Isomorphic Weil sheaves have the same characteristic polynomial of the local Frobenius at a
closed point. -/
theorem charpoly_frobeniusEnd_stalk_of_iso {F G : WeilSheaf k₀ l X} (e : F ≅ G)
    (x : X.finitePoints) :
    (F.stalk x).frobeniusEnd.charpoly = (G.stalk x).frobeniusEnd.charpoly :=
  ((stalkEquivOfIso e x).charpoly_frobeniusEnd).symm

/-- The stalks of a zero Weil sheaf are zero. -/
theorem subsingleton_stalk_of_isZero {F : WeilSheaf k₀ l X} (hF : IsZero F)
    (x : X.finitePoints) : Subsingleton (F.stalk x).carrier :=
  ModuleCat.subsingleton_of_isZero ((WeilCoefficients.toModuleCat l).map_isZero
    ((stalkFunctor k₀ l (Scheme.Hom.geometricFiberPointOfFinitePoint _ x)).map_isZero hF))

end WeilSheaf

variable [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

namespace WeilComplex

/-- Blueprint `thm-trf-l-function-euler-product`: Euler-product form of the trace formula.

Let `X₀` be a separated scheme of finite type over `k₀ = 𝔽_q` and `K` a Weil complex on `X₀`
with coefficients in `ℚ̄_ℓ`, `ℓ ≠ p`. Write `F` for the global geometric Frobenius on
`H_cⁱ(X, K)` and, for a closed point `x` of degree `e_x`, `F_x` for the local Frobenius on the
stalks `𝓗ʲ(K)_x̄`. Then

`L (X₀, K, T) = ∏_x det (1 - T ^ {e_x} F_x ∣ K_x̄)⁻¹`
`  = ∏_i det (1 - T F ∣ H_cⁱ(X, K)) ^ ((-1) ^ (i + 1))`

as formal power series over `ℚ̄_ℓ`, the product over the closed points being locally finite:
for every `n`, the coefficient of `T ^ n` of the finite product over any finite set `s` of
closed points containing those of degree at most `n` is the coefficient of `T ^ n` of the
right-hand side. Here `S` and `T` are finite sets of degrees outside of which `H_cⁱ(X, K)`,
respectively the cohomology sheaves `𝓗ʲ(K)`, vanish. -/
theorem coeff_prod_inv_alternatingCharpolyRevProd_stalk (K : WeilComplex k₀ l X)
    {S T : Finset ℤ}
    (hS : ∀ i ∉ S, Subsingleton (WeilComplex.compactlySupportedCohomology K i).carrier)
    (hT : ∀ j ∉ T, IsZero ((homologySheaf j).obj K)) (n : ℕ) (s : Finset X.finitePoints)
    (hs : ∀ x : X.finitePoints, (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ≤ n → x ∈ s) :
    coeff n (∏ x ∈ s, (LinearMap.alternatingCharpolyRevProd T
        (fun j ↦ (WeilComplex.stalk K j x).frobeniusEnd)
          ((X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1))⁻¹) =
      coeff n (LinearMap.alternatingCharpolyRevProd S
        (fun i ↦ (WeilComplex.compactlySupportedCohomology K i).frobeniusEnd) 1)⁻¹ :=
  sorry

end WeilComplex

namespace WeilSheaf

/-- The Euler-product form of the trace formula for a Weil sheaf `F` placed in degree zero:
for every `n` and every finite set `s` of closed points containing those of degree at most `n`,

`coeff_n ∏_{x ∈ s} det (1 - T ^ {e_x} F_x ∣ F_x̄)⁻¹`
`  = coeff_n ∏_i det (1 - T F ∣ H_cⁱ(X, F)) ^ ((-1) ^ (i + 1))`,

for a finite set `S` of degrees outside of which `H_cⁱ(X, F)` vanishes. This is
`AlgebraicGeometry.WeilComplex.coeff_prod_inv_alternatingCharpolyRevProd_stalk` for the Weil
complex `F[0]`, whose only cohomology sheaf is `𝓗⁰ = F`. -/
theorem coeff_prod_inv_localPolynomial_stalk (F : WeilSheaf k₀ l X) {S : Finset ℤ}
    (hS : ∀ i ∉ S, Subsingleton (F.compactlySupportedCohomology i).carrier) (n : ℕ)
    (s : Finset X.finitePoints)
    (hs : ∀ x : X.finitePoints, (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 ≤ n → x ∈ s) :
    coeff n (∏ x ∈ s, (((F.stalk x).localPolynomial.comp
        (Polynomial.X ^ (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1) : Polynomial _) :
          (PadicAlgCl l)⟦X⟧)⁻¹) =
      coeff n (LinearMap.alternatingCharpolyRevProd S
        (fun i ↦ (F.compactlySupportedCohomology i).frobeniusEnd) 1)⁻¹ := by
  have h := WeilComplex.coeff_prod_inv_alternatingCharpolyRevProd_stalk (toComplex.obj F)
    (T := {0}) hS
    (fun j hj ↦ WeilComplex.isZero_homologySheaf_singleComplex (Finset.notMem_singleton.1 hj) F)
    n s hs
  refine Eq.trans (congrArg (coeff n) (Finset.prod_congr rfl fun x _ ↦ ?_)) h
  refine congrArg Inv.inv ?_
  rw [LinearMap.alternatingCharpolyRevProd, Finset.prod_singleton, if_pos even_zero,
    FrobeniusModule.localPolynomial, LinearMap.charpolyRev, LinearMap.charpolyRev,
    WeilComplex.stalk, charpoly_frobeniusEnd_stalk_of_iso
      ((toComplexCompHomologySheafIso (k₀ := k₀) (l := l) (X := X)).app F) x]
  rfl

end WeilSheaf

end AlgebraicGeometry
