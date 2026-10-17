/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.CurveTestDatum
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Coefficients

/-!
# Base change towards spectra of fields

Let `K` be a field and `X` a scheme of finite type over `K`. We show that the structure morphism
`a : X ⟶ Spec K` satisfies the base-change property `BC(a, Λ, q)` universally, in every degree
`q`, for a coefficient ring `Λ` killed by an integer `n` invertible in `K`
(`AlgebraicGeometry.Etale.universalBaseChangeProperty_of_field`, blueprint `lem-kun-0f1i`): for
every base change `X' = X ×_K S' ⟶ S'`, every quasi-compact quasi-separated `g : T ⟶ S'` and
every sheaf `F` of `Λ`-modules on `T_ét`, the exchange morphism `p'⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F`
is an isomorphism.

The proof is an induction on `q`, as for the smooth base change theorem
(`AlgebraicGeometry.Etale.universalBaseChangeProperty_of_smoothOfRelativeDimension_one`):

* in degree zero, after replacing `K` by its perfect closure and `X` by its reduction (étale
  cohomology is invariant under universal homeomorphisms) the morphism is flat, of finite
  presentation, with geometrically reduced fibres, and the degree-zero base change theorem
  `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero` applies;
* in degree `q ≥ 1`, a first failure is witnessed, by
  `AlgebraicGeometry.Etale.exists_isPullback_not_isZero_higherDirectImage` (Stacks 0F08), by a
  nonzero higher direct image `R^q h_* (Λ/dΛ)` along the geometric generic fibre `h` of a base
  change of `a` to an affine integral scheme with algebraically closed function field; this
  higher direct image vanishes by blueprint `lem-kun-0f1i-normal`
  (`AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_isAlgClosed`).

## Main statements

- `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_field`: degree zero.
- `AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_isAlgClosed`
  (`lem-kun-0f1i-normal`).
- `AlgebraicGeometry.Etale.universalBaseChangeProperty_of_field` (`lem-kun-0f1i`).

## References

- Stacks Project, Lemma 0F1I, <https://stacks.math.columbia.edu/tag/0F1I>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Degree zero of blueprint `lem-kun-0f1i`: for a scheme `X` locally of finite type over a field
`K`, the structure morphism `a : X ⟶ Spec K` satisfies the degree-zero base-change property
universally, for every coefficient ring.

After the base change to the perfect closure of `K` and the passage to the reduction, both
universal homeomorphisms which do not change the étale sites, the morphism is flat, locally of
finite presentation and has geometrically reduced fibres (blueprint
`lem-kun-geometric-reduced-perfect`), so that the degree-zero base change theorem (blueprint
`lem-kun-0eys`, `AlgebraicGeometry.Etale.universalBaseChangeProperty_zero`) applies. -/
theorem Etale.universalBaseChangeProperty_zero_of_field {K : Type u} [Field K]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] :
    Etale.UniversalBaseChangeProperty Λ a 0 :=
  sorry

/-- Blueprint `lem-kun-0f1i-normal`: the normal integral case.

Let `K` be a field, `n` an integer invertible in `K` and killing `Λ`, and `X` a scheme of finite
type over `K`. Let `X' = X ×_K S'` be the base change of `X` to an affine integral scheme `S'`
with algebraically closed function field, let `L` be an algebraically closed extension of that
function field, and let `h : Y ⟶ X'` be the fibre of `X' ⟶ S'` over the resulting geometric
generic point `Spec L ⟶ S'`. Then `R^q h_* (Λ/dΛ) = 0` for all `q ≥ 1` and `d ∣ n`.

The blueprint takes `L` to be the function field itself; the general algebraically closed
extension is what `AlgebraicGeometry.Etale.exists_isPullback_not_isZero_higherDirectImage`
produces. -/
theorem Etale.isZero_higherDirectImage_constantModSheaf_of_isAlgClosed {K : Type u} [Field K]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    (n : ℕ) (hn : IsUnit (n : K)) (hΛ : (n : Λ) = 0)
    {S' X' : Scheme.{u}} (s : S' ⟶ Spec (.of K)) (b : X' ⟶ X) (p' : X' ⟶ S')
    (hpb : IsPullback b p' a s) [IsAffine S'] [IsIntegral S']
    (hnorm : ∀ x : S', IsIntegrallyClosed (S'.presheaf.stalk x))
    [IsAlgClosed S'.functionField] {L : Type u} [Field L] [IsAlgClosed L]
    (i : S'.functionField ⟶ CommRingCat.of L) {Y : Scheme.{u}} (e : Y ⟶ Spec (.of L))
    (h : Y ⟶ X') (sq : IsPullback e h (Spec.map i ≫ S'.fromSpecStalk (genericPoint S')) p')
    (d : ℕ) (hd : d ∣ n) (q : ℤ) (hq : 1 ≤ q) :
    IsZero (Etale.higherDirectImage Λ h q (Etale.constantModSheaf Λ Y d)) :=
  sorry

/-- Blueprint `lem-kun-0f1i`: base change towards spectra of fields.

Let `K` be a field, `X` a scheme of finite type over `K` with structure morphism
`a : X ⟶ Spec K`, and `n` an integer invertible in `K` which kills the coefficient ring `Λ`.
Then `BC(a, Λ, q)` holds universally in every degree `q`: for every base change
`p' : X' = X ×_K S' ⟶ S'`, every quasi-compact quasi-separated `g : T ⟶ S'` and every sheaf `F`
of `Λ`-modules on `T_ét`, the exchange morphism `p'⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` for the
cartesian square `Y = X' ×_{S'} T` is an isomorphism.

The proof is an induction on `q`: degree zero is
`AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_field`, and a first failure in
degree `q ≥ 1` would produce, by
`AlgebraicGeometry.Etale.exists_isPullback_not_isZero_higherDirectImage` (blueprint
`lem-kun-0f1d`), a nonzero higher direct image which vanishes by
`AlgebraicGeometry.Etale.isZero_higherDirectImage_constantModSheaf_of_isAlgClosed`. -/
@[stacks 0F1I]
theorem Etale.universalBaseChangeProperty_of_field {K : Type u} [Field K] {X : Scheme.{u}}
    (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a] (n : ℕ)
    (hn : IsUnit (n : K)) (hΛ : (n : Λ) = 0) (q : ℤ) :
    Etale.UniversalBaseChangeProperty Λ a q :=
  sorry

end AlgebraicGeometry
