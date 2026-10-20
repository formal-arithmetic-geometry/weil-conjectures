/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NX
-/
module

public import Sheaf.AlgebraicGeometry.CohomologicalDimension
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension
import Sheaf.FieldTheory.FiniteFieldAbsoluteGalois
import Sheaf.AlgebraicGeometry.EllCohomologicalDimensionComparison
import Sheaf.RepresentationTheory.ProfiniteCyclicTorsionCohomology
import WeilConjectures.AlgebraicGeometry.Sites.GaloisModule
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.CategoryTheory.Sites.Point.Torsion

/-!
# Cohomological dimension of the base field

Source: blueprint `sec-six-functors-basics/sk-lem-base-field-cd`, order 1507;
Stacks Project, Tags 03QQ and 010T (blueprint: sk-lem-base-field-cd).
The dimension and its local prime-power torsion convention are those of `sk-def-cd`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.ProEtale

private theorem finite_field_torsion_bound (K : Type u) [Field K] [Finite K] :
    Scheme.HasTorsionEtaleCohomologicalDimensionLE (Spec (.of K)) 1 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let Ω := SeparableClosure K
  let G := Gal(Ω / K)
  let Z := GrpCat.of (Multiplicative ℤ)
  obtain ⟨τ, _, _, e, he⟩ := finiteField_absoluteGaloisGroup K Ω
  have hpow (z : ℤ) : e (τ ^ z) =
      ProfiniteGrp.ProfiniteCompletion.etaFn Z (Multiplicative.ofAdd z) := by
    rw [map_zpow, he]
    have hz : (Multiplicative.ofAdd (1 : ℤ)) ^ z = Multiplicative.ofAdd z := by
      apply Multiplicative.toAdd.injective
      change z • (1 : ℤ) = z
      simp
    exact ((ProfiniteGrp.ProfiniteCompletion.eta Z).hom.map_zpow
      (Multiplicative.ofAdd (1 : ℤ)) z).symm.trans (congrArg _ hz)
  have hdense : DenseRange (fun z : ℤ ↦ τ ^ z) := by
    have h := (ProfiniteGrp.ProfiniteCompletion.denseRange Z).comp
      (show Function.Surjective (Multiplicative.ofAdd : ℤ → Z) from
        fun z ↦ ⟨z.toAdd, rfl⟩).denseRange
      continuous_of_discreteTopology
    have h' := e.symm.surjective.denseRange.comp h e.symm.continuous
    change DenseRange (fun z : ℤ ↦ e.symm
      (ProfiniteGrp.ProfiniteCompletion.etaFn Z (Multiplicative.ofAdd z))) at h'
    convert h' using 1
    funext z
    rw [← hpow, e.symm_apply_apply]
  have hquot (N : ℕ) (hN : 0 < N) :
      ∃ χ : G →ₜ* Multiplicative (ZMod N), χ τ = Multiplicative.ofAdd 1 := by
    let : NeZero N := ⟨Nat.ne_of_gt hN⟩
    let P := ProfiniteGrp.of (Multiplicative (ZMod N))
    let f : Z ⟶ GrpCat.of P := GrpCat.ofHom (Int.castAddHom (ZMod N)).toMultiplicative
    let χ := ProfiniteGrp.ProfiniteCompletion.lift f
    refine ⟨χ.hom.comp (ContinuousMonoidHom.toContinuousMonoidHom e), ?_⟩
    change χ (e τ) = _
    rw [he]
    have hc := CategoryTheory.ConcreteCategory.congr_hom
      (ProfiniteGrp.ProfiniteCompletion.lift_eta f)
      (Multiplicative.ofAdd (1 : ℤ))
    change χ (ProfiniteGrp.ProfiniteCompletion.etaFn Z (Multiplicative.ofAdd (1 : ℤ))) =
      Multiplicative.ofAdd ((1 : ℤ) : ZMod N) at hc
    simpa only [Int.cast_one] using hc
  intro F hF q hq
  let M := (Scheme.etaleSheafEquivDiscreteModule K Ω).functor.obj F
  have ht : ∀ x : M.obj.V, IsOfFinAddOrder x :=
    (Scheme.galoisPoint K Ω).isAddTorsion_sheafFiber hF
  have hH : Subsingleton (CategoryTheory.Sheaf.H F q) := by
    have := DiscreteModule.subsingleton_H_of_dense_generator_cyclic_quotients.{u, u + 1}
      τ hdense hquot M ht (by omega : 2 ≤ q)
    exact (Scheme.sheafHAddEquivGaloisH K Ω F q).injective.subsingleton
  obtain ⟨c⟩ := Scheme.nonempty_sheafH_extDerivedIso (Spec (.of K)) q
  exact AddCommGrpCat.isZero_iff_subsingleton.mp
    ((AddCommGrpCat.isZero_iff_subsingleton.mpr hH).of_iso (c.app F).symm)


/-- The `ℓ`-cohomological dimension of an algebraically closed field is zero, and
that of a finite field is at most one. There is no restriction on the characteristic.

Source: blueprint `sec-six-functors-basics/sk-lem-base-field-cd`, order 1507;
Stacks Project, Tags 03QQ and 010T (blueprint: sk-lem-base-field-cd).

Proof: For an algebraically closed field, use the separably closed torsion étale
bound and the étale/pro-étale comparison. The value lies in `WithTop ℕ`, so the
bound by zero gives equality by `zero_le`.

For a finite field, choose its separable closure. The existing additive equivalence
of abelian étale sheaves with discrete Galois modules identifies sheaf cohomology
with `DiscreteModule.H`, and a torsion sheaf has torsion geometric fibre. The
Frobenius theorem identifies the Galois group with the profinite completion of ℤ.
Density of ℤ gives a dense integer generator; the universal property of the
completion extends reduction modulo every positive integer to a continuous cyclic
quotient sending Frobenius to one.

Apply `subsingleton_H_of_dense_generator_cyclic_quotients`. Its proof refines the
finite period a of a smooth coinduced function to the cyclic quotient of order ae,
where e kills its finite image. The full norm is e times the period norm, hence
zero; finite cyclic partial sums give a primitive. The coinduced short exact
sequence gives vanishing in degree two, and its torsion quotient allows dimension
shifting in every higher degree. This realizes the finite cyclic refinement and
norm cancellation without constructing the filtered colimit of periodic complexes.
Transfer this vanishing through the field/Galois and sheaf-H/Ext-derived comparison,
then apply the torsion étale/pro-étale bound with the identity of the affine spectrum.
No common exponent for the whole torsion module and no characteristic restriction
are used.
-/
theorem cohomologicalDimension_baseField (ℓ : ℕ) (hℓ : Nat.Prime ℓ)
    (K : Type u) [Field K] :
    (IsAlgClosed K → cohomologicalDimension ℓ hℓ (Spec (.of K)) = 0) ∧
      (Finite K → cohomologicalDimension ℓ hℓ (Spec (.of K)) ≤ 1) := by
  constructor
  · intro hK
    let : IsAlgClosed K := hK
    apply le_antisymm _ zero_le
    exact (ellCohomologicalDimension_etale_comparison ℓ hℓ (Spec (.of K))
      (CategoryTheory.CategoryStruct.id (Spec (.of K))) 0).2.2.2
      (Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed K)
  · intro hK
    let : Finite K := hK
    exact (ellCohomologicalDimension_etale_comparison ℓ hℓ (Spec (.of K))
      (CategoryTheory.CategoryStruct.id (Spec (.of K))) 1).2.2.2 (finite_field_torsion_bound K)

end AlgebraicGeometry.ProEtale
