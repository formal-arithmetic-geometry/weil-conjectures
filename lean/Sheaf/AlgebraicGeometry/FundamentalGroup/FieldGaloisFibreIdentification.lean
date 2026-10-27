/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q67
-/
module

public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction
public import Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber
public import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import Sheaf.GroupTheory.CompleteGroupForgetfulAutomorphisms
import WeilConjectures.FieldTheory.EtaleFieldGaloisClassification
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Sheaf.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalence

/-! # The field Galois group and the finite étale geometric fibre

Source: Stacks Project, Tags 0BNE and 0BQ9, `pione.tex`,
lemma-fundamental-group-Galois-group and remark-variance
(blueprint: lem-dl-a1-field-galois-fibre-identification).

The fundamental group is expressed in its finite-etale fibre-functor model, `Aut (fiber s)`.
The recorded FLC model is identified with it by the fibre-compatible equivalence
`exists_finiteEtale_flc_equivalence_sheaf`. No new fibre functor or topology is defined.
The closure hypotheses are the components of `IsSepClosure` and `IsAlgClosure`, via
`isSepClosure_iff` and `isAlgClosure_iff`; in particular no perfectness is assumed.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The canonical field fundamental-group identification, including unique extension of
Galois automorphisms and the natural, equivariant comparison of the two point sets.
Source: Stacks Project, Tags 0BNE and 0BQ9, `pione.tex`,
lemma-fundamental-group-Galois-group and remark-variance
(blueprint: lem-dl-a1-field-galois-fibre-identification).

Proof, following the eight DAG steps:
1. `lem-kun-sep-closed-finite-extension-purely-inseparable` makes each finite simple
extension of Ks inside Ω purely inseparable. Algebraic-closure uniqueness extends σ;
Frobenius injectivity gives uniqueness, also giving multiplicativity of extension.
2. `lem-weil-pbc-separable-closure-exists-galois` makes Ks/K Galois. By
`lem-weil-pbc-etale-fibre-discrete-separable-points`, a finite etale Q is a finite disjoint
union of spectra of finite separable fields. Every embedding of such a field into Ω lands
in Ks, since its separable minimal polynomials split there. This gives the bijections b,
including for the empty scheme. Postcomposition gives their naturality.
3. Contravariance of Spec gives the homomorphism j, with the displayed action. The equality
between the extended automorphism and σ on Ks gives the displayed equivariance of b.
4. `lem-exc-galois-krull-finite-limit` identifies Gal(Ks/K) with the closed compatibility
subgroup of a product of finite groups; `lem-galois-closed-subgroup-product-finite-groups`
therefore makes it profinite in precisely the Krull topology.
5. Apply the compact case of `lem-sfb-complete-group-forgetful-automorphisms`. Its open
coset orbits are finite by compactness.
6. `lem-exc-etale-field-galois-classification` represents those orbits by finite separable
fields. Transport a natural fibre automorphism through b to those orbits. Full faithfulness
makes it natural on the orbit category, so reconstruction gives a unique σ. Naturality on
component inclusions extends the formula to every Q. This proves bijectivity of j.
7. A point stabilizer fixes a finite subfield, so it is Krull-open. Conversely each open
subgroup occurs as the stabilizer in its represented coset orbit. Thus j and its inverse
are continuous for the existing evaluation topology.
8. `thm-galois-lc-etale` identifies this finite-etale fibre model with the FLC-stalk model
of `def-galois-fibre-functor`, preserving evaluation topologies and actions. -/
theorem field_galois_fibre_identification
    (K Ks Ω : Type u) [Field K] [Field Ks] [Field Ω]
    [Algebra K Ks] [IsSepClosed Ks] [Algebra.IsSeparable K Ks]
    [Algebra Ks Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic Ks Ω]
    [Algebra K Ω] [IsScalarTower K Ks Ω] :
    ∃ j : Gal(Ks/K) ≃ₜ* Aut (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))),
      (∀ σ : Gal(Ks/K), ∃! τ : Gal(Ω/K),
        ∀ a : Ks, τ (algebraMap Ks Ω a) = algebraMap Ks Ω (σ a)) ∧
      (∀ (σ : Gal(Ks/K)) (τ : Gal(Ω/K)),
        (∀ a : Ks, τ (algebraMap Ks Ω a) = algebraMap Ks Ω (σ a)) →
        ∀ (Q : (Spec (.of K)).FiniteEtale)
          (t : (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))).obj Q),
          ((j σ).hom.app Q t).left = Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ t.left) ∧
      (∃ b : ∀ Q : (Spec (.of K)).FiniteEtale,
          (fiber (pointOfAlgebra Ks (𝟙 (Spec (.of K))))).obj Q ≃
            (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))).obj Q,
        (∀ (Q : (Spec (.of K)).FiniteEtale)
          (t : (fiber (pointOfAlgebra Ks (𝟙 (Spec (.of K))))).obj Q),
          (b Q t).left = Spec.map (CommRingCat.ofHom (algebraMap Ks Ω)) ≫ t.left) ∧
        (∀ (Q Q' : (Spec (.of K)).FiniteEtale) (f : Q ⟶ Q')
          (t : (fiber (pointOfAlgebra Ks (𝟙 (Spec (.of K))))).obj Q),
          b Q' ((fiber (pointOfAlgebra Ks (𝟙 (Spec (.of K))))).map f t) =
            (fiber (pointOfAlgebra Ω (𝟙 (Spec (.of K))))).map f (b Q t)) ∧
        (∀ (σ : Gal(Ks/K)) (Q : (Spec (.of K)).FiniteEtale)
          (t : (fiber (pointOfAlgebra Ks (𝟙 (Spec (.of K))))).obj Q),
          b Q ((galoisToAut (𝟙 (Spec (.of K))) σ).hom.app Q t) =
            (j σ).hom.app Q (b Q t))) := by
  sorry

end AlgebraicGeometry.Scheme.FiniteEtale
