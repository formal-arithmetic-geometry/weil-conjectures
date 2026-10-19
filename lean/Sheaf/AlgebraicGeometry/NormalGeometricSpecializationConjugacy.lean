/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q44
-/
module

public import Sheaf.AlgebraicGeometry.StrictLocalizationPointChange
public import Sheaf.RingTheory.ExcellentRing
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Etale.Field
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.RingTheory.StrictHenselizationTriples
import Sheaf.Paper.StrictHenselizationFunctoriality
import Sheaf.RingTheory.EtaleColimitNormalLocalDomain
import Sheaf.RingTheory.IndEtaleStability
import Sheaf.RingTheory.WeaklyEtaleField
import Sheaf.RingTheory.MapIntoHenselianColimit

/-! # Conjugacy of generic-to-closed geometric specializations

Source: ILO, Travaux de Gabber, Expose XVII, proof of Lemma 3.5.8 and
Proposition 3.6.1, pp. 277-278
(blueprint: lem-per-normal-geometric-specialization-conjugacy).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Specializations exist, are conjugate under the generic geometric automorphisms,
and intertwine every closed geometric automorphism, also for different generic closures.
Source: ILO XVII 3.5.8 and 3.6.1, pp. 277-278
(blueprint: lem-per-normal-geometric-specialization-conjugacy).

Proof (the six DAG steps):
1. Write S = Spec A, K = Frac A, and B for the strict henselization at barS.
By lem-weil-pbc-etale-local-ring-triples and lem-weil-pbc-strict-henselization-triples,
B is a local filtered colimit of etale A-algebras, strictly henselian, with residue
field the separable closure of kappa(s) in the chosen closed algebraic closure.
Use lem-weil-pbc-strict-henselization-functoriality for the pointed residue identification.
At the generic point these same results identify the strict localization with Spec K^s.
By lem-weil-pbc-etale-colimit-normal-local-domain, B is a domain and A embeds into B.
2. Invert the nonzero elements of A in B. By lem-weil-pbc-ind-etale-stability and
lem-weil-pbc-weak-etale-field this domain C is weakly etale over K and every finitely
generated K-subalgebra is finite etale. By lem-weil-pbc-etale-algebra-over-field-product,
it is a finite product of separable fields; as a nonzero subring of a domain it has
one factor. Each nonzero element of C therefore has an inverse in K[c], so C is the
field F = Frac B, separable algebraic over K. Specializations are exactly K-embeddings
F into K^s, restricted to B, by contravariance of affine spectra.
3. Choose an algebraic closure L of F. It is algebraic over K: the finitely many
coefficients of an equation lie in a finite K-extension, and the finite span of
powers of the root gives a polynomial over K. By lem-pc-algebraic-closure-exists-unique,
L is K-isomorphic to the chosen generic algebraic closure. The image of F lies in
K^s by def-weil-pbc-relative-separable-closure. Its restriction to B gives existence.
4. For two embeddings i,i' of F into the generic closure, that closure is an algebraic
closure of F under either embedding. Uniqueness of algebraic closures over F gives
an automorphism a with a i = i'. It fixes K, preserves K^s, and gives the required
geometric automorphism and the equation t' = t composed with sigma on strict localizations.
No normality of the intermediate extension F/K is required.
5. A closed geometric automorphism preserves the separable residue closure.
Apply lem-weil-pbc-map-into-henselian-colimit to B with this residue action to obtain
the unique local A-endomorphism. Apply it to the inverse residue action and use
uniqueness to see it is an automorphism. This is the canonical point-change map
by its pointed characterization. Composing any t with it is another specialization;
step 4 supplies sigma and the compatibility equation.
6. For two different chosen generic closures, each is an algebraic closure of F via
its supplied specialization. Uniqueness over F gives an isomorphism between them,
fixing K and identifying their separable closures. Taking spectra gives the cross-choice
conjugacy equation. Replacing the second specialization by its composite with the
closed-point action gives the last equation. Step 3 supplies existence for both choices. -/
theorem normal_geometric_specialization_conjugacy
    (S : Scheme.{u}) [IsAffine S] [IsNoetherian S] [IsIntegral S]
    [HenselianLocalRing Γ(S, ⊤)]
    (_hExcellent : IsExcellent Γ(S, ⊤))
    (_hNormal : ∀ (p : Ideal Γ(S, ⊤)) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (s : S) (_hs : S.isoSpec.hom s = IsLocalRing.closedPoint Γ(S, ⊤))
    {Ωη₁ Ωη₂ Ωs : Type u}
    [Field Ωη₁] [IsAlgClosed Ωη₁] [Field Ωη₂] [IsAlgClosed Ωη₂]
    [Field Ωs] [IsAlgClosed Ωs]
    [Algebra (S.residueField (genericPoint S)) Ωη₁]
    [IsAlgClosure (S.residueField (genericPoint S)) Ωη₁]
    [Algebra (S.residueField (genericPoint S)) Ωη₂]
    [IsAlgClosure (S.residueField (genericPoint S)) Ωη₂]
    [Algebra (S.residueField s) Ωs] [IsAlgClosure (S.residueField s) Ωs]
    (barη₁ : Spec (.of Ωη₁) ⟶ S) (barη₂ : Spec (.of Ωη₂) ⟶ S)
    (barS : Spec (.of Ωs) ⟶ S)
    (_hη₁ : barη₁ = Spec.map (CommRingCat.ofHom
      (algebraMap (S.residueField (genericPoint S)) Ωη₁)) ≫
        S.fromSpecResidueField (genericPoint S))
    (_hη₂ : barη₂ = Spec.map (CommRingCat.ofHom
      (algebraMap (S.residueField (genericPoint S)) Ωη₂)) ≫
        S.fromSpecResidueField (genericPoint S))
    (_hS : barS = Spec.map (CommRingCat.ofHom (algebraMap (S.residueField s) Ωs)) ≫
      S.fromSpecResidueField s) :
    Nonempty {t : strictHenselizationScheme barη₁ ⟶ strictHenselizationScheme barS //
      t ≫ strictHenselizationStructuralMap barS = strictHenselizationStructuralMap barη₁} ∧
    Nonempty {t : strictHenselizationScheme barη₂ ⟶ strictHenselizationScheme barS //
      t ≫ strictHenselizationStructuralMap barS = strictHenselizationStructuralMap barη₂} ∧
    (∀ t t' : {t : strictHenselizationScheme barη₁ ⟶ strictHenselizationScheme barS //
        t ≫ strictHenselizationStructuralMap barS = strictHenselizationStructuralMap barη₁},
      ∃ (σ : Aut (Spec (.of Ωη₁))) (hσ : σ.hom ≫ barη₁ = barη₁),
        t'.val = strictLocalizationPointChange barη₁ barη₁ σ hσ ≫ t.val) ∧
    (∀ (τ : Aut (Spec (.of Ωs))) (hτ : τ.hom ≫ barS = barS)
      (t : {t : strictHenselizationScheme barη₁ ⟶ strictHenselizationScheme barS //
        t ≫ strictHenselizationStructuralMap barS = strictHenselizationStructuralMap barη₁}),
      ∃ (σ : Aut (Spec (.of Ωη₁))) (hσ : σ.hom ≫ barη₁ = barη₁),
        t.val ≫ strictLocalizationPointChange barS barS τ hτ =
          strictLocalizationPointChange barη₁ barη₁ σ hσ ≫ t.val) ∧
    (∀ (t₁ : {t : strictHenselizationScheme barη₁ ⟶ strictHenselizationScheme barS //
        t ≫ strictHenselizationStructuralMap barS = strictHenselizationStructuralMap barη₁})
      (t₂ : {t : strictHenselizationScheme barη₂ ⟶ strictHenselizationScheme barS //
        t ≫ strictHenselizationStructuralMap barS = strictHenselizationStructuralMap barη₂}),
      ∃ (σ : Spec (.of Ωη₂) ≅ Spec (.of Ωη₁)) (hσ : σ.hom ≫ barη₁ = barη₂),
        t₂.val = strictLocalizationPointChange barη₂ barη₁ σ hσ ≫ t₁.val) ∧
    (∀ (τ : Aut (Spec (.of Ωs))) (hτ : τ.hom ≫ barS = barS)
      (t₁ : {t : strictHenselizationScheme barη₁ ⟶ strictHenselizationScheme barS //
        t ≫ strictHenselizationStructuralMap barS = strictHenselizationStructuralMap barη₁})
      (t₂ : {t : strictHenselizationScheme barη₂ ⟶ strictHenselizationScheme barS //
        t ≫ strictHenselizationStructuralMap barS = strictHenselizationStructuralMap barη₂}),
      ∃ (σ : Spec (.of Ωη₂) ≅ Spec (.of Ωη₁)) (hσ : σ.hom ≫ barη₁ = barη₂),
        t₂.val ≫ strictLocalizationPointChange barS barS τ hτ =
          strictLocalizationPointChange barη₂ barη₁ σ hσ ≫ t₁.val) := by
  sorry

end AlgebraicGeometry.Scheme
