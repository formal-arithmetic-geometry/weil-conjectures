/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Sheaf.RingTheory.GeneralizedHenselizationAtPrime
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.RingTheory.StrictlyHenselianNormal
import Sheaf.TraceFormula.HenselizationPrimeIndEtale
import Sheaf.RingTheory.IntegralComponentHenselianPermanence
import WeilConjectures.RingTheory.EtaleColimitNormalLocalDomain
import WeilConjectures.AlgebraicGeometry.GabberQuotientLocalizations
import Sheaf.RingTheory.HenselianFiniteEtaleEquivalence
import Sheaf.RingTheory.IndEtaleStability
import WeilConjectures.RingTheory.MapIntoHenselianColimit
import Sheaf.RingTheory.WeaklyEtaleField
import Sheaf.RingTheory.StrictHenselizationFiniteLifts
import Mathlib.FieldTheory.Extension
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Localization.Integral
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Henselian local inertia inside a global separable closure

Source: Stacks Project, pione.tex, Section 0BSD and Lemma 0BSW (lemma-identify-inertia).
(blueprint: lem-dl-a1-henselian-global-inertia-comparison)

The auxiliary maps specialize the recorded strict henselization construction. Its geometric
point takes values in an algebraic closure of the chosen separable residue closure, so no
perfectness assumption on the residue field is imposed.
-/

@[expose] public section
set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped Pointwise

namespace Algebra

/-- The closed geometric point specifying the chosen separable residue closure.
Source: Stacks Project, Section 0BSD, setup preceding Lemma 0BSW.
(blueprint: lem-dl-a1-henselian-global-inertia-comparison) -/
noncomputable def henselianInertiaPoint (A κs : Type u) [CommRing A] [IsLocalRing A]
    [Field κs] [Algebra (ResidueField A) κs] :
    Spec (.of (AlgebraicClosure κs)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom
    (((algebraMap κs (AlgebraicClosure κs)).comp (algebraMap (ResidueField A) κs)).comp
      (residue A)))

/-- The recorded strict henselization at the specified closed geometric point.
Source: Stacks Project, Section 0BSD; the pointed colimit is Tag 04HX.
(blueprint: lem-dl-a1-henselian-global-inertia-comparison) -/
noncomputable abbrev henselianInertiaStrictRing (A κs : Type u) [CommRing A] [IsLocalRing A]
    [Field κs] [Algebra (ResidueField A) κs] : CommRingCat.{u} :=
  Scheme.strictHenselizationRing (henselianInertiaPoint A κs)

/-- The structural map from the base chart into the recorded strict henselization.
Source: Stacks Project, Section 0BSD, compatible henselization diagram.
(blueprint: lem-dl-a1-henselian-global-inertia-comparison) -/
noncomputable def henselianInertiaStrictBase (A κs : Type u) [CommRing A] [IsLocalRing A]
    [Field κs] [Algebra (ResidueField A) κs] : A →+* henselianInertiaStrictRing A κs :=
  ((Scheme.smallStrictHenselizationColimitIso (henselianInertiaPoint A κs)).inv.hom).comp
    (Scheme.SpecPointedEtaleNeighborhood.ι
    { R := CommRingCat.of A
      hom := 𝟙 _
      etale := inferInstance
      pt := CommRingCat.ofHom
        (((algebraMap κs (AlgebraicClosure κs)).comp
          (algebraMap (ResidueField A) κs)).comp (residue A))
      w := Category.comp_id _ }).hom

/-- Evaluation of the colimit at its chosen geometric point, transported through the
canonical comparison of the small and all-affine colimits.
Source: Stacks Project, Section 0BSD and Tag 04HX.
(blueprint: lem-dl-a1-henselian-global-inertia-comparison) -/
noncomputable def henselianInertiaStrictEval (A κs : Type u) [CommRing A] [IsLocalRing A]
    [Field κs] [Algebra (ResidueField A) κs] :
    henselianInertiaStrictRing A κs →+* AlgebraicClosure κs :=
  ((Scheme.smallStrictHenselizationColimitIso (henselianInertiaPoint A κs)).hom ≫
    Scheme.strictHenselizationEval (henselianInertiaPoint A κs)).hom

/-- Compatible local embeddings in the diagram of Section 0BSD, with the specified
map on separable residue fields. This only bundles the diagram's commutativities,
locality and injectivity; it assumes no Galois comparison.
Source: Stacks Project, Section 0BSD, setup preceding Lemma 0BSW.
(blueprint: lem-dl-a1-henselian-global-inertia-comparison) -/
def CompatibleHenselianInertiaEmbeddings
    {A H R T κs : Type u} [CommRing A] [CommRing H] [CommRing R] [CommRing T]
    [IsLocalRing H] [IsLocalRing R] [IsLocalRing T] [Field κs] [Algebra A H]
    (aR : A →+* R) (aT : A →+* T) (r : R →+* κs)
    (j : κs →+* ResidueField T) (h : H →+* T) (c : H →+* R) (i : R →+* T) : Prop :=
  c.comp (algebraMap A H) = aR ∧ h.comp (algebraMap A H) = aT ∧ i.comp c = h ∧
    IsLocalHom h ∧ IsLocalHom c ∧ IsLocalHom i ∧
    Function.Injective h ∧ Function.Injective c ∧ Function.Injective i ∧
    (residue T).comp i = j.comp r

/-- Henselian local inertia is exactly the global inertia subgroup for the chosen prime.
Source: Stacks Project, Section 0BSD and Lemma 0BSW (lemma-identify-inertia).
(blueprint: lem-dl-a1-henselian-global-inertia-comparison)

Proof, following the sixteen steps of the DAG node:
1. The integral closure B is a normal domain with fraction field Ω by
   lem-weil-pbc-integral-closure-algebraic-extension-normal. Its localization T at q
   is normal with the same fraction field by lem-weil-pbc-localization-normal-domain,
   and strictly henselian by lem-weil-pbc-gabber-quotient-localizations with ideal zero.
   Its residue field E is algebraic over κ by reduction of monic equations.
2. The henselization universal property gives the unique local map H to T.
   Use lem-trf-henselization-prime-ind-etale and
   lem-weil-pbc-etale-colimit-normal-local-domain for normality and injectivity of H.
3. The generic fibre of H over A is ind-etale. By lem-weil-pbc-ind-etale-stability,
   lem-weil-pbc-weak-etale-field and lem-weil-pbc-etale-algebra-over-field-product,
   each finitely generated subalgebra is a finite separable field. Thus the generic
   fibre is Frac(H); its map to Ω is injective.
4. Use lem-wf-strict-henselization-finite-lifts for the pointed strict henselization R.
   The same normal-colimit lemma gives its normality and injectivity over H.
5. Embed κs in E by lem-exc-etale-embedding-extension-sepclosed. The unique local lift
   R to T exists by lem-weil-pbc-map-into-henselian-colimit with the prescribed residue.
6. Repeat the generic-fibre argument for R over H. This embeds Frac(R) in Ω.
   By lem-weil-pbc-separable-closure-exists-galois, Ω remains a separable closure
   over Frac(H) and Frac(R).
7. A decomposition-group element acts locally on T. Uniqueness of H to T makes it
   fix H and hence Frac(H).
8. The integral closure C of H in Ω is henselian local by
   lem-trf-integral-component-henselian-permanence: it is an integral domain, hence
   has no idempotents other than zero and one.
9. C equals T inside Ω. Normality gives C contained in T. Conversely B is contained
   in C, and each denominator outside q is outside C's unique maximal ideal, hence
   is a unit. Their maximal ideals therefore contract to the same q in B.
10. An automorphism fixing Frac(H) preserves C and its unique maximal ideal, hence q.
    Together with step 7 this identifies the decomposition group.
11. E over the image of κs is purely inseparable by
    lem-weil-pbc-separable-first-purely-inseparable and lem-pc-sepclosed-finite-sep-trivial.
    Restriction of residue automorphisms to κs has kernel exactly global inertia.
12. An inertia element fixes R by uniqueness of its local lift with the prescribed
    residue map. Conversely an automorphism fixing Frac(R) fixes κs, hence E by
    pure inseparability. This identifies inertia with Aut over Frac(R).
13. By lem-weil-pbc-henselian-finite-etale-equivalence lift any κ-automorphism of κs
    uniquely to all finite Galois residue lifts. Full faithfulness makes them
    compatible, so they induce an automorphism of R and Frac(R).
14. Extend it to Ω by lem-exc-etale-embedding-extension-sepclosed. Normality and
    algebraicity make this embedding onto, since it permutes each finite root set.
    Thus the residue homomorphism is surjective.
15. Pointwise stabilizers of finite subsets of Ω give the Krull neighbourhood bases.
    Their intersections with D and I are exactly the bases for the intrinsic groups,
    giving the two continuous multiplicative equivalences.
16. Lift finite residue generators to R. Their pointwise stabilizer is open and lies
    in the inverse image of the residue stabilizer; this proves continuity. The
    local inertia kernel maps onto I under the identification with D. Uniqueness of
    the residue-compatible lift applies to every chosen compatible embedding.
-/
theorem henselianGlobalInertiaComparison
    (A K Ω H κs : Type u)
    [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    [Algebra A Ω] [IsScalarTower A K Ω]
    (q : Ideal (integralClosure A Ω)) [q.IsMaximal]
    (hq : Ideal.comap (algebraMap A (integralClosure A Ω)) q = maximalIdeal A)
    [CommRing H] [HenselianLocalRing H]
    [Algebra (Localization.AtPrime (maximalIdeal A)) H]
    [Algebra A H] [IsScalarTower A (Localization.AtPrime (maximalIdeal A)) H]
    (hH : IsHenselizationAtPrime' A (maximalIdeal A) H)
    [Field κs] [Algebra (ResidueField A) κs] [IsSepClosure (ResidueField A) κs] :
    ∃ (_ : IsDomain H) (_ : IsDomain (henselianInertiaStrictRing A κs))
      (_ : IsLocalRing (henselianInertiaStrictRing A κs))
      (eH : ResidueField H ≃+* ResidueField A)
      (r : henselianInertiaStrictRing A κs →+* κs),
      (∀ a : A, eH (residue H (algebraMap A H a)) = residue A a) ∧
      Function.Surjective r ∧ RingHom.ker r = maximalIdeal (henselianInertiaStrictRing A κs) ∧
      (algebraMap κs (AlgebraicClosure κs)).comp r = henselianInertiaStrictEval A κs ∧
      (∃ j : κs →+* ResidueField (Localization.AtPrime q),
        ∀ a : A, j (algebraMap (ResidueField A) κs (residue A a)) =
          residue (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) a)) ∧
      ∀ j : κs →+* ResidueField (Localization.AtPrime q),
        (∀ a : A, j (algebraMap (ResidueField A) κs (residue A a)) =
          residue (Localization.AtPrime q) (algebraMap A (Localization.AtPrime q) a)) →
        (∃ (h : H →+* Localization.AtPrime q)
          (c : H →+* henselianInertiaStrictRing A κs)
          (i : henselianInertiaStrictRing A κs →+* Localization.AtPrime q),
          CompatibleHenselianInertiaEmbeddings (henselianInertiaStrictBase A κs)
            (algebraMap A (Localization.AtPrime q)) r j h c i) ∧
        ∀ (h : H →+* Localization.AtPrime q)
          (c : H →+* henselianInertiaStrictRing A κs)
          (i : henselianInertiaStrictRing A κs →+* Localization.AtPrime q),
          CompatibleHenselianInertiaEmbeddings (henselianInertiaStrictBase A κs)
            (algebraMap A (Localization.AtPrime q)) r j h c i →
          ∃ (_ : Algebra (FractionRing H) Ω)
            (_ : Algebra (FractionRing (henselianInertiaStrictRing A κs)) Ω),
            (∀ x : H, algebraMap (FractionRing H) Ω (algebraMap H (FractionRing H) x) =
              Ideal.atPrimeToField q (h x)) ∧
            (∀ x : henselianInertiaStrictRing A κs,
              algebraMap (FractionRing (henselianInertiaStrictRing A κs)) Ω
                (algebraMap _ (FractionRing (henselianInertiaStrictRing A κs)) x) =
                  Ideal.atPrimeToField q (i x)) ∧
            IsSepClosure (FractionRing H) Ω ∧
            ∃ (eD : MulAction.stabilizer (Ω ≃ₐ[K] Ω) q ≃ₜ* (Ω ≃ₐ[FractionRing H] Ω))
              (eI : q.inertia (Ω ≃ₐ[K] Ω) ≃ₜ*
                (Ω ≃ₐ[FractionRing (henselianInertiaStrictRing A κs)] Ω))
              (res : MulAction.stabilizer (Ω ≃ₐ[K] Ω) q →*
                (κs ≃ₐ[ResidueField A] κs)),
              (∀ (σ : MulAction.stabilizer (Ω ≃ₐ[K] Ω) q) (x : Ω), eD σ x = σ.val x) ∧
              (∀ (σ : q.inertia (Ω ≃ₐ[K] Ω)) (x : Ω), eI σ x = σ.val x) ∧
              Continuous res ∧ Function.Surjective res ∧
              (∀ (σ : MulAction.stabilizer (Ω ≃ₐ[K] Ω) q)
                (x : henselianInertiaStrictRing A κs),
                j (res σ (r x)) = residue (Localization.AtPrime q)
                  (Ideal.atPrimeMap q σ.val σ.property (i x))) ∧
              res.ker.map (MulAction.stabilizer (Ω ≃ₐ[K] Ω) q).subtype =
                q.inertia (Ω ≃ₐ[K] Ω) ∧
              ((res.comp eD.symm.toMonoidHom).ker).map
                ((MulAction.stabilizer (Ω ≃ₐ[K] Ω) q).subtype.comp eD.symm.toMonoidHom) =
                  q.inertia (Ω ≃ₐ[K] Ω) := by
  sorry

end Algebra
