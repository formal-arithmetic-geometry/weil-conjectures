/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.ConstructibleSheaf.Refinement
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.AlgebraicGeometry.IsFiniteTypeEtaleModuleSheaf
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import WeilConjectures.ConstructibleSheaf.Biproduct
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
import Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses
import Sheaf.Paper.SfCommonStageWeilCohomology
/-! # Constructible internal Hom from an etale site-perfect complex

Source: Weil conjectures blueprint, sec-six-functors/sk-thm-sf-hom-ctf,
node lem-sf-ext-sheaf-constructible, order 2197
(blueprint: lem-sf-ext-sheaf-constructible); Stacks Project, Tags 08J7, 08JB, 03EM, 03RX.

The two statements retain the arbitrary scheme, the varying local bounds and ranks,
and the absence of a finite Tor-amplitude hypothesis on the second variable.
The recorded finite quotient is placed in the coefficient universe of the etale API.
The etale sheaf encoding uses the existing closed internal Hom and its derived version.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Every cohomology sheaf of internal Hom from an etale site-perfect complex into a
bounded constructible complex is constructible.
Source: blueprint order 2197 (blueprint: lem-sf-ext-sheaf-constructible).

Proof:
1. Choose a bounded cohomology interval for M and a finite constructible immersed
stratification for each of its finitely many nonzero cohomology sheaves. Intersect
these stratifications using lem-weil-pbc-constructible-stratification-intersection
and lemma-constructible-of-refines. The finite-module-value bridge
lem-weil-pbc-finite-locally-constant-module-values identifies the lisse formulations.
2. On a member U of the perfectness cover choose its bounded finite-summand model P.
The restriction clause of lem-weil-pbc-ringed-internal-hom-exact-restriction identifies
restricted RHom with Hom-complex(P,I), for a K-injective representative I of M|U.
3. Evaluation on a finite basis gives Hom(A^r,B)=B^r. The displayed splitting of P^p
exhibits Hom(P^p,B) as the image of an idempotent on B^r, hence an exact functor of B.
Thus its cohomology is Hom(P^p,H^q(I)). This concerns internal sheaf Hom, not global
projectivity of a free sheaf.
4. For a fixed stratum S form V=U times_X S. Exact inverse image preserves the finite
sums and the splitting. Basis evaluation and the retract therefore identify the
pulled-back Hom complex with Hom(P|V,I|V); the identifications commute with both
terms of the Hom differential. No K-injectivity of I|V is asserted.
5. The cohomology of I|V is the pullback of the lisse cohomology on S, by exact inverse
image and lemma-constructible-pullback-finite and -locally-constant.
6. Hom(P^p|V,H^q(I|V)) is finite locally constant: it is the kernel of 1-e on a finite
sum of finite locally constant sheaves. Apply lemma-constructible-flc-biproduct and
the kernel clause of lemma-constructible-flc-serre.
7. Filter the Hom complex by components vanishing for p>t. Its differential preserves
this filtration. It is finite since P is bounded, with single-column quotients
Hom(P^t|V,I|V)[t], whose cohomology is lisse by the preceding calculation.
8. Induct through this finite filtration. The cohomology long exact sequence makes
each middle cohomology an extension of a kernel by a cokernel of lisse sheaves.
Use lem-weil-pbc-complex-ses-homology-long-exact and lemma-constructible-flc-serre.
9. Base change the perfectness cover to S and compose its members' trivializing
covers. The covering base-change and composition lemmas and the finite-value bridge
give finite local constancy on S. The one fixed stratification proves constructibility
in every degree. No finite subcover or uniform bound on the local models is used. -/
theorem constructible_cohomology_derivedHom_of_etale_sitePerfect
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    (K M : DerivedCategoryModule (Padic.coefficientExtensionRing l E n) X)
    (_hK : ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ α : U.I₀,
      ∃ P : CochainComplex (Sheaf (U.X α).smallEtaleTopology
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) ℤ,
        Nonempty (_root_.DerivedCategory.Q.obj P ≅
          (upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))
            (U.f α)).mapDerivedCategory.obj K) ∧
        (∃ a b : ℤ, a ≤ b ∧ ∀ p : ℤ, (p < a ∨ b < p) → IsZero (P.X p)) ∧
        ∀ p : ℤ, ∃ r : ℕ,
          ∃ ι : P.X p ⟶
              (constantSheaf (U.X α).smallEtaleTopology
                (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))).obj
                (ModuleCat.of (Padic.coefficientExtensionRing l E n)
                  (Fin r → Padic.coefficientExtensionRing l E n)),
          ∃ π : (constantSheaf (U.X α).smallEtaleTopology
                (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))).obj
                (ModuleCat.of (Padic.coefficientExtensionRing l E n)
                  (Fin r → Padic.coefficientExtensionRing l E n)) ⟶ P.X p,
            ι ≫ π = 𝟙 (P.X p))
    (_hM : @DerivedCategory.isBoundedConstructible.{u} (Padic.coefficientExtensionRing l E n)
      _ (Padic.finite_coefficientExtensionRing l E n hn) X M) :
    ∀ i : ℤ, @Scheme.IsConstructibleEtaleModuleSheaf.{u} X
      (Padic.coefficientExtensionRing l E n) _ (Padic.finite_coefficientExtensionRing l E n hn)
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) i).obj
        (((derivedHom (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) X).obj
          (op K)).obj M)) := by
  sorry

/-- For a finite locally free sheaf F and a constructible sheaf G, all nonzero-degree
sheaf Ext objects vanish, and the ordinary internal Hom sheaf is constructible.
Source: blueprint order 2197 (blueprint: lem-sf-ext-sheaf-constructible).

Proof:
10. Choose an etale cover on which F is a finite sum of copies of the coefficient
sheaf. For G in degree zero choose a K-injective representative I. The internal Hom
complex from F[0] is I^r by basis evaluation. Its cohomology vanishes in every degree
j different from zero, including negative degrees. These evaluation identifications
commute with restrictions, so the sheaf axiom descends vanishing and identifies H^0
with the ordinary internal Hom. Apply the preceding nine-step fixed-stratification
argument to F[0],G[0] to obtain constructibility of that degree-zero sheaf. Rank zero
and the empty scheme are included. -/
theorem extSheaf_vanish_and_hom_constructible_of_etale_finiteLocallyFree
    (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X : Scheme.{u})
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)))
    (_hF : ∃ U : Scheme.Cover.{u} Scheme.etalePrecoverage X, ∀ α : U.I₀,
      ∃ r : ℕ, Nonempty
        ((upperStar (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) (U.f α)).obj F ≅
          (constantSheaf (U.X α).smallEtaleTopology
            (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))).obj
            (ModuleCat.of (Padic.coefficientExtensionRing l E n)
              (Fin r → Padic.coefficientExtensionRing l E n))))
    (_hG : @Scheme.IsConstructibleEtaleModuleSheaf.{u} X
      (Padic.coefficientExtensionRing l E n) _ (Padic.finite_coefficientExtensionRing l E n hn) G) :
    (∀ j : ℤ, j ≠ 0 → IsZero
      ((_root_.DerivedCategory.homologyFunctor
        (Sheaf X.smallEtaleTopology
          (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n))) j).obj
        (((derivedHom (ModuleCat.{u + 1} (Padic.coefficientExtensionRing l E n)) X).obj
          (op ((_root_.DerivedCategory.singleFunctor _ 0).obj F))).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj G)))) ∧
    @Scheme.IsConstructibleEtaleModuleSheaf.{u} X
      (Padic.coefficientExtensionRing l E n) _ (Padic.finite_coefficientExtensionRing l E n hn)
      ((ihom F).obj G) := by
  sorry

end AlgebraicGeometry.Etale
