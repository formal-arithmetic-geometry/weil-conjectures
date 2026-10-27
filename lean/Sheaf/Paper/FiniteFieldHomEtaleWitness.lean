/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q68
-/
module

public import Sheaf.Paper.FiniteFieldInternalHomFiniteness
public import Sheaf.Paper.FiniteDiscreteOrdinaryEncoding
public import Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules
public import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules
import Sheaf.AlgebraicGeometry.ConstantFieldTorBounds
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # A bounded etale model for finite-field internal Hom

Source: Bhatt--Scholze, Lemma 6.7.13, Definition 6.5.1 and Lemma 6.3.16;
Stacks Tag 09AL (blueprint: lem-sfb-finite-field-hom-etale-witness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Canonical presentation transport from fixed scalars to internal modules.
The chosen encoding is normalized on every constant section; its forward functor
is the specified section-action equivalence followed by scalar restriction.
Thus its inverse is determined up to the unique adjunction isomorphism used here.
Source: Stacks Tags 00YV and 03CY; Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-sfb-finite-field-hom-etale-witness). -/
def finiteFieldFixedToInternal (A : Type u) [Field A] [Finite A] (X : Scheme.{u}) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (finiteFieldCondensedRing A) X)) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := discreteTopology_bot A
  exact (Classical.choice (FiniteDiscreteOrdinary.encoding_exists A X)).fixedDerived.inverse

/-- The canonical etale comparison inverse image, followed by normalized coefficient
presentation transport. It is the ordinary exact inverse image, with no completion.
Source: Stacks Tags 099R and 09AL; Bhatt--Scholze, Definition 6.5.1
(blueprint: lem-sfb-finite-field-hom-etale-witness). -/
def finiteFieldEtalePullback (A : Type u) [Field A] [Finite A] (X : Scheme.{u}) :
    DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A))) ⥤
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (finiteFieldCondensedRing A) X)) :=
  (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).mapDerivedCategory ⋙
    finiteFieldFixedToInternal A X

/-- The ambient relative derived internal Hom of the two specified inverse images.
Source: Bhatt--Scholze, Lemma 6.7.13 and Definition 6.5.1
(blueprint: lem-sfb-finite-field-hom-etale-witness). -/
def finiteFieldEtaleInternalHom (A : Type u) [Field A] [Finite A] (X : Scheme.{u})
    (C_P C_Q : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A)))) :=
  ((CondensedRing.derivedHom (finiteFieldCondensedRing A) X).obj
    (op ((finiteFieldEtalePullback A X).obj C_P))).obj
      ((finiteFieldEtalePullback A X).obj C_Q)

/-- The pulled-back inputs and their ambient internal Hom are bounded constructible.
A single bounded etale representative of that Hom has every Tor interval containing
its cohomology, and hence finite Tor amplitude. Fixed-scalar sheaves are the retained
presentation of modules over the constant ring sheaf in the recorded dependency.

Source: Bhatt--Scholze, Lemma 6.7.13 with R=A and m=0, Definition 6.5.1,
Lemma 6.3.16; Stacks Tag 09AL; the Tor-amplitude-detected paragraph of
sk-cor-pe-finite-tor-comparison-noetherian.proof.md
(blueprint: lem-sfb-finite-field-hom-etale-witness).

Proof:
1. The field A is Noetherian. Apply sk-thm-pe-constructible-comparison to C_P
and C_Q. Exactness from det-pe-classical-sheaves-modules and
lem-weil-pbc-exact-functor-complex-cohomology preserves their bounds. A finite
affine cover of the Noetherian scheme X refines their affine-local stratifications
to one finite constructible locally closed stratification. Finite generation over
A is finite dimensionality, so these are the finite constant scalar models of
sk-def-sfb-constructible. The normalized coefficient encoding keeps this meaning.
2. Apply lem-sfb-finite-field-internal-hom-finiteness to these inverse images.
Its geometric and coefficient hypotheses are exactly those stated here; neither
input is assumed site-perfect. This gives bounded constructibility of the Hom.
3. Essential surjectivity in sk-thm-pe-constructible-comparison gives a bounded
constructible etale antecedent C of the Hom. This uses descent of the object,
without claiming that inverse image commutes with internal Hom.
4. Choose bounds for C and use lem-sfb-bounded-representative, namely
DerivedCategory.exists_iso_Q_obj_of_isGE_of_isLE, to choose D and Q(D) isomorphic
to C. Transport the constructible cohomology and compose the pulled-back
isomorphism with the descent isomorphism. Fix D before choosing a,b below.
5. For any ordered cohomological interval of the Hom, apply
lem-sfb-constant-field-tor-bounds. Tensoring the descent isomorphism preserves
cohomology. The reflection direction of det-pe-finite-tor-comparison-noetherian
then gives this same Tor interval for C, hence for Q(D). This is the ordinary
K-flat tensor tested against every degree-zero etale module sheaf. Boundedness
of the Hom supplies one ordered interval, proving the final finite-Tor clause.
The base field may be arbitrary of the indicated characteristic. -/
theorem finiteField_hom_etale_witness
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (A : Type u) [Field A] [Finite A] [CharP A l]
    (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [CompactSpace X] [QuasiSeparatedSpace X]
    (C_P C_Q : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} A))))
    (hP_bounded : DerivedCategory.TStructure.t.bounded C_P)
    (hQ_bounded : DerivedCategory.TStructure.t.bounded C_Q)
    (hP_cons : ∀ q : ℤ, Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj C_P))
    (hQ_cons : ∀ q : ℤ, Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf
      ((DerivedCategory.homologyFunctor _ q).obj C_Q)) :
    constantModelBoundedConstructible (finiteFieldCondensedRing A) X
      ((finiteFieldEtalePullback A X).obj C_P) ∧
    constantModelBoundedConstructible (finiteFieldCondensedRing A) X
      ((finiteFieldEtalePullback A X).obj C_Q) ∧
    constantModelBoundedConstructible (finiteFieldCondensedRing A) X
      (finiteFieldEtaleInternalHom A X C_P C_Q) ∧
    ∃ D : CochainComplex (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ,
      (∃ m n : ℤ, m ≤ n ∧ D.IsStrictlyGE m ∧ D.IsStrictlyLE n) ∧
      (∀ q : ℤ, Scheme.IsAffineLocallyConstructibleEtaleModuleSheaf (D.homology q)) ∧
      Nonempty ((finiteFieldEtalePullback A X).obj (DerivedCategory.Q.obj D) ≅
        finiteFieldEtaleInternalHom A X C_P C_Q) ∧
      (∀ a b : ℤ, a ≤ b →
        (∀ q : ℤ, q < a ∨ b < q → IsZero
          ((DerivedCategory.homologyFunctor _ q).obj
            (finiteFieldEtaleInternalHom A X C_P C_Q))) →
        ∀ (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
          (q : ℤ), q < a ∨ b < q → IsZero
          ((DerivedCategory.homologyFunctor _ q).obj
            (((Etale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).obj
              (DerivedCategory.Q.obj D)).obj ((DerivedCategory.singleFunctor _ 0).obj N)))) ∧
      ∃ a b : ℤ, a ≤ b ∧
        ∀ (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
          (q : ℤ), q < a ∨ b < q → IsZero
          ((DerivedCategory.homologyFunctor _ q).obj
            (((Etale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} A)) X).obj
              (DerivedCategory.Q.obj D)).obj ((DerivedCategory.singleFunctor _ 0).obj N))) := by
  sorry

end AlgebraicGeometry.ProEtale
