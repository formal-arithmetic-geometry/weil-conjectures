/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q74
-/
module

public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.SixFunctors.EtaleOpenTensor
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.SixFunctors.EtaleHomThickLocus
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Sheaf.SmoothPurity.InternalAdjunctionEvaluation
import Sheaf.Paper.EtaleLocallyClosedShriek

/-! # Coefficient change of the stratum internal-adjunction pairing

Source: Weil blueprint, sec-six-functors/sk-prop-sf-biduality-general,
thm-coef-finite-hom, proof paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change).

The helpers expand the specified closed/open factorization. Ordinary direct image
is written as Rg_* Rj_*, using the canonical composition identification. Tensor
arguments are reversed from the displayed pairing, consistently with the published
left-tensor/Hom adjunction. Thus the projection is the closed proper projection
followed by the inverse open projection, and the last arrow is the pasted counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.CoefficientPairingChange

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]
variable {S Z X : Scheme.{u}}

/-- The given factorized compact-support functor, not a chosen compactification.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
abbrev shriek (A : Type (u + 1)) [CommRing A]
    (g : Z ⟶ X) (j : S ⟶ Z) [IsOpenImmersion j] :=
  derivedExtension (A := A) j ⋙ R(lowerStar (ModuleCat A) g)

/-- Ordinary direct image through the canonical composition identification.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
abbrev star (A : Type (u + 1)) [CommRing A] (g : Z ⟶ X) (j : S ⟶ Z) :=
  R(lowerStar (ModuleCat A) j) ⋙ R(lowerStar (ModuleCat A) g)

/-- The actual closed exceptional right adjoint followed by exact open restriction.
Source: thm-coef-finite-hom, paragraph 4; lem-exc-closed-ambient
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
abbrev exceptional (A : Type (u + 1)) [CommRing A] [Finite A]
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j] :=
  (R(lowerStar (ModuleCat A) g)).rightAdjoint ⋙ derivedRestriction (A := A) j

/-- The exceptional counit is the counit of the composite open/closed adjunction.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def counit (A : Type (u + 1)) [CommRing A] [Finite A]
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (M : DerivedCategoryModule A X) :
    (shriek A g j).obj ((exceptional A g j).obj M) ⟶ M :=
  ((derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat A) j).comp
    (Adjunction.ofIsLeftAdjoint (R(lowerStar (ModuleCat A) g)))).counit.app M

/-- The ordinary inverse-image/direct-image counit for the composite factorization.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def ordinaryCounit (A : Type (u + 1)) [CommRing A]
    (g : Z ⟶ X) (j : S ⟶ Z) (Q : DerivedCategoryModule A S) :
    L(upperStar (ModuleCat A) j).obj
      (L(upperStar (ModuleCat A) g).obj ((star A g j).obj Q)) ⟶ Q :=
  ((derivedUpperStarLowerStarAdjunction (ModuleCat A) g).comp
    (derivedUpperStarLowerStarAdjunction (ModuleCat A) j)).counit.app Q

/-- The specified inverse compact-support projection: closed proper projection
followed by the inverse open tensor map. Its tensor order matches left-tensor/Hom.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def projection (A : Type (u + 1)) [CommRing A]
    (g : Z ⟶ X) (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (T : DerivedCategoryModule A X) :
    ((derivedTensor (ModuleCat A) X).obj ((shriek A g j).obj L)).obj T ⟶
      (shriek A g j).obj
        (((derivedTensor (ModuleCat A) S).obj L).obj
          (L(upperStar (ModuleCat A) j).obj (L(upperStar (ModuleCat A) g).obj T))) :=
  ((rightDerivedLowerStarProjectionMap (ModuleCat A) g).app
      ((derivedExtension (A := A) j).obj L)).app T ≫
    R(lowerStar (ModuleCat A) g).map
      (((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat A) j).inv.app L).app
        (L(upperStar (ModuleCat A) g).obj T))

/-- The internal-adjunction arrow, defined by exactly the stated evaluation pairing.
The ordinary counit is applied before evaluation, and the exceptional counit last.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def internalAdjunction (A : Type (u + 1)) [CommRing A] [Finite A]
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X) :
    (star A g j).obj
        (((derivedHom (ModuleCat A) S).obj (op L)).obj ((exceptional A g j).obj M)) ⟶
      ((derivedHom (ModuleCat A) X).obj (op ((shriek A g j).obj L))).obj M :=
  ((derivedTensorHomAdjunction (ModuleCat A) ((shriek A g j).obj L)).homEquiv _ _)
    (projection A g j L _ ≫
      (shriek A g j).map
        (((derivedTensor (ModuleCat A) S).obj L).map
            (ordinaryCounit A g j _) ≫
          (derivedTensorHomAdjunction (ModuleCat A) L).counit.app
            ((exceptional A g j).obj M)) ≫ counit A g j M)

/-- The specified compact-support coefficient map: c_g followed by g_*(q_j).
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def compactComparison (φ : A →+* B) (g : Z ⟶ X) (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj ((shriek A g j).obj L) ⟶
      (shriek B g j).obj ((scalarExtension φ S).obj L) :=
  finiteCoefficientDirectImageMap φ g ((derivedExtension (A := A) j).obj L) ≫
    R(lowerStar (ModuleCat B) g).map ((openScalarExtension φ j).hom.app L)

/-- The ordinary counit-defined coefficient comparison in composition coordinates.
Source: thm-coef-finite-hom, paragraph 4; lem-coef-finite-direct-image
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def ordinaryComparison (φ : A →+* B) (g : Z ⟶ X) (j : S ⟶ Z)
    (Q : DerivedCategoryModule A S) :
    (scalarExtension φ X).obj ((star A g j).obj Q) ⟶
      (star B g j).obj ((scalarExtension φ S).obj Q) :=
  finiteCoefficientDirectImageMap φ g (R(lowerStar (ModuleCat A) j).obj Q) ≫
    R(lowerStar (ModuleCat B) g).map (finiteCoefficientDirectImageMap φ j Q)

/-- The coefficient Hom map is the transpose of coefficient change of evaluation.
No inverse of this map is used or assumed.
Source: thm-coef-finite-hom, paragraph 1 and paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def evaluationComparison (φ : A →+* B) (T : Scheme.{u})
    (K M : DerivedCategoryModule A T) :
    (scalarExtension φ T).obj (((derivedHom (ModuleCat A) T).obj (op K)).obj M) ⟶
      ((derivedHom (ModuleCat B) T).obj (op ((scalarExtension φ T).obj K))).obj
        ((scalarExtension φ T).obj M) :=
  ((derivedTensorHomAdjunction (ModuleCat B) ((scalarExtension φ T).obj K)).homEquiv _ _)
    ((etaleHomTensorComparison T φ K _).hom ≫
      (scalarExtension φ T).map ((derivedTensorHomAdjunction (ModuleCat A) K).counit.app M))

/-- The displayed normalization of the specified exceptional comparison.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def CounitCompatible [Finite A] [Finite B] (φ : A →+* B)
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (M : DerivedCategoryModule A X)
    (b : (scalarExtension φ S).obj ((exceptional A g j).obj M) ≅
      (exceptional B g j).obj ((scalarExtension φ X).obj M)) : Prop :=
  compactComparison φ g j ((exceptional A g j).obj M) ≫
      (shriek B g j).map b.hom ≫ counit B g j ((scalarExtension φ X).obj M) =
    (scalarExtension φ X).map (counit A g j M)

/-- The exact equality of arrows in the node, with every comparison expanded by
its fixed construction above. This transparent proposition has no further data.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def PairingChangeEquation [Finite A] [Finite B] (φ : A →+* B)
    (g : Z ⟶ X) [IsClosedImmersion g] (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategoryModule A S) (M : DerivedCategoryModule A X)
    (b : (scalarExtension φ S).obj ((exceptional A g j).obj M) ≅
      (exceptional B g j).obj ((scalarExtension φ X).obj M)) : Prop :=
  ordinaryComparison φ g j _ ≫
      (star B g j).map
        (evaluationComparison φ S L _ ≫
          ((derivedHom (ModuleCat B) S).obj
            (op ((scalarExtension φ S).obj L))).map b.hom) ≫
      internalAdjunction B g j ((scalarExtension φ S).obj L) ((scalarExtension φ X).obj M) ≫
      ((derivedHom (ModuleCat B) X).map (compactComparison φ g j L).op).app
        ((scalarExtension φ X).obj M) =
    (scalarExtension φ X).map (internalAdjunction A g j L M) ≫
      evaluationComparison φ X ((shriek A g j).obj L) M

/-- The positive-level quotient ring with the standard module-universe lift.
Source: thm-coef-finite-hom, paragraph 4; def-weil-l-adic-coefficient-extension
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
abbrev coefficient (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ+) :=
  ULift.{u + 1} (Padic.coefficientExtensionRing l E n)

/-- Finiteness is the dependency theorem at the positive level, with a universe lift.
Source: def-weil-l-adic-coefficient-extension, clause 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
instance coefficientFinite (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n : ℕ+) :
    Finite (coefficient l E n) :=
  Equiv.ulift.finite_iff.mpr (Padic.finite_coefficientExtensionRing l E n n.property)

/-- Reduction is the quotient factor map of the actual uniformizer-power ideals.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change). -/
def reduction (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (n m : ℕ+) (hmn : m ≤ n) :
    coefficient l E n →+* coefficient l E m :=
  RingHom.ulift.{u + 1, u + 1} (Ideal.Quotient.factor
    (S := Padic.coefficientExtensionIdeal l E n)
    (T := Padic.coefficientExtensionIdeal l E m) (Ideal.pow_le_pow_right hmn))

/-- The stratum internal-adjunction comparison is exactly the evaluation transpose.
Source: thm-coef-finite-hom, paragraph 4
(blueprint: lem-coef-internal-adjunction-pairing-change).

Proof:
1. Transpose the open tensor/scalar square under j_! ⊣ j^*. Both adjuncts are
   the restriction/tensor identification (lem-coef-etale-open-tensor).
2. Transpose the closed proper projection/scalar square under g^* ⊣ Rg_*.
   Its two adjuncts are the coefficient change of 1 tensor the ordinary counit
   (lem-coef-finite-direct-image). The pushed object here is j_!L.
3. Paste these squares and use naturality of c_g to obtain the compact-support
   projection square, with no ordinary counit or c_s in it.
4. The assumed equation for b identifies the final exceptional counits.
5. By its definition, the transpose of u is coefficient change of evaluation
   (lem-sfb-dc-hom-scalar-adjunction).
6. Apply lem-asd-internal-adjunction-evaluation to the left composite. The
   ordinary-counit normalization of c_s moves it past restriction. Naturality
   of evaluation gives b followed by coefficient change of evaluation; then
   the projection square and naturality of q_s give the A pairing, extended
   to B, followed by q_{s,N}, s_!(b), and the B exceptional counit. Step 4
   replaces those last three factors by coefficient change of the A counit.
7. The transpose of the right composite is coefficient change of the same
   A pairing, by the evaluation normalization of v. No invertibility of v
   is needed.
8. Injectivity of the tensor-Hom bijection gives the equality. All composition,
   associativity and restriction identifications are the canonical ones.
-/
theorem internalAdjunction_pairing_change
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n m : ℕ+) (hmn : m ≤ n)
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [IsSeparated (X ↘ Spec (CommRingCat.of D.k))]
    {S Z : Scheme.{u}} (g : Z ⟶ X) [IsClosedImmersion g]
    (j : S ⟶ Z) [IsOpenImmersion j]
    (M : DerivedCategoryModule (coefficient l E n) X)
    (L : DerivedCategoryModule (coefficient l E n) S)
    (_hM : WeilConjectures.finiteTorConstructibleEtale l E n n.property X M)
    (_hL : WeilConjectures.finiteTorConstructibleEtale l E n n.property S L)
    (_hN : WeilConjectures.finiteTorConstructibleEtale l E n n.property S
      ((exceptional (coefficient l E n) g j).obj M))
    (_hQ : WeilConjectures.finiteTorConstructibleEtale l E n n.property S
      (((derivedHom (ModuleCat (coefficient l E n)) S).obj (op L)).obj
        ((exceptional (coefficient l E n) g j).obj M)))
    (b : (scalarExtension (reduction l E n m hmn) S).obj
        ((exceptional (coefficient l E n) g j).obj M) ≅
      (exceptional (coefficient l E m) g j).obj
        ((scalarExtension (reduction l E n m hmn) X).obj M))
    (_hb : CounitCompatible (reduction l E n m hmn) g j M b) :
    PairingChangeEquation (reduction l E n m hmn) g j L M b := by
  sorry

end AlgebraicGeometry.Etale.CoefficientPairingChange
