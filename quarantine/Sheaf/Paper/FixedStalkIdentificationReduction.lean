/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.Paper.TraceFormulaCoefficientConventions
public import Sheaf.Paper.PointSectionsFiniteReduction
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.Paper.BasicOperationsCoefficientReduction
public import Sheaf.Paper.IntegralFinitePullbackComposition
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
public import Sheaf.Paper.PointProEtaleSectionsExact
public import Sheaf.Paper.FiniteTorStability
import Sheaf.Paper.DerivedPullbackTensorIso

/-!
# Finite reduction of the canonical fixed-point stalk identification

Source: blueprint `main-20261015`, `sec-trace-formula/sk-prop-trace-adic/`
`prop-trf-adic-coefficient-morphism-systems.proof.md`, Proof (3), last sentence
(blueprint: lem-trf-fixed-stalk-identification-reduction).

Positive exponents N and j are written m+1 and n+1. The point field is arbitrary;
it need not equal the fixed algebraic closure of the finite base field.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

section QuotientPresentation

variable (k : Type u) [Field k] (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary quotient extensions in the two published interfaces coincide.
Source: Stacks Tag 06YY; blueprint trace-adic Proof (1)
(blueprint: lem-trf-fixed-stalk-identification-reduction).
Proof: the composite of the successive DVR quotient maps sends the class of a to the
class of a, so equals the direct quotient by surjectivity of the quotient map.
Constant sheafification preserves this equality. Both extension functors have the
specified sheafified tensor objects and maps; functor extensionality identifies them.
The positive exponents are m+1 and n+1, including the identity quotient. -/
theorem pointFiniteReductionQuotientExtension_eq (m n : ℕ) (h : n ≤ m) :
    pointFiniteReductionSheafExtension k l E (m + 1) (n + 1) (Nat.succ_le_succ h) =
      coefficientFiniteQuotientExtension l E (Spec (.of k)) h := by
  sorry

/-- The equality of ordinary quotient extensions, viewed as a natural isomorphism.
Source: Stacks Tag 06YY (blueprint: lem-trf-fixed-stalk-identification-reduction). -/
def pointFiniteReductionQuotientExtensionIso (m n : ℕ) (h : n ≤ m) :=
  eqToIso (pointFiniteReductionQuotientExtension_eq k l E m n h)

/-- Additivity with the point universe made explicit for the comparison on complexes.
Source: Stacks Tag 06YY (blueprint: lem-trf-fixed-stalk-identification-reduction). -/
instance pointFiniteReductionQuotientExtensionAdditive (m n : ℕ) (h : n ≤ m) :
    (coefficientFiniteQuotientExtension l E (Spec (.of k)) h).Additive :=
  coefficientFiniteQuotientExtensionAdditive l E (Spec (.of k)) h

/-- The ordinary identification applied termwise, with the additive instances explicit.
Source: Stacks Tag 06YY (blueprint: lem-trf-fixed-stalk-identification-reduction). -/
def pointFiniteReductionQuotientComplexIso (m n : ℕ) (h : n ≤ m) :
    (pointFiniteReductionSheafExtension k l E (m + 1) (n + 1)
        (Nat.succ_le_succ h)).mapHomologicalComplex (.up ℤ) ≅
      (coefficientFiniteQuotientExtension l E (Spec (.of k)) h).mapHomologicalComplex
        (.up ℤ) := by
  letI := coefficientFiniteQuotientExtensionAdditive l E (Spec (.of k)) h
  exact NatIso.mapHomologicalComplex
    (F := pointFiniteReductionSheafExtension k l E (m + 1) (n + 1)
      (Nat.succ_le_succ h))
    (G := coefficientFiniteQuotientExtension l E (Spec (.of k)) h)
    (pointFiniteReductionQuotientExtensionIso k l E m n h) (.up ℤ)

/-- The unique identification of the derived quotients that preserves their counits.
Source: Stacks Tags 06YY and 06XN; blueprint trace-adic Proof (1)
(blueprint: lem-trf-fixed-stalk-identification-reduction).
Proof: transport the ordinary functor by the preceding equality. Both derived functors
are the everywhere-defined left derived functor of this same termwise extension.
Uniqueness of left derived functors gives a counit-compatible natural isomorphism.
On a K-flat representative the two counits are invertible, giving the displayed square.
Every complex has a K-flat resolution, so these squares also prove uniqueness. -/
theorem pointFiniteReductionQuotientTensorIso_existsUnique (m n : ℕ) (h : n ≤ m) :
    ∃! e : pointFiniteReductionSheafTensor k l E (m + 1) (n + 1)
          (Nat.succ_le_succ h) ≅ coefficientFiniteQuotientDerived l E (Spec (.of k)) h,
      ∀ (P : CochainComplex (normalizedDVRModules l E (Spec (.of k)) m) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology (Spec (.of k)))
          (R := integralCoefficientCommRingSheaf l E (Spec (.of k)) m) P),
        e.hom.app (DerivedCategory.Q.obj P) ≫
            (coefficientFiniteQuotientModel l E (Spec (.of k)) h P hP).hom =
          pointFiniteReductionSheafCounit k l E (m + 1) (n + 1) (Nat.succ_le_succ h) P ≫
            DerivedCategory.Q.map
              ((pointFiniteReductionQuotientComplexIso k l E m n h).hom.app P) := by
  sorry

/-- The counit-compatible identification, determined uniquely on K-flat representatives.
Source: Stacks Tags 06YY and 06XN (blueprint: lem-trf-fixed-stalk-identification-reduction). -/
def pointFiniteReductionQuotientTensorIso (m n : ℕ) (h : n ≤ m) :=
  (pointFiniteReductionQuotientTensorIso_existsUnique k l E m n h).exists.choose

/-- The published point-sections comparison with its quotient-section normalization.
Its source theorem specifies its value on every bounded-above flat representative;
these representatives determine the comparison, including identity and tower cases.
Source: blueprint trace-adic Proof (1) (blueprint: lem-trf-fixed-stalk-identification-reduction). -/
def pointFiniteReductionCanonical [IsAlgClosed k] (hl : IsUnit (l : k))
    (m n : ℕ) (h : n ≤ m) :=
  (point_sections_finite_reduction k l E hl).choose (m + 1) (n + 1)
    (Nat.succ_le_succ (Nat.zero_le m)) (Nat.succ_le_succ (Nat.zero_le n))
    (Nat.succ_le_succ h)

end QuotientPresentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The stalk complex S_R(M) is exact point sections after the recorded finite pullback.
Source: blueprint trace-adic Proof (3), last sentence
(blueprint: lem-trf-fixed-stalk-identification-reduction). -/
def fixedStalkSections (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (y : Spec (.of Ω) ⟶ X) (n : ℕ) :=
  finiteDerivedPullback l E n y ⋙ pointFiniteReductionSections Ω l E (n + 1)

/-- The fixed-point identification iota, as a natural isomorphism on ambient complexes.
The equality y followed by h equals y identifies the source of the composition map.
No Weil structure or endomorphism of the coefficient ring is part of this map.
Source: blueprint trace-adic Proof (3), last sentence
(blueprint: lem-trf-fixed-stalk-identification-reduction). -/
def fixedStalkIdentification (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {X : Scheme.{u}} (h : X ⟶ X) (y : Spec (.of Ω) ⟶ X)
    (hy : y ≫ h = y) (n : ℕ) :
    fixedStalkSections l E Ω y n ≅
      finiteDerivedPullback l E n h ⋙ fixedStalkSections l E Ω y n :=
  letI : Finite (finiteCoefficientRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
  Functor.isoWhiskerRight
      (eqToIso (congrArg (fun f ↦ finiteDerivedPullback l E n f) hy.symm) ≪≫
        sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) y h)
      (pointFiniteReductionSections Ω l E (n + 1)) ≪≫
    Functor.associator _ _ _

/-- Finite coefficient reduction commutes with the fixed-point stalk identification,
canonically and naturally in K.
Source: blueprint trace-adic Proof (3), last sentence
(blueprint: lem-trf-fixed-stalk-identification-reduction).

The natural isomorphism sigma is specified by the published point-sections comparison,
its counit-compatible change of quotient presentation, and the canonical quotient/pullback
comparison at y. Thus it is the sigma of the node, not an arbitrary natural isomorphism.
The final equation is r(iota_A) followed by sigma_(h*K) followed by S_B(mu_h,K), equal
to sigma_K followed by iota_B. The existential hHK only supplies the domain proof needed
to evaluate that same natural isomorphism at h*K; it imposes no hypothesis on h.

Proof:
1. Write P_R for pullback at y, H_R for pullback by h, and r_T for derived coefficient
   extension. Finite pullback is exact termwise inverse image. Its composition map,
   after y h = y, gives d_R : P_R -> P_R H_R; exact sections give iota_R. The prime l
   is a unit in Ω: its image from the finite base field is nonzero since l differs
   from p, and the geometric point induces the required field embedding.
2. Apply the composition clause of lem-pur-derived-pullback-tensor-iso to h, y and the
   constant coefficient sheaf B, using lem-pur-derived-change-of-rings to retain the
   B action. Canonical tensor representatives give
   P_B(mu_h) eta_(H_A K) r_t(d_A) = d_B eta_K as B-linear derived morphisms.
3. For bounded-above point complexes use the natural comparison tau of
   lem-trf-point-sections-finite-reduction. Its naturality applies to d_A itself;
   it need not be the pullback of a map on X. Compose the preceding identity with
   tau_(P_A K). The counit-compatible quotient identification does not change the
   map on representatives. This gives the specified sigma and the displayed square.
4. The graph of a k-endomorphism of the separated finite-type geometric fibre is
   closed. The graph factorization makes h separated and finite type, so clause (i)
   of thm-sf-ctf-stability gives h*K in D^b_ctf. Exact pullback of bounded K is bounded
   above at y, as required by tau. Every comparison is natural; sigma is a natural
   isomorphism on the full finite-Tor constructible category. No properness, Weil
   structure, or coefficient endomorphism is used. -/
theorem fixedStalkIdentification_finite_reduction
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (h : D.geometricFiber X₀ ⟶ D.geometricFiber X₀)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ (D.geometricFiber X₀).left) (hy : y ≫ h.left = y)
    (m n : ℕ) (hnm : n ≤ m) :
    ∃ hlΩ : IsUnit (l : Ω),
    ∃ σ : (finiteTorConstructible l E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) (D.geometricFiber X₀).left).ι ⋙
          fixedStalkSections l E Ω y m ⋙
            pointFiniteReductionModuleTensor l E (m + 1) (n + 1) (Nat.succ_le_succ hnm) ≅
        (finiteTorConstructible l E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) (D.geometricFiber X₀).left).ι ⋙
          coefficientFiniteQuotientDerived l E (D.geometricFiber X₀).left hnm ⋙
            fixedStalkSections l E Ω y n,
      (∀ K : (finiteTorConstructible l E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) (D.geometricFiber X₀).left).FullSubcategory,
        ∃ hP : pointFiniteReductionBoundedAbove Ω l E (m + 1)
            ((finiteDerivedPullback l E m y).obj K.obj),
          σ.hom.app K =
            (pointFiniteReductionCanonical Ω l E hlΩ m n hnm).hom.app
                ⟨(finiteDerivedPullback l E m y).obj K.obj, hP⟩ ≫
              (pointFiniteReductionSections Ω l E (n + 1)).map
                ((pointFiniteReductionQuotientTensorIso Ω l E m n hnm).hom.app
                  ((finiteDerivedPullback l E m y).obj K.obj)) ≫
              (pointFiniteReductionSections Ω l E (n + 1)).map
                ((pullbackTensorQuotient l E y hnm).hom.app K.obj)) ∧
      ∀ K : (finiteTorConstructible l E (m + 1)
          (Nat.succ_le_succ (Nat.zero_le m)) (D.geometricFiber X₀).left).FullSubcategory,
        ∃ hHK : finiteTorConstructible l E (m + 1)
            (Nat.succ_le_succ (Nat.zero_le m)) (D.geometricFiber X₀).left
            ((finiteDerivedPullback l E m h.left).obj K.obj),
          (pointFiniteReductionModuleTensor l E (m + 1) (n + 1)
              (Nat.succ_le_succ hnm)).map
              ((fixedStalkIdentification l E Ω h.left y hy m).hom.app K.obj) ≫
            σ.hom.app ⟨(finiteDerivedPullback l E m h.left).obj K.obj, hHK⟩ ≫
            (fixedStalkSections l E Ω y n).map
              ((pullbackTensorQuotient l E h.left hnm).hom.app K.obj) =
          σ.hom.app K ≫
            (fixedStalkIdentification l E Ω h.left y hy n).hom.app
              ((coefficientFiniteQuotientDerived l E (D.geometricFiber X₀).left hnm).obj
                K.obj) := by
  sorry

end WeilConjectures
