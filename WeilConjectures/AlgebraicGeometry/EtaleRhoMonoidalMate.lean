/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.FiniteEtaleDualizingNormalization
public import WeilConjectures.AlgebraicGeometry.Pur9Invertible
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.AlgebraicGeometry.ComparisonTorAmplitude
import WeilConjectures.AlgebraicGeometry.PullbackTorAmplitude
import WeilConjectures.AlgebraicGeometry.FiniteCoefficientTensorCtf
import WeilConjectures.Algebra.Homology.DerivedTensor
import WeilConjectures.AlgebraicGeometry.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitude
import WeilConjectures.AlgebraicGeometry.ProEtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.AlgebraicGeometry.SfIntegralConstructible
import WeilConjectures.AlgebraicGeometry.ProEtaleCohomologicalSupport
import WeilConjectures.AlgebraicGeometry.SfDerivedComplete
import WeilConjectures.AlgebraicGeometry.EtaleSumExtensionTensor
import WeilConjectures.SixFunctors.RingedDerivedMonoidalComparisons
import WeilConjectures.AlgebraicGeometry.CompactSupportComparisonUnit
import WeilConjectures.AlgebraicGeometry.EtaleAmbientAdjointLocality
import WeilConjectures.AlgebraicGeometry.EtaleSupportMapCompatibility
import WeilConjectures.AlgebraicGeometry.FiniteCompactProjectionFormula
import WeilConjectures.AlgebraicGeometry.ProjectionComparisonEtaleOrigin
import WeilConjectures.AlgebraicGeometry.QuasiFiniteCompactSupportExact
import WeilConjectures.AlgebraicGeometry.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ConstructibleExceptionalAdjunctionCoefficients
import WeilConjectures.AlgebraicGeometry.FiniteProjectionActionLaws
import WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
import WeilConjectures.AlgebraicGeometry.ProjectionMateExact
import WeilConjectures.AlgebraicGeometry.PurityCoprojection
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.StandingExceptionalComposition

/-!
# The normalized etale comparison preserves projection mates

Source: main-20261015, sec-smooth-purity/sk-thm-regular, Step 4(ii), and
sk-lem-coprojection, the five-Hom calculation
(blueprint: lem-pur-etale-rho-monoidal-mate).

The maps are written on every etale origin of the pro-etale Dctf inputs, exactly as in
`FiniteEtaleNormalization.domain` and `.rho`. The specified comparison, tensor and
compact-support comparisons carry these maps to the small pro-etale category.
The mate is specified uniquely by its counit/projection equation. The well-definedness
proof records the cancellation identifying this equation with the node's displayed
inverse-twist composite, including its adjunction unit normalization.

## Main definitions and statements

* `OperationData`, `operations`, `finiteDataWitness`, `finiteData`: the canonical operations.
* `finiteData_eq` and `finiteRho`: their exact specification and transported normalized rho.
* `IsFiniteKappa`: the uniquely determining projection/counit equation.
* `finiteKappa_existsUnique` and `finiteKappa`: the canonical normalized mate.
* `finiteKappa_normalization`: independence and the inverse co-projection normalization.
* `finite_etale_rho_monoidal_mate`: compatibility with the specified etale rho.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.EtaleProjectionMate

/-- The actual operations used in the projection-mate equation, packaged to keep
kernel checking from expanding derived functor implementations. No field is an
assumption in the finite statement: `operations` fills every field canonically.
Source: sk-thm-regular Step 4(ii), specified PF and tensor/pullback/counit operations
(blueprint: lem-pur-etale-rho-monoidal-mate). -/
structure OperationData
    (C : Type v) (D : Type w) [Category.{u} C] [Category.{u} D] where
  tensorT : C ⥤ C ⥤ C
  tensorS : D ⥤ D ⥤ D
  unitT : C
  F : D ⥤ C
  G : C ⥤ D
  Q : C ⥤ D
  counit : G ⋙ F ⟶ 𝟭 C
  projection : ∀ (L : D) (N : C), (tensorT.obj (F.obj L)).obj N ⟶
    F.obj ((tensorS.obj L).obj (Q.obj N))
  mu : ∀ K N : C, Q.obj ((tensorT.obj K).obj N) ≅
    (tensorS.obj (Q.obj K)).obj (Q.obj N)

/-- Fill the operation package with the existing etale tensor, compact-support,
exceptional, pullback, counit, specified projection and tensor-pullback maps.
Source: sk-thm-regular Step 4(ii), notation F,G,P,PF,epsilon,mu
(blueprint: lem-pur-etale-rho-monoidal-mate). -/
def operations
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {S T : Scheme.{u}} (h : S ⟶ T) [c : HasCompactification h] :
    OperationData (_root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
      (_root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) where
  tensorT := Etale.derivedTensor (ModuleCat.{u + 1} Λ) T
  tensorS := Etale.derivedTensor (ModuleCat.{u + 1} Λ) S
  unitT := FiniteEtaleNormalization.coefficientUnit (ModuleCat.{u + 1} Λ) T
  F := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) h
  G := Etale.rightDerivedUpperShriek Λ h
  Q := (Etale.upperStar (ModuleCat.{u + 1} Λ) h).leftDerivedFunctor
  counit := (Etale.rightDerivedUpperShriekAdjunction Λ h).counit
  projection := fun L N => ((Etale.projectionMap (ModuleCat.{u + 1} Λ) h).app L).app N
  mu := Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) h

/-- The concrete finite operation data in the normalization dependency's fixed
Nagata compactification. The body is the fully specified existing construction;
opacity prevents accidental kernel expansion of resolution machinery.
Source: sk-thm-regular Step 4(ii), finite etale-origin coordinates
(blueprint: lem-pur-etale-rho-monoidal-mate). -/
opaque finiteDataWitness
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {S T : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (T ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (h : S ⟶ T) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    : {d : OperationData (Etale.DerivedCategoryModule P.Coefficient T)
        (Etale.DerivedCategoryModule P.Coefficient S) //
        d = operations P.Coefficient h
          (c := FiniteEtaleNormalization.compactification P h)} :=
  ⟨operations P.Coefficient h
    (c := FiniteEtaleNormalization.compactification P h), rfl⟩

/-- The concrete canonical operations, extracted from their opaque package together
with its equality specification. Source: sk-thm-regular Step 4(ii), fixed operations
(blueprint: lem-pur-etale-rho-monoidal-mate). -/
def finiteData
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {S T : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (T ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (h : S ⟶ T) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    : OperationData (Etale.DerivedCategoryModule P.Coefficient T)
      (Etale.DerivedCategoryModule P.Coefficient S) :=
  (finiteDataWitness P h).val

/-- The operation wrapper contains exactly the specified upstream data.
Source: sk-thm-regular Step 4(ii), fixed operations
(blueprint: lem-pur-etale-rho-monoidal-mate).

Proof: The property field of finiteDataWitness is precisely this equality;
finiteData is its value field. Thus the specification remains available without
unfolding the opaque implementation. -/
theorem finiteData_eq
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {S T : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (T ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (h : S ⟶ T) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    : finiteData P h = operations P.Coefficient h
      (c := FiniteEtaleNormalization.compactification P h) := by
  sorry

/-- The actual normalized rho in the operation wrapper's coordinates, transported
by the equality to the specified operations; no new comparison is chosen.
Source: sk-thm-regular Step 4(ii), normalized comparison rho
(blueprint: lem-pur-etale-rho-monoidal-mate). -/
def finiteRho
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {S T : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (T ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (h : S ⟶ T) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [Etale h] : (finiteData P h).G ≅ (finiteData P h).Q :=
  eqToIso (congrArg OperationData.G (finiteData_eq P h)) ≪≫
    FiniteEtaleNormalization.rho P h ≪≫
    (eqToIso (congrArg OperationData.Q (finiteData_eq P h))).symm

/-- The counit/projection equation, using only the fixed canonical data.
Source: sk-thm-regular Step 4(ii), Steps 1-3, and the co-projection normalization
(blueprint: lem-pur-etale-rho-monoidal-mate). -/
def IsFiniteKappa
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {S T : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (T ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (h : S ⟶ T) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (K N : Etale.DerivedCategoryModule P.Coefficient T)
    (f : ((finiteData P h).tensorS.obj ((finiteData P h).G.obj K)).obj
      ((finiteData P h).Q.obj N) ⟶
    (finiteData P h).G.obj (((finiteData P h).tensorT.obj K).obj N)) : Prop :=
  (finiteData P h).projection ((finiteData P h).G.obj K) N ≫
    (finiteData P h).F.map f ≫ (finiteData P h).counit.app _ =
  ((finiteData P h).tensorT.map ((finiteData P h).counit.app K)).app N

/-- The counit equation uniquely determines the mate specified by the inverse-twist
composite, rather than only an isomorphism of its endpoints.
Source: sk-thm-regular Step 4(ii), Steps 1-3 of the DAG proof
(blueprint: lem-pur-etale-rho-monoidal-mate).

Proof: Exceptional preservation, pullback Tor preservation and tensor closure put
GK, PN, GK tensor PN and K tensor N in Dctf. Choose bounded etale origins and
reflect Tor amplitude. Full faithfulness and the finite compact projection formula
make the specified PF at GK,N invertible. The inverse-twist composite T satisfies
T PF = id by the tensor-action law with N,N', its coefficient-unit normalization,
and the triangle identity of (- tensor N') adjoint (- tensor N). In particular
its transpose q is PF inverse followed by the exceptional counit tensor identity.
The exceptional Hom bijection sends q to a morphism satisfying IsFiniteKappa.
Conversely, multiply that equation by PF inverse; the injective Hom bijection then
forces any two solutions to coincide. This identifies the unique solution with
the node's original composite, including its tensor-adjunction normalization. -/
theorem finiteKappa_existsUnique
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {S T : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (T ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (h : S ⟶ T) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (K N : Etale.DerivedCategoryModule P.Coefficient T)
    (hK : FiniteEtaleNormalization.domain P T K)
    (hN : FiniteEtaleNormalization.domain P T N)
    (d : TensorInvertibleData
      (fun L M => (((finiteData P h).tensorT.obj L).obj M)) (finiteData P h).unitT N)
    (hM : FiniteEtaleNormalization.domain P T d.inverse) :
    ∃! f : ((finiteData P h).tensorS.obj ((finiteData P h).G.obj K)).obj
      ((finiteData P h).Q.obj N) ⟶
    (finiteData P h).G.obj (((finiteData P h).tensorT.obj K).obj N), IsFiniteKappa P h K N f := by
  sorry

/-- The unique counit-normalized morphism. The preceding theorem determines its
actual morphism, so choice postpones only the proof of its defining property.
Source: sk-thm-regular Step 4(ii), kappa with its inverse-twist transpose
(blueprint: lem-pur-etale-rho-monoidal-mate). -/
def finiteKappa
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {S T : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (T ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (h : S ⟶ T) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (K N : Etale.DerivedCategoryModule P.Coefficient T)
    (hK : FiniteEtaleNormalization.domain P T K)
    (hN : FiniteEtaleNormalization.domain P T N)
    (d : TensorInvertibleData
      (fun L M => (((finiteData P h).tensorT.obj L).obj M)) (finiteData P h).unitT N)
    (hM : FiniteEtaleNormalization.domain P T d.inverse) :
    ((finiteData P h).tensorS.obj ((finiteData P h).G.obj K)).obj
      ((finiteData P h).Q.obj N) ⟶
    (finiteData P h).G.obj (((finiteData P h).tensorT.obj K).obj N) :=
  (finiteKappa_existsUnique P h K N hK hN d hM).exists.choose

/-- The canonical inverse is unique and independent of inverse data. The projection
normalization identifies its inverse with the co-projection of lem-pur-coprojection
when h is closed. Source: sk-thm-regular Step 4(ii), parenthetical normalization
(blueprint: lem-pur-etale-rho-monoidal-mate).

Proof: The finite projection formula applies on Dctf (exceptional preservation,
pullback Tor preservation and tensor closure). The tensor-action law, its unit
normalization and the triangle identity of the tensor adjunction cancel the inserted
inverse twist, giving q = PF inverse followed by counit tensor identity. This no
longer contains d, so the exceptional Hom bijection proves independence. The
five-Hom chain in lem-pur-coprojection is the same conjugation in reverse.
For a closed immersion its bijections and Yoneda give the canonical co-projection
isomorphism, whose inverse is kappa by the displayed counit equation. -/
theorem finiteKappa_normalization
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {S T : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (T ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (h : S ⟶ T) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (K N : Etale.DerivedCategoryModule P.Coefficient T)
    (hK : FiniteEtaleNormalization.domain P T K)
    (hN : FiniteEtaleNormalization.domain P T N)
    (d : TensorInvertibleData
      (fun L M => (((finiteData P h).tensorT.obj L).obj M)) (finiteData P h).unitT N)
    (hM : FiniteEtaleNormalization.domain P T d.inverse) :
    (∀ (d' : TensorInvertibleData
      (fun L M => (((finiteData P h).tensorT.obj L).obj M)) (finiteData P h).unitT N),
      ∀ (hM' : FiniteEtaleNormalization.domain P T d'.inverse),
        finiteKappa P h K N hK hN d hM = finiteKappa P h K N hK hN d' hM') ∧
    (IsClosedImmersion h → ∃ c : (finiteData P h).G.obj
        (((finiteData P h).tensorT.obj K).obj N) ≅
      ((finiteData P h).tensorS.obj ((finiteData P h).G.obj K)).obj
        ((finiteData P h).Q.obj N),
      c.inv = finiteKappa P h K N hK hN d hM ∧ IsFiniteKappa P h K N c.inv) := by
  sorry

/-- The normalized etale comparison preserves the specified projection mate.
The second equality is its equivalent co-projection form, with c the inverse of kappa.
The domain tests every etale origin of the original pro-etale Dctf objects.
Source: main-20261015, sk-thm-regular Step 4(ii)
(blueprint: lem-pur-etale-rho-monoidal-mate).

Proof:
1. Exceptional preservation, pullback Tor preservation and tensor closure put all
inputs in Dctf. Choose bounded etale origins, reflect their Tor amplitudes, and use
full faithfulness of site comparison. The finite compact projection formula makes
PF invertible on these inputs.
2. The tensor-action law and unit normalization give T PF = id, using the triangle
identity of the tensor adjunction. Thus the defining transpose is counit tensor identity
following PF inverse. It is independent of inverse data.
3. The five-Hom conjugation chain of lem-pur-coprojection gives this same transpose;
for a closed immersion its inverse is the specified co-projection.
4. Transport the maps, tensor, evaluations and mu through the canonical monoidal
site comparison (projection-comparison-etale-origin and ringed-derived-monoidal
comparisons). Full faithfulness reduces the equality to ordinary etale origins.
5. Write d for the proper-support/sum identification and p for the sum projection.
Etale-support-map-compatibility gives d PF = p (d tensor identity). Normalization
of rho gives epsilon-sum S(rho) d = epsilon-exceptional.
6. The derived sum-extension-tensor fold identity gives
 epsilon-sum S(mu inverse) = (epsilon-sum tensor identity) p inverse.
All symmetries here are the canonical signed derived symmetries.
7. Transpose Q = (rho tensor identity) followed by mu inverse under the normalized
F adjoint P. Naturality of p inverse and the two equations in step 5 turn its
transpose into (epsilon-exceptional tensor identity) PF inverse, namely q.
Injectivity of the adjunction Hom bijection proves the first displayed equality.
8. Every factor in Q and rho is invertible. Thus kappa is invertible; multiplying
the first equality by mu and kappa inverse proves the co-projection equality. -/
theorem finite_etale_rho_monoidal_mate
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {S T : Scheme.{u}}
    [S.Over (Spec (.of P.field.k))] [T.Over (Spec (.of P.field.k))]
    [IsSeparated (S ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (S ↘ Spec (.of P.field.k))]
    [QuasiCompact (S ↘ Spec (.of P.field.k))]
    [IsSeparated (T ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    (h : S ⟶ T) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    [Etale h]
    (K N : Etale.DerivedCategoryModule P.Coefficient T)
    (hK : FiniteEtaleNormalization.domain P T K)
    (hN : FiniteEtaleNormalization.domain P T N)
    (d : TensorInvertibleData
      (fun L M => (((finiteData P h).tensorT.obj L).obj M)) (finiteData P h).unitT N)
    (hM : FiniteEtaleNormalization.domain P T d.inverse) :
    finiteKappa P h K N hK hN d hM ≫ (finiteRho P h).hom.app
        (((finiteData P h).tensorT.obj K).obj N) =
      ((finiteData P h).tensorS.map ((finiteRho P h).hom.app K)).app
          ((finiteData P h).Q.obj N) ≫ ((finiteData P h).mu K N).inv ∧
    ∃ c : (finiteData P h).G.obj (((finiteData P h).tensorT.obj K).obj N) ≅
      ((finiteData P h).tensorS.obj ((finiteData P h).G.obj K)).obj
        ((finiteData P h).Q.obj N),
      c.inv = finiteKappa P h K N hK hN d hM ∧
      (finiteRho P h).hom.app (((finiteData P h).tensorT.obj K).obj N) ≫
        ((finiteData P h).mu K N).hom =
      c.hom ≫ ((finiteData P h).tensorS.map ((finiteRho P h).hom.app K)).app
        ((finiteData P h).Q.obj N) := by
  sorry

end AlgebraicGeometry.ProEtale.EtaleProjectionMate
