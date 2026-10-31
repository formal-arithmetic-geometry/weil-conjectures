/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.SfIdentificationData
import WeilConjectures.AlgebraicGeometry.FiniteGeometricPointCohomology
import WeilConjectures.CategoryTheory.ShiftedInvertibleEvaluation
import WeilConjectures.SixFunctors.SfIdentificationGeometricModels
import WeilConjectures.SixFunctors.SfIdentificationGlobalComparison
import WeilConjectures.SixFunctors.FiniteCoefficientDegreewisePairing

/-! # Smooth Poincare identification

Source: latest blueprint, sk-thm-sf-identification.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local instance 10000] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace WeilConjectures.SixFunctors

variable (ell : ℕ) [Fact ell.Prime]
  (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
  (Λ : ScalarSixRing.{u}) (c : PurityTransport.Coefficient ell)
  (e : c.bundled.{u} ell ≅ Λ)
  (X : Over (Spec (.of D.k))) [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] (d : ℕ)
  [SmoothOfRelativeDimension d X.hom] (cf : Compactification X.hom)
  (K : ConstantModelConstructibleFiniteTor Λ.X X.left)

private lemma shiftedEvaluationForIdentification
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (K T W : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) [(tensorLeft K).CommShift ℤ]
    (hT : IsInvertible T) (n : ℤ) (γ : T⟦n⟧ ≅ W) :
    ∃ j : ((ihom K).obj (𝟙_ _) ⊗ T) ⟦n⟧ ≅ (ihom K).obj W,
      K ◁ j.hom ≫ (ihom.ev K).app W =
        ((tensorLeft K).commShiftIso n).hom.app _ ≫
          (shiftFunctor _ n).map (pairingTwistedEvaluation Λ K T) ≫ γ.hom := by
  obtain ⟨j, hj⟩ := MonoidalClosed.shiftedInvertibleEvaluation K T W hT n γ
  refine ⟨j, ?_⟩
  unfold pairingTwistedEvaluation
  exact hj

private lemma identificationPairing_eq_derived
    (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (Λ : ScalarSixRing.{u}) (c : PurityTransport.Coefficient ell)
    (e : c.bundled.{u} ell ≅ Λ)
    (X : Over (Spec (.of D.k))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (cf : Compactification X.hom)
    (K : ConstantModelConstructibleFiniteTor Λ.X X.left)
    (hK : IsPerfectOnCoefficientSite Λ.X X.left K.obj) :
    identificationPairing ell D hEll Λ c e X d cf K =
      derivedPoincarePairing ell D hEll Λ c e X d cf K hK := by
  rfl

set_option linter.style.maxHeartbeats false in
set_option linter.style.setOption false in
attribute [local irreducible] Functor.commShiftIso pairingTwistedEvaluation
  MonoidalClosed.curry in
-- The assembly unfolds several large categorical expressions.
set_option linter.style.haveILetI false in
set_option maxHeartbeats 2000000 in
/-- Smooth derived Poincare identification in ordinary condensed modules.
Source: latest blueprint, sk-thm-sf-identification, main assertion and Complement
(blueprint: sk-thm-sf-identification).

Proof: (1) algebraic closure gives cd_ell(k)=0 and hence the Brown exceptional
adjoint on Loc(Dctf). Apply normalized smooth purity to the coefficient unit.
Invertible-factor Hom cancellation gives j, characterized by its evaluation
square. Local bounded finite-projective representatives dualize term by term,
with differential d(f)=(-1)^(|f|+1) f d, and their splittings dualize to splittings.
(2) Inverse tensor--Hom exchange at a and the coefficient unit is the first
evaluation-normalized global Verdier isomorphism g. Naturality of the mixed cup,
the evaluation equation for j, and the purity/counit normalization identify its
precomposition with RΓ(j) with precisely beta. Thus beta's transpose is that
composite and its inverse is RΓ(j^-1) followed after g^-1 in diagrammatic order.
All transposes use the native signed symmetry.
(3) Internal-Hom and twist stability give the claimed Dctf memberships. Finite
geometric-point cohomology makes both scalar factors perfect. Proper compact
coincidence supplies chi and the ordinary-support specialization.
(4) For A_E,n, duality into the self-injective coefficient ring is exact. On a
bounded projective scalar representative it computes derived duality and
commutes with cohomology. Applying H^-i to the transpose identifies the second
cohomology module with the full module dual of H^i_c, with the same evaluation.
Finite biduality gives the other adjoint. The shift convention makes its degree
2d-i before the shift, including negative i and zero complexes. -/
theorem sf_identification (E : PadicAlgCl.FiniteIntermediateField ell)
    (_hΛ : IsPurityFrobeniusCoefficient ell E Λ) :
    IdentificationAssertion ell D hEll Λ c e X d cf K := by
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  obtain ⟨hR, hs, hmodels⟩ :=
    sfIdentificationGeometricModels ell D hEll Λ c e X d cf K E _hΛ
  refine ⟨(cohomologicalDimension_baseField ell (Fact.out : ell.Prime) D.k).1
    inferInstance, hR, hs, ?_⟩
  intro R
  have hmodelsR := hmodels R
  obtain ⟨γ, htrace, hT, hdual, hVerdierDual, hline, htwist, hsite, hP, hQ, hproper⟩ :=
    hmodelsR
  have hshift := shiftedEvaluationForIdentification Λ.X X.left K.obj
    (smoothTraceCoefficientLine ell Λ c e X.left d) (R.upper.obj ⟨𝟙_ _, hs⟩).obj
      hT (2 * (d : ℤ)) γ
  obtain ⟨j, hj⟩ := hshift
  have hglobal := sfIdentificationGlobalComparison ell D hEll Λ c e X d cf K
    E _hΛ hs R γ j htrace hj
  obtain ⟨g, hg, hβg⟩ := hglobal
  have hβ : MonoidalClosed.IsPerfectPairing
      (identificationPairing ell D hEll Λ c e X d cf K) := by
    constructor
    rw [hβg]
    infer_instance
  refine ⟨γ, j, htrace, hj, hdual, hVerdierDual, hline, htwist, hsite, hP, hQ,
    hβ, ?_, g, hg, hβg, ?_, ?_⟩
  · intro hK
    exact identificationPairing_eq_derived ell D hEll Λ c e X d cf K hK
  · intro hp
    obtain ⟨χ⟩ := hproper hp
    exact ⟨χ, hβ.whiskerRight_comp χ.hom⟩
  · intro _hp _hK hfinite
    exact finiteCoefficientDegreewisePairing ell Λ hfinite
      (identificationPairing ell D hEll Λ c e X d cf K) hP hβ

end WeilConjectures.SixFunctors
