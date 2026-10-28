/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M7
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower
import Sheaf.SixFunctors.NormalizedDVRQuotientSystemRealization
import Sheaf.SixFunctors.CoefHomScalarNaturality

/-! # Scalar realization of a normalized tower as a quotient system -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Realize a normalized tower on the quotient sequence site, and compare its
completed-coefficient mapping tower with quotient-linear Hom. No finite dualizing
identifications, exceptional adjunction, compact support, or limit is used here.

Source: prop-coef-integral-dualizing, second paragraph, first scalar-adjunction
comparison; Stacks 079P, 070I, 07A6 and 0941.
(blueprint: lem-coef-integral-dualizing-mapping-tower-system-model).

Proof: choose a complex representing T.M 0. Inductively, once a complex Q_n
represents T.M n, transport tau(n+1,n) to a derived map into the restriction of
Q_n. Represent this map by a roof with a quasi-isomorphism on its source, in the
source quotient-module category. Choose the roof's middle complex as Q_(n+1).
The other leg is then a strict quotient-linear chain map to Q_n, and the
quasi-isomorphism supplies its identification with T.M(n+1). Composing successors
and transposing gives a complex Q of quotient systems. Its finite evaluations
have the isomorphisms a below; the cocycle gives their coherence for all h. Restriction
to the completed ring and T have the same evaluated transitions by a's coherence
and T.tower_tau. Sequential tower fullness lifts that compatible family to an
isomorphism, since all evaluations are invertible. This step concerns one fixed
tower, so no functorial choice of such lifts is used. Apply the sequence-site
scalar tensor-restriction adjunction to identify Hom from the constant completed
input into restricted Q with quotient-linear Hom from its derived reduction.
The normalized reduction adjunction identifies that reduction with S.reduction.
The section-preserving constant-sequence equivalence and derived scalar-section
square identify the actual R-linear section towers. These comparisons are natural
in the input before localization: precomposition is a map of the same Hom
complexes. They therefore give the last natural isomorphism for every S. For a
zero tower or empty scheme all constructions remain the zero complexes. -/
theorem integralDualizing_mapping_tower_system_model
    (T : NormalizedDVRTower l E X D hl) :
    ∃ (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
      (a : ∀ n : ℕ, T.M n ≅
        (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q)),
      (∀ {m n : ℕ} (h : n ≤ m),
        T.tau h ≫ (normalizedDVRRes l E X h).map (a n).hom =
          (a m).hom ≫ (coefficientSequenceDerivedTransition l E X h).app
            (coefTraceInput l E X Q)) ∧
      ∀ S : CoefficientDerivedSystemCalculus l E X,
        Nonempty (integralDualizingMappingTower l E X T.tower ≅
          (sfIntegralConstructible l E X).ι.op ⋙ coefPairingHom l E X S Q) := by
  obtain ⟨Q, a, ha, ⟨b⟩⟩ := normalizedDVR_quotient_system_realization l E X D hl T
  refine ⟨Q, a, ha, ?_⟩
  intro S
  obtain ⟨c⟩ := coefHom_scalar_naturality l E X Q S
  let H := (Functor.curry.obj (coefHomConstantInternalHom l E X)).flip
  let e := H.mapIso ((coefHomEquivalence l E X).inverse.mapDerivedCategory.mapIso b)
  let d := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (coefHomDerivedConstant l E X).op e)
    (coefHomConstantDerivedSections l E X)
  exact ⟨Functor.isoWhiskerLeft (sfIntegralConstructible l E X).ι.op (d ≪≫ c)⟩

end WeilConjectures
